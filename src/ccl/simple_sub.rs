//! Simple-sub algorithm core: the constraint solver.
//!
//! The solver operates **directly on [`crate::ccl::Type`]** — there is no
//! separate internal type representation. An inference variable is a
//! [`Type::Infer`] carrying a mutable [`crate::ccl::InferVar`] (lower/upper
//! bound lists); `constrain_subtype` mutates those bounds in place, and the
//! `compact`/`simplify`/`coalesce` pipeline resolves a bound graph back into
//! a concrete `Type`. The only intermediate is the internal `CompactType`
//! used by simplification.
//!
//! # Refinements
//!
//! Refinements ride the lattice natively as **refinement-tag sets**. A
//! refined type `{T | S}` carries a set `S` of [`Refinement`] tags
//! (matched by structural predicate equality — see [`Refinement`]'s
//! `PartialEq` — but never by predicate implication). Subtyping is
//! superset-on-tags, structurally identical to record width-subtyping
//! (`{T | p, q} <: {T | p}`, and `{T | p} <: T`); a tag set therefore
//! merges with the same polarity rule as `rec` (positive ⇒ intersect,
//! negative ⇒ union) and is preserved verbatim through simplification
//! (tags are positional, never folded into a variable's identity, so
//! co-occurrence merging cannot move or drop them). A refinement is
//! *required*, so `constrain_subtype` is strict in the other
//! direction: an unrefined value does **not** flow into a refined position
//! (`T ⊀ {T | p}`). Acquiring a refinement is an explicit operation — the
//! interpreter compiles a refinement on a *collection domain* to a runtime
//! `Restrict`/`Filter` at the iteration boundary
//! ([`crate::interpreter::operator_conversion`]'s `iterate_type`); it is not
//! modelled as subsumption here. The predicate `Expr` of each tag lives in
//! [`crate::ccl::Refinement`] and is inferred/coalesced like any other
//! sub-tree.
//!
//! # Reference
//!
//! Implements the algorithm from Parreaux, "The Simple Essence of Algebraic
//! Subtyping" (ICFP 2020).

// The `constrain` cycle cache keys on `(Type, Type)`. `Type` has interior
// mutability (an `Infer` var's `RefCell` bounds), but its `Hash`/`Eq` are
// identity-by-`uid` and never inspect the bounds — so mutating a variable's
// bounds during solving cannot change a key's hash. The lint's hazard
// therefore doesn't apply here.
#![allow(clippy::mutable_key_type)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::subst::Subst;
use crate::ccl::{
    BaseType, Bound, InferVar, InferVarId, Level, Refinement, Type, fresh_infer_var_id,
};

/// Identifies a field inside a structural record/tuple, or a variant tag.
///
/// `Index` is used for tuple-shaped records (positional projection);
/// `Name` for named-field records. The constrain_subtype solver treats them
/// uniformly under width-subtyping; the closed-tuple-vs-record
/// distinction is materialized only at coalesce time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldKey {
    /// Positional field (tuple index).
    Index(usize),
    /// Named field.
    Name(SmolStr),
}

impl std::fmt::Display for FieldKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // Positional keys render as a bare index, matching tuple/record
            // projection (`.0`, `.1`); the dot prefix in tag/field contexts
            // is supplied by the caller, so a positional sum reads `.0`, `.1`.
            FieldKey::Index(n) => write!(f, "{n}"),
            FieldKey::Name(s) => write!(f, "{s}"),
        }
    }
}

/// The level of `ty` — the maximum scope level of any inference variable
/// occurring inside it. Leaves and `Hole` are level 0; `Refinement` defers
/// to its inner type (refinements are lattice-blind). Used by `extrude` and by
/// let-generalization (`infer_simple_sub::should_generalize`, which generalizes
/// a binding when its type's level exceeds the binding level).
pub fn type_level(ty: &Type) -> Level {
    match ty {
        Type::Infer(v) => v.level,
        Type::Fun {
            domain: d,
            codomain: c,
            ..
        } => type_level(d).max(type_level(c)),
        Type::Tuple(ts) => ts.iter().map(type_level).max().unwrap_or(0),
        Type::Record(fs) => fs.iter().map(|(_, t)| type_level(t)).max().unwrap_or(0),
        Type::Variant(tags) => tags.iter().map(|(_, t)| type_level(t)).max().unwrap_or(0),
        Type::Refinement(inner, _) => type_level(inner),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole => 0,
    }
}

/// Construct a fresh inference variable at the given level, as a [`Type`]
/// for direct use in constraint emission.
pub fn fresh_var(level: Level) -> Type {
    Type::Infer(InferVar::fresh(level))
}

/// Wrap a [`BaseType`] as a primitive [`Type`].
pub fn prim(b: BaseType) -> Type {
    Type::Base(b)
}

/// Build a function [`Type`] from domain and codomain.
pub fn fun(d: Type, c: Type) -> Type {
    Type::Fun {
        name: None,
        domain: Box::new(d),
        codomain: Box::new(c),
    }
}

// ---------------------------------------------------------------------------
// Polymorphic schemes
// ---------------------------------------------------------------------------

/// A polymorphic type scheme.
///
/// `body` may contain [`Type::Infer`] vars whose `level` exceeds `level`.
/// Those are the *quantified* variables — at each use site they are
/// replaced with fresh variables via [`PolyScheme::instantiate`]. Vars
/// whose level is ≤ `level` leaked in from an outer scope and stay fixed.
///
/// # Usage
///
/// Two sources of schemes: (1) operator/projection signatures that are
/// inherently polymorphic (`Compare : ∀α. α → α → Bool`,
/// `Proj(Index n) : ∀α. {n: α, …} → α`, etc.), built once in
/// `OperatorSchemes`; and (2) let-generalization — a multi-use function
/// binding is generalized into a `PolyScheme` at its binding level
/// (`infer_simple_sub::scoped_let`) and `instantiate`d per use. See
/// `design-simple-sub.md` for the rationale.
#[derive(Debug, Clone)]
pub struct PolyScheme {
    /// Quantification cutoff: vars in `body` at level > `self.level`
    /// are universally quantified.
    pub level: Level,
    /// Scheme body. May contain quantified vars (level > self.level)
    /// and free vars (level ≤ self.level).
    pub body: Type,
}

impl PolyScheme {
    /// A monotype scheme: no quantified variables. Convenience for
    /// scalar operator types like `Bool → Bool`.
    pub fn mono(body: Type) -> Self {
        Self { level: 0, body }
    }

    /// Construct a polytype with the given quantification cutoff.
    pub fn poly(level: Level, body: Type) -> Self {
        Self { level, body }
    }

    /// Mint a fresh copy of `body` with quantified variables replaced
    /// by fresh variables at `current_level`.
    ///
    /// Called at every use site of the scheme to ensure each occurrence
    /// gets independent constraints (e.g. two uses of `Compare` can
    /// compare `Int`s and `String`s respectively without conflict).
    pub fn instantiate(&self, current_level: Level) -> Type {
        freshen_above(
            self.level,
            &self.body,
            FreshenLevel::At(current_level),
            &mut HashMap::new(),
        )
    }
}

/// Cache for [`freshen_above`], mapping each original quantified
/// variable to its single fresh replacement so multiple occurrences
/// share the same fresh var.
pub type FreshenCache = HashMap<InferVarId, Rc<InferVar>>;

/// The level [`freshen_above`] assigns to each fresh variable it mints.
#[derive(Clone, Copy)]
pub enum FreshenLevel {
    /// Mint every fresh variable at this one level. Use-site instantiation
    /// wants the copy to live at the *use's* level so it integrates with that
    /// site's constraints.
    At(Level),
    /// Mint each fresh variable at its *original* variable's level, preserving
    /// the relative level structure. Per-type specialization (the
    /// `infer_simple_sub::monomorphize` pass) wants this: a definition may
    /// contain nested generalized `let`s whose deeper levels must survive, or
    /// the inner generalization stops being recognized.
    Preserve,
}

/// Walk `ty` and replace every variable at level > `lim` with a fresh
/// variable (level chosen by `target`). Variables at level ≤ `lim` are kept
/// as-is — they're free in the surrounding scope, not quantified.
///
/// The bounds of each quantified variable are themselves freshened
/// (recursively), so the fresh copy carries the same constraints as the
/// original.
pub fn freshen_above(
    lim: Level,
    ty: &Type,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Type {
    if type_level(ty) <= lim {
        return ty.clone();
    }
    match ty {
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole => ty.clone(),
        Type::Fun {
            name,
            domain: d,
            codomain: c,
        } => Type::Fun {
            name: name.clone(),
            domain: Box::new(freshen_above(lim, d, target, cache)),
            codomain: Box::new(freshen_above(lim, c, target, cache)),
        },
        Type::Tuple(ts) => Type::Tuple(
            ts.iter()
                .map(|t| freshen_above(lim, t, target, cache))
                .collect(),
        ),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), freshen_above(lim, t, target, cache)))
                .collect(),
        ),
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), freshen_above(lim, t, target, cache)))
                .collect(),
        ),
        Type::Refinement(inner, r) => Type::Refinement(
            Box::new(freshen_above(lim, inner, target, cache)),
            // O2 (deferred): the predicate is shared by `Rc` across instantiations
            // rather than copied with its type slots freshened through this same
            // `cache`. That is only load-bearing for a *polymorphic* (let-
            // generalized) refined value used at several types — the prototype's
            // scenario M. Our dependent refinements are introduced monomorphically
            // (group-by, comprehension filters), so freshening never crosses a
            // refined value today; the design (O2/O3) flags faithful copy-and-
            // freshen of predicate type slots as the separable polymorphic-case
            // requirement. Doing it safely needs a refinement-cycle guard (a
            // predicate's slot may reference its own refined type), so it is left
            // for the polymorphic-dependent-function work rather than rushed here.
            r.clone(),
        ),
        Type::Infer(tv) => {
            if let Some(existing) = cache.get(&tv.uid) {
                return Type::Infer(Rc::clone(existing));
            }
            // Mint the fresh variable at the level `target` dictates: the use
            // site's level (`At`) or the original's own level (`Preserve`).
            let new_level = match target {
                FreshenLevel::At(level) => level,
                FreshenLevel::Preserve => tv.level,
            };
            let v = InferVar::fresh(new_level);
            cache.insert(tv.uid, Rc::clone(&v));

            // Snapshot bounds before recursing — the recursion may touch
            // other variables but must not see partially-mutated state.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                (s.lower.clone(), s.upper.clone())
            };
            // Freshen the bound's type; the edge substitution rides along
            // unchanged here (its own type slots are freshened in the
            // predicate-freshening stage).
            let new_lows: Vec<_> = lows
                .iter()
                .map(|b| Bound {
                    ty: freshen_above(lim, &b.ty, target, cache),
                    subst: b.subst.clone(),
                })
                .collect();
            let new_ups: Vec<_> = ups
                .iter()
                .map(|b| Bound {
                    ty: freshen_above(lim, &b.ty, target, cache),
                    subst: b.subst.clone(),
                })
                .collect();
            {
                let mut s = v.bounds.borrow_mut();
                s.lower = new_lows;
                s.upper = new_ups;
            }
            Type::Infer(v)
        }
    }
}

// ---------------------------------------------------------------------------
// Constraint solver
// ---------------------------------------------------------------------------

/// Errors raised by [`constrain_subtype`].
///
/// Mapped onto [`crate::ccl::infer::InferError`] by the constraint emitter
/// at use sites.
#[derive(Debug, Clone)]
pub enum ConstrainError {
    /// `lhs` and `rhs` cannot be related by the subtyping rules of
    /// [`Type`] — e.g. two distinct primitives, a function compared
    /// to a record, etc.
    Mismatch {
        /// The offending lhs type.
        lhs: Type,
        /// The offending rhs type.
        rhs: Type,
    },
    /// A record/tuple-on-record/tuple constraint required a field/position
    /// that lhs did not have. Width-subtyping says rhs's keys must be a
    /// subset of lhs's; this is the violation.
    MissingField {
        /// The missing key.
        key: FieldKey,
        /// The lhs record/tuple that should have contained the key.
        in_type: Type,
    },
    /// A variant-on-variant constraint had a tag in lhs that rhs did
    /// not accept. The dual of [`Self::MissingField`]: variant width-
    /// subtyping inverts records, so rhs's tag set must be a *super*set
    /// of lhs's, and the violation is an *extra* tag on lhs rather than a
    /// missing field.
    ExtraTag {
        /// The tag present in lhs but not accepted by rhs.
        tag: FieldKey,
        /// The rhs variant that should have accepted the tag.
        in_type: Type,
    },
}

/// Cache of in-progress subtyping checks. Breaks cycles introduced through
/// variable bounds.
///
/// Keyed by the `(lhs, rhs)` pair *by value*. Identity at [`Type::Infer`] is
/// by `uid` (see [`InferVar`]), so this is cycle-safe (a recursive type's
/// graph re-enters through a shared `Infer`, whose hash/eq stop at the uid)
/// and de-dups structurally-equal constraints. Only var-involving pairs are
/// inserted; purely-structural constraints are finite trees that bottom out.
pub type ConstrainCache = HashSet<(Type, Type)>;

/// Cache for [`extrude`], keyed by the polar pair (variable uid, polarity).
///
/// Each polarity gets its own extruded copy so positive and negative
/// occurrences of the same variable can be approximated independently
/// (see Parreaux 2020 §3.4).
pub type ExtrudeCache = HashMap<(InferVarId, bool), Rc<InferVar>>;

/// Constrain `lhs <: rhs`, mutating variable bounds in place.
///
/// The cache argument breaks cycles; pass a fresh empty `HashSet` at
/// the top of each constraint emission and reuse it for the recursive
/// subtyping the rule fires.
pub fn constrain_subtype(
    lhs: &Type,
    rhs: &Type,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    constrain_go(lhs, rhs, &Subst::id(), cache)
}

/// Constrain `lhs <: rhs` under a correspondence `sigma : ctx(lhs) → ctx(rhs)`
/// that aligns the two sides' Pi binders.
///
/// `sigma` is `Subst::id()` for ordinary monomorphic constraints — in which
/// case every arm below reduces exactly to the substitution-free solver. A
/// non-identity `sigma` is *derived* when constraining two function types
/// whose codomains mention their binders (the Pi-vs-Pi arm mints the binder
/// correspondence) and is recorded on the constraint edges so the coalesce
/// walk can compose it (design §3.6).
///
/// Edge-storage convention: a `Bound { ty, subst }` recorded on variable `V`
/// reads, in `V`'s context, as `subst.apply(ty)` — i.e. `subst : ctx(ty) →
/// ctx(V)`. Lower edges therefore carry `sigma` (source `lhs` → holder `V`);
/// upper edges carry `sigma⁻¹` (the holder is the source, so the morphism to
/// the bound is inverted). Only renames are inverted, which is why a
/// correspondence is always a rename.
fn constrain_go(
    lhs: &Type,
    rhs: &Type,
    sigma: &Subst,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // The trivial-equality short-circuit is only sound when the edge carries
    // no transformation — under a non-identity correspondence `lhs` and `rhs`
    // live in different contexts even when structurally equal.
    if sigma.is_id() && lhs == rhs {
        return Ok(());
    }

    // Cycle-break: only constraints involving variables can recur.
    // Non-variable structural types are regular trees; their constraints
    // bottom out without revisiting themselves. Key by value — identity at
    // `Infer` is by `uid`, so this is cycle-safe. The correspondence is not
    // part of the key: like the prototype's var-pair cache, deduping on the
    // `(lhs, rhs)` pair alone is what guarantees termination on cyclic edges.
    let either_var = matches!(lhs, Type::Infer(_)) || matches!(rhs, Type::Infer(_));
    if either_var && !cache.insert((lhs.clone(), rhs.clone())) {
        return Ok(());
    }

    match (lhs, rhs) {
        // Leaf types match by structural equality.
        (Type::Base(a), Type::Base(b)) if a == b => Ok(()),
        (Type::UIntRange(a), Type::UIntRange(b)) if a == b => Ok(()),
        (Type::DataSource(a), Type::DataSource(b)) if a == b => Ok(()),

        // Function: contravariant on domain, covariant on codomain. The
        // codomain edge *derives* the binder correspondence — aligning the two
        // Pi binders `k ↦ x` — and carries it onward (design §3.6); the domain
        // edge flips the correspondence with the polarity. When neither side is
        // a Pi (both names `None`) the correspondence is unchanged, so this is
        // exactly the ordinary contravariant/covariant rule.
        (
            Type::Fun {
                name: n0,
                domain: d0,
                codomain: c0,
            },
            Type::Fun {
                name: n1,
                domain: d1,
                codomain: c1,
            },
        ) => {
            // The domain edge flips sides, so the correspondence must run
            // rhs → lhs. A rename inverts exactly. A σ carrying a discharge
            // does not invert — and unlike the var arms' reverse-edge bounds
            // (which live in the post-discharge context, making the id
            // fallback exact there), the lhs domain here is a *pre*-discharge
            // type that may still mention the discharged binder. Transport it
            // forward into rhs context instead and compare under the identity.
            match sigma.invert() {
                Some(inv) => constrain_go(d1, d0, &inv, cache)?,
                None => constrain_go(d1, &sigma.apply_type(d0), &Subst::id(), cache)?,
            }
            let cod_sigma = match (n0, n1) {
                (Some(k), Some(x)) => sigma.extended_rename(k, x),
                _ => sigma.clone(),
            };
            constrain_go(c0, c1, &cod_sigma, cache)
        }

        // Tuple: positional width-subtyping. A longer/equal tuple is a
        // subtype, so every position rhs requires must exist in lhs.
        (Type::Tuple(a), Type::Tuple(b)) => {
            for (i, t1) in b.iter().enumerate() {
                match a.get(i) {
                    Some(t0) => constrain_go(t0, t1, sigma, cache)?,
                    None => {
                        return Err(ConstrainError::MissingField {
                            key: FieldKey::Index(i),
                            in_type: lhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // Record: named width-subtyping. rhs's fields must all appear in lhs.
        (Type::Record(a), Type::Record(b)) => {
            for (name, t1) in b {
                match a.iter().find(|(n, _)| n == name) {
                    Some((_, t0)) => constrain_go(t0, t1, sigma, cache)?,
                    None => {
                        return Err(ConstrainError::MissingField {
                            key: FieldKey::Name(SmolStr::from(name.as_str())),
                            in_type: lhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // Variant: width-subtyping is the dual. lhs's tags must all appear
        // in rhs (with a payload subtype check). Payload depth is covariant.
        (Type::Variant(a), Type::Variant(b)) => {
            for (k, t0) in a {
                match b.iter().find(|(bk, _)| bk == k) {
                    Some((_, t1)) => constrain_go(t0, t1, sigma, cache)?,
                    None => {
                        return Err(ConstrainError::ExtraTag {
                            tag: k.clone(),
                            in_type: rhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // Variable on lhs, rhs has compatible level: append rhs to upper
        // bounds (stored in `lv`'s context, so under `sigma⁻¹`), propagate to
        // all known lower bounds (composing each lower edge with `sigma`).
        (Type::Infer(lv), _) if type_level(rhs) <= lv.level => {
            let lows = {
                let mut s = lv.bounds.borrow_mut();
                s.upper
                    .push(Bound::with_subst(rhs.clone(), sigma.invert_or_id()));
                s.lower.clone()
            };
            for low in lows {
                constrain_go(&low.ty, rhs, &Subst::then(&low.subst, sigma), cache)?;
            }
            Ok(())
        }

        // Variable on rhs, lhs has compatible level: append lhs to lower
        // bounds (stored in `rv`'s context, so under `sigma`), propagate to
        // all known upper bounds (composing each upper edge's inverse).
        (_, Type::Infer(rv)) if type_level(lhs) <= rv.level => {
            let ups = {
                let mut s = rv.bounds.borrow_mut();
                s.lower.push(Bound::with_subst(lhs.clone(), sigma.clone()));
                s.upper.clone()
            };
            for up in ups {
                constrain_go(
                    lhs,
                    &up.ty,
                    &Subst::then(sigma, &up.subst.invert_or_id()),
                    cache,
                )?;
            }
            Ok(())
        }

        // Level mismatch: variable's level is below the other side's.
        // Lift the other side down via extrude and retry.
        (Type::Infer(lv), _) => {
            let new_rhs = extrude(rhs, false, lv.level, &mut ExtrudeCache::new());
            constrain_go(lhs, &new_rhs, sigma, cache)
        }
        (_, Type::Infer(rv)) => {
            let new_lhs = extrude(lhs, true, rv.level, &mut ExtrudeCache::new());
            constrain_go(&new_lhs, rhs, sigma, cache)
        }

        // Refinement subtyping:
        //   {b₁ | S₁} <: {b₂ | S₂}  iff  b₁ <: b₂  and  σ(S₂) ⊆ σ(S₁) ∪ tags(b₁)
        // (more refinements ⇒ subtype). Refinements match by [`Refinement`]'s
        // `PartialEq` — structural predicate equality — so a tag join planning
        // re-minted in a fresh cell still matches; never by predicate
        // implication. The two sides live in different binder contexts, so an
        // lhs tag is transported through the correspondence (`σ(S₁)`, via
        // [`Subst::force_refinement`]) before comparing: a predicate mentioning
        // a Pi binder matches its renamed — or, when a discharge edge composed
        // into σ on the way through a variable, *discharged* — copy on the
        // rhs. Under the identity this is plain structural equality. The lhs
        // carries every
        // refinement rhs requires when its explicit layers `S₁` plus whatever
        // its *base* `b₁` carries cover `S₂`.
        //
        // `peel_refinements` strips the explicit layers down to the bases, so a
        // top-level refinement whose base is a variable reaches here rather than
        // the var arms above. That base variable can still acquire the deficit
        // `S₂ \ S₁`, so we flow it onto the variable (`b₁ <: {b₂ | deficit}`)
        // rather than rejecting — the refinement analog of how the
        // record/function arms thread structure through variables. The
        // requirement then fails later iff the variable resolves to a concrete
        // base lacking those tags. Without this, a value that is *already*
        // refined could never be cast to add a further tag (nested
        // list-comprehension filters: `{D|p} ⇒ V <: {?a|q} ⇒ V`), even though
        // the assignment `?a := {D|p}` exists.
        //
        // When `b₁` is *concrete* and the deficit is non-empty it is a genuine
        // mismatch: an unrefined value cannot stand in where a refined one is
        // demanded (`T ⊀ {T|p}`), and a value refined by S₁ cannot carry a
        // *different* refinement it lacks (`{T|q} ⊀ {T|p}`). Acquiring a
        // refinement on a concrete value is an explicit `Restrict`, not
        // subsumption.
        (Type::Refinement(..), _) | (_, Type::Refinement(..)) => {
            let (lbase, lrefs) = peel_refinements(lhs);
            let (rbase, rrefs) = peel_refinements(rhs);
            // The refinements rhs requires that no σ-transported lhs layer
            // matches (by `Refinement`'s structural `PartialEq`).
            let lrefs_in_rhs_ctx: Vec<Refinement> =
                lrefs.iter().map(|l| sigma.force_refinement(l)).collect();
            let deficit: Vec<&Refinement> = rrefs
                .iter()
                .copied()
                .filter(|r| !lrefs_in_rhs_ctx.contains(r))
                .collect();
            if deficit.is_empty() {
                // lhs's explicit layers already supply every refinement rhs requires.
                constrain_go(lbase, rbase, sigma, cache)
            } else if matches!(lbase, Type::Infer(_)) {
                // Variable base: flow the deficit onto it (`b₁ <: {b₂ | deficit}`)
                // rather than rejecting; it fails later iff the variable
                // resolves to a concrete base lacking those tags.
                let demanded = wrap_refinements(rbase, &deficit);
                constrain_go(lbase, &demanded, sigma, cache)
            } else {
                Err(ConstrainError::Mismatch {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })
            }
        }

        _ => Err(ConstrainError::Mismatch {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }),
    }
}

/// Peel all outer [`Type::Refinement`] layers, returning the bare base type
/// and the refinement tags carried by the peeled layers (outermost first).
fn peel_refinements(ty: &Type) -> (&Type, Vec<&Refinement>) {
    let mut refs = Vec::new();
    let mut cur = ty;
    while let Type::Refinement(inner, r) = cur {
        refs.push(r);
        cur = inner;
    }
    (cur, refs)
}

/// Re-wrap `base` in the given [`Type::Refinement`] layers (passed
/// outermost-first), preserving their order.
///
/// Used by [`constrain_subtype`]'s refinement arm to rebuild the deficit
/// refinement `{rbase | S₂ \ S₁}` from the rhs's own layers, so the kept tags
/// retain their real [`crate::ccl::Refinement`] payloads (predicate `Rc`s).
fn wrap_refinements(base: &Type, refs: &[&Refinement]) -> Type {
    refs.iter().rev().fold(base.clone(), |acc, r| {
        Type::Refinement(Box::new(acc), (*r).clone())
    })
}

/// Lift `ty` so that all its variables live at level ≤ `target_level`.
///
/// When a constraint crosses level boundaries (e.g. an outer-scope variable
/// gets constrained against an inner-scope type), variables at higher
/// levels must be approximated by fresh variables at the target level so
/// the constraint can be recorded locally. `pol` selects which bound to
/// preserve: positive (`true`) keeps the lower bound, negative (`false`)
/// keeps the upper bound.
///
/// Outside generalized `let`s every variable shares level 0, so extrude is a
/// no-op there; it fires for real once let-generalization (`scoped_let`) mints
/// RHS variables at a deeper level and a cross-level constraint arises (the
/// constrain_subtype solver's level-mismatch branches).
pub fn extrude(ty: &Type, pol: bool, target_level: Level, cache: &mut ExtrudeCache) -> Type {
    if type_level(ty) <= target_level {
        return ty.clone();
    }
    match ty {
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole => ty.clone(),
        Type::Fun {
            name,
            domain: d,
            codomain: c,
        } => Type::Fun {
            name: name.clone(),
            domain: Box::new(extrude(d, !pol, target_level, cache)),
            codomain: Box::new(extrude(c, pol, target_level, cache)),
        },
        Type::Tuple(ts) => Type::Tuple(
            ts.iter()
                .map(|t| extrude(t, pol, target_level, cache))
                .collect(),
        ),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), extrude(t, pol, target_level, cache)))
                .collect(),
        ),
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                // Variant payloads are covariant — same polarity, no flip.
                .map(|(k, t)| (k.clone(), extrude(t, pol, target_level, cache)))
                .collect(),
        ),
        Type::Refinement(inner, r) => Type::Refinement(
            Box::new(extrude(inner, pol, target_level, cache)),
            r.clone(),
        ),
        Type::Infer(tv) => {
            if let Some(existing) = cache.get(&(tv.uid, pol)) {
                return Type::Infer(Rc::clone(existing));
            }
            // Conservative approximation: a fresh variable at the target
            // level, linked to the original by the appropriate bound.
            let nvs = InferVar::fresh(target_level);
            cache.insert((tv.uid, pol), Rc::clone(&nvs));

            // Snapshot the bounds we'll need to extrude before we mutate
            // the original; otherwise we'd race the borrow checker.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                (s.lower.clone(), s.upper.clone())
            };

            if pol {
                // Positive: original flows into new var. Original gains
                // `nvs` as an upper bound; new var inherits original's
                // lower bounds (extruded at the same polarity).
                tv.bounds
                    .borrow_mut()
                    .upper
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|b| Bound {
                        ty: extrude(&b.ty, pol, target_level, cache),
                        subst: b.subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().lower = new_lows;
            } else {
                // Negative: new var flows into original. Original gains
                // `nvs` as a lower bound; new var inherits original's
                // upper bounds.
                tv.bounds
                    .borrow_mut()
                    .lower
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|b| Bound {
                        ty: extrude(&b.ty, pol, target_level, cache),
                        subst: b.subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().upper = new_ups;
            }
            Type::Infer(nvs)
        }
    }
}

// ---------------------------------------------------------------------------
// Coalesce: CompactGraph -> ccl::Type
// ---------------------------------------------------------------------------

/// Errors raised by [`coalesce_compact`].
///
/// These are reported back to the caller and ultimately mapped onto
/// [`crate::ccl::infer::InferError`].
#[derive(Debug, Clone)]
pub enum CoalesceError {
    /// A variable's bounds at a positive position (or the upper bounds at
    /// a negative position) included multiple incompatible structural
    /// types — e.g. `Int` and `String` both flowing into the same value.
    /// The solver rejects this rather than inventing an anonymous (untagged)
    /// sum from the collision — a genuinely tagged `Variant` is a single
    /// shape and never triggers this.
    IncompatibleBounds {
        /// `true` = positive polarity (lower bounds forming a union);
        /// `false` = negative polarity (upper bounds forming an intersection).
        polarity: bool,
        /// UIDs of the simple-sub variables that contributed these bounds.
        vars: Vec<InferVarId>,
        /// Pretty representation of the conflicting bounds.
        details: String,
    },
    /// A record-shaped variable still had open width at coalesce time —
    /// no closing equality constraint pinned its full set of fields.
    /// Mirrors today's `UnresolvedPartial` error so existing callers see
    /// the same error semantics.
    UnresolvedPartial {
        /// Whether the open record is index-keyed (tuple) or name-keyed
        /// (record), for diagnostic clarity.
        kind: PartialKind,
        /// Pretty representation of the partial fields.
        details: String,
    },
    /// A recursive (cyclic) type was inferred. The solver deliberately
    /// rejects these per the plan's R2 review note; they would otherwise
    /// silently arise from programs like `λx. x x`.
    RecursiveType {
        /// Pretty representation of the cycle entry point.
        details: String,
    },
}

/// Distinguishes a partial tuple (Index keys) from a partial record
/// (Name keys) for [`CoalesceError::UnresolvedPartial`] diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialKind {
    /// Index-keyed; would coalesce to `Type::Tuple` if dense and closed.
    Tuple,
    /// Name-keyed; would coalesce to `Type::Record` if closed.
    Record,
}

// ---------------------------------------------------------------------------
// CompactType + compact_type: bound-graph flattening
// ---------------------------------------------------------------------------
//
// `compact_type` walks a `Type` and produces a `CompactType` per
// position, transitively expanding variable bounds at the appropriate
// polarity and merging structurally (records by union/intersection of
// fields, functions by polar recursion).
//
// `simplify_type` — the polar co-occurrence analyzer that merges
// redundant variables — is implemented and wired between `compact_type`
// and `coalesce_compact`. The one stubbed path is recursive-variable
// merging (guarded by `rec_vars.contains_key`), which only fires when
// recursive types are present; it is deferred until those are supported.

/// "Atomic" leaf-shaped types other than functions and records.
///
/// CompactType bundles all of these into a single set per position;
/// merging two CompactTypes unions their atom sets, which is the
/// correct behavior at both polarities (atomic types are nominal —
/// `Int` and `String` either match or don't, no field-level subtyping).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomKey {
    /// Primitive (Int, UInt, String, Bool, Unit).
    Prim(BaseType),
    /// Finite index range `[0, n)`.
    UIntRange(usize),
    /// Externally-registered data source.
    Source(SmolStr),
}

impl AtomKey {
    fn from_type(ty: &Type) -> Option<AtomKey> {
        match ty {
            Type::Base(b) => Some(AtomKey::Prim(b.clone())),
            Type::UIntRange(n) => Some(AtomKey::UIntRange(*n)),
            Type::DataSource(n) => Some(AtomKey::Source(SmolStr::from(n.as_str()))),
            _ => None,
        }
    }

    fn to_type(&self) -> Type {
        match self {
            AtomKey::Prim(b) => Type::Base(b.clone()),
            AtomKey::UIntRange(n) => Type::UIntRange(*n),
            AtomKey::Source(n) => Type::DataSource(n.to_string()),
        }
    }
}

/// Flat per-position representation of a type.
///
/// At positive position, this conceptually represents a *union* of the
/// listed components (`vars ⊔ atoms ⊔ rec ⊔ fun`). At negative
/// position, an *intersection*. Cambra's output type system supports
/// neither directly, so [`coalesce_compact`] picks a single concrete
/// type from these bag-of-types contributions and errors on conflict.
#[derive(Debug, Clone, Default)]
pub struct CompactType {
    /// Variable contributions from this position. Multiple variables
    /// can co-occur (e.g. when two projection morphisms both flow into
    /// the same parameter, both record-vars accumulate here).
    pub vars: BTreeSet<InferVarId>,
    /// Atomic-type contributions.
    pub atoms: BTreeSet<AtomKey>,
    /// Record fields, if any. At positive polarity these are
    /// intersected (kept only when both sides have the field); at
    /// negative, unioned (kept when either side has the field).
    ///
    /// `None` and `Some(empty)` are **distinct** and both load-bearing in
    /// [`merge`](Self::merge): `None` means "no record component here" and
    /// acts as the merge *identity* (the other side passes through
    /// untouched — it imposes nothing, i.e. ⊤). `Some(map)` means a record
    /// shape is present; `Some(empty)` specifically arises from
    /// *intersecting* two disjoint field sets at positive polarity and is
    /// the *absorbing* element, not the identity. Collapsing to a bare
    /// `BTreeMap` would conflate the two, and the intersect identity (⊤)
    /// has no finite-map representation anyway.
    pub rec: Option<BTreeMap<FieldKey, CompactType>>,
    /// Variant tags, if any. The polarities are the **dual** of `rec`:
    /// at positive polarity tags are *unioned* (a producer of `[A]` or
    /// `[B]` could emit `[A, B]`); at negative polarity tags are
    /// *intersected* (a consumer accepting `[A, B]` AND `[B, C]` only
    /// reliably handles `[B]`). Payload merge for matching tags uses
    /// the same polarity as the outer merge (covariant depth).
    ///
    /// `None` vs `Some(empty)` carry the same distinct meanings as for
    /// [`rec`](Self::rec) — `None` is the merge identity, `Some(empty)`
    /// the absorbing element (here from intersecting disjoint tag sets at
    /// negative polarity).
    pub var: Option<BTreeMap<FieldKey, CompactType>>,
    /// Function shape, if any: an optional Pi binder name plus the domain
    /// and codomain. Recursively merged with polarity flip on the domain.
    /// The name is preserved so a dependent codomain's refinement predicate
    /// keeps its binder bound through coalesce; it is stripped at
    /// materialization when the codomain does not actually reference it
    /// (keeping ordinary functions `name: None`).
    pub fun: Option<(Option<String>, Box<CompactType>, Box<CompactType>)>,
    /// Refinement-tag contributions at this position. A set with `==`
    /// membership (deduplicated by [`Refinement`]'s structural `PartialEq`),
    /// stored as a `Vec` in first-insertion order. A refinement-set is
    /// width-subtyped exactly like `rec`: more refinements ⇒ subtype
    /// (`{T | p, q} <: {T | p}`), so at positive polarity the sets are
    /// *intersected* and at negative *unioned* (see
    /// [`CompactType::merge`]). The stored [`Refinement`] is the payload
    /// carried to coalesce.
    pub refinements: Vec<Refinement>,
}

impl CompactType {
    fn empty() -> Self {
        Self::default()
    }

    /// Merge two CompactTypes at the given polarity.
    ///
    /// - `vars`, `atoms`: union (always).
    /// - `rec`: at positive polarity, *intersect* keys (a value of both
    ///   `{a, b}` and `{a, c}` is reliably only `{a}`); at negative,
    ///   *union* keys.
    /// - `fun`: recursively merge each side, flipping polarity on the
    ///   domain.
    fn merge(pol: bool, lhs: CompactType, rhs: CompactType) -> CompactType {
        let mut vars = lhs.vars;
        vars.extend(rhs.vars);
        let mut atoms = lhs.atoms;
        atoms.extend(rhs.atoms);
        let rec = match (lhs.rec, rhs.rec) {
            // `None` is the identity: a position with no record component
            // imposes nothing, so the other side passes through. A present
            // `Some(empty)` is *not* identity — see the `rec` field docs.
            (None, r) | (r, None) => r,
            (Some(a), Some(b)) => Some(Self::merge_records(pol, a, b)),
        };
        let var = match (lhs.var, rhs.var) {
            (None, v) | (v, None) => v,
            (Some(a), Some(b)) => Some(Self::merge_variants(pol, a, b)),
        };
        let fun = match (lhs.fun, rhs.fun) {
            (None, f) | (f, None) => f,
            (Some((na, la, ra)), Some((nb, lb, rb))) => Some((
                // Prefer a present binder name; two distinct names at one
                // position only arise for unrelated functions merging, where
                // either is as good (the name is stripped at coalesce unless
                // the codomain references it).
                na.or(nb),
                Box::new(Self::merge(!pol, *la, *lb)),
                Box::new(Self::merge(pol, *ra, *rb)),
            )),
        };
        let refinements = Self::merge_refinements(pol, lhs.refinements, rhs.refinements);
        CompactType {
            vars,
            atoms,
            rec,
            var,
            fun,
            refinements,
        }
    }

    /// Merge two refinement-tag sets. The set-op tracks
    /// polarity the same way `rec` does — positive ⇒ *intersect*,
    /// negative ⇒ *union* — because refinement-sets width-subtype like
    /// record fields (more refinements ⇒ subtype). At a positive
    /// position the value reliably carries only the tags *both*
    /// sides guarantee; at a negative position a consumer that may
    /// impose either set imposes their union.
    fn merge_refinements(pol: bool, lhs: Vec<Refinement>, rhs: Vec<Refinement>) -> Vec<Refinement> {
        if pol {
            // The types are being unioned, so the refinement tags should be intersected.
            lhs.into_iter().filter(|r| rhs.contains(r)).collect()
        } else {
            // The types are being intersected, so the refinement tags should be unioned.
            let mut out = lhs;
            for r in rhs {
                if !out.contains(&r) {
                    out.push(r);
                }
            }
            out
        }
    }

    /// Merge two variant-tag maps. Variant width-sub is the **dual** of
    /// records: at positive polarity tags are *unioned* (a producer of
    /// `[A]` OR `[B]` could emit either), at negative polarity they are
    /// *intersected* (a consumer accepting `[A,B]` AND `[B,C]` only
    /// reliably handles `[B]`). Payload depth at matching tags is
    /// covariant — payloads recurse at the outer polarity `pol`, not
    /// flipped.
    fn merge_variants(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // Variants invert the set-op vs records (so `!pol` selects
        // intersect-vs-union) but keep payload polarity at the outer
        // `pol` (covariant depth, same as records).
        Self::merge_keyed(!pol, pol, lhs, rhs)
    }

    /// Merge two record-field maps. At positive polarity fields are
    /// *intersected* (the union of two record values has at least the
    /// fields common to both), at negative polarity they are *unioned*
    /// (a function accepting both `{a,b}` and `{a,c}` accepts `{a,b,c}`).
    /// Payload depth at matching fields is covariant — payloads recurse
    /// at the outer polarity `pol`.
    fn merge_records(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // For records the set-op aligns with polarity (pos = intersect)
        // and payload polarity also tracks `pol` (covariant depth).
        Self::merge_keyed(pol, pol, lhs, rhs)
    }

    /// Shared keyed-merge skeleton used by both records and variants.
    ///
    /// The two flags are independent because the relationship between
    /// the outer polarity and the *set operation on keys* differs
    /// between records (pos = intersect) and variants (pos = union),
    /// while the relationship between the outer polarity and *payload
    /// recursion* is the same in both (covariant depth, recurse at
    /// outer polarity).
    ///
    /// - `intersect_keys = true`: keep only keys present on both sides.
    /// - `intersect_keys = false`: keep keys present on either side.
    /// - `payload_pol`: polarity passed to the recursive
    ///   [`CompactType::merge`] for matching payloads.
    ///
    /// See [`Self::merge_records`] and [`Self::merge_variants`] for how
    /// outer polarity maps onto these two flags at each call site.
    fn merge_keyed<K: Ord + Clone>(
        intersect_keys: bool,
        payload_pol: bool,
        lhs: BTreeMap<K, CompactType>,
        rhs: BTreeMap<K, CompactType>,
    ) -> BTreeMap<K, CompactType> {
        let mut out = BTreeMap::new();
        if intersect_keys {
            for (k, v_lhs) in &lhs {
                if let Some(v_rhs) = rhs.get(k) {
                    out.insert(
                        k.clone(),
                        Self::merge(payload_pol, v_lhs.clone(), v_rhs.clone()),
                    );
                }
            }
        } else {
            for (k, v_lhs) in lhs {
                let merged = match rhs.get(&k) {
                    Some(v_rhs) => Self::merge(payload_pol, v_lhs, v_rhs.clone()),
                    None => v_lhs,
                };
                out.insert(k, merged);
            }
            for (k, v_rhs) in rhs {
                out.entry(k).or_insert(v_rhs);
            }
        }
        out
    }

    fn from_atom(a: AtomKey) -> Self {
        let mut atoms = BTreeSet::new();
        atoms.insert(a);
        Self {
            atoms,
            ..Self::default()
        }
    }

    fn from_var(uid: InferVarId) -> Self {
        let mut vars = BTreeSet::new();
        vars.insert(uid);
        Self {
            vars,
            ..Self::default()
        }
    }
}

/// Compact type with side-table of recursive variable definitions.
///
/// `rec_vars[uid]` holds the bound for a recursive variable; its
/// occurrences in `term` and elsewhere are represented by
/// `CompactType { vars: {uid}, .. }`. The solver rejects residual
/// recursive types at coalesce time (per plan R2), so non-empty
/// `rec_vars` is itself an error condition unless we're handling a
/// user-annotated recursive type — which we don't yet.
#[derive(Debug, Clone)]
pub struct CompactGraph {
    pub term: CompactType,
    pub rec_vars: BTreeMap<InferVarId, CompactType>,
}

/// Walk a `Type`, transitively expanding variable bounds at the
/// appropriate polarity, and produce a CompactType.
///
/// The `parents` set tracks variables whose bounds we are currently
/// walking, so that spurious cycles (`?a <: ?b` and `?b <: ?a`) — which
/// don't represent real recursive types — get pruned.
pub fn compact_type(ty: &Type) -> CompactGraph {
    let mut recursive: HashMap<(InferVarId, bool), InferVarId> = HashMap::new();
    let mut rec_vars: BTreeMap<InferVarId, CompactType> = BTreeMap::new();
    let term = compact_go(
        ty,
        true,
        &Subst::id(),
        &BTreeSet::new(),
        &mut HashSet::new(),
        &mut recursive,
        &mut rec_vars,
    );
    CompactGraph { term, rec_vars }
}

/// Compact `ty` at polarity `pol`, composing `subst_acc` — the substitution
/// accumulated from the edges walked so far — into every refinement predicate
/// materialized along the way. `subst_acc` is `Subst::id()` for ordinary
/// (non-dependent) types, in which case it is a perfect no-op and this behaves
/// exactly as the substitution-free solver. A non-identity accumulator arises
/// from Pi-binder correspondences and dependent-application discharges: each
/// bound edge composes its own `subst` in (`then(edge_subst, subst_acc)`), and
/// the composite is applied where a refinement predicate is reached — the
/// coalesce-time forcing of suspended substitutions (design §3.6).
fn compact_go(
    ty: &Type,
    pol: bool,
    subst_acc: &Subst,
    parents: &BTreeSet<InferVarId>,
    in_process: &mut HashSet<(InferVarId, bool)>,
    recursive: &mut HashMap<(InferVarId, bool), InferVarId>,
    rec_vars: &mut BTreeMap<InferVarId, CompactType>,
) -> CompactType {
    match ty {
        // Atomic types contribute a single atom. A term substitution never
        // touches an atom, so `subst_acc` is irrelevant here.
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) => {
            CompactType::from_atom(AtomKey::from_type(ty).unwrap())
        }
        // Refinements ride the lattice as a refinement-tag set: compact
        // the underlying type, then attach this layer's tag. Walking a
        // variable's bound that is `Refinement(D, r)` therefore unions `r`
        // into that variable's compacted position — the propagation path.
        // The accumulated substitution is *forced* here: it rewrites the
        // predicate's free binders (e.g. discharging a dependent application's
        // argument) before the tag lands in the position.
        Type::Refinement(inner, r) => {
            let mut ct = compact_go(
                inner, pol, subst_acc, parents, in_process, recursive, rec_vars,
            );
            let r = subst_acc.force_refinement(r);
            if !ct.refinements.contains(&r) {
                ct.refinements.push(r);
            }
            ct
        }
        // A bare `Hole` shouldn't reach the solver (emission turns it into a
        // fresh var), but treat it as no contribution for exhaustiveness.
        Type::Hole => CompactType::empty(),
        Type::Fun {
            name,
            domain: d,
            codomain: c,
        } => {
            // Function: domain is contravariant. A fresh `parents` set
            // per child mirrors Scala's `Set.empty` argument — cycles
            // span only one variable's bound chain, not across
            // function boundaries.
            let dom = compact_go(
                d,
                !pol,
                subst_acc,
                &BTreeSet::new(),
                in_process,
                recursive,
                rec_vars,
            );
            // A Pi binder shadows the accumulated substitution inside the
            // codomain (it binds the name locally), so restrict it there.
            let cod_acc = match name {
                Some(b) => subst_acc.shadow(b),
                None => subst_acc.clone(),
            };
            let cod = compact_go(
                c,
                pol,
                &cod_acc,
                &BTreeSet::new(),
                in_process,
                recursive,
                rec_vars,
            );
            CompactType {
                fun: Some((name.clone(), Box::new(dom), Box::new(cod))),
                ..Default::default()
            }
        }
        // Tuples and records share the structural `rec` representation,
        // keyed by `Index` and `Name` respectively.
        Type::Tuple(ts) => {
            let mut compacted = BTreeMap::new();
            for (i, v) in ts.iter().enumerate() {
                compacted.insert(
                    FieldKey::Index(i),
                    compact_go(
                        v,
                        pol,
                        subst_acc,
                        &BTreeSet::new(),
                        in_process,
                        recursive,
                        rec_vars,
                    ),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..Default::default()
            }
        }
        Type::Record(fs) => {
            let mut compacted = BTreeMap::new();
            for (n, v) in fs {
                compacted.insert(
                    FieldKey::Name(SmolStr::from(n.as_str())),
                    compact_go(
                        v,
                        pol,
                        subst_acc,
                        &BTreeSet::new(),
                        in_process,
                        recursive,
                        rec_vars,
                    ),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..Default::default()
            }
        }
        Type::Variant(tags) => {
            // Variant payloads are covariant — recurse at the same
            // polarity (no flip, unlike Fun's domain). The merge rule
            // for variants flips records' polarity behaviour, but
            // payload depth is unaffected.
            let mut compacted = BTreeMap::new();
            for (k, v) in tags {
                compacted.insert(
                    k.clone(),
                    compact_go(
                        v,
                        pol,
                        subst_acc,
                        &BTreeSet::new(),
                        in_process,
                        recursive,
                        rec_vars,
                    ),
                );
            }
            CompactType {
                var: Some(compacted),
                ..Default::default()
            }
        }
        Type::Infer(state) => {
            let uid = state.uid;
            let key = (uid, pol);
            if in_process.contains(&key) {
                if parents.contains(&uid) {
                    // Spurious cycle (a <: b and b <: a with no
                    // structural intermediary). Drop the bound.
                    return CompactType::empty();
                }
                // Real recursive cycle: mint a fresh UID to mark this slot.
                // We need only the identifier here — the cycle is surfaced
                // by `coalesce_compact` as a `RecursiveType` error before
                // any level-sensitive code observes it — so we don't
                // allocate a full `InferVar` (no bounds, no level value
                // to defend).
                let placeholder = *recursive.entry(key).or_insert_with(fresh_infer_var_id);
                return CompactType::from_var(placeholder);
            }
            in_process.insert(key);
            // The opposite-polarity fallback below is monomorphization's
            // coalesce-time *read* for a contravariant position. A function
            // domain is negative, so an argument flowing in (`arg <: domain`) is
            // recorded as a *lower* bound of the domain var — but negative
            // coalesce reads *upper* bounds. The fallback recovers the concrete
            // type from the lower side. Choosing a concrete type for a
            // negative-position var that only ever receives `arg` *is*
            // monomorphizing it; the answer is the concrete `arg`.
            //
            // Algebraic subtyping's "principal" answer for such a var is
            // `∀α ⊇ arg. …`, which would need a `Type::ForAll`. Cambra uses
            // implicit, level-based polymorphism and lowers it to concrete code,
            // so the desired output here is the concrete `arg`, not a quantifier
            // — this is a pragmatic fit, not a ban on ever representing `∀`.
            //
            // The read is sound because every variable reaching coalesce is
            // *monomorphically determined* — pinned to one type by its uses, or
            // its bounds collide into `IncompatibleBounds` (never a silent
            // mis-type). This invariant is the structural-collision check; it
            // predates let-polymorphism. A generalized binding's definition is
            // never coalesced (`infer_simple_sub` skips it); only its per-use
            // instantiations reach here, each fixed by one use site, then
            // specialized by the post-coalesce `monomorphize` pass.
            let s = state.bounds.borrow();
            let primary = if pol { &s.lower } else { &s.upper };
            // When the polarity-correct list is empty we fall back to the
            // opposite-polarity bounds (see the rationale above). Track which
            // polarity the bounds came from so we walk + merge them at THAT
            // polarity — record merge is asymmetric (union at negative,
            // intersection at positive), and using the wrong polarity collapses
            // disjoint-field records to the empty record at coalesce time. Fix
            // for the multi-gen iter-record case: lambda param `__iter_record`
            // accumulates upper bounds (open records `{.0}` and `{.1}`) from
            // projections; we want their negative-polarity union (both fields)
            // when the Var is coalesced at positive polarity, not the
            // positive-polarity intersection (empty).
            //
            // This fallback handles a *bare* under-determined domain var: it
            // materializes the type locally at coalesce from the lower-bound
            // side. The other half of the contravariant-domain story — a
            // *structured* domain (a tuple/record with `Infer`s inside, which
            // this per-var read cannot reassemble) — is recovered separately
            // by `coalesce_node`'s `specialize_projection_domain` /
            // `specialize_lambda_domain`. Both Apply edges are one-way (no
            // emit-time reverse whose eager cross-component propagation would
            // cover these halves); see `design-simple-sub.md` ("Apply is
            // one-way" and "Closing the single-sided blind spots").
            let primary_bounds = primary.clone();
            let opposite_bounds = if pol {
                s.upper.clone()
            } else {
                s.lower.clone()
            };
            drop(s);
            // Walk bounds, transitively expanding. We fold the bounds'
            // contributions *without* seeding from the variable's own identity
            // (`CompactType::from_var(uid)`) and inject the var id only at the
            // end. Seeding with `from_var` would mix the variable's *empty*
            // refinement set into the merge, and at positive polarity `merge`
            // *intersects* refinement sets (`merge_refinements`) — so the empty
            // seed would intersect away every bound's tags (∅ is absorbing under
            // intersection). The variable identity must be refinement-*neutral*;
            // `rec`/`var`/`fun` get this for free from their `None` merge
            // identity, but refinement sets have no such sentinel, so we keep
            // the var out of the structural fold.
            let mut new_parents = parents.clone();
            new_parents.insert(uid);
            let mut bound: Option<CompactType> = None;
            for b in &primary_bounds {
                // Compose this edge's substitution onto the accumulator before
                // descending: a bound reached transitively through `v → w → …`
                // arrives with every edge's morphism composed (design §3.6).
                // Identity edges leave `subst_acc` unchanged (the common case).
                let inner_acc = Subst::then(&b.subst, subst_acc);
                let bc = compact_go(
                    &b.ty,
                    pol,
                    &inner_acc,
                    &new_parents,
                    in_process,
                    recursive,
                    rec_vars,
                );
                bound = Some(match bound {
                    None => bc,
                    Some(acc) => CompactType::merge(pol, acc, bc),
                });
            }
            // Opposite-polarity fallback: walk the other side too if the
            // primary walk did not produce any concrete (atom / shape)
            // contribution. Without this, a variable whose only concrete
            // information lives on the opposite polarity coalesces to
            // `Type::Infer(?N)` instead of its real type — most commonly
            // a fresh lambda param whose Apply-site bound flows in at the
            // opposite polarity from where the lambda is coalesced. This is the
            // coalesce-time read of monomorphization; it is sound because every
            // var reaching coalesce is monomorphically determined (one type or
            // an `IncompatibleBounds` error). See the rationale above.
            let no_concrete = bound
                .as_ref()
                .is_none_or(|b| b.atoms.is_empty() && b.rec.is_none() && b.fun.is_none());
            if no_concrete {
                for b in &opposite_bounds {
                    let inner_acc = Subst::then(&b.subst, subst_acc);
                    let bc = compact_go(
                        &b.ty,
                        !pol,
                        &inner_acc,
                        &new_parents,
                        in_process,
                        recursive,
                        rec_vars,
                    );
                    bound = Some(match bound {
                        None => bc,
                        Some(acc) => CompactType::merge(!pol, acc, bc),
                    });
                }
            }
            // Inject the variable's own identity (refinement-neutral) so it
            // shows up in the CompactType — equivalent to the old `from_var`
            // seed for `vars`, but without polluting the refinement merge.
            let mut bound = bound.unwrap_or_else(CompactType::empty);
            bound.vars.insert(uid);
            in_process.remove(&key);
            // Recursive types: store the bound under the placeholder
            // variable and emit a reference.
            if let Some(rec_uid) = recursive.get(&key) {
                let rec_uid = *rec_uid;
                rec_vars.insert(rec_uid, bound);
                return CompactType::from_var(rec_uid);
            }
            bound
        }
    }
}

// ---------------------------------------------------------------------------
// Type simplification: co-occurrence analysis
// ---------------------------------------------------------------------------

/// An item that can appear in a co-occurrence set during [`simplify_type`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CoOccItem {
    Var(InferVarId),
    Atom(AtomKey),
}

/// Simplify a [`CompactGraph`] by per-polarity co-occurrence analysis.
///
/// Two simplifications:
///
/// 1. **Polar-only elimination.** A variable that appears at only one
///    polarity contributes no structural information (any concrete value
///    filling the one polarity is unconstrained on the other side). It is
///    dropped: its position becomes empty, which coalesces to `Type::Infer`.
///
/// 2. **Co-occurrence merging.** If variable `v` always appears together with
///    variable `w` at a given polarity, and symmetrically `w` always appears
///    with `v`, they carry identical information and `w` can be merged into
///    `v`. Only non-recursive variables are merged with non-recursive ones,
///    and recursive with recursive (mixing would violate strict polarity for
///    recursive types).
///
/// 3. **Atomic absorption.** If atom `A` co-occurs with variable `v` at both
///    polarities, `v` is "sandwiched" between two structural `A` constraints
///    and is redundant; it is dropped.
///
/// The operation is currently cosmetic (all types are monomorphic) but
/// becomes load-bearing once let-polymorphism introduces genuine polar
/// asymmetry. It is placed between [`compact_type`] and
/// [`coalesce_compact`] in the pipeline.
///
/// **Refinements need no special handling here.** Refinement tags live on
/// each [`CompactType`] *position* (`ct.refinements`), not on variable
/// identity, and [`simplify_reconstruct`] copies them through unchanged while
/// `var_subst` only ever rewrites or drops variable uids. Co-occurring
/// variables (the merge candidates) sit in the same position and therefore
/// carry the same tags, so merging or eliminating a variable can never move
/// or lose a refinement. (The classic "merge x>0 with x<10" hazard applies
/// only to representations that fold the predicate into the variable's
/// identity; ours keeps them positional.)
///
/// Recursive variables: the solver never produces non-empty `rec_vars`
/// today, so the recursive-variable merge path is guarded but remains
/// unexercised until recursive types are supported.
pub fn simplify_type(cty: CompactGraph) -> CompactGraph {
    // All variable UIDs encountered during the walk.
    let mut all_vars: BTreeSet<InferVarId> = cty.rec_vars.keys().cloned().collect();
    // Guards against re-entering a rec-var bound during analysis.
    let mut rec_processed: BTreeSet<InferVarId> = BTreeSet::new();
    // co_occurrences[(pol, uid)] = set of items that ALWAYS co-occur with uid at polarity pol.
    let mut co_occurrences: HashMap<(bool, InferVarId), HashSet<CoOccItem>> = HashMap::new();

    // Phase 1: analysis — walk the term, collecting co-occurrence sets.
    simplify_analyze(
        &cty.term,
        true,
        &cty.rec_vars,
        &mut all_vars,
        &mut rec_processed,
        &mut co_occurrences,
    );

    // Phase 2: decision — determine substitutions.
    let mut var_subst: HashMap<InferVarId, Option<InferVarId>> = HashMap::new();

    // Eliminate polar-only non-recursive variables.
    for &v in &all_vars {
        if !cty.rec_vars.contains_key(&v) {
            let has_pos = co_occurrences.contains_key(&(true, v));
            let has_neg = co_occurrences.contains_key(&(false, v));
            if has_pos != has_neg {
                var_subst.insert(v, None);
            }
        }
    }

    // Unify co-occurring variables; absorb atom-sandwiched variables.
    let all_vars_vec: Vec<InferVarId> = all_vars.iter().cloned().collect();
    for &v in &all_vars_vec {
        if var_subst.contains_key(&v) {
            continue;
        }
        for pol in [true, false] {
            let occs: Vec<CoOccItem> = co_occurrences
                .get(&(pol, v))
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect();
            for item in occs {
                if var_subst.contains_key(&v) {
                    break; // v was just eliminated; stop processing
                }
                match item {
                    CoOccItem::Var(w) if w != v && !var_subst.contains_key(&w) => {
                        // Only merge rec↔rec or non-rec↔non-rec.
                        if cty.rec_vars.contains_key(&v) != cty.rec_vars.contains_key(&w) {
                            continue;
                        }
                        // Merge w into v when v always co-occurs in w's set at pol.
                        let v_in_w = co_occurrences
                            .get(&(pol, w))
                            .map(|s| s.contains(&CoOccItem::Var(v)))
                            .unwrap_or(false);
                        if v_in_w {
                            var_subst.insert(w, Some(v));
                            if cty.rec_vars.contains_key(&w) {
                                // Both recursive: rec-bound merging deferred until recursive types land.
                                // (Never reached today — rec_vars is always empty.)
                            } else {
                                // Non-recursive: intersect v's !pol co-occs with w's !pol co-occs.
                                let w_neg: HashSet<CoOccItem> =
                                    co_occurrences.get(&(!pol, w)).cloned().unwrap_or_default();
                                if let Some(v_neg) = co_occurrences.get_mut(&(!pol, v)) {
                                    v_neg.retain(|t| *t == CoOccItem::Var(v) || w_neg.contains(t));
                                }
                            }
                        }
                    }
                    CoOccItem::Atom(ref atom) => {
                        // v is sandwiched: atom co-occurs with v at both polarities.
                        let neg_has_atom = co_occurrences
                            .get(&(!pol, v))
                            .map(|s| s.contains(&CoOccItem::Atom(atom.clone())))
                            .unwrap_or(false);
                        if neg_has_atom {
                            var_subst.insert(v, None);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Phase 3: reconstruction — apply var_subst to the term and rec_var bounds.
    let new_rec_vars: BTreeMap<InferVarId, CompactType> = cty
        .rec_vars
        .iter()
        .filter(|&(&uid, _)| !var_subst.contains_key(&uid))
        .map(|(&uid, bound)| (uid, simplify_reconstruct(bound.clone(), &var_subst)))
        .collect();

    CompactGraph {
        term: simplify_reconstruct(cty.term, &var_subst),
        rec_vars: new_rec_vars,
    }
}

/// Walk a [`CompactType`], recording per-polarity co-occurrences for each variable.
///
/// At each position, the co-occurrence set for variable `v` is intersected
/// with the set of items present at that position. This implements the
/// "always appears with" invariant: after a full walk, `co_occurrences[(pol,
/// v)]` contains only items that appeared alongside `v` every time `v` was
/// seen at polarity `pol`.
fn simplify_analyze(
    ct: &CompactType,
    pol: bool,
    input_rec_vars: &BTreeMap<InferVarId, CompactType>,
    all_vars: &mut BTreeSet<InferVarId>,
    rec_processed: &mut BTreeSet<InferVarId>,
    co_occurrences: &mut HashMap<(bool, InferVarId), HashSet<CoOccItem>>,
) {
    // Items present at this position (vars + atoms).
    let here: HashSet<CoOccItem> = ct
        .vars
        .iter()
        .map(|&v| CoOccItem::Var(v))
        .chain(ct.atoms.iter().map(|a| CoOccItem::Atom(a.clone())))
        .collect();

    for &tv in &ct.vars {
        all_vars.insert(tv);
        // Intersect existing co-occurrence set with items here, or initialize it.
        match co_occurrences.entry((pol, tv)) {
            std::collections::hash_map::Entry::Occupied(mut e) => {
                e.get_mut().retain(|x| here.contains(x));
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(here.clone());
            }
        }
        // If tv has a recursive bound in the input, process it once (guards cycles).
        if let Some(bound) = input_rec_vars.get(&tv)
            && rec_processed.insert(tv)
        {
            simplify_analyze(
                bound,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }

    // Recurse into record fields (same polarity) and function (flip domain polarity).
    if let Some(fields) = &ct.rec {
        for v in fields.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    // Variant payloads recurse at the same polarity (covariant depth),
    // matching how records' payloads behave.
    if let Some(tags) = &ct.var {
        for v in tags.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    if let Some((_, dom, cod)) = &ct.fun {
        simplify_analyze(
            dom,
            !pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
        simplify_analyze(
            cod,
            pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
    }
}

/// Apply `var_subst` to a [`CompactType`], producing the simplified version.
fn simplify_reconstruct(
    ct: CompactType,
    var_subst: &HashMap<InferVarId, Option<InferVarId>>,
) -> CompactType {
    let new_vars: BTreeSet<InferVarId> = ct
        .vars
        .iter()
        .flat_map(|&tv| match var_subst.get(&tv) {
            Some(Some(w)) => Some(*w), // replaced by w
            Some(None) => None,        // eliminated
            None => Some(tv),          // unchanged
        })
        .collect();

    let new_rec = ct.rec.map(|fields| {
        fields
            .into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_var = ct.var.map(|tags| {
        tags.into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_fun = ct.fun.map(|(name, dom, cod)| {
        (
            name,
            Box::new(simplify_reconstruct(*dom, var_subst)),
            Box::new(simplify_reconstruct(*cod, var_subst)),
        )
    });

    CompactType {
        vars: new_vars,
        atoms: ct.atoms,
        rec: new_rec,
        var: new_var,
        fun: new_fun,
        refinements: ct.refinements,
    }
}

// ---------------------------------------------------------------------------
// Coalesce: CompactGraph → ccl::Type
// ---------------------------------------------------------------------------

/// Materialize a CompactType into `ccl::Type`.
///
/// Multiple atom contributions at the same position is an error
/// (`IncompatibleBounds`) — the solver won't invent an anonymous sum from a
/// primitive collision. A
/// CompactType with no concrete contributions coalesces to a fresh
/// `Type::Infer` (caller's `check_fully_typed` reports it).
///
/// Variable contributions are *consumed* — they don't appear directly
/// in the output. Their information already flowed into the bound list
/// during `compact_type`. If a variable contributes nothing structural
/// (no atom/rec/fun) and there are no co-occurring atoms, we emit
/// `Type::Infer`.
pub fn coalesce_compact(graph: &CompactGraph) -> Result<Type, CoalesceError> {
    if !graph.rec_vars.is_empty() {
        return Err(CoalesceError::RecursiveType {
            details: format!("{} recursive variable(s) in graph", graph.rec_vars.len()),
        });
    }
    coalesce_compact_go(&graph.term, true)
}

fn coalesce_compact_go(ct: &CompactType, polarity: bool) -> Result<Type, CoalesceError> {
    // Count concrete (non-variable) contributions to pick the output
    // type. With multiple distinct contributions, we would need
    // a Union/Intersection — we error instead.
    let mut atoms: Vec<Type> = ct.atoms.iter().map(|a| a.to_type()).collect();
    let mut shapes: Vec<Type> = Vec::new();

    if let Some(rec) = &ct.rec {
        shapes.push(materialize_record(rec, polarity)?);
    }
    if let Some(var) = &ct.var {
        shapes.push(materialize_variant(var, polarity)?);
    }
    if let Some((name, dom, cod)) = &ct.fun {
        let d = coalesce_compact_go(dom, !polarity)?;
        let c = coalesce_compact_go(cod, polarity)?;
        // Strip the Pi binder unless the codomain's refinement predicates
        // actually reference it (design §3.2 / O10): keeps ordinary functions
        // `name: None` while a genuinely dependent codomain keeps its binder
        // bound.
        let kept_name = name
            .clone()
            .filter(|b| crate::ccl::subst::type_free_vars(&c).contains(b));
        shapes.push(Type::Fun {
            name: kept_name,
            domain: Box::new(d),
            codomain: Box::new(c),
        });
    }

    let mut all = Vec::new();
    all.append(&mut atoms);
    all.append(&mut shapes);

    let inner = match all.len() {
        0 => {
            // No concrete contribution; emit a fresh Infer slot.
            // check_fully_typed reports it as UnresolvedInfer if it
            // survives.
            Type::Infer(InferVar::fresh(0))
        }
        1 => all.remove(0),
        _ => {
            // Multiple incompatible contributions. Reject.
            let pretty = all
                .iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let vars: Vec<InferVarId> = ct.vars.iter().copied().collect();
            return Err(CoalesceError::IncompatibleBounds {
                polarity,
                vars,
                details: pretty,
            });
        }
    };

    // Re-wrap the refinement tags carried at this position. `extent_of`
    // and `iterate_type` both strip refinements at every depth and compose
    // the resulting `Restrict`s, so the wrap order is semantically
    // irrelevant; first-insertion order in the `Vec` makes it stable.
    let out = ct
        .refinements
        .iter()
        .fold(inner, |acc, r| Type::Refinement(Box::new(acc), r.clone()));
    Ok(out)
}

/// Materialize a variant-tag map into [`Type::Variant`], preserving tag
/// order by name (BTreeMap iterates in key order, so output is stable).
/// Payloads coalesce at the same polarity as the outer (covariant depth).
fn materialize_variant(
    tags: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    let mut out = Vec::with_capacity(tags.len());
    for (k, v) in tags {
        out.push((k.clone(), coalesce_compact_go(v, polarity)?));
    }
    Ok(Type::Variant(out))
}

fn materialize_record(
    rec: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    if rec.is_empty() {
        return Ok(Type::Tuple(Vec::new()));
    }
    let all_index = rec.keys().all(|k| matches!(k, FieldKey::Index(_)));
    let all_name = rec.keys().all(|k| matches!(k, FieldKey::Name(_)));

    if all_index {
        let mut indexed: Vec<(usize, &CompactType)> = rec
            .iter()
            .map(|(k, v)| match k {
                FieldKey::Index(i) => (*i, v),
                _ => unreachable!(),
            })
            .collect();
        indexed.sort_by_key(|(i, _)| *i);
        let dense = indexed
            .iter()
            .enumerate()
            .all(|(pos, (idx, _))| pos == *idx);
        if dense {
            // Closed dense tuple.
            let mut out = Vec::with_capacity(indexed.len());
            for (_, v) in indexed {
                out.push(coalesce_compact_go(v, polarity)?);
            }
            Ok(Type::Tuple(out))
        } else {
            // Sparse indices — an open record-var (e.g. an isolated
            // index-projection domain) that never got pinned to a closed
            // tuple shape during inference. It is genuinely
            // under-determined and unconstructable by the runtime, so it
            // coalesces to a fresh `Type::Infer` (an ambiguous-type
            // condition, reported by `check_fully_typed` if it survives to
            // the program's output). Note: still recurse the payloads so
            // any nested var bounds are visited even though we discard the
            // shape.
            for (_, v) in indexed {
                coalesce_compact_go(v, polarity)?;
            }
            Ok(Type::Infer(InferVar::fresh(0)))
        }
    } else if all_name {
        let mut out = Vec::with_capacity(rec.len());
        for (k, v) in rec {
            let name = match k {
                FieldKey::Name(s) => s.to_string(),
                _ => unreachable!(),
            };
            out.push((name, coalesce_compact_go(v, polarity)?));
        }
        // We don't have a way to distinguish open vs closed name-keyed
        // records at this layer (no field-count invariant analogous
        // to dense indices). For now, emit Record always — the
        // existing path's Record/PartialRecord distinction is driven
        // by lowering, which already differentiates field-set-known
        // sites from projection sites.
        Ok(Type::Record(out))
    } else {
        Err(CoalesceError::UnresolvedPartial {
            kind: PartialKind::Record,
            details: format!(
                "mixed Index/Name keys: {:?}",
                rec.keys().collect::<Vec<_>>()
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_var_has_no_bounds() {
        let v = InferVar::fresh(0);
        let s = v.bounds.borrow();
        assert!(s.lower.is_empty());
        assert!(s.upper.is_empty());
        assert_eq!(v.level, 0);
    }

    /// Regression: mutually-constrained inference variables form an `Rc`
    /// cycle through their bounds (`?a <: ?b` stores `?b` in `?a`'s upper
    /// bounds and vice versa). Reference counting alone never reclaims it;
    /// the owning [`InferArena`](crate::ccl::infer::InferArena)'s `Drop` is
    /// what clears the bounds and breaks the cycle.
    /// If this fails, the cycle is leaking again.
    #[test]
    fn mutually_constrained_vars_leak_via_rc_cycle() {
        use crate::ccl::infer::InferArena;
        use std::rc::Weak;

        // Activate an arena so the two `fresh_var` mints below are owned by
        // it; its `Drop` is what clears the bounds and breaks the cycle.
        let arena = InferArena::new();

        let a = fresh_var(0);
        let b = fresh_var(0);
        let mut cache = ConstrainCache::new();
        // ?a <: ?b and ?b <: ?a — the ordinary "spurious cycle" the solver
        // tolerates; nothing recursive or exotic is required.
        constrain_subtype(&a, &b, &mut cache).unwrap();
        constrain_subtype(&b, &a, &mut cache).unwrap();

        let (wa, wb): (Weak<InferVar>, Weak<InferVar>) = match (&a, &b) {
            (Type::Infer(va), Type::Infer(vb)) => (Rc::downgrade(va), Rc::downgrade(vb)),
            _ => unreachable!("fresh_var yields Type::Infer"),
        };

        // Drop every external strong handle. The cache also holds `Type`
        // clones (its keys are `(Type, Type)`), so it must go too — it is
        // dropped at the end of a real constraint-emission pass anyway.
        drop(cache);
        drop(a);
        drop(b);

        // Tearing down the arena clears both cells' bounds, severing the
        // mutual `Rc` edges. Only after this can the refcounts reach zero.
        drop(arena);

        assert!(
            wa.upgrade().is_none() && wb.upgrade().is_none(),
            "expected the Rc cycle to be reclaimed; both inference vars leaked"
        );
    }

    #[test]
    fn level_of_compound_is_max_of_components() {
        let v0 = fresh_var(0);
        let v1 = fresh_var(1);
        let f = fun(v0, v1);
        assert_eq!(type_level(&f), 1);
    }

    #[test]
    fn primitives_have_level_zero() {
        let p = prim(BaseType::Int);
        assert_eq!(type_level(&p), 0);
    }

    /// Build a `Type` from `FieldKey`-keyed fields: all-`Name` → `Record`,
    /// otherwise a dense `Tuple` (the only product shapes `ccl::Type` has).
    /// Sparse-`Index` inputs have no `Type` form — tests that need them
    /// build the `CompactType` directly.
    fn record(fields: &[(FieldKey, Type)]) -> Type {
        if fields.iter().all(|(k, _)| matches!(k, FieldKey::Name(_))) {
            Type::Record(
                fields
                    .iter()
                    .map(|(k, t)| match k {
                        FieldKey::Name(n) => (n.to_string(), t.clone()),
                        _ => unreachable!(),
                    })
                    .collect(),
            )
        } else {
            Type::Tuple(fields.iter().map(|(_, t)| t.clone()).collect())
        }
    }

    /// Build `{base | marker}` — a `Type::Refinement` whose tag's predicate
    /// encodes `marker` (an `Int(marker)` literal). Refinements compare by
    /// structural predicate equality (see [`Refinement`]'s `PartialEq`), so
    /// equal markers match and distinct markers stay distinct.
    fn refined(base: Type, marker: i64) -> Type {
        use crate::ccl::{Lit, TypedExpr};
        use std::cell::RefCell;
        let r = Refinement {
            predicate: Rc::new(RefCell::new(TypedExpr::lit(Lit::Int(marker)))),
        };
        Type::Refinement(Box::new(base), r)
    }

    #[test]
    fn refined_superset_is_subtype() {
        // {Int | p, q} <: {Int | p}  — more refinements ⇒ subtype.
        let (p, q) = (1, 2);
        let lhs = refined(refined(prim(BaseType::Int), p), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn refined_missing_tag_is_not_subtype() {
        // {Int | q} </: {Int | p}  — a q-refined value cannot stand in for a
        // p-refined one. `refined` gives p and q structurally-distinct
        // predicates, so the tags don't match.
        let (p, q) = (1, 2);
        let lhs = refined(prim(BaseType::Int), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn structurally_equal_predicate_matches_across_cells() {
        // {Int | p} <: {Int | q} when p and q carry *structurally identical*
        // predicates in distinct cells — exactly what join planning produces
        // by re-minting a refinement at each marker. Equality of the
        // predicate `Expr`, not cell identity, decides the match
        // (`Refinement: PartialEq`).
        use crate::ccl::{Lit, TypedExpr};
        use std::cell::RefCell;
        let mk = || {
            Type::Refinement(
                Box::new(prim(BaseType::Int)),
                Refinement {
                    predicate: Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true)))),
                },
            )
        };
        let lhs = mk();
        let rhs = mk();
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn structurally_equal_refinements_hash_equal() {
        // The `Hash`/`Eq` contract: structurally-equal refinements in
        // distinct cells are `==`, so they must also hash equal — otherwise the
        // `ConstrainCache` (`HashSet<(Type, Type)>`) cycle-break could miss a
        // match. Pins consistency between `Refinement`'s `PartialEq` and `Hash`.
        use crate::ccl::{Lit, TypedExpr};
        use std::cell::RefCell;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mk = || {
            Type::Refinement(
                Box::new(prim(BaseType::Int)),
                Refinement {
                    predicate: Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true)))),
                },
            )
        };
        let a = mk();
        let b = mk();
        let hash = |t: &Type| {
            let mut h = DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        };
        assert_eq!(a, b, "structurally-equal refinements must be ==");
        assert_eq!(hash(&a), hash(&b), "== refinements must hash equal");

        // The cache scenario: the second structurally-equal pair is recognised
        // as already present.
        let mut cache = ConstrainCache::new();
        assert!(cache.insert((a.clone(), prim(BaseType::Int))));
        assert!(!cache.insert((b, prim(BaseType::Int))));

        // A structurally *different* predicate must not collapse into it.
        let c = Type::Refinement(
            Box::new(prim(BaseType::Int)),
            Refinement {
                predicate: Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(false)))),
            },
        );
        assert_ne!(a, c, "distinct predicates must stay distinct");
    }

    #[test]
    fn refined_drops_to_base() {
        // {Int | p} <: Int  — dropping a refinement is widening.
        let p = 1;
        let lhs = refined(prim(BaseType::Int), p);
        let rhs = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn refined_var_base_absorbs_deficit() {
        // {?a | q} <: {Int | p}: the explicit layer only supplies q, but the
        // base variable ?a can acquire the deficit {p}, so the constraint
        // succeeds by flowing `?a <: {Int | p}`. This is what lets a value
        // that is *already* refined be cast to add a further tag (nested
        // list-comprehension filters: `{D|p} ⇒ V <: {?a|q} ⇒ V`); a ground
        // `{p} ⊆ {q}` check would reject it.
        let (p, q) = (1, 2);
        let a = fresh_var(0);
        let lhs = refined(a.clone(), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
        // The deficit must have been recorded on ?a as the upper bound
        // `{Int | p}`, so coalescing ?a yields a base carrying p.
        let Type::Infer(v) = &a else { unreachable!() };
        let expected = refined(prim(BaseType::Int), p);
        assert!(
            v.bounds.borrow().upper.iter().any(|u| u.ty == expected),
            "?a should carry {{Int | p}} as an upper bound, got {:?}",
            v.bounds.borrow().upper
        );
    }

    #[test]
    fn refined_concrete_base_still_rejects_deficit() {
        // {Int | q} </: {Int | p}: with a *concrete* base there is nothing to
        // absorb the deficit, so the strict rejection (`{T|q} ⊀ {T|p}`) is
        // preserved — only a variable base can acquire missing tags.
        let (p, q) = (1, 2);
        let lhs = refined(prim(BaseType::Int), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn unrefined_does_not_flow_into_refined() {
        // Int </: {Int | p}  — a refinement is *required*, not one the
        // consumer silently applies. An unrefined value cannot stand in
        // where a refined one is demanded; acquiring the refinement is an
        // explicit `Restrict`, not subsumption.
        let p = 1;
        let lhs = prim(BaseType::Int);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn distinct_refinements_survive_simplification() {
        // A record carrying two *different* refinement tags at two field
        // positions must round-trip through compact → simplify → coalesce
        // with both tags intact (they are positional, not folded into a
        // variable identity, so co-occurrence analysis cannot merge them).
        let (p, q) = (1, 2);
        let ty = Type::Record(vec![
            ("a".to_string(), refined(prim(BaseType::Int), p)),
            ("b".to_string(), refined(prim(BaseType::Int), q)),
        ]);
        let out = coalesce_compact(&simplify_type(compact_type(&ty))).unwrap();
        assert_eq!(out, ty);
    }

    #[test]
    fn var_constrained_to_refined_coalesces_refined() {
        // A fresh var equated to a refined type (both bounds) must coalesce
        // *carrying* the refinement, not drop it to the bare base. Solver-level
        // property: equality bounds may still arise (e.g. `bind_annotation`,
        // `require_eq` on list elements), so tags must survive them.
        let p = 1;
        let v = fresh_var(0);
        let refined_int = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        // v ⟺ {Int | p}
        constrain_subtype(&v, &refined_int, &mut cache).unwrap();
        constrain_subtype(&refined_int, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(out, refined_int, "var equated to {{Int|p}} lost its tag");
    }

    #[test]
    fn apply_index_var_coalesces_refined() {
        // Solver-level tag-propagation property: an index var `v` equated
        // (both bounds) with the domain `dom` of a function shape that is
        // itself equated with `{d | p} ⇒ cod` (d ⟺ Int). The tag `p` must
        // propagate through the var⇄var equality chain onto `v`'s coalesced
        // type, `{Int | p}` — refinements ride the lattice; they must not be
        // dropped at var merges.
        let p = 1;
        let d = fresh_var(0);
        let cod = fresh_var(0);
        let dom = fresh_var(0);
        let cap = fresh_var(0);
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        // d ⟺ Int
        constrain_subtype(&d, &prim(BaseType::Int), &mut cache).unwrap();
        constrain_subtype(&prim(BaseType::Int), &d, &mut cache).unwrap();
        // fn = {d|p} ⇒ cod
        let fn_ty = fun(refined(d.clone(), p), cod.clone());
        // as_function_eq: fn ⟺ dom ⇒ cap
        let shape = fun(dom.clone(), cap.clone());
        constrain_subtype(&fn_ty, &shape, &mut cache).unwrap();
        constrain_subtype(&shape, &fn_ty, &mut cache).unwrap();
        // constrain_argument(v, dom): two-way
        constrain_subtype(&v, &dom, &mut cache).unwrap();
        constrain_subtype(&dom, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(
            out,
            refined(prim(BaseType::Int), p),
            "Apply index var lost its tag"
        );
    }

    #[test]
    fn constrain_identical_primitives_succeeds() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&a, &b, &mut cache).is_ok());
    }

    #[test]
    fn constrain_distinct_primitives_fails() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::String);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&a, &b, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn constrain_function_propagates_contravariance() {
        // (Int -> Int) <: (Int -> Int) — succeeds.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_ok());
    }

    #[test]
    fn constrain_function_mismatch_on_codomain_fails() {
        // (Int -> Int) <: (Int -> String) — fails on codomain.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::String));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_err());
    }

    #[test]
    fn constrain_record_width_subtyping_succeeds() {
        // {a: Int, b: Bool} <: {a: Int} — drop field b, OK.
        let lhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let rhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn constrain_record_missing_field_fails() {
        // {a: Int} <: {a: Int, b: Bool} — lhs lacks field b.
        let lhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let rhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::MissingField { .. })
        ));
    }

    #[test]
    fn constrain_var_against_prim_records_upper_bound() {
        // α <: Int → α gains Int as an upper bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &p, &mut cache).unwrap();
        if let Type::Infer(state) = &v {
            let s = state.bounds.borrow();
            assert_eq!(s.upper.len(), 1);
            assert!(s.lower.is_empty());
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_prim_against_var_records_lower_bound() {
        // Int <: α → α gains Int as a lower bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&p, &v, &mut cache).unwrap();
        if let Type::Infer(state) = &v {
            let s = state.bounds.borrow();
            assert!(s.upper.is_empty());
            assert_eq!(s.lower.len(), 1);
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_var_to_var_records_bound_without_immediate_propagation() {
        // Setup: α has upper Int. Then β <: α.
        //
        // Note: simple-sub's constrain_subtype rule, when both sides are
        // variables, fires the Var-on-lhs branch first and registers
        // rhs (α) directly in lhs (β)'s upper bounds. α's existing
        // uppers are NOT eagerly transferred to β — that transitive
        // chain (β <: Int) is recovered at simplification time by
        // walking the bounds graph.
        let alpha = fresh_var(0);
        let beta = fresh_var(0);
        let int_ty = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&alpha, &int_ty, &mut cache).unwrap();
        constrain_subtype(&beta, &alpha, &mut cache).unwrap();

        if let Type::Infer(state) = &beta {
            let s = state.bounds.borrow();
            assert_eq!(s.upper.len(), 1);
            // The recorded upper bound is α itself, not Int.
            assert!(matches!(&s.upper[0].ty, Type::Infer(_)));
        } else {
            unreachable!()
        }
    }

    #[test]
    fn coalesce_primitive_round_trips() {
        let s = prim(BaseType::Int);
        assert_eq!(
            coalesce_compact(&compact_type(&s)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_function_preserves_shape() {
        let s = fun(prim(BaseType::Int), prim(BaseType::Bool));
        let t = coalesce_compact(&compact_type(&s)).unwrap();
        assert_eq!(
            t,
            Type::Fun {
                name: None,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Bool))
            }
        );
    }

    #[test]
    fn coalesce_dense_index_record_becomes_tuple() {
        let r = record(&[
            (FieldKey::Index(0), prim(BaseType::Int)),
            (FieldKey::Index(1), prim(BaseType::String)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    #[test]
    fn coalesce_named_record_becomes_record() {
        let r = record(&[
            (FieldKey::Name("x".into()), prim(BaseType::Int)),
            (FieldKey::Name("y".into()), prim(BaseType::Bool)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Record(vec![
                ("x".to_string(), Type::Base(BaseType::Int)),
                ("y".to_string(), Type::Base(BaseType::Bool))
            ])
        );
    }

    #[test]
    fn coalesce_sparse_index_emits_infer() {
        // A sparse Index record (e.g. an isolated index-projection domain
        // that never closed to a dense tuple) is under-determined and
        // unconstructable, so coalesce emits a fresh `Type::Infer`. There
        // is no `ccl::Type` for a sparse-index product, so build the
        // `CompactType` directly (the input the solver would produce
        // internally).
        let mut rec = BTreeMap::new();
        rec.insert(
            FieldKey::Index(0),
            CompactType::from_atom(AtomKey::Prim(BaseType::Int)),
        );
        rec.insert(
            FieldKey::Index(2),
            CompactType::from_atom(AtomKey::Prim(BaseType::String)),
        );
        let graph = CompactGraph {
            term: CompactType {
                rec: Some(rec),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        let t = coalesce_compact(&graph).unwrap();
        assert!(matches!(t, Type::Infer(_)), "expected Infer, got {t:?}");
    }

    #[test]
    fn coalesce_var_with_one_lower_bound_at_positive_position() {
        // α : lower=[Int]. At positive, coalesces to Int.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_one_upper_bound_at_negative_position() {
        // α : upper=[Int]. compact_type at default polarity (positive
        // top-level) walks a Var's lower bounds; the opposite-polarity
        // fallback in compact_go pulls in upper bounds when lowers are
        // empty, so this still resolves to Int. Will tighten once
        // simplify_type lands.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &prim(BaseType::Int), &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_no_bounds_emits_infer() {
        let v = fresh_var(0);
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer, got {:?}", other),
        }
    }

    #[test]
    fn coalesce_var_with_incompatible_lowers_fails() {
        // α : lower=[Int, String]. The solver rejects unions — both
        // primitives flow into the atom set, and coalesce_compact
        // emits IncompatibleBounds when more than one concrete
        // contribution survives.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        constrain_subtype(&prim(BaseType::String), &v, &mut cache).unwrap();
        assert!(matches!(
            coalesce_compact(&compact_type(&v)),
            Err(CoalesceError::IncompatibleBounds { .. })
        ));
    }

    #[test]
    fn coalesce_self_referential_var_emits_infer() {
        // α with α directly in its own lower bounds. compact_type's
        // `parents` filter treats this as a spurious cycle (no
        // structural intermediary), drops the bound, and
        // returns a CompactType containing just the variable. With no
        // concrete contributions, coalesce_compact emits Type::Infer.
        //
        // Real recursive bounds (α reachable from itself through a
        // structural intermediary, e.g. `α <: Fun(α, _)`) flow through
        // compact_type's structural recursion — a `Function` boundary
        // resets `parents` to empty, so re-encountering α at the same
        // polarity inside the Fun body triggers the
        // placeholder/RecursiveType path. One-way constraint emission
        // produces no such cycles today (even `λx. x x` types cleanly);
        // the path is defensive.
        let v = fresh_var(0);
        if let Type::Infer(state) = &v {
            state.bounds.borrow_mut().lower.push(Bound::conc(v.clone()));
        }
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer for spurious self-cycle, got {other:?}"),
        }
    }

    #[test]
    fn constrain_propagates_when_var_already_has_lower_bound() {
        // β has Int as a lower bound (e.g. Int has flowed in). Now
        // constrain_subtype β <: String. The propagation rule pushes the new
        // upper through β's existing lowers, raising Int <: String —
        // which fails as expected.
        let beta = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &beta, &mut cache).unwrap();
        let result = constrain_subtype(&beta, &prim(BaseType::String), &mut cache);
        assert!(matches!(result, Err(ConstrainError::Mismatch { .. })));
    }

    #[test]
    fn constrain_function_via_var_succeeds() {
        // λx. x typed as α -> α; constrain_subtype α -> α <: Int -> Int succeeds.
        let v = fresh_var(0);
        let identity = fun(v.clone(), v.clone());
        let int_to_int = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&identity, &int_to_int, &mut cache).is_ok());
    }

    // ------- simplify_type unit tests ----------------------------------------

    /// Build a fresh [`InferVarId`] for use in hand-constructed CompactTypes.
    fn fresh_uid() -> InferVarId {
        InferVar::fresh(0).uid
    }

    #[test]
    fn simplify_polar_only_elimination() {
        // term: Fun(dom={a}, cod={a,b})
        // b appears only at positive polarity (cod) → eliminated.
        // a appears at both → kept.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();

        let dom = CompactType {
            vars: [uid_a].into_iter().collect(),
            ..Default::default()
        };
        let cod = CompactType {
            vars: [uid_a, uid_b].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: Some((None, Box::new(dom), Box::new(cod))),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (_, dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.contains(&uid_a), "a kept in dom");
        assert!(cod_s.vars.contains(&uid_a), "a kept in cod");
        assert!(!cod_s.vars.contains(&uid_b), "b eliminated from cod");
    }

    #[test]
    fn simplify_atomic_absorption() {
        // term: Fun(dom={a,Int}, cod={a,Int})
        // Int co-occurs with a at both polarities → a is sandwiched and eliminated.
        let uid_a = fresh_uid();
        let int_key = AtomKey::Prim(BaseType::Int);

        let make_side = |vars: BTreeSet<InferVarId>| CompactType {
            vars,
            atoms: [int_key.clone()].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    None,
                    Box::new(make_side([uid_a].into_iter().collect())),
                    Box::new(make_side([uid_a].into_iter().collect())),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (_, dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.is_empty(), "a absorbed in dom");
        assert!(cod_s.vars.is_empty(), "a absorbed in cod");
        assert!(dom_s.atoms.contains(&int_key), "Int remains in dom");
        assert!(cod_s.atoms.contains(&int_key), "Int remains in cod");
    }

    #[test]
    fn simplify_co_occurrence_merge() {
        // term: Fun(dom={a,b}, cod={a,b})
        // a and b always appear together at both polarities → one merged into the other.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();
        let both: BTreeSet<InferVarId> = [uid_a, uid_b].into_iter().collect();

        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    None,
                    Box::new(CompactType {
                        vars: both.clone(),
                        ..Default::default()
                    }),
                    Box::new(CompactType {
                        vars: both,
                        ..Default::default()
                    }),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (_, dom_s, cod_s) = simplified.term.fun.unwrap();
        assert_eq!(dom_s.vars.len(), 1, "one var after merge in dom");
        assert_eq!(cod_s.vars.len(), 1, "one var after merge in cod");
        assert_eq!(dom_s.vars, cod_s.vars, "same representative in dom and cod");
    }

    #[test]
    fn simplify_identity_both_polarities_preserved() {
        // term: Fun(dom={a}, cod={a})
        // a appears at both polarities; no simplification applies.
        let uid_a = fresh_uid();

        let graph = CompactGraph {
            term: CompactType {
                fun: Some((
                    None,
                    Box::new(CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    }),
                    Box::new(CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    }),
                )),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let (_, dom_s, cod_s) = simplified.term.fun.unwrap();
        assert!(dom_s.vars.contains(&uid_a), "a preserved in dom");
        assert!(cod_s.vars.contains(&uid_a), "a preserved in cod");
    }

    // -----------------------------------------------------------------------
    // Variant — constrain_subtype, compact merging, coalesce
    // -----------------------------------------------------------------------

    /// Helper: build a `Type::Variant({tag: payload, ...})` with named
    /// (`FieldKey::Name`) tags.
    fn variant<const N: usize>(tags: [(&str, Type); N]) -> Type {
        Type::Variant(
            tags.into_iter()
                .map(|(k, v)| (FieldKey::Name(SmolStr::from(k)), v))
                .collect(),
        )
    }

    /// `[A] <: [A, B]` — subtype's tag set is a subset of supertype's. Accept.
    #[test]
    fn variant_width_sub_accept() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs, &mut cache).expect("[A] <: [A, B] should hold");
    }

    /// `[A, B] <: [A]` — supertype is missing a tag that lhs has. Reject.
    #[test]
    fn variant_width_sub_reject_missing_tag() {
        let lhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let rhs = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        let err = constrain_subtype(&lhs, &rhs, &mut cache)
            .expect_err("[A, B] <: [A] should be rejected: B not in rhs");
        match err {
            ConstrainError::ExtraTag { tag, .. } => {
                assert_eq!(tag, FieldKey::Name(SmolStr::from("B")))
            }
            other => panic!("expected ExtraTag, got {other:?}"),
        }
    }

    /// Payload depth is covariant: `[A(Int)] <: [A(Int)]` passes,
    /// `[A(Int)] <: [A(Str)]` fails on payload mismatch.
    #[test]
    fn variant_payload_covariance() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs_ok = variant([("A", prim(BaseType::Int))]);
        let rhs_bad = variant([("A", prim(BaseType::String))]);

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_ok, &mut c).expect("equal payloads accept");

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_bad, &mut c)
            .expect_err("Int payload should not flow into String payload");
    }

    /// Variable on lhs flowed against a variant: rhs becomes upper bound;
    /// subsequent lower-bound additions on lhs propagate against rhs.
    #[test]
    fn variant_var_lhs_propagation() {
        let v = fresh_var(0);
        let upper = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &upper, &mut cache).unwrap();
        // The propagation rule recorded `upper` on v's upper bounds. A
        // subsequent `concrete <: v` adds concrete to lower and propagates
        // it against upper — concrete must satisfy `concrete <: upper`.
        let concrete_ok = variant([("A", prim(BaseType::Int))]);
        constrain_subtype(&concrete_ok, &v, &mut cache).expect("[A(Int)] <: v <: [A(Int)] ok");

        let v2 = fresh_var(0);
        let upper2 = variant([("A", prim(BaseType::Int))]);
        let mut cache2 = ConstrainCache::new();
        constrain_subtype(&v2, &upper2, &mut cache2).unwrap();
        let concrete_bad = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        constrain_subtype(&concrete_bad, &v2, &mut cache2)
            .expect_err("[A, B] must not flow into v whose upper is [A]");
    }

    /// Compact merge at positive polarity unions tags.
    #[test]
    fn compact_merge_variants_positive_unions() {
        let int_a = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let int_b = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("B")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(true, int_a, int_b);
        let var = merged.var.expect("variant present");
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
    }

    /// Compact merge at negative polarity intersects tags.
    #[test]
    fn compact_merge_variants_negative_intersects() {
        let int_ab = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("A")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let int_bc = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("C")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(false, int_ab, int_bc);
        let var = merged.var.expect("variant present");
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("C"))));
    }

    /// Payload-depth polarity for variant merge: payloads at matching
    /// tags must recurse at the *outer* variant polarity (covariant
    /// depth), NOT the flipped polarity used to pick "union vs
    /// intersect tags". The two are independent and the helper has to
    /// thread them separately.
    ///
    /// To make the difference visible we use records as payloads —
    /// record-field merging is itself polarity-sensitive (pos =
    /// intersect, neg = union). At positive variant polarity the
    /// payload should merge at pos → record fields intersect.
    #[test]
    fn compact_merge_variants_propagates_outer_polarity_to_payloads() {
        // Both sides have tag "A". Payload on lhs: CompactType { rec:
        // {a: ?} }, payload on rhs: CompactType { rec: {b: ?} }.
        let payload_a = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("a")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let payload_b = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("b")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let lhs = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_a)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let rhs = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_b)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        // Outer positive variant merge: tags union (one tag A here).
        // Payload depth covariant → payload merges at pos → record
        // fields intersect → empty rec map (no field in both).
        let merged = CompactType::merge(true, lhs, rhs);
        let var = merged.var.expect("variant present");
        let payload = var.get(&FieldKey::Name(SmolStr::from("A"))).expect("tag A");
        let rec = payload.rec.as_ref().expect("payload rec present");
        assert!(
            rec.is_empty(),
            "positive payload merge intersects fields; got {rec:?}"
        );
    }

    /// Coalesce a variant `Type` into `Type::Variant` with preserved tags.
    #[test]
    fn coalesce_variant_roundtrips_to_type_variant() {
        let v = variant([
            ("Some", prim(BaseType::Int)),
            ("None", prim(BaseType::Unit)),
        ]);
        let scheme = simplify_type(compact_type(&v));
        let ty = coalesce_compact(&scheme).expect("coalesce ok");
        match ty {
            Type::Variant(tags) => {
                let names: Vec<String> = tags.iter().map(|(n, _)| n.to_string()).collect();
                // BTreeMap iteration order is by FieldKey key — Name tags
                // sort lexicographically.
                assert_eq!(names, vec!["None", "Some"]);
            }
            other => panic!("expected Variant, got {other}"),
        }
    }

    // ---- Dependent refinements: correspondence derivation + coalesce-time
    // forcing of suspended substitutions (prototype scenarios K/L). These
    // exercise the non-identity substitution paths the monomorphic suite never
    // reaches.

    use crate::ccl::subst::Subst;
    use crate::ccl::{BinOpKind, CompareKind, Lit, TypedExpr};
    use std::cell::RefCell;
    use std::rc::Rc;

    /// Build a refinement whose predicate is the **bare** `__elem > <rhs>` —
    /// the element is the implicit `REFINEMENT_BINDER`, free in the predicate,
    /// exactly as real refinements are shaped (no element-binding lambda).
    fn gt_refinement(rhs: TypedExpr) -> Refinement {
        let pred = TypedExpr::binop(
            TypedExpr::var(crate::ccl::REFINEMENT_BINDER),
            BinOpKind::Compare(CompareKind::Greater),
            rhs,
        );
        Refinement {
            predicate: Rc::new(RefCell::new(pred)),
        }
    }

    fn coalesce(ty: &Type) -> Type {
        coalesce_compact(&compact_type(ty)).expect("coalesce")
    }

    /// The refinement predicate of a `Fun(Refinement(_, r), _)`, rendered.
    fn domain_predicate(ty: &Type) -> String {
        let Type::Fun { domain, .. } = ty else {
            panic!("expected fun, got {ty}");
        };
        let Type::Refinement(_, r) = domain.as_ref() else {
            panic!("expected refined domain, got {domain}");
        };
        crate::ccl::symbolic::symbolic(&r.predicate.borrow())
    }

    // L — a Pi-vs-Pi constraint DERIVES the binder correspondence `[k ↦ x]`,
    // renaming the codomain refinement's reference to the bound key.
    #[test]
    fn pi_correspondence_renames_codomain_refinement() {
        let arena = crate::ccl::infer::InferArena::new();
        let result = fresh_var(0);
        let Type::Infer(result_var) = &result else {
            unreachable!()
        };

        // g : (k: Int) ⇒ ({i | i > k} ⇒ Int)
        let g_ty = Type::pi(
            "k",
            prim(BaseType::Int),
            Type::fun(
                Type::Refinement(
                    Box::new(prim(BaseType::Int)),
                    gt_refinement(TypedExpr::var("k")),
                ),
                prim(BaseType::Int),
            ),
        );
        // expected : (x: Int) ⇒ result
        let expected = Type::pi("x", prim(BaseType::Int), result.clone());

        let mut cache = ConstrainCache::new();
        constrain_subtype(&g_ty, &expected, &mut cache).expect("constrain");

        // result coalesces to `{i | i > x} ⇒ Int` — k renamed to the expected
        // binder x by the derived correspondence.
        let res = coalesce(&Type::Infer(Rc::clone(result_var)));
        assert_eq!(domain_predicate(&res), "__elem > x");
        drop(arena);
    }

    // K — a discharge `[x ↦ 0]` on a var edge composes with the correspondence
    // at coalesce, yielding the fully-substituted predicate `i > 0`: the
    // dependent application `g(0)`.
    #[test]
    fn dependent_application_discharges_through_coalesce() {
        let arena = crate::ccl::infer::InferArena::new();
        let result = fresh_var(0);
        let Type::Infer(result_var) = &result else {
            unreachable!()
        };

        let g_ty = Type::pi(
            "k",
            prim(BaseType::Int),
            Type::fun(
                Type::Refinement(
                    Box::new(prim(BaseType::Int)),
                    gt_refinement(TypedExpr::var("k")),
                ),
                prim(BaseType::Int),
            ),
        );
        let expected = Type::pi("x", prim(BaseType::Int), result.clone());
        let mut cache = ConstrainCache::new();
        constrain_subtype(&g_ty, &expected, &mut cache).expect("constrain");

        // The application term γ: its type is `result` under the discharge
        // [x ↦ 0] (what emit_apply mints).
        let gamma = fresh_var(0);
        let Type::Infer(gamma_var) = &gamma else {
            unreachable!()
        };
        gamma_var.bounds.borrow_mut().lower.push(Bound::with_subst(
            Type::Infer(Rc::clone(result_var)),
            Subst::discharge("x", TypedExpr::lit(Lit::Int(0))),
        ));

        let app_ty = coalesce(&Type::Infer(Rc::clone(gamma_var)));
        // g(0) : {i | i > 0} ⇒ Int — both the correspondence rename and the
        // discharge fired, composed along the coalesce walk.
        assert_eq!(domain_predicate(&app_ty), "__elem > 0");
        drop(arena);
    }
}

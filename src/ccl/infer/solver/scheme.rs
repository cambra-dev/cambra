//! Polymorphic schemes and freshening (instantiation).
//!
//! [`PolyScheme`] is the generalized-type representation; [`freshen_above`]
//! and its helpers mint a fresh copy of a scheme body (or a specialization
//! clone's whole subtree) at a use-site level, renaming quantified variables
//! uniformly across terms, types, refinement predicates, and the suspended
//! discharge payloads riding bound edges.

use std::collections::HashMap;
use std::rc::Rc;

use super::traits::{TraitObligation, TraitObligationId};
use crate::ccl::subst::Subst;
use crate::ccl::ty::{FunKind, FunKindVar, FunKindVarId};
use crate::ccl::{Bound, InferVar, InferVarId, Level, Refinement, Type, TypedExpr};

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
/// inherently polymorphic (`Max : ∀α γ. (α ⤇ γ) ⇒ γ`,
/// `Proj(Index n) : ∀α. {n: α, …} → α`, etc.), built once in
/// `OperatorSchemes`; and (2) let-generalization — a multi-use function
/// binding is generalized into a `PolyScheme` at its binding level
/// (`infer::context::scoped_let`) and `instantiate`d per use. See
/// `design/type-inference.md` for the rationale.
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
            &mut FreshenCache::new(),
        )
    }
}

/// Cache for [`freshen_above`]: each original quantified variable maps to its
/// single fresh replacement so multiple occurrences share the same fresh var,
/// and each quantified channel-domain name ([`Type::ChanDom`]) maps to its
/// single fresh (or pre-seeded — see [`seed_chan_dom_pairings`]) rename.
#[derive(Default)]
pub struct FreshenCache {
    /// Original quantified var → its fresh replacement.
    pub vars: HashMap<InferVarId, Rc<InferVar>>,
    /// Original quantified channel-domain name → its rename. Seeded by
    /// `specialize_use` with use-site pairings; unpaired names mint fresh.
    pub chan_doms: HashMap<crate::ccl::Name, crate::ccl::Name>,
    /// Original quantified kind variable → its fresh replacement. A generalized
    /// function's kind ([`FunKind::Var`]) must be decided *per use*, just
    /// like the type it quantifies: two instantiations that flow into differently
    /// -kinded contexts (one demanding `Data`, one `Compute`) must not share a
    /// `FunKindVar` cell, or forcing one contaminates the other into a spurious
    /// `DomainJoinConflict`. Freshening mints one `κ'` per original `κ` (bounds
    /// copied so def-intrinsic forcing survives), consistently within a copy.
    pub kind_vars: HashMap<FunKindVarId, Rc<FunKindVar>>,
    /// Original trait obligation → its per-instantiation copy, for the same reason
    /// as [`kind_vars`](Self::kind_vars): a generalized function's operator
    /// requirements are quantified along with the variables they constrain, so each
    /// use resolves *its own* copy. `λ 𝑥 → 𝑥 + 1` generalizes to
    /// `∀A O. A ⇒ O requires Addable(A, Int ⇝ O)`; sharing one obligation across uses
    /// would let a `String` use narrow the `Int` use's candidate set to nothing.
    pub obligations: HashMap<TraitObligationId, Rc<TraitObligation>>,
}

impl FreshenCache {
    pub fn new() -> Self {
        Self::default()
    }
}

/// The level [`freshen_above`] assigns to each fresh variable it mints.
#[derive(Clone, Copy)]
pub enum FreshenLevel {
    /// Mint every fresh variable at this one level. Use-site instantiation
    /// wants the copy to live at the *use's* level so it integrates with that
    /// site's constraints.
    At(Level),
    /// Mint each fresh variable at its *original* variable's level, preserving
    /// the relative level structure. Per-type specialization
    /// (`infer::solve::specialize_use`) wants this: a definition may
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
/// Freshen a function's kind at instantiation. A concrete kind
/// (`Data`/`Compute`) is intrinsic and copies through. An unresolved
/// [`FunKind::Var`] is *quantified*: mint one fresh `FunKindVar` per original
/// (cached by `uid` so repeated occurrences of the same `κ` in one copy stay
/// identified), seeding it with a copy of the original's bounds so any
/// def-intrinsic forcing is preserved while use-site forcing lands on the fresh
/// cell — decoupling instantiations (see [`FreshenCache::kind_vars`]).
fn freshen_kind(kind: &FunKind, cache: &mut FreshenCache) -> FunKind {
    match kind {
        FunKind::Compute | FunKind::Data => kind.clone(),
        FunKind::Var(kv) => FunKind::Var(freshen_kind_var(kv, cache)),
    }
}

/// Mint (or retrieve, cached by `uid`) the per-instantiation copy of a
/// quantified kind var, carrying across whatever the def site was pinned to.
///
/// Caching by `uid` is what keeps repeated occurrences of one `κ` in a single
/// copy identified; the copy decouples *this* instantiation's pin from the
/// definition's and from every sibling instantiation's.
fn freshen_kind_var(kv: &Rc<FunKindVar>, cache: &mut FreshenCache) -> Rc<FunKindVar> {
    if let Some(f) = cache.kind_vars.get(&kv.uid) {
        return f.clone();
    }
    let f = FunKindVar::fresh();
    f.adopt_pin(kv);
    cache.kind_vars.insert(kv.uid, Rc::clone(&f));
    f
}

/// The highest level of any inference variable **reachable** in `ty` — including
/// the ones inside refinement predicates' own type slots.
///
/// This is deliberately *not* [`type_level`], and the difference is the whole
/// point. The two answer different questions:
///
/// * [`type_level`] asks "does this participate in the lattice above `lim`?", for
///   extrusion, bound-recording scope, and let-generalization. A refinement is
///   lattice-blind, so it defers to its base and the predicate is correctly
///   invisible; a `ChanDom` reports 0 so a rigid atom flows through bounds
///   unchanged. Both are load-bearing there.
/// * Freshening asks "does this contain a variable I must **copy**?" A predicate
///   carries real type slots holding real quantified variables, so for *this*
///   question they count.
///
/// Sharing one function between the two is what let an unfreshened predicate into
/// a specialization clone: `type_level` reports the base's level for a nested
/// refinement, so a type whose only above-`lim` content lives in a predicate
/// short-circuits and is returned verbatim — still pointing at the definition's
/// live inference variables, which `src/ccl/design/type-inference.md`
/// ("3.1 Let-Polymorphism is Freshening (Instantiation)") states it must not.
/// The symptom is a duplicate specialization: the clone reaches the same
/// generalized `let` twice, once through freshened variables and once through
/// the definition's own.
fn freshen_level(ty: &Type) -> Level {
    fn predicate_level(expr: &TypedExpr) -> Level {
        let mut lvl = 0;
        expr.walk_type_slots(|t| lvl = lvl.max(freshen_level(t)));
        expr.walk_children(|c| lvl = lvl.max(predicate_level(c)));
        lvl
    }
    // One walk, not `type_level` plus a second descent: `walk_children` already
    // reaches every structural position, so the only thing to add is the
    // predicate it documents itself as skipping. `ChanDom` needs no arm — it has
    // no children and is not an `Infer`, so it contributes 0, which is the same
    // answer `type_level` gives it and for the same reason.
    let mut lvl = match ty {
        Type::Infer(v) => v.level,
        _ => 0,
    };
    if let Type::Refinement(_, r) = ty {
        lvl = lvl.max(predicate_level(&r.predicate));
    }
    ty.walk_children(|c| lvl = lvl.max(freshen_level(c)));
    lvl
}

pub fn freshen_above(
    lim: Level,
    ty: &Type,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Type {
    // The short-circuit asks [`freshen_level`], not `type_level`: a refinement's
    // predicate holds type slots whose quantified variables a low base hides, and
    // freshening has to copy them (see [`freshen_level`] for why the two levels
    // are different questions). A `ChanDom` is exempt outright: it deliberately
    // reports level 0 (its level must not trigger extrusion — see `type_level`),
    // so its quantification is decided by the arm below from its *stored*
    // introduction level.
    if !matches!(ty, Type::ChanDom(..)) && freshen_level(ty) <= lim {
        return ty.clone();
    }
    match ty {
        // `BoundedHole` is a *pre-inference* annotation marker: `normalize_annotation`
        // erases it into a bounded variable before any constraint is emitted, so
        // the solver never sees one.
        Type::BoundedHole(_) => {
            unreachable!(
                "Type::BoundedHole reached the solver; `normalize_annotation` must erase it"
            )
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_) => ty.clone(),
        // A channel domain minted inside the generalized definition
        // (level > lim) is *quantified* exactly like a variable — each
        // instantiation is its own channel. But a rigid name cannot be
        // identified through bounds the way a fresh var can, so instantiation
        // renames it here, cache-consistently ([`FreshenCache::chan_doms`] —
        // pre-seeded by `specialize_use` so the clone agrees with the use
        // site's pass-1 instantiation names). A free channel (level ≤ lim, a
        // captured outer defer) keeps its name: every instantiation's
        // contributions union into the one shared channel.
        Type::ChanDom(name, lvl) => {
            if lvl.0 <= lim {
                return ty.clone();
            }
            let fresh = cache
                .chan_doms
                .entry(name.clone())
                .or_insert_with(|| crate::ccl::Name::fresh(name.base()))
                .clone();
            let new_level = match target {
                FreshenLevel::At(level) => level,
                FreshenLevel::Preserve => lvl.0,
            };
            Type::ChanDom(fresh, crate::ccl::ChanLevel(new_level))
        }
        Type::Fun {
            name,
            kind,
            domain: d,
            codomain: c,
        } => Type::Fun {
            name: name.clone(),
            kind: freshen_kind(kind, cache),
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
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), freshen_above(lim, t, target, cache)))
                .collect(),
            *openness,
        ),
        // Freshening is polarity-free (it copies structure, not constraints),
        // so the invariant payload recurses like any other position.
        // Both children recurse (mirror `Fun`): freshening the `domain` is
        // what lets a `Mut` param's fresh domain var generalize, so each call
        // site instantiates its own domain (induction index vs. `Txn`).
        Type::History {
            value,
            domain,
            kind,
        } => Type::History {
            value: Box::new(freshen_above(lim, value, target, cache)),
            domain: Box::new(freshen_above(lim, domain, target, cache)),
            kind: *kind,
        },
        Type::Refinement(inner, r) => Type::Refinement(
            Box::new(freshen_above(lim, inner, target, cache)),
            // Faithfully freshen the predicate's own type slots through the same
            // `cache`, so a specialization's predicate is a proper freshen
            // instance — its slots are the clone's fresh variables, driven
            // concrete by the use's pin — rather than sharing the definition's
            // unresolved ones. Immutable predicate terms are acyclic, so this
            // cannot loop.
            freshen_refinement_predicate(lim, r, target, cache),
        ),
        Type::Infer(tv) => {
            if let Some(existing) = cache.vars.get(&tv.uid) {
                return Type::Infer(Rc::clone(existing));
            }
            // Mint the fresh variable at the level `target` dictates: the use
            // site's level (`At`) or the original's own level (`Preserve`).
            let new_level = match target {
                FreshenLevel::At(level) => level,
                FreshenLevel::Preserve => tv.level,
            };
            // A freshened clone stands where the original stood, so it
            // inherits the original's telescope: the bounds copied below were
            // recorded against that scope.
            let v = InferVar::fresh_in(new_level, &tv.telescope);
            cache.vars.insert(tv.uid, Rc::clone(&v));

            // Snapshot bounds before recursing — the recursion may touch
            // other variables but must not see partially-mutated state.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                (Rc::clone(s.lower()), Rc::clone(s.upper()))
            };
            // Freshen the bound's type *and* its edge substitutions' discharge
            // payloads: a payload is a captured argument *term* whose type
            // slots still reference the source graph's variables, so it is
            // freshened through the same `cache` (the uniform term+type freshen
            // that subsumes the old separate `freshen_bound_substs` sweep).
            let new_lows: Vec<_> = lows
                .iter()
                .map(|b| Bound {
                    self_subst: freshen_subst_payloads(lim, &b.self_subst, target, cache),
                    ty: freshen_above(lim, &b.ty, target, cache),
                    ty_subst: freshen_subst_payloads(lim, &b.ty_subst, target, cache),
                })
                .collect();
            let new_ups: Vec<_> = ups
                .iter()
                .map(|b| Bound {
                    self_subst: freshen_subst_payloads(lim, &b.self_subst, target, cache),
                    ty: freshen_above(lim, &b.ty, target, cache),
                    ty_subst: freshen_subst_payloads(lim, &b.ty_subst, target, cache),
                })
                .collect();
            {
                let mut s = v.bounds.borrow_mut();
                s.set_lower(new_lows);
                s.set_upper(new_ups);
            }
            freshen_watches(lim, tv, &v, target, cache);
            Type::Infer(v)
        }
    }
}

/// Copy `tv`'s trait obligations onto its freshened counterpart `v`.
///
/// Runs *after* the bounds write-back, so an obligation reached through a bound has
/// already had its variables freshened into the cache and the copy's watches line up
/// with the copy's variables.
///
/// The clone is inserted into the cache **before** its associated positions are
/// freshened.
/// The obligation graph is cyclic — an obligation holds its output type, which holds
/// a variable, which watches the obligation — so freshening the output re-enters
/// here, and a clone that is not yet reachable would be minted twice: once per
/// operand, each watching a different copy, and neither ever narrowed by both
/// operands.
fn freshen_watches(
    lim: Level,
    tv: &Rc<InferVar>,
    v: &Rc<InferVar>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) {
    let watches = tv.watches.borrow().clone();
    for (obligation, pos) in watches {
        if let Some(existing) = cache.obligations.get(&obligation.uid) {
            existing.watch(&Type::Infer(Rc::clone(v)), pos);
            continue;
        }
        // Phase 1: a copy carrying the original's candidate set, with the output
        // position still pointing at the definition's — enough to be reachable.
        let copy = TraitObligation::new_from(&obligation);
        cache.obligations.insert(obligation.uid, Rc::clone(&copy));
        copy.watch(&Type::Infer(Rc::clone(v)), pos);
        // Phase 2: now that re-entry finds the copy, freshen the output.
        copy.set_assoc_types(
            obligation
                .assoc_types()
                .iter()
                .map(|ty| freshen_above(lim, ty, target, cache))
                .collect(),
        );
    }
}

/// Freshen a refinement's predicate: clone the (immutable) predicate term,
/// freshen its type slots through `cache`, and install a fresh `Rc`. See
/// [`freshen_above`]'s `Refinement` arm.
///
/// This does not preserve predicate `Rc` sharing, and unlike the rebuilding
/// passes it threads no [`PredMemo`](crate::ccl::ccl_utils::PredMemo). The
/// `Rc::new` is unconditional, so N type slots of one clone that shared an `Rc`
/// going in come out with N distinct `Rc`s, and planning — whose compile memo is
/// `Rc`-keyed — compiles each separately. Known and not currently fixed: the
/// downstream cost is unmeasured, and the fix (memoize on
/// [`PredicateId`](crate::ccl::PredicateId) with `PredMemo`'s keepalive
/// discipline, or keep the origin `Rc` when the freshen is vacuous) is chosen
/// only once that cost is known. See `ccl/design/type-inference.md`, "One known
/// exception, scoped and unfixed: generic instantiation", for the numbers and
/// the decision.
///
/// A sharing fix here has to keep one id-set per term: reusing one rebuilt `Rc`
/// across the slots that shared an `Rc` going in is one term riding many slots,
/// and returning the origin `Rc` when the freshen is vacuous is the same.
/// Producing two *distinct* terms with equal ids is what nothing may do, and
/// nothing yet checks.
fn freshen_refinement_predicate(
    lim: Level,
    r: &Refinement,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Refinement {
    let mut pred = (*r.predicate).clone();
    freshen_expr_type_slots(&mut pred, lim, target, cache);
    Refinement::born(Rc::new(pred))
}

/// Freshen every type slot reachable from an expression, through one shared
/// [`FreshenCache`], recursing into child terms. Slot coverage is
/// [`TypedExpr::walk_type_slots_mut`]'s — `expr.ty`, the user annotation, each
/// binder's declared type, a `Cast`'s target — rather than enumerated here, so a
/// new type-slot-bearing variant cannot leave a clone with a mix of fresh and
/// original variables. Used to freshen a
/// specialization clone's whole subtree (`infer::solve::specialize_use`)
/// and, via [`freshen_refinement_predicate`], a refinement predicate's slots.
///
/// Refinement predicates carried on those types are freshened by
/// [`freshen_above`] (its `Refinement` arm), so this walk reaches *every* type
/// in the AST. A definition's interior carries variables (e.g. `Proj` seeds)
/// that never appear in its root type; missing them would leave a clone with a
/// mix of fresh and original variables and coalesce to an unresolved type.
pub fn freshen_expr_type_slots(
    expr: &mut TypedExpr,
    lim: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) {
    expr.walk_type_slots_mut(|ty| *ty = freshen_above(lim, ty, target, cache));
    expr.walk_children_mut(|c| freshen_expr_type_slots(c, lim, target, cache));
}

/// Structurally pair a use site's resolved instantiation type against the
/// definition's type, seeding `out` with def-name → use-name entries for each
/// *quantified* (level > `lim`) channel-domain name. Pass-1 instantiation
/// minted the use side's names ([`freshen_above`]'s `ChanDom` arm); the
/// specialization clone must reuse *those* names — a rigid name, unlike a
/// variable, cannot be identified with its instantiation through the pin's
/// bounds — so `specialize_use` seeds the clone's [`FreshenCache`] with these
/// pairings before freshening.
///
/// Positions are matched constructor-wise through refinements; a position
/// where the sides disagree structurally (an unexercised placeholder, a
/// collapsed union) is skipped — the clone then mints a fresh name there and
/// any stale consumer name surfaces at the post-channelize strict typecheck
/// rather than silently.
pub fn seed_chan_dom_pairings(
    use_ty: &Type,
    def_ty: &Type,
    lim: Level,
    out: &mut HashMap<crate::ccl::Name, crate::ccl::Name>,
) {
    let mut seen = std::collections::HashSet::new();
    seed_pairings_go(use_ty, def_ty, lim, out, &mut seen);
}

fn seed_pairings_go(
    use_ty: &Type,
    def_ty: &Type,
    lim: Level,
    out: &mut HashMap<crate::ccl::Name, crate::ccl::Name>,
    seen: &mut std::collections::HashSet<InferVarId>,
) {
    fn peel(ty: &Type) -> &Type {
        match ty {
            Type::Refinement(inner, _) => peel(inner),
            _ => ty,
        }
    }
    // The definition side is unresolved — a slot is often a *variable* whose
    // bounds carry the structure (a lambda definition's type is a var bounded
    // by its `Fun`). Descend through the bounds, once per var (`seen` guards
    // the cyclic bound graph). The use side is resolved; a placeholder var
    // there has no bounds and pairs nothing.
    if let Type::Infer(dv) = peel(def_ty) {
        if seen.insert(dv.uid) {
            let (lows, ups) = {
                let s = dv.bounds.borrow();
                (Rc::clone(s.lower()), Rc::clone(s.upper()))
            };
            for b in lows.iter().chain(ups.iter()) {
                seed_pairings_go(use_ty, &b.ty, lim, out, seen);
            }
        }
        return;
    }
    if let Type::Infer(uv) = peel(use_ty) {
        if seen.insert(uv.uid) {
            let (lows, ups) = {
                let s = uv.bounds.borrow();
                (Rc::clone(s.lower()), Rc::clone(s.upper()))
            };
            for b in lows.iter().chain(ups.iter()) {
                seed_pairings_go(&b.ty, def_ty, lim, out, seen);
            }
        }
        return;
    }
    match (peel(use_ty), peel(def_ty)) {
        (Type::ChanDom(u, _), Type::ChanDom(d, dlvl)) if dlvl.0 > lim && u != d => {
            let prev = out.insert(d.clone(), u.clone());
            debug_assert!(
                prev.is_none_or(|p| p == *u),
                "seed_chan_dom_pairings: definition channel `{d}` paired against two \
                 distinct use-site names"
            );
        }
        (Type::ChanDom(..), Type::ChanDom(..)) => {}
        (
            Type::Fun {
                domain: ud,
                codomain: uc,
                ..
            },
            Type::Fun {
                domain: dd,
                codomain: dc,
                ..
            },
        ) => {
            seed_pairings_go(ud, dd, lim, out, seen);
            seed_pairings_go(uc, dc, lim, out, seen);
        }
        (Type::Tuple(us), Type::Tuple(ds)) => {
            for (u, d) in us.iter().zip(ds) {
                seed_pairings_go(u, d, lim, out, seen);
            }
        }
        (Type::Record(us), Type::Record(ds)) => {
            for ((un, u), (dn, d)) in us.iter().zip(ds) {
                if un == dn {
                    seed_pairings_go(u, d, lim, out, seen);
                }
            }
        }
        // Openness plays no part in *pairing* payloads: this walks two structurally
        // corresponding types and matches arms by tag, which is the same work whether
        // either side commits to further arms.
        (Type::Variant(us, _), Type::Variant(ds, _)) => {
            for ((uk, u), (dk, d)) in us.iter().zip(ds) {
                if uk == dk {
                    seed_pairings_go(u, d, lim, out, seen);
                }
            }
        }
        (
            Type::History {
                value: uv,
                domain: ud,
                ..
            },
            Type::History {
                value: dv,
                domain: dd,
                ..
            },
        ) => {
            seed_pairings_go(uv, dv, lim, out, seen);
            seed_pairings_go(ud, dd, lim, out, seen);
        }
        // A feed handle reads through to its stream `Fun(domain, value)`
        // during coalescing (`dissolve_read_feeds`), so the use side may be
        // the dissolved `Fun` where the definition still carries the
        // `History` — or vice versa. Pair the corresponding slots.
        (
            Type::Fun {
                domain: ud,
                codomain: uc,
                ..
            },
            Type::History {
                value: dv,
                domain: dd,
                ..
            },
        ) => {
            seed_pairings_go(ud, dd, lim, out, seen);
            seed_pairings_go(uc, dv, lim, out, seen);
        }
        (
            Type::History {
                value: uv,
                domain: ud,
                ..
            },
            Type::Fun {
                domain: dd,
                codomain: dc,
                ..
            },
        ) => {
            seed_pairings_go(ud, dd, lim, out, seen);
            seed_pairings_go(uv, dc, lim, out, seen);
        }
        _ => {}
    }
}

/// Freshen the discharge payloads of a bound edge's substitution: each captured
/// argument *term* has its type slots renamed through `cache`. Renames carry no
/// term, so only [`crate::ccl::subst::Mapping::Discharge`] entries are touched.
fn freshen_subst_payloads(
    lim: Level,
    subst: &Subst,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Subst {
    let mut subst = subst.clone();
    subst.for_each_discharge_term_mut(&mut |t| freshen_expr_type_slots(t, lim, target, cache));
    subst
}

#[cfg(test)]
mod tests {
    use super::super::type_level;
    use super::*;
    use crate::ccl::ty::{FunKind, FunKindVar, KindPin};
    use crate::ccl::{BaseType, InferVar};

    #[test]
    fn freshening_mints_a_distinct_kind_var_per_instantiation() {
        // A generalized function's kind must be decided per use. Freshening
        // a Fun whose kind is an unpinned var must mint a *new* FunKindVar (the pin
        // copied), not share the original — otherwise pinning one instantiation's
        // kind contaminates the other into a spurious `DomainJoinConflict`.
        let kv = FunKindVar::fresh();
        kv.pin_data(); // a def-intrinsic answer to carry onto each instantiation
        // A quantified domain (level > lim) so the Fun is instantiated, not
        // early-returned as a captured/monomorphic shape.
        let f = Type::Fun {
            name: None,
            kind: FunKind::Var(Rc::clone(&kv)),
            domain: Box::new(Type::Infer(InferVar::fresh(5))),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let mut cache = FreshenCache::new();
        let fresh = freshen_above(0, &f, FreshenLevel::At(1), &mut cache);
        let Type::Fun {
            kind: FunKind::Var(kv2),
            ..
        } = fresh
        else {
            panic!("expected a kind var on the freshened function");
        };
        assert_ne!(
            kv.uid, kv2.uid,
            "instantiation must mint a distinct kind var"
        );
        assert_eq!(
            kv2.pin(),
            KindPin::Data,
            "the definition's pin is copied to the fresh var"
        );
        // Pinning the fresh instantiation must not reach back to the original.
        kv2.pin_compute();
        assert_eq!(
            kv.pin(),
            KindPin::Data,
            "the original var stays decoupled from this instantiation"
        );
    }

    /// A quantified variable reachable *only* through a refinement predicate must
    /// still be freshened.
    ///
    /// The shape is the one a comprehension produces: a `Fun` whose every
    /// structural position is ground (`[0,2] ⇒ Int`), carrying a refinement whose
    /// base is also ground — so `type_level` reports 0 for the whole thing — while
    /// the predicate holds a level-5 variable. Short-circuiting on `type_level`
    /// returns the type verbatim and the clone keeps pointing at the definition's
    /// live variable, which shows up downstream as a *duplicate* specialization:
    /// the clone reaches one generalized `let` through both the freshened variable
    /// and the original.
    ///
    /// Guarding a top-level `Refinement` is not enough — one level of nesting is
    /// what the real shape has, and what this pins.
    #[test]
    fn a_variable_reachable_only_through_a_predicate_is_freshened() {
        let quantified = InferVar::fresh(5);
        // A predicate term whose *type slot* holds the quantified variable.
        let predicate = Rc::new(
            TypedExpr::lit(crate::ccl::Lit::Bool(true))
                .with_ty(Type::Infer(Rc::clone(&quantified))),
        );
        let refined_domain = Type::Refinement(
            Box::new(Type::UIntRange(3)), // ground base: hides the predicate's level
            Refinement::sharing(&predicate),
        );
        let ty = Type::Fun {
            name: None,
            kind: FunKind::Compute,
            domain: Box::new(refined_domain),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        assert_eq!(
            type_level(&ty),
            0,
            "precondition: `type_level` cannot see the predicate's variable"
        );

        let mut cache = FreshenCache::new();
        let fresh = freshen_above(0, &ty, FreshenLevel::At(1), &mut cache);

        let Type::Fun { domain, .. } = &fresh else {
            panic!("expected a function type");
        };
        let Type::Refinement(_, r) = &**domain else {
            panic!("expected the refinement to survive freshening");
        };
        let Type::Infer(v) = &r.predicate.ty else {
            panic!("expected the predicate's type slot to stay a variable");
        };
        assert_ne!(
            v.uid, quantified.uid,
            "a quantified variable reachable only through a predicate must be \
             freshened — sharing it with the definition mints a duplicate \
             specialization"
        );
    }
}

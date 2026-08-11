//! Polymorphic schemes and freshening (instantiation).
//!
//! [`PolyScheme`] is the generalized-type representation; [`freshen_above`]
//! and its helpers mint a fresh copy of a scheme body (or a specialization
//! clone's whole subtree) at a use-site level, renaming quantified variables
//! uniformly across terms, types, refinement predicates, and the suspended
//! discharge payloads riding bound edges.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ccl::subst::Subst;
use crate::ccl::ty::{FunKind, FunKindVar, FunKindVarId};
use crate::ccl::{Bound, InferVar, InferVarId, Level, Refinement, Type, TypedExpr};

use super::type_level;

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
    /// function's arrow kind ([`FunKind::Var`]) must be decided *per use*, just
    /// like the type it quantifies: two instantiations that flow into differently
    /// -kinded contexts (one demanding `Data`, one `Compute`) must not share a
    /// `FunKindVar` cell, or forcing one contaminates the other into a spurious
    /// `DomainJoinConflict`. Freshening mints one `κ'` per original `κ` (bounds
    /// copied so def-intrinsic forcing survives), consistently within a copy.
    pub kind_vars: HashMap<FunKindVarId, Rc<FunKindVar>>,
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
/// Freshen a function's arrow kind at instantiation. A concrete kind
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
/// quantified kind var, mirroring its def-site `<:` links onto the fresh copies.
///
/// Copying the bounds alone is not enough: a `<:` link is load-bearing when a
/// force arrives *after* instantiation (a use-site force on one instantiation
/// must still reach a linked sibling). Each edge `x <: y` is drawn exactly once
/// — from `x`'s `uppers` — while `lowers` are recursed only to guarantee every
/// linked var is minted; inserting into the cache before recursing terminates a
/// link cycle on the cache hit.
fn freshen_kind_var(kv: &Rc<FunKindVar>, cache: &mut FreshenCache) -> Rc<FunKindVar> {
    if let Some(f) = cache.kind_vars.get(&kv.uid) {
        return f.clone();
    }
    let f = FunKindVar::fresh();
    *f.bounds.borrow_mut() = *kv.bounds.borrow();
    cache.kind_vars.insert(kv.uid, Rc::clone(&f));
    let (uppers, lowers) = kv.links();
    for u in &uppers {
        let fu = freshen_kind_var(u, cache);
        FunKindVar::link(&f, &fu);
    }
    for l in &lowers {
        // The edge `l <: kv` is drawn from `l`'s side (its `uppers` include
        // `kv`); recurse only so `l`'s copy exists to carry it.
        freshen_kind_var(l, cache);
    }
    f
}

pub fn freshen_above(
    lim: Level,
    ty: &Type,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Type {
    // A `Refinement`'s `type_level` reflects only its base, but its predicate
    // term carries its own type slots (which may hold quantified variables a
    // low base hides). So never short-circuit a refinement on `type_level`;
    // descend and freshen the predicate slots too (each leaf slot still
    // short-circuits on its own level). A `ChanDom` is likewise exempt: it
    // deliberately reports `type_level` 0 (its level must not trigger
    // extrusion — see `type_level`), so its quantification is decided by the
    // arm below from its *stored* introduction level.
    if !matches!(ty, Type::Refinement(..) | Type::ChanDom(..)) && type_level(ty) <= lim {
        return ty.clone();
    }
    match ty {
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Txn | Type::Hole => {
            ty.clone()
        }
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
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), freshen_above(lim, t, target, cache)))
                .collect(),
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
            let v = InferVar::fresh(new_level);
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
            Type::Infer(v)
        }
    }
}

/// Freshen a refinement's predicate: clone the (immutable) predicate term,
/// freshen its type slots through `cache`, and install a fresh `Rc`. See
/// [`freshen_above`]'s `Refinement` arm.
///
/// **This does not preserve predicate `Rc` sharing, and unlike the rebuilding
/// passes it threads no [`PredMemo`](crate::ccl::ccl_utils::PredMemo).** The
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
/// Note the freshened copy's predicate interior carries the *origin's*
/// [`NodeId`](crate::ccl::provenance::NodeId)s: predicate interiors are outside
/// the id domain (`ccl/design/provenance.md`), so nothing reads or checks them and
/// a sharing fix here has no identity consequence.
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
        (Type::Variant(us), Type::Variant(ds)) => {
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
    use super::*;
    use crate::ccl::ty::{FunKind, FunKindVar};
    use crate::ccl::{BaseType, InferVar};

    #[test]
    fn freshening_mints_a_distinct_kind_var_per_instantiation() {
        // A generalized function's arrow kind must be decided per use. Freshening
        // a Fun whose kind is an unresolved var must mint a *new* FunKindVar (bounds
        // copied), not share the original — otherwise forcing one instantiation's
        // kind contaminates the other into a spurious `DomainJoinConflict`.
        let kv = FunKindVar::fresh();
        kv.bounds.borrow_mut().forced_data = true; // a def-intrinsic bound to carry
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
        assert!(
            kv2.bounds.borrow().forced_data,
            "def-intrinsic bounds are copied to the fresh var"
        );
        // Forcing the fresh instantiation must not reach back to the original.
        kv2.force_compute();
        assert!(
            !kv.bounds.borrow().forced_compute,
            "the original var stays decoupled from this instantiation"
        );
    }

    #[test]
    fn freshening_mirrors_kind_var_links_onto_instantiation() {
        // Two `<:`-linked kind vars in one scheme must stay linked after
        // freshening, so a use-site force on one instantiation still reaches its
        // sibling. Copying the bounds alone (the flags present at def time) would
        // drop the link and let a later force miss the far end.
        let lower = FunKindVar::fresh(); // κ₁
        let upper = FunKindVar::fresh(); // κ₂, with κ₁ <: κ₂
        FunKindVar::link(&lower, &upper);
        // A higher-order type with κ₁ on the (quantified) domain arrow and κ₂ on
        // the outer arrow; the Infer domain lifts both above `lim` so both are
        // instantiated rather than early-returned.
        let inner = Type::Fun {
            name: None,
            kind: FunKind::Var(Rc::clone(&lower)),
            domain: Box::new(Type::Infer(InferVar::fresh(5))),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let outer = Type::Fun {
            name: None,
            kind: FunKind::Var(Rc::clone(&upper)),
            domain: Box::new(inner),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let mut cache = FreshenCache::new();
        let fresh = freshen_above(0, &outer, FreshenLevel::At(1), &mut cache);
        let Type::Fun {
            kind: FunKind::Var(fresh_upper),
            domain: fresh_domain,
            ..
        } = fresh
        else {
            panic!("expected a kind var on the freshened outer function");
        };
        let Type::Fun {
            kind: FunKind::Var(fresh_lower),
            ..
        } = *fresh_domain
        else {
            panic!("expected a kind var on the freshened inner function");
        };
        assert_ne!(fresh_lower.uid, lower.uid);
        assert_ne!(fresh_upper.uid, upper.uid);
        // A `Compute` force on the fresh lower must propagate up the mirrored
        // link to the fresh upper — and not touch the originals.
        fresh_lower.force_compute();
        assert!(
            fresh_upper.bounds.borrow().forced_compute,
            "the def-site link κ₁ <: κ₂ must be mirrored onto the instantiation"
        );
        assert!(
            !upper.bounds.borrow().forced_compute,
            "the original vars stay decoupled from the instantiation"
        );
    }
}

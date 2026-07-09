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
use crate::ccl::{Bound, InferVar, InferVarId, Level, Refinement, Type, TypedExpr, TypedExprNode};

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
    // short-circuits on its own level).
    if !matches!(ty, Type::Refinement(..)) && type_level(ty) <= lim {
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
                s.lower = new_lows;
                s.upper = new_ups;
            }
            Type::Infer(v)
        }
    }
}

/// Freshen a refinement's predicate: clone the (immutable) predicate term,
/// freshen its type slots through `cache`, and install a fresh `Rc`. See
/// [`freshen_above`]'s `Refinement` arm.
fn freshen_refinement_predicate(
    lim: Level,
    r: &Refinement,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Refinement {
    let mut pred = (*r.predicate).clone();
    freshen_expr_type_slots(&mut pred, lim, target, cache);
    Refinement {
        predicate: Rc::new(pred),
    }
}

/// Freshen every type slot reachable from an expression — `expr.ty`, the user
/// annotation, each binder's declared type, a `Cast`'s target — through one
/// shared [`FreshenCache`], recursing into child terms. Used to freshen a
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
    expr.ty = freshen_above(lim, &expr.ty, target, cache);
    if let Some(annotation) = &mut expr.user_annotation {
        *annotation = freshen_above(lim, annotation, target, cache);
    }
    match &mut expr.node {
        TypedExprNode::Lambda { param, .. } => {
            param.ty = freshen_above(lim, &param.ty, target, cache);
        }
        TypedExprNode::Cast {
            target: cast_target,
            ..
        } => {
            *cast_target = freshen_above(lim, cast_target, target, cache);
        }
        TypedExprNode::Let { binding, .. } => {
            binding.ty = freshen_above(lim, &binding.ty, target, cache);
        }
        TypedExprNode::Case { branches, .. } => {
            for b in branches.iter_mut() {
                if let Some(p) = &mut b.pattern {
                    p.binding.ty = freshen_above(lim, &p.binding.ty, target, cache);
                }
            }
        }
        TypedExprNode::LetRec { bindings, .. } => {
            for (b, _) in bindings.iter_mut() {
                b.ty = freshen_above(lim, &b.ty, target, cache);
            }
        }
        TypedExprNode::For { target: t, .. } => {
            t.ty = freshen_above(lim, &t.ty, target, cache);
        }
        _ => {}
    }
    expr.walk_children_mut(|c| freshen_expr_type_slots(c, lim, target, cache));
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

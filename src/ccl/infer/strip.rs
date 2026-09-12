//! Post-coalesce phase: drop the refinements riding the type slots *inside* a
//! refinement predicate.
//!
//! A refinement's predicate is a term, and every node of that term carries a type
//! (`Refinement::predicate`). Those interior types accumulate refinements of their
//! own — `^+` records its sum, so the `1 ^+ 3` node inside the predicate
//! `__elem == 1 ^+ 3 ^+ 2` is itself typed `{Int | __elem == 1 ^+ 3}`. An interior
//! refinement restates what the predicate holding it already says, and it is the
//! copy a substitution leaves stale: coalesce discharges the predicate a type
//! carries as that type crosses a binder, and an interior copy the discharge did
//! not reach goes on naming the binder, which `check_scope_valid` reports as a
//! [`ScopeViolation`](crate::ccl::infer::InferError::ScopeViolation). Dropping the
//! interior refinements removes the second copy rather than keeping two in step.
//!
//! Erasure is the decision, and it is a stopgap. The defect is that substitution
//! does not descend into a predicate's interior type slots; the fix is to make it,
//! which retires this phase rather than shrinking it. Erasing instead is sound
//! because the interior copy carries no claim the predicate does not, and it is
//! bounded because it is the only thing that reads those slots — but it deletes
//! the evidence of the miss, so a substitution-descent gap in a *later* pass
//! arrives with nothing to report it.
//!
//! Nothing here memoizes across compiles. [`compiled_refinements`] is a `Vec`
//! searched by `contains` on every insert and every query, over
//! [`Refinement`]'s structural equality across whole predicate terms, and the
//! solver path behind it re-asks z3 per deficit with no memo on
//! `(base, lhs, rhs)`. Unmeasured.
//!
//! Two kinds of interior type survive.
//!
//! A refinement on a **data function's data** is exempt, body and all: planning
//! compiles such a predicate into a `Restrict`/`Iterate` at the iteration boundary
//! and operator conversion dispatches on the types of the nodes inside it, so
//! those interior types are read rather than restated. Exemption is a property of
//! the refinement, not of the position it was found at — see
//! [`compiled_refinements`].
//!
//! A `Cast`'s `target` is kept wherever it sits. It is the cast's operand rather
//! than an ascription of a node's type — `cast` takes the type it casts to as an
//! argument — and a comprehension's filter is read off it, so replacing it changes
//! what the term computes.

use crate::ccl::ccl_utils::{PredMemo, strip_refinements};
use crate::ccl::ty::FunKind;
use crate::ccl::{Expr, Refinement, Type};

/// Run the phase over a coalesced tree.
pub(super) fn strip_predicate_interiors(expr: &mut Expr) {
    let compiled = compiled_refinements(expr);
    strip_in_expr(expr, &compiled, &PredMemo::new());
}

/// Returns whether anything changed, which is what the predicate memo needs in
/// order to reuse a term instead of rebuilding it — a predicate with nothing to
/// strip keeps its `Rc`, so occurrences that arrived sharing one term leave
/// sharing one term.
fn strip_in_expr(expr: &mut Expr, compiled: &[Refinement], predicates: &PredMemo<()>) -> bool {
    let mut changed = false;
    expr.walk_type_slots_mut(|ty| changed |= strip_under_refinements(ty, compiled, predicates));
    expr.walk_children_mut(|child| changed |= strip_in_expr(child, compiled, predicates));
    changed
}

/// Strip inside the predicate of every refinement in `ty` that `compiled` does not
/// exempt.
fn strip_under_refinements(
    ty: &mut Type,
    compiled: &[Refinement],
    predicates: &PredMemo<()>,
) -> bool {
    let mut changed = false;
    if let Type::Refinement(_, refinements) = ty {
        refinements.rewrite_each(|_, refinement| {
            if !compiled.contains(refinement) {
                changed |= predicates.rebuild(refinement, &(), strip_type_slots);
            }
        });
    }
    // A refinement's `walk_children_mut` yields its base and not its predicates, so
    // this reaches refinements nested in the *structure* under `ty` and enters no
    // body. A body is entered only by `strip_type_slots`, which replaces the types
    // it finds instead of descending into them, so an interior refinement is never
    // itself rebuilt.
    ty.walk_children_mut(|child| changed |= strip_under_refinements(child, compiled, predicates));
    changed
}

/// Replace every type slot in `pred`'s subtree with its unrefined form.
fn strip_type_slots(pred: &mut Expr) -> bool {
    let mut changed = false;
    let mut go = |ty: &mut Type| {
        let stripped = strip_refinements(ty);
        if stripped != *ty {
            *ty = stripped;
            changed = true;
        }
    };
    // `walk_type_slots_mut` minus the `Cast` target this phase keeps (see the
    // module docs), which is why the slots are spelled out rather than walked.
    go(&mut pred.ty);
    pred.walk_binders_mut(|b| go(&mut b.ty));
    pred.walk_children_mut(|child| changed |= strip_type_slots(child));
    changed
}

/// The refinements planning compiles: those on a data function's data, plus every
/// refinement their predicates carry.
///
/// Collected over the whole tree before anything is rewritten, and matched by
/// [`Refinement`]'s own structural equality rather than by position or by
/// predicate `Rc`. Either alternative splits predicate sharing, which
/// `tests/predicate_sharing.rs` guards: one predicate term rides many type slots,
/// so a rule that exempts it at one slot and rewrites it at another leaves the
/// origin term and the rewritten one both live and structurally equal, which is
/// the split.
fn compiled_refinements(expr: &Expr) -> Vec<Refinement> {
    let mut out = Vec::new();
    collect_compiled_in_expr(expr, &mut out);
    out
}

fn collect_compiled_in_expr(expr: &Expr, out: &mut Vec<Refinement>) {
    expr.walk_type_slots(|ty| collect_compiled(ty, out));
    expr.walk_children(|child| collect_compiled_in_expr(child, out));
}

/// Walk for a data position, collecting nothing until one is reached.
fn collect_compiled(ty: &Type, out: &mut Vec<Refinement>) {
    if let Type::Fun {
        fun_kind,
        domain,
        codomain,
        ..
    } = ty
    {
        // The bar in `𝐴 ⤇ 𝐵` reads "the domain is the data", so a data function's
        // domain is the position whose refinements are filters. Every refinement
        // within it narrows that same data, at whatever depth the domain's
        // structure puts it.
        match fun_kind {
            FunKind::Data(_) => collect_all(domain, out),
            FunKind::Compute | FunKind::Var(_) => collect_compiled(domain, out),
        }
        collect_compiled(codomain, out);
        return;
    }
    ty.walk_children(|child| collect_compiled(child, out));
}

/// Collect every refinement in `ty`, including those reachable only through a
/// predicate.
fn collect_all(ty: &Type, out: &mut Vec<Refinement>) {
    if let Type::Refinement(_, refinements) = ty {
        for refinement in refinements {
            if !out.contains(refinement) {
                out.push(refinement.clone());
                collect_all_in_expr(&refinement.predicate, out);
            }
        }
    }
    ty.walk_children(|child| collect_all(child, out));
}

fn collect_all_in_expr(expr: &Expr, out: &mut Vec<Refinement>) {
    expr.walk_type_slots(|ty| collect_all(ty, out));
    expr.walk_children(|child| collect_all_in_expr(child, out));
}

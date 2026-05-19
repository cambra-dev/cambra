//! Miscellaneous utilities for working with CCL.

use crate::ccl::{Builtin, Expr, RefinementKind, Type, TypedExprNode};

/// Builds an application of a primitive combinator, setting the types based on
/// the input expression's type and the provided output type.
pub fn apply_primitive(expr: Expr, primitive: Builtin, output_ty: Type) -> Expr {
    apply_function(expr, Expr::builtin(primitive), output_ty)
}

/// Builds an application of a function, setting the types based on the input
/// expression's type and the provided output type.
pub fn apply_function(expr: Expr, function: Expr, output_ty: Type) -> Expr {
    let expr_ty = expr.ty.clone();
    Expr::apply(
        expr,
        function.with_ty(Type::fun(expr_ty, output_ty.clone())),
    )
    .with_ty(output_ty)
}

/// Builds a composition of expressions, setting the types based on the input
/// expressions' types. The first expression's domain type is used as the domain type of the
/// composition, and the last expression's codomain type is used as the codomain type of the composition.
pub fn typed_compose(elts: Vec<Expr>) -> Expr {
    let d_ty = elts[0].ty.domain().unwrap().clone();
    let c_ty = elts[elts.len() - 1].ty.codomain().unwrap().clone();
    Expr::compose(elts).with_ty(Type::fun(d_ty, c_ty))
}

/// Count free occurrences of `name` in `expr`, including occurrences in
/// any refinement predicates carried by the expression's type or by any
/// nested [`TypedExprNode::Lambda`]'s [`crate::ccl::Refinement`].
///
/// A variable is *free* at a use site when no enclosing
/// [`TypedExprNode::Lambda`] or [`TypedExprNode::Let`] inside `expr`
/// shadows the name on the path to that use; the count is the number of
/// such free uses.  [`TypedExprNode::Feed`] / [`TypedExprNode::Define`]
/// nodes treat their `name` field as a use of the defer-handle variable,
/// so writes to that defer count as occurrences too.
///
/// Used by:
/// - [`is_free`] — the bool wrapper for "does `name` appear at all?"
/// - [`crate::ccl::remove_defers`]'s `inline_defer` — to decide whether
///   a let-binding can be substituted away (≤1 occurrence across the
///   extracted values, no duplication risk) or should be preserved as a
///   `PendingLet` so the shared op-graph subexpression isn't duplicated.
pub fn count_free(name: &str, expr: &Expr) -> usize {
    let in_type = count_free_in_type(name, &expr.ty);
    let in_node = match &expr.node {
        TypedExprNode::Var(n) => (n == name) as usize,

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // `try_borrow().ok()` silently under-counts when a
            // refinement predicate is currently mutably borrowed.  See
            // the matching note on [`count_free_in_type`] for why this
            // is OK with today's callers and what to change if you
            // add one that runs mid-mutation.
            let in_refinement = refinement
                .as_ref()
                .and_then(|r| {
                    let RefinementKind::Predicate(pred_rc) = &r.kind;
                    pred_rc.try_borrow().ok().map(|p| count_free(name, &p))
                })
                .unwrap_or(0);
            // `param.name` shadows `name` inside the lambda body, but
            // any free occurrences in the refinement live in the
            // *outer* scope and so are not shadowed.
            let in_body = if param.name == name {
                0
            } else {
                count_free(name, body)
            };
            in_body + in_refinement
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // `binding.name` shadows `name` inside `body` only.
            count_free(name, bound_expr)
                + if binding.name == name {
                    0
                } else {
                    count_free(name, body)
                }
        }

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
            ..
        } => {
            // `init_args` and `source` are evaluated outside the loop's
            // param scope, so they're always counted.  `loop_body` is
            // inside the param scope; if any `params` shadow `name`,
            // its body uses don't count.
            let shadowed = params.iter().any(|p| p.name == name);
            let in_body = if shadowed {
                0
            } else {
                count_free(name, loop_body)
            };
            in_body
                + count_free(name, source)
                + init_args.iter().map(|a| count_free(name, a)).sum::<usize>()
        }

        // The `name` field of Feed/Define is a *use* of the defer handle
        // variable — `Feed("x", v)` is a write to the defer `x`, so `x`
        // is free here in addition to any free uses inside `value`.
        TypedExprNode::Feed {
            name: handle,
            value,
        }
        | TypedExprNode::Define {
            name: handle,
            value,
        } => (handle == name) as usize + count_free(name, value),

        // All remaining variants: just sum counts across the direct
        // children.  Atoms (Lit/Proj/Builtin/Source/Defer) have no
        // children, so the fold returns 0.
        _ => expr.fold_children(0, |acc, e| acc + count_free(name, e)),
    };
    in_node + in_type
}

/// Returns `true` if `name` appears free anywhere in `expr` — either in
/// the AST itself or inside a refinement predicate on its type.
///
/// Thin wrapper around [`count_free`]; see that function for the exact
/// shadowing rules.
pub fn is_free(name: &str, expr: &Expr) -> bool {
    count_free(name, expr) > 0
}

/// Count free occurrences of `name` inside any [`crate::ccl::Refinement`]
/// predicates carried by `ty`.  Walks structurally through `Fun`, `Tuple`,
/// and `Record` so that a refined leaf type nested anywhere inside still
/// contributes its predicate's occurrences.
///
/// This is needed because predicate refinements can name lambda
/// parameters (e.g. `[x for x in xs if x < y]` puts a refinement on the
/// source type whose predicate references `y`), and those occurrences
/// are just as much "uses of `name`" as occurrences in the term itself.
fn count_free_in_type(name: &str, ty: &Type) -> usize {
    // Refinement predicates are sub-expressions, not sub-types, so
    // `walk_children` does not descend into them — handle the predicate
    // here, then fold over the structural type children.
    let here = if let Type::Refinement(_, refinement) = ty {
        let RefinementKind::Predicate(pred_rc) = &refinement.kind;
        // `try_borrow().ok()` silently treats a failed borrow as
        // "zero occurrences."  This is intentional: callers
        // (`remove_defers::inline_defer`, etc.) run *between* CCL
        // passes when no refinement predicate is being mutated, so
        // a `borrow_mut` from somewhere else in the call stack
        // shouldn't happen.  We still use `try_borrow` defensively
        // — under-counting is a soundness issue only if a caller
        // relies on `>= 2` to gate a substitute-vs-preserve
        // decision, and a missed count would mean we substitute
        // away a shared binding.  If you add a caller that walks
        // an actively-mutating refinement, switch this to
        // `borrow()` so the mistake panics rather than
        // miscompiling.
        pred_rc
            .try_borrow()
            .ok()
            .map(|p| count_free(name, &p))
            .unwrap_or(0)
    } else {
        0
    };
    here + ty.fold_children(0, |acc, child| acc + count_free_in_type(name, child))
}

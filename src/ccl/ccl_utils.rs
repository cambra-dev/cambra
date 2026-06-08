//! Miscellaneous utilities for working with CCL.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use crate::ccl::infer::typecheck_subtype;
use crate::ccl::{
    BaseType, Builtin, Expr, Lit, Refinement, RefinementId, RefinementKind, Type, TypedExprNode,
    next_refinement_id,
};

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

/// Construct the trivially-true predicate `λ _ → true` over the given domain,
/// represented in point-free form as `true ▷ const`.
///
/// Returned expression has type `domain ⇒ Bool`.  Used by [`crate::ccl::planning`]
/// when emitting `iterate(pred)` at an unrefined iteration site, and matched by
/// op-conversion via [`is_trivially_true_predicate`] to skip the predicate's filter.
pub fn trivially_true_predicate(domain: Type) -> Expr {
    let bool_ty = Type::Base(BaseType::Bool);
    let true_lit = Expr::lit(Lit::Bool(true)).with_ty(bool_ty.clone());
    apply_primitive(true_lit, Builtin::Const, Type::fun(domain, bool_ty))
}

/// Returns `true` if `expr` is the trivially-true predicate `true ▷ const`
/// (the canonical predicate emitted at unrefined iteration sites by
/// [`crate::ccl::planning`]).
pub fn is_trivially_true_predicate(expr: &Expr) -> bool {
    let TypedExprNode::Apply { argument, function } = &expr.node else {
        return false;
    };
    matches!(&function.node, TypedExprNode::Builtin(Builtin::Const))
        && matches!(&argument.node, TypedExprNode::Lit(Lit::Bool(true)))
}

/// Construct `Apply(predicate, Iterate)`, the chain-head iteration-source
/// marker emitted by [`crate::ccl::planning`] at every iteration site.
/// `predicate` must have type `D ⇒ Bool` (a point-free combinator chain
/// after lambda elimination).
///
/// The result has type `{D | p} ⇒ {D | p}` — `iterate(p)` is the identity
/// on the predicate's refined domain.  As a special case, when `predicate`
/// is the trivially-true predicate (recognised by
/// [`is_trivially_true_predicate`]), the output type degenerates to
/// `D ⇒ D` with no refinement wrapper: the refinement would carry no
/// information, and skipping it keeps program dumps and golden tests
/// free of `{D | true ▷ const}` noise.  The refinement is fresh —
/// refinement IDs are used only for cycle detection in walkers and
/// extent caching, so a fresh ID per marker is safe.
///
/// Op-conversion compiles `Apply(p, Iterate)` to an `IterateExtent` tile
/// (plus a `Restrict` filter when the predicate is non-trivial).  The
/// Iterate arm requires `input=None` — mid-chain filtering is handled by
/// the separate [`make_restrict`] form.  Refinements are transparent
/// under [`crate::ccl::infer::typecheck`], so the symmetric
/// `{D | p} ⇒ {D | p}` shape composes cleanly against either a refined
/// or unrefined adjacent edge.
pub fn make_iterate(predicate: Expr) -> Expr {
    let domain = predicate
        .ty
        .domain()
        .expect("iterate predicate must have a function type")
        .clone();
    let refined = refine_with(domain, &predicate);
    apply_primitive(
        predicate,
        Builtin::Iterate,
        Type::fun(refined.clone(), refined),
    )
}

/// Construct the mid-chain filter `restrict(p)` **applied to its
/// `upstream` value-producer** — the term `Apply(upstream, Apply(p,
/// Restrict))`.
///
/// `restrict` is a *codomain-parametric function transformer*: given a
/// predicate `p : D ⇒ Bool` it narrows the domain of an upstream
/// `D ⇒ T`, passing the values `T` through unchanged.  So the transformer
/// `Apply(p, Restrict)` has type `(D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`, and
/// applying it to `upstream : D ⇒ T` yields `{d : D | p(d)} ⇒ T` — the
/// refinement on the **domain**, the value `T` preserved on the codomain.
///
/// This is application, not composition: `restrict`'s domain is a
/// *function* type, so it cannot sit as a morphism in a CCC `Compose`
/// chain (its honest type makes that ill-typed, and [`typecheck`] now
/// rejects it).  Modelling it as an applied higher-order function is what
/// keeps the emitted term well-typed — see [`crate::ccl::planning`].
///
/// `predicate` must have type `D ⇒ Bool` and `upstream` type `D ⇒ T`
/// (matching domains).  Emitted by [`crate::ccl::planning`] for every
/// filter step downstream of an iteration source — `JoinPlan::Loop` /
/// `JoinPlan::Hash` residual predicates and the outer layers of
/// nested-refinement iteration sites.  Op-conversion compiles it via the
/// generic applied-combinator arm: `upstream` is converted with
/// `input=None`, then the `Restrict` arm consumes it as `input=Some(_)`,
/// compiles the predicate against it, and wraps it in a `Restrict` tile.
/// Chain-head iteration is the separate [`make_iterate`] form.
///
/// [`typecheck`]: crate::ccl::infer::typecheck
pub fn make_restrict(predicate: Expr, upstream: Expr) -> Expr {
    let domain = predicate
        .ty
        .domain()
        .expect("restrict predicate must have a function type")
        .clone();
    let upstream_ty = upstream.ty.clone();
    let value_ty = upstream_ty
        .codomain()
        .expect("restrict upstream must have a function type D ⇒ T")
        .clone();
    debug_assert!(
        typecheck_subtype(&upstream_ty.domain().unwrap(), &domain),
        "restrict upstream domain {} must match predicate domain {}",
        upstream_ty.domain().unwrap(),
        domain,
    );
    // `{d : D | p(d)} ⇒ T` — refinement on the domain, value preserved.
    let refined_stream = Type::fun(refine_with(domain, &predicate), value_ty);
    // The transformer node `restrict(p) : (D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`.
    let restrict = apply_primitive(
        predicate,
        Builtin::Restrict,
        Type::fun(upstream_ty, refined_stream.clone()),
    );
    apply_function(upstream, restrict, refined_stream)
}

/// Wrap `base` in a fresh `Type::Refinement` carrying `predicate`,
/// unless the predicate is trivially true (then return `base` unchanged).
fn refine_with(base: Type, predicate: &Expr) -> Type {
    if is_trivially_true_predicate(predicate) {
        return base;
    }
    Type::Refinement(
        Box::new(base),
        Refinement {
            id: next_refinement_id(),
            description: String::new(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(predicate.clone()))),
        },
    )
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
/// - [`crate::ccl::desugar_defers`] — to detect when a defer's value
///   references another defer in the same cluster, and to decide
///   whether feed values reference other channels (cluster membership).
/// - [`crate::ccl::lambda_elim`] — to decide whether a lambda's body
///   captures its parameter (`const`-lift if not) and to test refinement
///   predicate occurrences for the let-in-lambda hoisting rules.
pub fn count_free(name: &str, expr: &Expr) -> usize {
    count_free_with_visited(name, expr, &mut HashSet::new())
}

/// Recursive worker for [`count_free`].  Threads a `visited` set of
/// already-walked [`crate::ccl::RefinementId`]s so that self-referential
/// refinements (a Lambda param `xs` whose type contains a refinement
/// whose predicate references `xs`) terminate cleanly.  Each refinement
/// is walked at most once per top-level [`count_free`] call — its
/// predicate's free-var count is collected on first encounter and
/// short-circuited on subsequent encounters.
fn count_free_with_visited(name: &str, expr: &Expr, visited: &mut HashSet<RefinementId>) -> usize {
    let in_type = count_free_in_type_with_visited(name, &expr.ty, visited);
    let in_node = match &expr.node {
        TypedExprNode::Var(n) => (n == name) as usize,

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // `try_borrow().ok()` silently under-counts when a
            // refinement predicate is currently mutably borrowed.  See
            // the matching note on [`count_free_in_type_with_visited`]
            // for why this is OK with today's callers.
            let in_refinement = refinement
                .as_ref()
                .and_then(|r| {
                    if !visited.insert(r.id) {
                        return Some(0);
                    }
                    let RefinementKind::Predicate(pred_rc) = &r.kind;
                    pred_rc
                        .try_borrow()
                        .ok()
                        .map(|p| count_free_with_visited(name, &p, visited))
                })
                .unwrap_or(0);
            // `param.name` shadows `name` inside the lambda body, but
            // any free occurrences in the refinement live in the
            // *outer* scope and so are not shadowed.
            let in_body = if param.name == name {
                0
            } else {
                count_free_with_visited(name, body, visited)
            };
            in_body + in_refinement
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            // `binding.name` shadows `name` inside `body` only.
            count_free_with_visited(name, bound_expr, visited)
                + if binding.name == name {
                    0
                } else {
                    count_free_with_visited(name, body, visited)
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
                count_free_with_visited(name, loop_body, visited)
            };
            in_body
                + count_free_with_visited(name, source, visited)
                + init_args
                    .iter()
                    .map(|a| count_free_with_visited(name, a, visited))
                    .sum::<usize>()
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
        } => (handle == name) as usize + count_free_with_visited(name, value, visited),

        // A `Case` branch's structural pattern binds its payload name,
        // shadowing `name` inside that branch's guard and body.
        // `walk_children` only visits child Exprs and can't see that
        // `pattern.binding.name` shadows `name`, so it would over-count
        // free occurrences in shadowing branches. Handle `Case` explicitly.
        // (Guard-only branches have `pattern: None` and never shadow.)
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            let scrut = scrutinee
                .as_ref()
                .map_or(0, |s| count_free_with_visited(name, s, visited));
            scrut
                + branches
                    .iter()
                    .map(|b| {
                        if b.pattern.as_ref().is_some_and(|p| p.binding.name == name) {
                            0
                        } else {
                            count_free_with_visited(name, &b.guard, visited)
                                + count_free_with_visited(name, &b.body, visited)
                        }
                    })
                    .sum::<usize>()
        }

        // VariantCtor payload and all other variants: just sum counts
        // across the direct children.  Atoms (Lit/Proj/Builtin/Source/
        // Defer) have no children, so the fold returns 0.
        _ => {
            let mut sum = 0;
            expr.walk_children(|e| sum += count_free_with_visited(name, e, visited));
            sum
        }
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

/// Recursive worker for the type-walking side of [`count_free`].  Same
/// `visited` set is threaded through to break self-referential
/// refinement cycles.
///
/// `try_borrow().ok()` in [`walk_refined_predicates`] silently treats a
/// failed borrow as "zero occurrences."  This is intentional: callers
/// run *between* CCL passes when no refinement predicate is being
/// mutated, so a `borrow_mut` from elsewhere in the call stack
/// shouldn't happen.  We still use `try_borrow` defensively —
/// under-counting is a soundness issue only if a caller relies on
/// `>= 2` to gate a substitute-vs-preserve decision, and a missed
/// count would mean we substitute away a shared binding.  If you add
/// a caller that walks an actively-mutating refinement, switch the
/// helper to `borrow()` so the mistake panics rather than
/// miscompiling.
fn count_free_in_type_with_visited(
    name: &str,
    ty: &Type,
    visited: &mut HashSet<RefinementId>,
) -> usize {
    let mut count = 0;
    walk_refined_predicates(ty, visited, &mut |pred, vis| {
        count += count_free_with_visited(name, pred, vis);
    });
    count
}

/// Walk every [`Type::Refinement`] reachable from `ty` and invoke `f`
/// on its predicate expression by *shared* reference.  Each refinement
/// is visited at most once per call (keyed by [`RefinementId`] in
/// `visited`) — this breaks cycles that arise when a refinement's
/// predicate has type slots referencing the same refinement
/// (e.g. inference sharing the `Rc<RefCell<Expr>>` across all places
/// the refined value surfaces).
///
/// If the predicate is currently mutably borrowed higher up the call
/// stack, the visit is silently skipped — the outer borrow is already
/// processing it.
///
/// The callback receives `visited` so it can recurse back into
/// [`walk_refined_predicates`] (or its `_mut` variant) when the
/// predicate's own subexpressions carry types that contain further
/// refinements.
///
/// This helper is the single source of truth for the
/// type-walk + visited-set cycle-handling pattern used by
/// [`count_free_in_type_with_visited`], [`crate::ccl::infer::check_fully_typed`],
/// and [`crate::ccl::lambda_elim`]'s post-pass type-refinement walk.
/// See [`walk_refined_predicates_mut`] for the mutable variant used by
/// [`crate::ccl::lambda_elim`].
/// A related dual-mechanism (try_borrow_mut fallback without an
/// explicit visited set) lives in [`crate::ccl::simplify::simplify`]
/// — see the note there for why that site can't use this helper today.
pub fn walk_refined_predicates<F>(ty: &Type, visited: &mut HashSet<RefinementId>, f: &mut F)
where
    F: FnMut(&Expr, &mut HashSet<RefinementId>),
{
    if let Type::Refinement(_, refinement) = ty
        && visited.insert(refinement.id)
    {
        let RefinementKind::Predicate(pred_rc) = &refinement.kind;
        if let Ok(p) = pred_rc.try_borrow() {
            f(&p, visited);
        }
    }
    ty.walk_children(|child| walk_refined_predicates(child, visited, f));
}

/// Mutable analog of [`walk_refined_predicates`].  Uses
/// `try_borrow_mut`; silently skips refinements whose predicate is
/// already mutably borrowed elsewhere in the call stack (the outer
/// pass is processing the same predicate).
pub fn walk_refined_predicates_mut<F>(ty: &mut Type, visited: &mut HashSet<RefinementId>, f: &mut F)
where
    F: FnMut(&mut Expr, &mut HashSet<RefinementId>),
{
    if let Type::Refinement(_, refinement) = ty
        && visited.insert(refinement.id)
    {
        let RefinementKind::Predicate(pred_rc) = &refinement.kind;
        if let Ok(mut p) = pred_rc.try_borrow_mut() {
            f(&mut p, visited);
        }
    }
    ty.walk_children_mut(|child| walk_refined_predicates_mut(child, visited, f));
}

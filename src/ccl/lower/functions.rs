//! Lambda / `def` / parameter lowering.
//!
//! Multi-arg lambdas and functions are uncurried to a single tupled-parameter
//! lambda whose body substitutes each named argument with a projection of the
//! synthetic tuple — keeping the tree free of curried `Lambda` chains.

use std::collections::HashSet;

use super::*;
use crate::{
    ccl::{Expr, Name, Type, TypedExprNode},
    chl_parser::ast::{Param, Span, Spanned},
};

/// If `param` is annotated `Mut[…]` (a pass-by-reference store parameter),
/// return its store type `Mut[V, _]`. Returns `None` for any non-`Mut`
/// annotation (or an unannotated parameter). Mirrors the `Mut[…]` stamping of an
/// induction introduction (`lower/stmts.rs :: mut_annotation_parts`).
///
/// The sequencing domain is left inferred (`D = Hole` → a fresh variable,
/// generalized per call site): the call-site argument's `Mut` type pins `D` by
/// the invariant `(Mut, Mut)` edge, and leaving it open lets one
/// `def bump(c: Mut[Int])` serve every induction accumulator.
fn mut_param_store_type(param: &Param) -> Option<Result<Type, LoweringError>> {
    let annotation = param.annotation.as_ref()?;
    match mut_annotation_parts(annotation) {
        Some(Ok(value)) => Some(Ok(Type::History {
            value: Box::new(value),
            domain: Box::new(Type::Hole),
            kind: crate::ccl::HistoryKind::Store,
        })),
        Some(Err(e)) => Some(Err(e)),
        None => None,
    }
}

/// Validate that the function or lambda has at least one parameter.
///
/// The CHL parser already rejects `*args`, `**kwargs`, keyword-only and
/// default arguments at the syntactic level, so the only remaining check
/// is that there is at least one positional parameter. Shared between
/// [`lower_lambda`] and [`lower_function_body`].
pub(super) fn validate_function_params(
    fn_span: Span,
    params: &[Param],
) -> Result<(), LoweringError> {
    if params.is_empty() {
        return Err(LoweringError::unsupported(
            fn_span,
            "function/lambda with no parameters not supported",
        ));
    }
    Ok(())
}

/// Wrap `body_expr` in a single uncurried lambda over `args`.
///
/// Single-arg `(x): body` → `λ x → body`.
///
/// Multi-arg `(x, y, ...): body` becomes a single lambda whose parameter is
/// a synthetic tuple `__arg_tuple_<N>`, with each named argument substituted
/// in the body by its projection of that tuple:
///
/// ```text
/// (x, y): body  ⟹  λ __arg_tuple_N → body[x := __arg_tuple_N.0,
///                                          y := __arg_tuple_N.1]
/// ```
///
/// Each multi-arg call mints a fresh `N` via
/// [`LoweringContext::fresh_tuple_arg`] so that nested multi-arg
/// lambdas/defs cannot capture each other's tuple parameter; without the
/// unique suffix, an outer substitution inserting `Var("__arg_tuple")` into
/// an inner lambda's body would be captured by the inner binder of the same
/// name.
///
/// In-place substitution (rather than wrapping the body in `let`-bindings)
/// avoids introducing function-typed `Let` nodes; when `lambda_elim`
/// rewrites a `Let` under a lambda, the bound variable's type is lifted to
/// `ParamTy ⇒ T`, producing `zip(.0, .1)`-shaped morphisms that downstream
/// passes would then need to simplify back to `id` before operator
/// conversion can compile them (simplify has no such rule today).
/// Substitution sidesteps that whole rewrite chain.
///
/// Shared between [`lower_lambda`] and [`lower_function_body`] so that both
/// `lambda x, y: …` and `def f(x, y): …` pair with [`lower_call`]'s
/// tupled-argument shape and never emit a curried `Expr::Lambda` chain that
/// `lambda_elim` would fold into an unsupported `curry(body)` — the one
/// exception being a pass-by-reference `Mut` parameter, which stays a *named*
/// curried binder (see the `Mut`-param arm below); such functions are always
/// inlined, so their curried chain never reaches `lambda_elim`.
pub(super) fn uncurry_params(
    params: &[Param],
    body_expr: Expr,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if params.len() == 1 {
        // A `Mut[…]`-annotated single parameter is a pass-by-reference store:
        // bind it at `Mut[V, D]` so body references carry `Mut` (reads deref,
        // writes lower to `MutWrite`) and inference generalizes its domain per
        // call site. The annotation rides `user_annotation` too, so the
        // discipline check's rule 3 (no *unannotated* `Mut` binding) treats it
        // as the deliberate declaration it is. Non-`Mut` params stay `Hole`
        // (inferred), as before.
        let param_ty = match mut_param_store_type(&params[0]) {
            Some(Ok(mut_ty)) => mut_ty,
            _ => Type::Hole,
        };
        let mut lam = Expr::lambda(params[0].name.as_str(), param_ty.clone(), body_expr);
        if matches!(param_ty, Type::History { .. })
            && let TypedExprNode::Lambda { param, .. } = &mut lam.node
        {
            param.user_annotation = Some(param_ty);
        }
        return Ok(lam);
    }
    // A function with a pass-by-reference `Mut` parameter is curried into a
    // chain of *named* lambdas rather than tupled: a `Mut` parameter must stay a
    // named binder so inlining renames the callee's `MutWrite` target to the
    // caller's store (a tuple projection cannot be a write target — the
    // cross-function transactional writer `def transfer(src, dst, amt)`). Such
    // functions are always inlined (a `Mut`-param function must reach its call
    // sites), so the curried chain never survives to `lambda_elim`. Call sites
    // apply curried to match (see `lower_call`, keyed on `mut_param_fns`).
    if params.iter().any(|p| mut_param_store_type(p).is_some()) {
        return Ok(params.iter().rev().fold(body_expr, |acc, param| {
            let param_ty = match mut_param_store_type(param) {
                Some(Ok(mut_ty)) => mut_ty,
                _ => Type::Hole,
            };
            let mut lam = Expr::lambda(param.name.as_str(), param_ty.clone(), acc);
            if matches!(param_ty, Type::History { .. })
                && let TypedExprNode::Lambda { param: p, .. } = &mut lam.node
            {
                p.user_annotation = Some(param_ty);
            }
            lam
        }));
    }

    // Mint the tuple name after `body_expr` is lowered so that inner
    // multi-arg lambdas (which bump the counter during body lowering)
    // receive strictly smaller ids than the outer lambda. Together with
    // the reserved `__arg_tuple_` prefix (user code cannot bind
    // double-underscore names here), this guarantees the outer
    // substitution's inserted `Var(outer_name)` never collides with an
    // inner binder.
    let tuple_name = ctx.fresh_tuple_arg();
    let body_with_subs = params.iter().enumerate().fold(body_expr, |acc, (i, arg)| {
        let proj = Expr::apply(Expr::var(&tuple_name), Expr::proj_index(i));
        substitute_param_in_body(acc, &Name::raw(arg.name.as_str()), &proj)
    });
    Ok(Expr::lambda(&tuple_name, Type::Hole, body_with_subs))
}

/// Lower a CHL lambda expression to an [`Expr::Lambda`] via
/// [`uncurry_params`].
///
/// Users who want genuine currying still write it explicitly
/// (`lambda x: lambda y: ...` or an explicit `curry(f)` call); those nest
/// through the general Lambda rule and remain unsupported past operator
/// conversion — tracked as follow-up work.
///
/// `validate_function_params` only checks for at least one parameter; the
/// CHL parser already rejects `*args`, `**kwargs`, defaults, and keyword-only
/// arguments at parse time.
pub(super) fn lower_lambda(
    lambda_span: Span,
    params: &[Param],
    body: &Spanned<ChlExpr>,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_params(lambda_span, params)?;
    // Store-ness of a `Mut[…]`-annotated parameter is its *type* (stamped by
    // `uncurry_params`), checked post-inference.
    let body_expr = lower_expr(body, ctx);
    uncurry_params(params, body_expr?, ctx)
}

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`,
/// respecting binder shadowing introduced by inner `Lambda` and `Let` nodes.
///
/// Used during multi-arg lambda lowering to rewrite named CHL parameters as
/// projections of a synthetic tuple variable. A thin wrapper over the uniform
/// engine's in-place mode ([`crate::ccl::subst::Subst::rewrite_expr`]), which
/// traverses type slots too: a comprehension filter that references an
/// enclosing multi-arg lambda's parameter — e.g.
/// `lambda lo, hi: sum([x for x in data if x >= lo])` — lowers the filter
/// into the comprehension's `Cast::target` predicate with `lo` free in it,
/// and the engine rewrites it there along with the term spine.
///
/// Capture is structurally impossible at this (pre-uniquify, raw-name) call
/// site: the replacement's `Var` uses the reserved `__arg_tuple_` prefix
/// that user code cannot bind, with a fresh unique id per multi-arg lambda
/// ([`LoweringContext::fresh_tuple_arg`]), so the engine's no-capture assert
/// cannot fire.
fn substitute_param_in_body(expr: Expr, name: &Name, replacement: &Expr) -> Expr {
    let mut expr = expr;
    crate::ccl::subst::Subst::discharge_in_place(&mut expr, name, replacement);
    expr
}

/// Lower a Python function definition body to a CCL expression.
///
/// Delegates entirely to [`lower_stmts_inner`] with the function's
/// parameter names as `outer_bindings`. If the function body's final
/// statement is a `for`-loop with a yield chain, it is lowered as a
/// generator; otherwise it's a regular function body.
pub(super) fn lower_function_body(
    fn_span: Span,
    params: &[Param],
    body: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_params(fn_span, params)?;
    let outer_bindings: HashSet<String> =
        params.iter().map(|p| p.name.as_str().to_string()).collect();

    // Surface a malformed `Mut[…]` parameter annotation eagerly: `uncurry_params`
    // treats a `Some(Err(_))` store type as an unannotated `Hole` parameter, so
    // without this the real error would be silently swallowed.
    for param in params {
        if let Some(Err(e)) = mut_param_store_type(param) {
            return Err(e);
        }
    }

    // http_serve is not permitted inside function bodies.
    let body_result = lower_stmts_inner(body, &outer_bindings, ctx, false);
    uncurry_params(params, body_result?, ctx)
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // Regular function definition tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Simple function: body is a single expression.
    #[case(
        "\
def inc(x):
    x + 1
inc",
        "\
let inc : (_ ⇒ _) = λ x → x + 1
in inc"
    )]
    // Multi-param function: uncurried to a single tupled-parameter lambda.
    #[case(
        "\
def add(x, y):
    x + y
add",
        "\
let add : (_ ⇒ _) = λ __arg_tuple_0 → __arg_tuple_0.0 + __arg_tuple_0.1
in add"
    )]
    fn test_lower_function_def(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }
}

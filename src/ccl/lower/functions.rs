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

/// If `param` is annotated `Mut[V]` (a pass-by-reference store parameter),
/// return the store type `Mut[V, D]` with an inferred sequencing domain
/// (`D = Hole` → a fresh inference variable, generalized per call site so one
/// `def bump(c: Mut[Int])` serves an induction accumulator whose domain is the
/// loop it runs over). Returns `None` for any non-`Mut` annotation (or an
/// unannotated parameter). Mirrors the `Mut[…]` stamping of an induction
/// introduction (`lower/stmts.rs :: mut_annotation_value_type`).
fn mut_param_store_type(param: &Param) -> Option<Result<Type, LoweringError>> {
    let annotation = param.annotation.as_ref()?;
    match mut_annotation_value_type(annotation) {
        Some(Ok(value)) => Some(Ok(Type::Mut {
            value: Box::new(value),
            domain: Box::new(Type::Hole),
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

/// Reject a multi-parameter function/lambda carrying any `Mut` (pass-by-reference)
/// parameter. Single-parameter pass-by-reference works on this branch; the
/// multi-parameter case (`def transfer(src: Mut[_], dst: Mut[_], amt)`) lands
/// with the transaction work, where a `Mut` param is lowered as a *named*
/// curried binder. A `Mut` param must be a named binder because inlining renames
/// the callee's `MutWrite` target to the caller's store, and a tuple projection
/// (the uncurried multi-arg encoding) is not a `Name` — so silently uncurrying a
/// `Mut` param would drop the callee's store writes. Reject rather than mislower.
fn reject_multiparam_mut(span: Span, params: &[Param]) -> Result<(), LoweringError> {
    if params.len() > 1 && params.iter().any(|p| mut_param_store_type(p).is_some()) {
        return Err(LoweringError::unsupported(
            span,
            "multi-parameter pass-by-reference (a `Mut` parameter alongside other \
             parameters) is not supported yet",
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
/// `lambda_elim` would fold into an unsupported `curry(body)`.
pub(super) fn uncurry_params(
    span: Span,
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
        // (inferred), as before. Multi-arg pass-by-ref lands with transactions.
        let param_ty = match mut_param_store_type(&params[0]) {
            Some(Ok(mut_ty)) => mut_ty,
            _ => Type::Hole,
        };
        let mut lam = Expr::lambda(params[0].name.as_str(), param_ty.clone(), body_expr);
        if matches!(param_ty, Type::Mut { .. })
            && let TypedExprNode::Lambda { param, .. } = &mut lam.node
        {
            param.user_annotation = Some(param_ty);
        }
        return Ok(lam);
    }
    // Backstop for the lambda path (`lower_lambda`), whose body is an
    // expression and so lowers without tripping `lower_function_body`'s early
    // reject; a `def` is already rejected before its body is lowered.
    reject_multiparam_mut(span, params)?;
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
    // No store book-keeping here: store-ness is the parameter's *type*. A
    // parameter spelled like an outer store is a distinct binding with its own
    // (non-`Mut`) type, so a body write to it is rejected by the post-inference
    // check, not silently absorbed. `uncurry_params` stamps a `Mut[…]`-annotated
    // parameter's `Mut` type.
    let body_expr = lower_expr(body, ctx)?;
    uncurry_params(lambda_span, params, body_expr, ctx)
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
    // A `Mut` parameter alongside others (multi-param pass-by-reference) is not
    // supported on this branch — reject *before* lowering the body, so the error
    // names the real limitation rather than a downstream "last statement must be
    // a bare expression" symptom from the store write failing to be a `MutWrite`.
    reject_multiparam_mut(fn_span, params)?;
    // Surface a malformed `Mut[…]` parameter annotation eagerly: `uncurry_params`
    // (which stamps a pass-by-reference parameter's `Mut` type from its
    // annotation) treats a non-`Mut`/`Err` annotation as an inferred hole, so
    // without this the malformed-annotation error would be swallowed.
    for p in params {
        if let Some(Err(e)) = mut_param_store_type(p) {
            return Err(e);
        }
    }
    let outer_bindings: HashSet<String> =
        params.iter().map(|p| p.name.as_str().to_string()).collect();

    // No store book-keeping: store-ness is a parameter's *type* (a `Mut[…]`
    // annotation, stamped by `uncurry_params`), known post-inference. A plain
    // parameter spelled like an outer store is a distinct binding with its own
    // non-`Mut` type, so a body write to it is rejected by the check rather than
    // masked here. http_serve is not permitted inside function bodies.
    let body_result = lower_stmts_inner(body, &outer_bindings, ctx, false)?;
    uncurry_params(fn_span, params, body_result, ctx)
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

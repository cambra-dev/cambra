//! Lambda / `def` / parameter lowering.
//!
//! Multi-arg lambdas and functions are uncurried to a single tupled-parameter
//! lambda whose body substitutes each named argument with a projection of the
//! synthetic tuple — keeping the tree free of curried `Lambda` chains.

use std::collections::HashSet;

use super::*;
use crate::{
    ccl::{Expr, Name, Type, TypedExprNode},
    chl_parser::ast::{AnnotationMode, Param, Span, Spanned},
};

/// The binder a `=> T` output annotation introduces to check the body's result.
/// Reserved (double-underscore) so it cannot collide with a user name.
const OUTPUT_BINDER: &str = "__output";

/// If `param` is annotated `Mut(…)` (a pass-by-reference mutable-variable parameter),
/// return its mutable type `Mut(V, D)` and whether it is **transactional**
/// (`Mut(V, Txn)`). Returns `None` for any non-`Mut` annotation (or an
/// unannotated parameter). Mirrors the `Mut(…)` stamping of an induction
/// introduction (`lower/stmts.rs :: mut_annotation_parts`).
///
/// The sequencing domain is left inferred (`D = Hole` → a fresh variable,
/// generalized per call site) even for a `Txn` mutable variable param: the call-site
/// argument's `Mut(_, Txn)` type pins `D = Txn` by the invariant `(Mut, Mut)`
/// edge, and leaving it open lets one `def bump(c: Mut(Int))` serve both an
/// induction accumulator and a mutable variable. The transactional flag *is* returned
/// so the body's `with begin():` writes register as transactional at lowering
/// time (the block-classification decision runs before inference).
fn mut_param_history_type(
    param: &Param,
    ctx: &mut LoweringContext,
) -> Option<Result<(Type, bool), LoweringError>> {
    let annotation = param.annotation.as_ref()?;
    match mut_annotation_parts(&annotation.ty, ctx) {
        // A `Mut(…)` annotation is exact wherever it is written, for the reason it is
        // exact at a `:=` introduction: [`Type::History`] is invariant in both
        // payloads, so `<: Mut(V)` admits exactly `Mut(V, D)` and says nothing `:`
        // does not (`lower::stmts::check_mut_decl_annotation`).
        Some(Ok(_)) if annotation.mode == AnnotationMode::Bounded => {
            Some(Err(LoweringError::unsupported(
                param.name_span,
                format!(
                    "`{} <: Mut(…)` bounds a mutable parameter by its own type: `Mut` is \
                     invariant in its value type, so `<:` claims nothing `:` does not. \
                     Write `{}: Mut(…)`",
                    param.name, param.name
                ),
            )))
        }
        Some(Ok((value, is_txn))) => Some(Ok((
            Type::History {
                value: Box::new(value),
                domain: Box::new(Type::Hole),
                kind: crate::ccl::HistoryKind::Overwrite,
            },
            is_txn,
        ))),
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
/// `\x, y -> …` and `def f(x, y): …` pair with [`lower_call`]'s
/// tupled-argument shape and never emit a curried `Expr::Lambda` chain that
/// `lambda_elim` would fold into an unsupported `curry(body)` — the one
/// exception being a pass-by-reference `Mut` parameter, which stays a *named*
/// curried binder (see the `Mut`-param arm below); such functions are always
/// inlined, so their curried chain never reaches `lambda_elim`.
pub(super) fn uncurry_params(
    params: &[Param],
    body_expr: Expr,
    fn_span: Span,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    if params.len() == 1 {
        // A `Mut(…)`-annotated single parameter is a pass-by-reference mutable variable:
        // bind it at `Mut(V, D)` so body references carry `Mut` (reads deref,
        // writes lower to `MutWrite`) and inference generalizes its domain per
        // call site. That binder type *is* the declaration — a `Lambda` param is
        // one of the two binders that may hold a mutable variable, and nothing asks an
        // annotation about it. Non-`Mut` params stay `Hole` (inferred), as before.
        // Multi-arg pass-by-ref lands with transactions.
        let param_ty = match mut_param_history_type(&params[0], ctx) {
            Some(Ok((mut_ty, _is_txn))) => mut_ty,
            _ => Type::Hole,
        };
        let mut lam = Expr::lambda(params[0].name.as_str(), param_ty.clone(), body_expr);
        if let TypedExprNode::Lambda { param, .. } = &mut lam.node {
            // A `Mut(…)` annotation is already *in* `param.ty` above, and
            // `emit_lambda` binds at `user_annotation.or(param.ty)`, so restating it
            // as an annotation would be the same type twice.
            if let Some(ann) = &params[0].annotation
                && mut_param_history_type(&params[0], ctx).is_none()
            {
                // Any *other* annotation (`int`, `List[T]`, …) is a
                // **checking-mode** declaration: attach it so `emit_lambda` binds
                // the param at its declared type and an ill-typed argument is
                // rejected at the call site. Without this the annotation was
                // silently dropped and the param inferred purely from its body (so
                // `def g(a: int)` with an identity body accepted any argument).
                param.declare(lower_type_annotation(ann, ctx)?);
            }
        }
        return Ok(lam);
    }
    // A function with a pass-by-reference `Mut` parameter is curried into a
    // chain of *named* lambdas rather than tupled: a `Mut` parameter must stay a
    // named binder so inlining renames the callee's `MutWrite` target to the
    // caller's mutable variable (a tuple projection cannot be a write target — the
    // cross-function transactional writer `def transfer(src, dst, amt)`). Such
    // functions are always inlined (a `Mut`-param function must reach its call
    // sites), so the curried chain never survives to `lambda_elim`. Call sites
    // apply curried to match (see `lower_call`, keyed on `mut_param_fns`).
    if params
        .iter()
        .any(|p| mut_param_history_type(p, ctx).is_some())
    {
        return Ok(params.iter().rev().fold(body_expr, |acc, param| {
            let param_ty = match mut_param_history_type(param, ctx) {
                Some(Ok((mut_ty, _is_txn))) => mut_ty,
                _ => Type::Hole,
            };
            let mut lam = Expr::lambda(param.name.as_str(), param_ty.clone(), acc);
            if matches!(param_ty, Type::History { .. })
                && let TypedExprNode::Lambda { param: p, .. } = &mut lam.node
            {
                p.declare(param_ty);
            }
            // Each curried lambda images one written parameter; the outermost
            // is re-tagged identically by the `def`/lambda caller.
            ctx.tag_image(lam, fn_span)
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
    let up = "lower.uncurry_proj";
    let body_with_subs = params.iter().enumerate().fold(body_expr, |acc, (i, arg)| {
        // The projection plumbing is manufactured per *occurrence*: the
        // substitution deep-freshens this template's INTERIOR into every
        // occurrence of the parameter while each occurrence keeps its own
        // id/attribution (see `substitute_param_in_body`), so tag the template's
        // three nodes as machinery leaves.
        //
        // The template itself never enters the tree. Its two interior ids reach
        // the tree as the freshened copies the frame below captures, so they are
        // origins of live nodes; its ROOT does not — each occurrence's own id
        // replaces it — so that one id is tagged and then carried by nothing.
        // Harmless in the product (the projection is filtered to the output tree,
        // so the entry drops out), and the reason there is no produced-side leak
        // class: see `design/provenance.md`, "The collapse".
        let var = ctx.tag_machinery(Expr::var(&tuple_name), fn_span, up);
        let idx = ctx.tag_machinery(Expr::proj_index(i), fn_span, up);
        let proj = ctx.tag_machinery(Expr::apply(var, idx), fn_span, up);
        substitute_param_in_body(acc, &Name::raw(arg.name.as_str()), &proj)
    });
    // Attach the *tuple* of per-parameter annotations (checking mode), mirroring the
    // single-parameter case: each annotated position is enforced at the call site,
    // unannotated positions ride `Hole` (inferred). Skip if no parameter is
    // annotated. (This arm has no `Mut` params — those are curried above.)
    let mut elem_anns: Vec<Type> = Vec::with_capacity(params.len());
    for p in params {
        elem_anns.push(match &p.annotation {
            Some(ann) => lower_type_annotation(ann, ctx)?,
            None => Type::Hole,
        });
    }
    let mut lam = Expr::lambda(&tuple_name, Type::Hole, body_with_subs);
    if elem_anns.iter().any(|t| !matches!(t, Type::Hole))
        && let TypedExprNode::Lambda { param, .. } = &mut lam.node
    {
        param.declare(Type::Tuple(elem_anns));
    }
    Ok(lam)
}

/// Lower a CHL lambda expression to an [`Expr::Lambda`] via
/// [`uncurry_params`].
///
/// Users who want genuine currying still write it explicitly
/// (`\x -> \y -> ...` or an explicit `curry(f)` call); those nest
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
    // Mutability of a `Mut(…)`-annotated parameter is its *type* (stamped by
    // `uncurry_params`), checked post-inference — there is no induction registry
    // to mask here. But a plain parameter spelled like an outer transactional
    // mutable variable is a genuine local, so SHADOW every parameter over the body
    // (popped on exit) to skip the out-of-block read gate for it — mirroring how
    // `uniquify` threads its env stack so a shadowed name reverts to its outer
    // meaning. The shadow set is keyed by pre-uniquify base name.
    let param_names: Vec<String> = params.iter().map(|p| p.name.as_str().to_string()).collect();
    let body_expr = ctx.with_shadowed(param_names, |ctx| lower_expr(body, ctx));
    uncurry_params(params, body_expr?, lambda_span, ctx)
}

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`,
/// respecting binder shadowing introduced by inner `Lambda` and `Let` nodes.
///
/// Used during multi-arg lambda lowering to rewrite named CHL parameters as
/// projections of a synthetic tuple variable. A thin wrapper over the uniform
/// engine's in-place mode ([`crate::ccl::subst::Subst::rewrite_expr`]), which
/// traverses type slots too: a comprehension filter that references an
/// enclosing multi-arg lambda's parameter — e.g.
/// `\lo, hi -> sum([x for x in data if x >= lo])` — lowers the filter
/// into the comprehension's `Cast::target` predicate with `lo` free in it,
/// and the engine rewrites it there along with the term spine.
///
/// **Root-carry** — the substitution engine's identity rule for a compound
/// replacement: it carries each *occurrence*'s own id onto the replacement root
/// (a preserve, so the root inherits the occurrence's own `Source` attribution)
/// and deep-freshens only the replacement's *interior* into fresh nodes. That is
/// what buys occurrence fidelity here: every `x` in `def f(x, y)`'s body becomes
/// its own `__arg_tuple.0` whose root still points at that `x`'s span, rather
/// than every projection mirroring the one shared `def` span. The interior
/// freshens land as ambient `Copy`s in the open lowering copy-frame below,
/// mirroring the template's machinery attribution — so every substituted node
/// stays covered by the lowering fold.
///
/// Capture is structurally impossible at this (pre-uniquify, raw-name) call
/// site: the replacement's `Var` uses the reserved `__arg_tuple_` prefix
/// that user code cannot bind, with a fresh unique id per multi-arg lambda
/// ([`LoweringContext::fresh_tuple_arg`]), so the engine's no-capture assert
/// cannot fire.
fn substitute_param_in_body(expr: Expr, name: &Name, replacement: &Expr) -> Expr {
    use crate::ccl::lineage::copy_frame;
    let mut expr = expr;
    // A lowering copy-frame: the discharge's interior freshens fire `on_copy`
    // into this frame, which flushes them as `Copy` LoweringSteps (mirroring the
    // template) into the always-on lowering log. A no-op when no session is
    // installed (the lower unit tests).
    let _frame = copy_frame("lower.uncurry_proj");
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
    output: Option<&Spanned<ChlExpr>>,
    body: &[Spanned<ChlStmt>],
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    validate_function_params(fn_span, params)?;
    let outer_bindings: HashSet<String> =
        params.iter().map(|p| p.name.as_str().to_string()).collect();

    // Scope every parameter's transactional registration to the body (restored
    // on exit), keyed on the pre-uniquify name a sibling function or outer
    // binding could reuse.
    //
    //  - A `Mut(_, Txn)`-annotated parameter is a pass-by-reference transactional
    //    mutable variable: register it so a body `x := …` / `x += …` inside a `with
    //    begin():` block is classified as a commit (the cross-function writer
    //    `def transfer(src, dst: Mut(_, Txn), …)`), and a bare read of it is gated.
    //  - An induction `Mut(V)` parameter needs no registry — its mutability is
    //    its `Type::History` (stamped by `uncurry_params`), checked post-inference. It
    //    is recorded here only so it is *not* shadowed below: a mutable variable keeps its
    //    gate, a plain local does not. A malformed `Mut(…)` annotation surfaces
    //    its error eagerly (before the body lowers).
    let snapshot = ctx.snapshot_transactional();
    let mut mut_param_names: HashSet<String> = HashSet::new();
    for param in params {
        if let Some(res) = mut_param_history_type(param, ctx) {
            let (_, is_txn) = match res {
                Ok(v) => v,
                Err(e) => {
                    ctx.restore_transactional(snapshot);
                    return Err(e);
                }
            };
            let name = param.name.as_str().to_string();
            if is_txn {
                ctx.register_transactional(name.clone());
            }
            mut_param_names.insert(name);
        }
    }

    // Shadow only the *non*-`Mut` parameters over the body: a plain param
    // spelled like an outer transactional mutable variable is a genuine local, so the
    // out-of-block read gate must skip it. A `Mut` param is a mutable variable in its own
    // right, so it keeps its gate — reading a `Mut(_, Txn)` param outside a `with
    // begin():` block in the body is still an error.
    let shadowed_params: Vec<String> = outer_bindings
        .iter()
        .filter(|n| !mut_param_names.contains(n.as_str()))
        .cloned()
        .collect();

    // http_serve is not permitted inside function bodies.
    let body_result = ctx.with_shadowed(shadowed_params, |ctx| {
        lower_stmts_inner(body, &outer_bindings, ctx, false)
    });

    // Revert the transactional registry — drop every `Mut(_, Txn)` param
    // registration and any `Mut(_, Txn)` local the body declared, keyed on the
    // pre-uniquify name a sibling function could reuse.
    ctx.restore_transactional(snapshot);

    // A `=> T` output annotation checks the body's result against `T`. Wrap the
    // body in an annotated let *inside* the lambda, so the annotation's predicate
    // sees the parameters in scope — a refinement `{Int where _ >= a}` refers to
    // parameter `a`. In the multi-arg case `uncurry_params` rewrites those
    // parameter references (in the term *and* in this annotation's type slot) to
    // tuple projections along with the rest of the body.
    let mut body_expr = body_result?;
    if let Some(output) = output {
        let output_ty = lower_type_expr(output, ctx)?;
        let ret = ctx.tag_image(Expr::var(OUTPUT_BINDER), output.span);
        body_expr = ctx.tag_image(
            Expr::let_bind_annotated(OUTPUT_BINDER, body_expr, ret, output_ty),
            output.span,
        );
    }

    // Tag the function's lambda wrapper with the `def` span. (The synthetic
    // tuple-arg lambda for the multi-param case is the user's function node,
    // so the def span is the right blame here.)
    let func = uncurry_params(params, body_expr, fn_span, ctx)?;
    Ok(ctx.tag_image(func, fn_span))
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

    /// Occurrence fidelity: in a multi-param `def` whose params occur more than
    /// once, uncurry substitutes a tuple-projection template into each occurrence,
    /// and each projection *root* keeps that occurrence's own id (see
    /// [`substitute_param_in_body`]), so it inherits that occurrence's own source
    /// span instead of the one `def` span every copy of the template shares. The
    /// corpus otherwise has no multi-param `def`, so pin the span fidelity here.
    #[test]
    fn uncurry_projection_roots_carry_occurrence_spans() {
        use crate::ccl::TypedExprNode;
        use crate::ccl::lineage::{Nature, RecorderSession, SourceProjection, collapse_lowering};
        use crate::ccl::provenance::NodeId;
        use crate::chl_parser::ast::Span;
        use std::collections::HashSet;

        // `def add(a, b):` newline `    a + a + b` newline `add(1, 2)` newline.
        // The two `a` occurrences sit at distinct source spans; `b` at a third.
        let src = "def add(a, b):\n    a + a + b\nadd(1, 2)\n";
        let a1 = Span::new(19, 20);
        let a2 = Span::new(23, 24);
        let b = Span::new(27, 28);

        let stmts = parse_module(src);
        let mut ctx = LoweringContext::default();
        let session = RecorderSession::lowering();
        let ccl = lower_stmts(&stmts, &mut ctx)
            .into_result()
            .expect("lowering failed");
        let log = session.into_lowering_log();

        let mut ids: HashSet<NodeId> = HashSet::new();
        fn all_ids(e: &Expr, acc: &mut HashSet<NodeId>) {
            acc.insert(e.node_id());
            e.walk_children(|c| all_ids(c, acc));
        }
        all_ids(&ccl, &mut ids);
        let (projection, leaks) = collapse_lowering(&log, &ids);
        assert!(leaks.is_empty(), "lowering fold is leak-free: {leaks:?}");

        // Collect the source span each uncurry-projection ROOT carries. A
        // projection node is `Apply { function: Proj(Index(_)) }` — its argument
        // is the synthetic tuple var. Its own id is the occurrence's, so its
        // projection entry is that occurrence's `Source` image.
        fn projection_spans(e: &Expr, proj: &SourceProjection, out: &mut Vec<Span>) {
            if let TypedExprNode::Apply { function, .. } = &e.node
                && matches!(function.node, TypedExprNode::Proj(_))
                && let Some(attr) = proj.get(&e.node_id())
            {
                assert_eq!(
                    attr.rewritten.nature,
                    Nature::Source,
                    "a root-carried projection preserves the occurrence's Source image"
                );
                out.extend(attr.spans.iter().copied());
            }
            e.walk_children(|c| projection_spans(c, proj, out));
        }
        let mut spans = Vec::new();
        projection_spans(&ccl, &projection, &mut spans);
        spans.sort_by_key(|s| (s.start, s.end));

        assert_eq!(
            spans,
            vec![a1, a2, b],
            "each projection root carries its OWN occurrence's span — the two `a` \
             uses at distinct spans, plus `b`, not the shared `def` span"
        );
    }
}

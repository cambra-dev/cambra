//! List-comprehension and generator-expression lowering to the CCL
//! `Lambda`/`Apply` encoding (identity, loop-join, and hash-join shapes).

use super::*;
use crate::{
    ccl::{
        BinOpKind, Expr, LogicKind, Name, Type,
        ccl_utils::{make_cast, refined_fn_type},
        uniquify,
    },
    chl_parser::ast::{AssignTarget, CompClause, Comprehension, Expr as ChlExpr, Spanned},
};

/// Lower a CHL list comprehension to the CCL Lambda/Apply encoding.
///
/// Handles three cases based on the number of generators and predicates:
///
/// **Single generator, no predicate** — identity encoding:
/// ```text
/// λ __iter_record → __iter_record ▷ lower(source) ▷ (λ var → lower(body))
/// ```
///
/// **Multiple generators / non-equality predicates** — loop-join encoding.
/// The outer lambda carries a [`Refinement`](crate::ccl::Refinement) predicate
/// with the combined guard expression; the runtime filters via a correlation vector:
/// ```text
/// λ __iter_record : {T | pred} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// **Two generators, single equality predicate** — hash-join encoding.
/// Detected by [`try_extract_ccl_equality_join`] on the lowered predicate.
/// The outer lambda carries the same [`Refinement`](crate::ccl::Refinement)
/// predicate (an equality `build_var == probe_var`); join planning
/// (`crate::ccl::join_plan`) recognises the equality shape and translates it to
/// an O(N+M) hash-join-based restriction:
/// ```text
/// λ __iter_record : {T | build_var == probe_var} →
///   __iter_record[0] ▷ lower(source0) ▷ (λ var0 →
///     __iter_record[1] ▷ lower(source1) ▷ (λ var1 → lower(body)))
/// ```
///
/// All lambdas are produced with `param.ty = Type::Hole`; [`crate::ccl::infer`]
/// converts the placeholder to a registered inference variable and fills in the
/// type annotations before compilation.
///
/// TODO this currently has an assumption that all generator variables have distinct names.
/// This might be a reasonable assumption that we should enforce, or we should fix scoping to
/// handle that case.
pub(super) fn lower_list_comp(
    comp: &Comprehension,
    ctx: &mut LoweringContext,
) -> Result<Expr, LoweringError> {
    // CHL's comprehension stores clauses (`for ... in ...` and `if ...`) in a
    // single flat list, interleaved in source order. Regroup into one
    // generator per `for`, each followed by any adjacent `if`s, so the rest
    // of this routine can operate on (target, iter, [guards]) triples.
    let generators = group_comp_clauses(&comp.clauses)?;

    // ---- Phase 1: Lower each generator's source and register its loop variable ----
    // We keep the source operators and index extents for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut gen_iter_vars: Vec<String> = Vec::new();

    for (target, iter, _) in generators.iter() {
        // Mint binder uids inside the source *now*, before Phase 5/6 clone it
        // into both the body chain and the loop-join predicate: copies of a
        // minted tree stay structurally equal (uids are preserved by
        // cloning), which is what lets inference dedup the predicate-side
        // refinement witnesses against the body-side ones. See the "mint before
        // copy" contract in `crate::ccl::uniquify`.
        let source = uniquify::run(lower_expr(iter, ctx)?);
        let var_name = extract_name_target(target, "comprehension target")?;
        gen_iter_vars.push(var_name);
        gen_sources.push(source);
    }

    // ---- Phase 2: Lower body and all predicates to CCL -------------------------
    // The generator variables are in scope over the element and guards — shadow
    // them so a body/guard read of a like-named transactional register is read
    // as the comprehension local, not gated as an out-of-block store read
    // (`[store for store in xs]`).
    let chl_preds: Vec<&Spanned<ChlExpr>> = generators
        .iter()
        .flat_map(|(_, _, ifs)| ifs.iter().copied())
        .collect();
    let (body, lowered_preds) = ctx.with_shadowed(gen_iter_vars.clone(), |ctx| {
        let body = lower_expr(&comp.element, ctx)?;
        // We hold on to the original CHL guard nodes only to build human-readable
        // description strings; all detection logic operates on the lowered CCL.
        let lowered_preds: Vec<Expr> = chl_preds
            .iter()
            .map(|e| lower_expr(e, ctx))
            .collect::<Result<_, _>>()?;
        Ok::<(Expr, Vec<Expr>), LoweringError>((body, lowered_preds))
    })?;

    // Combine all `if` guards into a single loop-join predicate (used when hash
    // join is not applicable — non-equality, 3+ generators, or multiple predicates).
    let mut pred_op: Option<Expr> = None;
    for (_chl_pred, lowered) in chl_preds.iter().zip(lowered_preds) {
        pred_op = Some(match pred_op {
            Some(lhs) => Expr::binop(lhs, BinOpKind::BoolLogic(LogicKind::And), lowered),
            None => lowered,
        });
    }

    // Sources for the loop-join restriction lambda are cloned from the
    // already-lowered gen_sources (Phase 5 drains it, so clone here).
    let mut pred_sources: Vec<Expr> = if pred_op.is_some() {
        gen_sources.clone()
    } else {
        Vec::new()
    };

    // ---- Phase 4: Build the outer iteration variable ------------------------------
    // Single generator: iterate directly over that source's index extent.
    // Multiple generators: pack all index extents into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a predicate: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see Phase 6).
    let single_gen = generators.len() == 1;
    let outer_var = "__iter_record";

    // Helper: build the index argument for generator `i`.
    // Single-gen: a bare VarRef to the outer variable.
    // Multi-gen: a RecordField projection of the i-th field from the outer record.
    let make_idx_arg = |var: Name, i: usize| -> Expr {
        let vref = Expr::var(var);
        if single_gen {
            vref
        } else {
            Expr::apply(vref, Expr::proj_index(i))
        }
    };

    // ---- Phase 5: Build the body as a nested Apply/Lambda chain ------------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    let mut body_expr: Expr = body;
    for (i, (iter_var, source)) in gen_iter_vars
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        body_expr = Expr::apply(
            Expr::apply(make_idx_arg(Name::raw(outer_var), i), source),
            Expr::lambda(iter_var, Type::Hole, body_expr),
        );
    }

    // ---- Phase 6: Attach restriction ----------
    if let Some(pred_op) = pred_op {
        // Non-equality or multi-predicate: loop-join restriction predicate.
        // The refinement's element is the implicit REFINEMENT_BINDER (the
        // record over which the correlation vector ranges); the predicate is a
        // bare boolean expression, not a lambda.
        let mut pred_expr: Expr = pred_op;
        for (i, (iter_var, pred_source)) in gen_iter_vars
            .iter()
            .zip(pred_sources.drain(..))
            .enumerate()
            .rev()
        {
            pred_expr = Expr::apply(
                Expr::apply(make_idx_arg(Name::elem(), i), pred_source),
                Expr::lambda(iter_var, Type::Hole, pred_expr),
            );
        }
        // A refined parameter lowers to a `cast(refined_fn_type, λ outer_var →
        // body_expr)` — a pure type-level assertion of the predicate-refined
        // domain.  The refinement is carried by the cast's target type; the
        // Cast Apply arm in `infer::emit` constructs the refined result
        // from it, and the generic annotation handler infers the predicate's
        // sub-expressions.
        let unrefined_lambda = Expr::lambda(outer_var, Type::Hole, body_expr);
        let target_ty = refined_fn_type(Type::Hole, pred_expr, Type::Hole);
        Ok(make_cast(unrefined_lambda, target_ty))
    } else {
        Ok(Expr::lambda(outer_var, Type::Hole, body_expr))
    }
}

// ---------------------------------------------------------------------------
// Comprehension regrouping
// ---------------------------------------------------------------------------

/// One generator clause regrouped from a CHL comprehension's flat clause list:
/// `(target, iter, ifs)`, where `ifs` is the sequence of `if`-guards that
/// followed this `for` in source order before the next `for`.
type CompGenerator<'a> = (
    &'a Spanned<AssignTarget>,
    &'a Spanned<ChlExpr>,
    Vec<&'a Spanned<ChlExpr>>,
);

/// Regroup the flat CHL comprehension clause list into one [`CompGenerator`]
/// per `for` clause.
///
/// CHL stores comprehension clauses (`for ... in ...` and `if ...`) in a
/// single list in source order; the downstream lowering logic expects each
/// generator's guards bundled with it, so we walk the clauses and attach each
/// `If` to its most recent `For`. A leading `If` (before any `For`) is a
/// parse-level error category but is defensively rejected here too.
fn group_comp_clauses(clauses: &[CompClause]) -> Result<Vec<CompGenerator<'_>>, LoweringError> {
    let mut out: Vec<CompGenerator<'_>> = Vec::new();
    for clause in clauses {
        match clause {
            CompClause::For { target, iter } => out.push((target, iter, Vec::new())),
            CompClause::If(guard) => {
                let Some(last) = out.last_mut() else {
                    return Err(LoweringError::unsupported(
                        guard.span,
                        "comprehension `if` clause must follow a `for` clause",
                    ));
                };
                last.2.push(guard);
            }
        }
    }
    // The CHL `comp_clauses` parser uses `.at_least(1)`, so the input list is
    // never empty in a parsed comprehension.
    assert!(
        !out.is_empty(),
        "group_comp_clauses: empty clause list (parser invariant violated)"
    );
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::*;
    use crate::ccl::symbolic::symbolic;
    use rstest::rstest;

    // -----------------------------------------------------------------------
    // List comprehension tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Identity: element passes through unchanged; lambdas are unannotated (infer fills them in).
    #[case(
        "[x for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)"
    )]
    // Constant body: loop variable unused in body.
    #[case(
        "[42 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → 42)"
    )]
    // BinOp body: loop variable used in arithmetic.
    #[case(
        "[x + 2 for x in [10, 20]]",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    // Outer capture: y is captured from an enclosing let binding.
    #[case(
        "\
y = 5
[x + y for x in [10, 20]]",
        "\
let y = 5
in λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + y)"
    )]
    // Nested comprehension: all lambdas unannotated; infer annotates them in a
    // subsequent pass.
    #[case(
        "[y for y in [x for x in [10, 20]]]",
        "λ __iter_record → __iter_record ▷ (λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)) ▷ (λ y → y)"
    )]
    fn test_lower_list_comp(#[case] code: &str, #[case] expected: &str) {
        let stmts = parse_module(code);
        let ccl = lower_stmts(&stmts, &mut LoweringContext::default())
            .into_result()
            .expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    // -----------------------------------------------------------------------
    // Generator expression tests
    // -----------------------------------------------------------------------

    #[rstest]
    // Generator expression: identical output to equivalent list comp.
    #[case(
        "(x for x in [10, 20])",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x)"
    )]
    #[case(
        "(x + 2 for x in [10, 20])",
        "λ __iter_record → __iter_record ▷ [10, 20] ▷ (λ x → x + 2)"
    )]
    fn test_lower_generator_expr(#[case] code: &str, #[case] expected: &str) {
        let expr = parse_expr(code);
        let ccl = lower_expr(&expr, &mut LoweringContext::default()).expect("lowering failed");
        assert_eq!(symbolic(&ccl), expected);
    }

    /// A source call nested inside a larger expression lowers correctly.
    #[test]
    fn test_lower_source_in_list_comp() {
        let mut ctx = LoweringContext::default();
        ctx.register_source("src", stub_source("src"));
        let stmts = parse_module("[x for x in src()]");
        let ccl = lower_stmts(&stmts, &mut ctx)
            .into_result()
            .expect("lowering failed");
        // The source node should appear in the symbolic output.
        assert!(
            symbolic(&ccl).contains("source(src)"),
            "expected source(src) in output, got: {}",
            symbolic(&ccl)
        );
    }
}

//! List-comprehension and generator-expression lowering to the CCL
//! `Lambda`/`Apply` encoding (identity, loop-join, and hash-join shapes).

use super::*;
use crate::{
    ccl::{
        BinOpKind, Branch, Expr, LogicKind, Name, Type, TypedExprNode,
        ccl_utils::{
            flatten_trailing_value_case, make_cast, refined_data_fun, synthesize_arm_predicate,
        },
        uniquify,
    },
    chl_parser::ast::{AssignTarget, CompClause, Comprehension, Expr as ChlExpr, Spanned},
};

/// The [`Type::SharedHole`] a source annotation uses to *name* its domain, if it
/// does. Only a name is adoptable: a `Hole` domain is anonymous (nothing else can
/// refer to it) and a concrete one is already settled.
fn named_data_domain(ann: &Type) -> Option<Type> {
    match ann {
        Type::Fun { domain, .. } => match domain.as_ref() {
            d @ Type::SharedHole(_) => Some(d.clone()),
            _ => None,
        },
        _ => None,
    }
}

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
    // We keep the source operators and index domains for later use when building the
    // Apply/Lambda chains.  Each loop variable is pushed onto the lowering scope so
    // that body and predicate expressions can reference it.
    let mut gen_sources: Vec<Expr> = Vec::new();
    let mut gen_iter_vars: Vec<String> = Vec::new();
    let mut gen_spans: Vec<Span> = Vec::new();

    for (target, iter, _) in generators.iter() {
        // Mint binder uids inside the source *now*, before Phase 5/6 clone it
        // into both the body chain and the loop-join predicate: copies of a
        // minted tree stay structurally equal (uids are preserved by
        // cloning), which is what lets inference dedup the predicate-side
        // refinements against the body-side ones. See the "mint before
        // copy" contract in `crate::ccl::uniquify`.
        let source = uniquify::run(lower_expr(iter, ctx)?);
        let var_name = extract_name_target(target, "comprehension target")?;
        gen_iter_vars.push(var_name);
        gen_sources.push(source);
        gen_spans.push(iter.span);
    }

    // ---- Phase 2: Lower body and all predicates to CCL -------------------------
    // The generator variables are in scope over the element and guards — shadow
    // them so a body/guard read of a like-named transactional mutable variable is read
    // as the comprehension local, not gated as an out-of-block mutable variable read
    // (`[x for x in xs]`).
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
    // Single generator: iterate directly over that source's index domain.
    // Multiple generators: pack all index domains into a Record so the body can
    // address each one via RecordField and the runtime produces the cartesian
    // product.
    // With a predicate: wrap in Restricted so the runtime filters via a correlation
    // vector computed from the predicate (see Phase 6).
    let single_gen = generators.len() == 1;
    let outer_var = "__iter_record";

    // Helper: build the index argument for generator `i` — untagged, for the
    // Phase-6 loop-join predicate chain only (predicate-position nodes live in
    // a type slot outside the `walk_children` domain and stay unseeded).
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

    // ---- Phase 4.5: Float a value-`Case` source out of the comprehension --------
    // `[e for x in (xs if c else ys)]` — a comprehension over a *conditional
    // collection* — lowers with a value-`Case` source. Iterating it directly
    // would bind the index variable to *both* choice domains (as the read index
    // and the result domain), which inference rejects as an untagged-sum
    // collision. Because the guards do not reference the comprehension variable,
    // the `Case` floats out soundly: `[e for x in Case{gᵢ→srcᵢ}]` ⟹
    // `Case{gᵢ → [e for x in srcᵢ]}` — each arm an ordinary map over a concrete
    // collection, the enclosing `Case` a value-`Case` over collections (compiled by
    // the gate fan-out). Single generator, no comprehension
    // filter; a nested conditional source floats per arm by recursion. (A
    // multi-generator or filtered comprehension over a conditional source is a
    // follow-up — it falls through to the direct path.)
    if single_gen
        && pred_op.is_none()
        && matches!(
            &gen_sources[0].node,
            TypedExprNode::Case { scrutinee: None, branches }
                if branches.iter().all(|b| b.pattern.is_none())
        )
    {
        let source = gen_sources.pop().expect("single generator has one source");
        return Ok(float_comp_source_case(
            source,
            &gen_iter_vars[0],
            &body,
            comp.element.span,
            ctx,
        ));
    }

    // ---- Phase 4.6: Fan out a value-`Case` *element* into filtered maps ----------
    // `[a if g(x) else b for x in xs]` — a comprehension whose *element* is a
    // per-element conditional — lowers with a value-`Case` body. The `Case`
    // cannot float out (its guards reference the comprehension variable `x`), so
    // instead fan out the source by each arm's first-match gate:
    // `[eᵢ if gᵢ … for x in xs]` ⟹ `⧺ᵢ [eᵢ for x in xs if π̂ᵢ]`,
    // `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`. Each arm restricts the source by its
    // (element-dependent) gate — the ordinary filter refinement — and maps by
    // that arm's value; the gates partition the source, so the union recombines
    // the arms by position into the fully-mapped collection. A `Copair`
    // (not a `Case`), so the compute-kinded per-arm maps do not need to join.
    // Single generator, no comprehension filter; the value arms may reference `x`.
    if single_gen
        && pred_op.is_none()
        && matches!(
            &body.node,
            TypedExprNode::Case { scrutinee: None, branches }
                if branches.iter().all(|b| b.pattern.is_none())
        )
    {
        let source = gen_sources.pop().expect("single generator has one source");
        return Ok(fan_out_element_case(
            source,
            &gen_iter_vars[0],
            outer_var,
            body,
            comp.element.span,
            ctx,
        ));
    }

    // ---- Phase 5: Build the body as a nested Apply/Lambda chain ------------------
    // Working innermost-first (reverse order) we wrap the accumulated expression:
    //   body = Apply(Lambda(iter_var_i, body), Apply(source_i, idx_arg_i))
    // All chain plumbing is manufactured encoding of the comprehension rule,
    // spanned to its generator's iterable.
    // An **unfiltered single-generator** comprehension iterates *exactly* its
    // source's domain, and nothing in the lowered shape says so: the `▷` records
    // only `__iter_record <: dom(source)`, the direction an argument flows. One
    // `SharedHole` states the equality, on the two positions the claim is about —
    // the comprehension's own `data_fun` domain and the source's. Both are
    // concrete `Data`, and a data domain is *invariant*
    // (`src/ccl/design/type-inference.md`, "Data domains are invariant"), so the
    // one-way `inferred <: ann` edge each annotation records becomes two and the
    // two domains are identified rather than merely ordered.
    //
    // Restricted to this shape because it is the only one where the equality
    // holds: a *filtered* comprehension's domain is `{D | pred}`, a strict subset
    // of its source's, and a *multi-generator* one's is a product of all of them.
    // Those keep their `Hole` and stay ordered by the argument edge alone.
    //
    // A source that already *names* its domain keeps that name: `groupby` stamps
    // its own key `SharedHole` there (`lower_call`), and adopting it says the
    // stronger, truer thing — this comprehension iterates the partition's keys —
    // where minting a second id would overwrite the annotation carrying it.
    let iter_dom = (single_gen && pred_op.is_none()).then(|| {
        gen_sources[0]
            .user_annotation
            .as_ref()
            .and_then(named_data_domain)
            .unwrap_or_else(|| ctx.fresh_shared_hole())
    });
    let lc = "lower.comprehension";
    let mut body_expr: Expr = body;
    for (i, (iter_var, source)) in gen_iter_vars
        .iter()
        .zip(gen_sources.drain(..))
        .enumerate()
        .rev()
    {
        let gspan = gen_spans[i];
        let idx_arg = if single_gen {
            ctx.tag_machinery(Expr::var(Name::raw(outer_var)), gspan, lc)
        } else {
            let vref = ctx.tag_machinery(Expr::var(Name::raw(outer_var)), gspan, lc);
            let proj = ctx.tag_machinery(Expr::proj_index(i), gspan, lc);
            ctx.tag_machinery(Expr::apply(vref, proj), gspan, lc)
        };
        // Only stamp a source that did not already name its domain — otherwise the
        // id came *from* its annotation and re-stamping would discard it.
        let source = match &iter_dom {
            Some(d) if source.user_annotation.is_none() => {
                source.with_user_annotation(Type::data_fun(d.clone(), Type::Hole))
            }
            _ => source,
        };
        let indexed_source = ctx.tag_machinery(Expr::apply(idx_arg, source), gspan, lc);
        let per_elem = ctx.tag_machinery(Expr::lambda(iter_var, Type::Hole, body_expr), gspan, lc);
        body_expr = ctx.tag_machinery(Expr::apply(indexed_source, per_elem), gspan, lc);
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
        // A refined parameter lowers to a `cast(refined_data_fun, λ outer_var →
        // body_expr)` — a pure type-level assertion of the predicate-refined
        // domain.  The refinement is carried by the cast's target type; the
        // Cast Apply arm in `infer::emit` constructs the refined result
        // from it, and the generic annotation handler infers the predicate's
        // sub-expressions.
        // The outer lambda and its cast wrapper are chain plumbing too;
        // whichever of them is the comprehension's root is re-tagged as the
        // expression's direct image by `lower_expr`.
        let element_span = comp.element.span;
        // The lambda under the cast is the *same collection* the cast re-views,
        // so it carries the same `Data` provenance stamp the unfiltered branch
        // puts on its lambda (below). The cast target's `Data` alone is not
        // enough: a cast re-views its value at the target's kind, so a `Compute`
        // lambda underneath is a second, contradictory answer to what this function
        // is — one that survives into elimination, where the point-free form of
        // the collection inherits the lambda's kind and reads as a capability.
        let unrefined_lambda = ctx.tag_machinery(
            Expr::lambda(outer_var, Type::Hole, body_expr)
                .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
            element_span,
            lc,
        );
        ctx.tag_predicate(&pred_expr, element_span, "lower.comp_filter_pred");
        let target_ty = refined_data_fun(Type::Hole, pred_expr, Type::Hole);
        Ok(ctx.tag_machinery(make_cast(unrefined_lambda, target_ty), element_span, lc))
    } else {
        // A comprehension is a **data collection** (a map over its source's
        // domain): stamp it `Data` by provenance. The `data_fun(_, _)` annotation
        // is a concrete-kind stamp (`emit_node`), the unfiltered counterpart of
        // the filtered branch's `refined_data_fun` (also `Data`) cast target — so a
        // comprehension is data-by-construction, not by a domain guess. (The
        // filtered branch above stamps its own lambda the same way, under a cast
        // whose `refined_data_fun` target then refines the domain.)
        Ok(ctx.tag_machinery(
            Expr::lambda(outer_var, Type::Hole, body_expr)
                .with_user_annotation(Type::data_fun(iter_dom.unwrap_or(Type::Hole), Type::Hole)),
            comp.element.span,
            lc,
        ))
    }
}

/// Hand out a tree copy of `origin` for one arm of a fan-out. Every arm is a
/// sibling, including the first: a fan-out places the same subtree under several
/// arms and no arm is privileged. The copy-frame records each copy as a `Copy` of
/// the origin, so every arm's attribution mirrors the original's.
///
/// Keeping the first arm's ids was measured at 30 ids saved over the whole
/// pipeline suite, max subtree 5 — which does not pay for a second code path.
fn fan_out_copy(origin: &Expr, label: &'static str) -> Expr {
    use crate::ccl::lineage::copy_frame;
    let _frame = copy_frame(label);
    origin.clone()
}

/// Float a value-`Case` *source* out of a single-generator comprehension:
/// `[e for x in Case{gᵢ→srcᵢ}]` ⟹ `Case{gᵢ → [e for x in srcᵢ]}`. Sound because
/// the guards do not reference the comprehension variable `x`. Recurses so a
/// nested conditional source flattens per arm; a concrete (non-`Case`) source
/// builds the ordinary map chain `λ __idx → __idx ▷ src ▷ (λ x → body)`.
fn float_comp_source_case(
    source: Expr,
    iter_var: &str,
    body: &Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let is_value_case = matches!(
        &source.node,
        TypedExprNode::Case { scrutinee: None, branches }
            if branches.iter().all(|b| b.pattern.is_none())
    );
    if is_value_case {
        let TypedExprNode::Case { branches, .. } = source.node else {
            unreachable!("guarded by is_value_case")
        };
        let floated = branches
            .into_iter()
            .map(|b| Branch {
                pattern: b.pattern,
                guard: b.guard,
                // The arm body *is* this arm's source collection; float into it.
                body: float_comp_source_case(b.body, iter_var, body, span, ctx),
            })
            .collect();
        // The rebuilt `Case` is the floated encoding of the rule, not an image of
        // anything the user wrote.
        return ctx.tag_machinery(
            Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: floated,
            }),
            span,
            "lower.comp_source_case",
        );
    }
    // Concrete source: `source ≫ (λ x → body)` — a `Compose`, *not* the apply
    // chain Phase 5 builds. The compose form is equivalent (a map applies the
    // body to each element) and is the shape the gate fan-out downstream reads.
    //
    // Stamped `Data` here, by the site that knows: a floated arm is a map over
    // its own source, so it is a collection. That is what lets two such arms of
    // a conditional source join as collections rather than colliding as
    // capabilities whose index domains would meet — and saying it on the node
    // lowering mints is what keeps it from being decided by whoever consumes it.
    let body = fan_out_copy(body, "lower.comp_source_case_body");
    let cs = "lower.comp_source_case";
    let elem_map = ctx.tag_machinery(Expr::lambda(iter_var, Type::Hole, body), span, cs);
    ctx.tag_machinery(
        Expr::compose(vec![source, elem_map])
            .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
        span,
        cs,
    )
}

/// Fan out a single-generator comprehension whose *element* is a value-`Case`
/// into a union of filtered maps: `[eᵢ if gᵢ … for x in src]` ⟹
/// `⧺ᵢ [eᵢ for x in src if π̂ᵢ]`, first-match `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`. Each arm is a
/// filtered map — the source restricted on its domain by the arm's
/// (element-dependent) gate (a `cast` carrying the refinement, exactly the shape
/// Phase 6 builds for a comprehension `if`-filter), composed with the arm's value
/// map. The gates partition the source, so the `++`-union recombines the arms by
/// position into the fully-mapped collection.
fn fan_out_element_case(
    source: Expr,
    iter_var: &str,
    outer_var: &str,
    body: Expr,
    span: Span,
    ctx: &mut LoweringContext,
) -> Expr {
    let TypedExprNode::Case { branches, .. } = body.node else {
        unreachable!("fan_out_element_case requires a Case body")
    };
    // Flatten a nested `elif` element (`a if p else b if q else c`, a trailing
    // `true → Case{…}`) into one flat partition, so each arm is a plain value.
    let branches = flatten_trailing_value_case(branches);
    let mut prior_guards: Vec<Expr> = Vec::new();
    // The source subtree is placed once per arm in the element map and once more in
    // that arm's gate, so every use after the first must be a freshened copy.
    let arms: Vec<Expr> = branches
        .into_iter()
        .map(|b| {
            let gate = synthesize_arm_predicate(&b.guard, &prior_guards);
            prior_guards.push(b.guard);
            // Element map: `λ __idx → __idx ▷ src ▷ (λ x → eᵢ)`. Every node here is
            // manufactured encoding of the fan-out rule — the arm *bodies* keep their
            // own images, recorded when they were lowered.
            let ec = "lower.comp_elem_case";
            let idx_var = ctx.tag_machinery(Expr::var(Name::raw(outer_var)), span, ec);
            let arm_src = fan_out_copy(&source, "lower.comp_elem_case_source");
            let read = ctx.tag_machinery(Expr::apply(idx_var, arm_src), span, ec);
            let arm_body = ctx.tag_machinery(Expr::lambda(iter_var, Type::Hole, b.body), span, ec);
            let applied = ctx.tag_machinery(Expr::apply(read, arm_body), span, ec);
            // The arm *is* a filtered comprehension — a collection — so it carries
            // the `Data` stamp, like every other comprehension lambda. The cast
            // below refines its domain by the arm's gate; the target's `Data`
            // does not reach the lambda underneath.
            let elem_map = ctx.tag_machinery(
                Expr::lambda(outer_var, Type::Hole, applied)
                    .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole)),
                span,
                ec,
            );
            // Gate over the source domain: `__elem ▷ src ▷ (λ x → π̂ᵢ)` — the bare
            // refinement predicate, matching Phase 6's loop-join filter shape.
            let gate_on_source = Expr::apply(
                Expr::apply(
                    Expr::var(Name::elem()),
                    fan_out_copy(&source, "lower.comp_elem_case_source"),
                ),
                Expr::lambda(iter_var, Type::Hole, gate),
            );
            // `gate_on_source` rides the cast target's refinement predicate — a
            // type slot outside the `walk_children` walk — so nothing else will
            // record its interior, and `collect_tree_ids` now enumerates it.
            // Sweep it (`design/provenance.md`, "Walking the ids", crossing 1).
            ctx.tag_predicate(&gate_on_source, span, "lower.comp_arm_gate_pred");
            let target = refined_data_fun(Type::Hole, gate_on_source, Type::Hole);
            ctx.tag_machinery(make_cast(elem_map, target), span, ec)
        })
        .collect();
    // A one-arm value `Case` (degenerate) is just the single filtered map.
    if arms.len() == 1 {
        arms.into_iter().next().expect("checked len == 1")
    } else {
        ctx.tag_machinery(Expr::copair(arms), span, "lower.comp_elem_case")
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

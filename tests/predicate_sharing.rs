//! Regression guard for **refinement-predicate `Rc` sharing** through type
//! inference.
//!
//! Predicates are immutable `Rc<TypedExpr>`s specifically so that a predicate
//! riding many type slots (a comprehension's filtered domain appears on its
//! source, map, cast, and consumer-contract types) is *one* allocation shared
//! by `Rc`, not one copy per occurrence. Every inference pass that rewrites
//! predicates (coalesce, retype) and every substitution
//! (`subst`/`lambda_elim`) threads a pass-scoped `ccl_utils::PredMemo` (or, for
//! substitution, keeps vacuous rewrites `Rc`-identical) to preserve that
//! sharing. If any pass regresses to an independent rebuild per occurrence, the
//! distinct-`Rc` count balloons multiplicatively with comprehension nesting —
//! which later makes planning recompile one predicate once per occurrence,
//! superlinearly.
//!
//! **What is asserted, and why it is not a threshold.** A split leaves a
//! recognizable shape: one origin term rebuilt into several `Rc`-distinct copies
//! that are *structurally equal*. Asserting "no two distinct predicate `Rc`s are
//! structurally equal" names that defect directly. A bound on the distinct-`Rc`
//! count cannot: it needs a magic number, it drifts as unrelated changes shift
//! the count, and slack in it silently tolerates the very growth it is meant to
//! catch.
//!
//! We measure at **post-inference** (cheap — milliseconds), which is where the
//! sharing is established and preserved; the downstream slowdown a regression
//! causes is in planning, but the *cause* is visible here as duplicated terms.
//!
//! **Known scope limit — this corpus is comprehension-only, and the invariant it
//! asserts is not true program-wide.** Generic instantiation
//! (`solver::scheme::freshen_refinement_predicate`) rebuilds predicates with an
//! unconditional `Rc::new` and no `PredMemo`, so any program whose UDF body
//! carries a predicate leaves structurally-equal `Rc`s behind:
//! `f = \xs -> [x for x in xs if x > 1]` measures 4 surplus of 9 distinct at one
//! call site, 29 of 38 at two. Adding such a program here **fails today** — do it
//! as the regression test when the split is fixed, not before. Tracked in the
//! lineage-redesign doc, §12.4(9); rationale in `ccl/design/type-inference.md`.

use cambra::ccl::ccl_utils::{distinct_predicate_rcs, reachable_refinements};
use cambra::ccl::infer::{TypeInferenceContext, infer};
use cambra::ccl::lower::{LoweringContext, lower_stmts};
use cambra::ccl::symbolic::symbolic;
use cambra::ccl::uniquify;
use cambra::ccl::{BaseType, Expr, Lit, Refinement, Type, TypedExprNode};
use cambra::chl_parser;
use std::rc::Rc;

/// Parse → lower → uniquify → infer `code` (the pipeline prefix through type
/// inference; comprehensions over literals need no source registration).
fn infer_source(code: &str) -> Expr {
    let module = chl_parser::parse_module(code)
        .value
        .expect("parse should succeed");
    let mut lctx = LoweringContext::default();
    let mut expr = lower_stmts(&module.body, &mut lctx)
        .value
        .expect("lowering should succeed");
    expr = uniquify::run(expr);
    let mut ictx = TypeInferenceContext::new();
    infer(&mut expr, &mut ictx).expect("inference should succeed");
    expr
}

/// Group `expr`'s `Rc`-distinct refinements by `Refinement`'s own (structural,
/// type-blind) equality and report every group with more than one member: each
/// surplus member is one refinement that entered inference as a single `Rc` and
/// left it as several — which is exactly what defeats planning's `Rc`-keyed
/// compile memo.
///
/// (Two *independently authored* predicates that happened to coincide would be a
/// false positive, so the programs below use pairwise-distinct filters — any
/// duplicate group is a genuine split.)
fn splits(expr: &Expr) -> (usize, String) {
    let mut groups: Vec<(Refinement, usize)> = Vec::new();
    for r in reachable_refinements(expr) {
        match groups.iter_mut().find(|(q, _)| *q == r) {
            Some(g) => g.1 += 1,
            None => groups.push((r, 1)),
        }
    }
    let surplus = groups.iter().map(|(_, n)| n - 1).sum();
    let detail = groups
        .iter()
        .filter(|(_, n)| *n > 1)
        .map(|(r, n)| format!("\n  {n}x  {}", symbolic(&r.predicate)))
        .collect();
    (surplus, detail)
}

/// Assert every structurally-distinct predicate in `code` survives inference as
/// exactly one `Rc`.
fn assert_no_split(code: &str) {
    let expr = infer_source(code);
    let (surplus, detail) = splits(&expr);
    assert_eq!(
        surplus,
        0,
        "inference left {surplus} redundant predicate `Rc`(s) of {} distinct: a structural \
         predicate was rebuilt per-occurrence instead of staying shared, which makes planning \
         recompile it once per occurrence.{detail}",
        distinct_predicate_rcs(&expr),
    );
}

/// The motivating case. Two levels of nesting are required: in a *singly*-nested
/// comprehension every predicate also rides some node's `ty`, so a pass that
/// misses the binder slots and cast targets happens to cost nothing. At two
/// levels, a filter predicate reachable only through a `Cast.target` appears —
/// and that is the slot `lambda_elim` and operator conversion read it from.
#[test]
fn nested_comprehension_shares_predicate_rcs() {
    assert_no_split(
        "[a + b
            for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
            for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
        if a != b]",
    );
}

/// Sharing must survive at every nesting depth, not just the one depth a fixture
/// happens to pin: the regression that made planning superlinear grew with depth.
/// Each `for … if a_i == a_{i+1}` binder contributes one distinct filter
/// predicate, and it must stay one `Rc`.
#[test]
fn filtered_join_nesting_stays_shared() {
    for n in 2..=6 {
        let binders: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        let sum = binders.join(" + ");
        let fors: String = binders
            .iter()
            .map(|b| format!("for {b} in [1, 2, 3]"))
            .collect::<Vec<_>>()
            .join(" ");
        let conds: String = binders
            .windows(2)
            .map(|w| format!("if {} == {}", w[0], w[1]))
            .collect::<Vec<_>>()
            .join(" ");
        assert_no_split(&format!("[{sum} {fors} {conds}]"));
    }
}

// ---------------------------------------------------------------------------
// Coverage of the metric itself.
//
// The assertions above are only as good as the traversal behind them: a metric
// blind to a type slot cannot observe a split there, and `Expr::walk_children`
// deliberately descends into *neither* binder-declared types nor a `Cast`'s
// `target` — the slot a comprehension filter's predicate actually lives in. A
// count-based guard with that blind spot stays green while the predicates it
// was written to protect are split. These pin each slot on a hand-built node,
// so they cannot go vacuous the way a program fixture can: once sharing is
// preserved, a cast's `target` and its `ty` hold the *same* `Rc` and a
// `ty`-only walk reaches everything.
// ---------------------------------------------------------------------------

/// `{Int | true}` over a fresh predicate `Rc`.
fn refined_int() -> Type {
    Type::refined_one(
        Type::Base(BaseType::Int),
        Refinement::born(Rc::new(Expr::lit(Lit::Bool(true)))),
    )
}

/// A predicate riding only a `Cast`'s `target`. `Expr::walk_children` visits a
/// cast's `value` but not its `target`, and downstream (`lambda_elim`, operator
/// conversion) reads the predicate from `target`.
#[test]
fn metric_counts_predicate_on_cast_target() {
    let expr = Expr::cast(Expr::lit(Lit::Int(1)), refined_int());
    assert_eq!(distinct_predicate_rcs(&expr), 1);
}

/// A predicate riding only a `Lambda`'s `param.ty`. `Expr::lambda` also stamps
/// the refinement onto the node's own `ty` (as the `Fun` domain), which *is*
/// traversed — so the node type is cleared to isolate the binder slot.
#[test]
fn metric_counts_predicate_on_lambda_param_slot() {
    let expr = Expr::lambda("x", refined_int(), Expr::var("x")).with_ty(Type::Hole);
    assert_eq!(distinct_predicate_rcs(&expr), 1);
}

/// A predicate riding only a `Let`'s `binding.ty`. `Expr::let_bind` copies
/// `bound_expr.ty` into `binding.ty`, so the bound expression's own type slot is
/// cleared to isolate the binder slot.
#[test]
fn metric_counts_predicate_on_let_binding_slot() {
    let mut expr = Expr::let_bind(
        "x",
        Expr::lit(Lit::Int(1)).with_ty(refined_int()),
        Expr::var("x"),
    );
    if let TypedExprNode::Let { bound_expr, .. } = &mut expr.node {
        bound_expr.ty = Type::Hole;
    }
    assert_eq!(distinct_predicate_rcs(&expr), 1);
}

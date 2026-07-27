//! **These tests currently FAIL.** They pin the gaps in the predicate-`Rc`
//! sharing guards added alongside `ccl_utils::PredMemo` — see
//! `tests/predicate_sharing.rs` for the guards themselves.
//!
//! Two related defects, one enabling the other:
//!
//! 1. [`distinct_predicate_rcs`] does not traverse **binder-slot types**
//!    (`Lambda`'s `param.ty`, `Let`'s `binding.ty`, `Cast`'s `target`), despite
//!    its doc-comment claiming it does. It recurses with `Expr::walk_children`,
//!    which is explicitly documented *not* to reach those slots. Predicates
//!    living only in a binder slot are invisible to it.
//!
//! 2. Because of (1), the sharing invariant is unmeasured for `Cast.target` —
//!    the slot where a list-comprehension's filter predicate actually lives
//!    (`inline.rs`: "the cast target is where its refinement predicate is
//!    written [...] `target` carries its own predicate `Rc`, independent of the
//!    one on `ty`"). Measured there, inference *does* still split sharing: a
//!    nested comprehension leaves inference with the same structural predicate
//!    scattered across several `Rc`s.
//!
//! Defect (1) is why the shipped guards are green: `distinct_predicate_rcs` is
//! the metric behind both the `retype` debug-assert tripwire in `infer::run`
//! and the assertions in `tests/predicate_sharing.rs`. Teaching it the
//! `Cast.target` arm alone is enough to trip that tripwire on the *existing*
//! `nested_comprehension_shares_predicate_rcs` input.

use cambra::ccl::ccl_utils::distinct_predicate_rcs;
use cambra::ccl::infer::{TypeInferenceContext, infer};
use cambra::ccl::lower::{LoweringContext, lower_stmts};
use cambra::ccl::symbolic::symbolic;
use cambra::ccl::{BaseType, Expr, Lit, PredicateId, Refinement, Type, TypedExprNode, uniquify};
use cambra::chl_parser;
use std::collections::HashSet;
use std::rc::Rc;

/// `{Int | true}` — a refinement over a fresh predicate `Rc`.
fn refined_int() -> Type {
    Type::Refinement(
        Box::new(Type::Base(BaseType::Int)),
        Refinement::born(Rc::new(Expr::lit(Lit::Bool(true)))),
    )
}

// ---------------------------------------------------------------------------
// Defect 1: `distinct_predicate_rcs` misses binder-slot types.
// ---------------------------------------------------------------------------

/// A predicate riding **only** a `Cast`'s `target` must be counted.
///
/// `Expr::walk_children` visits a `Cast`'s `value` but not its `target` (by
/// design — `target` is a type, reached via type walks), and
/// `distinct_predicate_rcs` adds no `Cast` arm of its own. So the count is 0.
///
/// This is the slot that matters most: a comprehension filter's predicate is
/// written on the cast target, and downstream (`lambda_elim`, operator
/// conversion) reads it from there.
#[test]
fn counts_predicate_on_cast_target() {
    let expr = Expr::cast(Expr::lit(Lit::Int(1)), refined_int());
    assert_eq!(
        distinct_predicate_rcs(&expr),
        1,
        "a predicate on a `Cast.target` is not counted — `distinct_predicate_rcs` \
         recurses with `Expr::walk_children`, which does not reach `target`"
    );
}

/// A predicate riding **only** a `Lambda`'s `param.ty` must be counted.
///
/// `Expr::lambda` also stamps the refinement onto the node's own `.ty` (as the
/// `Fun` domain), which *is* traversed — so the node type is cleared to isolate
/// the binder slot.
#[test]
fn counts_predicate_on_lambda_param_slot() {
    let expr = Expr::lambda("x", refined_int(), Expr::var("x")).with_ty(Type::Hole);
    assert_eq!(
        distinct_predicate_rcs(&expr),
        1,
        "a predicate on a `Lambda`'s `param.ty` is not counted"
    );
}

/// A predicate riding **only** a `Let`'s `binding.ty` must be counted.
///
/// `Expr::let_bind` copies `bound_expr.ty` into `binding.ty`, so the bound
/// expression's own type slot is cleared to isolate the binder slot.
#[test]
fn counts_predicate_on_let_binding_slot() {
    let mut expr = Expr::let_bind(
        "x",
        Expr::lit(Lit::Int(1)).with_ty(refined_int()),
        Expr::var("x"),
    );
    if let TypedExprNode::Let { bound_expr, .. } = &mut expr.node {
        bound_expr.ty = Type::Hole;
    }
    assert_eq!(
        distinct_predicate_rcs(&expr),
        1,
        "a predicate on a `Let`'s `binding.ty` is not counted"
    );
}

// ---------------------------------------------------------------------------
// Defect 2: inference splits sharing in the slot defect 1 hides.
// ---------------------------------------------------------------------------

/// The traversal [`distinct_predicate_rcs`] *documents* — every node's `.ty`,
/// `user_annotation`, **and binder-slot types** — collecting each distinct
/// predicate `Rc` it reaches.
fn collect_predicates(expr: &Expr) -> Vec<Rc<Expr>> {
    fn in_type(ty: &Type, out: &mut Vec<Rc<Expr>>, seen: &mut HashSet<PredicateId>) {
        if let Type::Refinement(_, r) = ty
            && seen.insert(r.predicate_id())
        {
            out.push(Rc::clone(&r.predicate));
            // A predicate's own subexpressions carry further refinements.
            in_expr(&r.predicate, out, seen);
        }
        ty.walk_children(|c| in_type(c, out, seen));
    }
    fn in_expr(e: &Expr, out: &mut Vec<Rc<Expr>>, seen: &mut HashSet<PredicateId>) {
        in_type(&e.ty, out, seen);
        if let Some(a) = &e.user_annotation {
            in_type(a, out, seen);
        }
        // The slots `Expr::walk_children` deliberately does not reach.
        match &e.node {
            TypedExprNode::Lambda { param, .. } => in_type(&param.ty, out, seen),
            TypedExprNode::Let { binding, .. } => in_type(&binding.ty, out, seen),
            TypedExprNode::Cast { target, .. } => in_type(target, out, seen),
            TypedExprNode::Case { branches, .. } => {
                for b in branches {
                    if let Some(p) = &b.pattern {
                        in_type(&p.binding.ty, out, seen);
                    }
                }
            }
            _ => {}
        }
        e.walk_children(|c| in_expr(c, out, seen));
    }
    let mut out = Vec::new();
    in_expr(expr, &mut out, &mut HashSet::new());
    out
}

/// Parse → lower → uniquify → infer (comprehensions over literals need no
/// source registration).
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

/// Sharing is preserved iff no two *distinct* predicate `Rc`s are structurally
/// equal: a rebuild pass that splits sharing produces exactly that shape — one
/// origin term rebuilt into several value-equal-but-`Rc`-distinct copies, which
/// is what defeats planning's `Rc`-keyed compile memo.
///
/// (`Refinement`'s `PartialEq` is structural, so equal-but-distinct is
/// detectable. Two *independently authored* predicates that happen to coincide
/// would be a false positive; the filters below — `c < d`, `e < f`, `a != b` —
/// are pairwise distinct, so any duplicate group is a genuine split.)
fn split_report(expr: &Expr) -> (usize, Vec<(String, usize)>) {
    let preds = collect_predicates(expr);
    let mut groups: Vec<(Rc<Expr>, usize)> = Vec::new();
    for p in &preds {
        match groups.iter_mut().find(|(q, _)| **q == **p) {
            Some(g) => g.1 += 1,
            None => groups.push((Rc::clone(p), 1)),
        }
    }
    let split = groups.iter().map(|(_, n)| n - 1).sum();
    let dups = groups
        .into_iter()
        .filter(|(_, n)| *n > 1)
        .map(|(p, n)| (symbolic(&p), n))
        .collect();
    (split, dups)
}

/// The motivating case. Post-inference, each inner comprehension's filter
/// predicate exists as **three** structurally-identical `Rc`s rather than one —
/// 7 distinct `Rc`s where 3 suffice.
///
/// The shipped `distinct_predicate_rcs` reports 5 for this same tree (it cannot
/// see the cast targets the duplicates ride), which is how
/// `nested_comprehension_shares_predicate_rcs` passes its `<= 8` bound.
#[test]
fn nested_comprehension_predicates_are_not_split() {
    let expr = infer_source(
        "[a + b
            for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
            for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
        if a != b]",
    );
    let (split, dups) = split_report(&expr);
    let detail: String = dups.iter().map(|(p, n)| format!("\n  {n}x  {p}")).collect();
    assert_eq!(
        split,
        0,
        "inference left {split} redundant predicate `Rc`(s): a structural predicate \
         was rebuilt per-occurrence instead of staying shared.{detail}\n\
         (invisible to `distinct_predicate_rcs`, which reports {} here because it \
          does not traverse `Cast.target`)",
        distinct_predicate_rcs(&expr)
    );
}

/// The metric must not under-report against the traversal it documents. Pins
/// defect 1 on a realistic tree rather than a hand-built node, so it stays
/// meaningful as `Expr`/`Type` gain variants.
///
/// A *singly*-nested comprehension does not discriminate — there, every
/// predicate also rides some node's `.ty`, so the missing binder-slot arms cost
/// nothing. The doubly-nested case is where predicates reachable only through a
/// `Cast.target` appear.
#[test]
fn metric_sees_every_predicate_it_claims_to() {
    let expr = infer_source(
        "[a + b
            for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
            for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
        if a != b]",
    );
    let complete = collect_predicates(&expr).len();
    let reported = distinct_predicate_rcs(&expr);
    assert_eq!(
        reported, complete,
        "`distinct_predicate_rcs` reports {reported} of {complete} reachable predicate \
         `Rc`s — it misses binder-slot types (`Lambda.param.ty`, `Let.binding.ty`, \
         `Cast.target`) that its doc-comment claims to cover"
    );
}

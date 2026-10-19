//! Failing guards for the review findings on the predicate-sharing work.
//!
//! Each test states one property the current code violates. They are written
//! against the smallest construction that exhibits the defect, not against a
//! source-level fixture, so a fix can be verified without reasoning about which
//! program shape happens to produce the sharing.

use cambra::ccl::ccl_utils::{
    PredMemo, distinct_predicate_rcs, is_free, walk_refined_predicates_mut,
};
use cambra::ccl::subst::Subst;
use cambra::ccl::{
    BinOpKind, CompareKind, Expr, Lit, Name, Refinement, Type, TypedExpr, TypedExprNode,
};
use std::rc::Rc;

fn var(s: &str) -> TypedExpr {
    TypedExpr::var(s)
}
fn int(n: i64) -> TypedExpr {
    TypedExpr::lit(Lit::Int(n))
}
fn gt(l: TypedExpr, r: TypedExpr) -> TypedExpr {
    TypedExpr::binop(l, BinOpKind::Compare(CompareKind::Greater), r)
}
/// `{_ | pred}`, a second occurrence of an existing predicate term.
fn refined(pred: &Rc<TypedExpr>) -> Type {
    Type::refined_one(Type::Hole, Refinement::sharing(pred))
}
/// The predicate term of a `{_ | p}`.
fn predicate_of(ty: &Type) -> &Rc<TypedExpr> {
    let [r] = ty.refinements() else {
        panic!("expected exactly one refinement, got {ty}");
    };
    &r.predicate
}

// ---------------------------------------------------------------------------
// Finding 1 — `subst`'s `PredMemo` is threaded across shadowing boundaries,
// but substitution is scope-dependent.
// ---------------------------------------------------------------------------

/// `rewrite_expr` rewrites a node's own type slots *before* descending under its
/// binders, and threads one memo across that crossing. So the occurrence rebuilt
/// in the outer scope is served to an occurrence inside a scope that **rebinds**
/// the substituted variable — applying a substitution under a binder that
/// shadows it.
///
/// Two substituted binders are needed: with only `k`, `under_binder_mut`'s
/// empty-restriction early return declines to enter the body at all.
#[test]
fn rewrite_does_not_leak_an_outer_rebuild_into_a_shadowing_scope() {
    let shared = Rc::new(gt(var("k"), int(0)));
    // λ k → (j > 0) : {_ | k > 0}          — the body's `k` is the lambda's own.
    //   with the lambda's own ty = ({_ | k > 0} ⇒ _), sharing that one predicate.
    let body = gt(var("j"), int(0)).with_ty(refined(&shared));
    let mut e =
        TypedExpr::lambda("k", Type::Hole, body).with_ty(Type::fun(refined(&shared), Type::Hole));

    // [k ↦ 5, j ↦ 6]: `j` keeps the body reachable, `k` is shadowed by the lambda.
    let s = Subst::then(
        &Subst::discharge("k", int(5)),
        &Subst::discharge("j", int(6)),
    );
    s.rewrite_expr(&mut e);

    let Type::Fun { domain, .. } = &e.ty else {
        panic!("function type preserved");
    };
    assert_eq!(
        **predicate_of(domain),
        gt(int(5), int(0)),
        "the outer occurrence is not under the binder, so it discharges"
    );

    let TypedExprNode::Lambda { body, .. } = &e.node else {
        panic!("lambda preserved");
    };
    assert_eq!(
        **predicate_of(&body.ty),
        gt(var("k"), int(0)),
        "the occurrence inside `λ k` refers to the lambda's own `k`, which the \
         substitution must not touch — but the memo served it the outer rebuild"
    );
}

/// Control for the test above: the *same two occurrences*, but as two distinct
/// `Rc`s. This passes — which localizes the defect to the memo rather than to
/// the shadowing walk, and shows that improving sharing is what exposes it.
#[test]
fn rewrite_respects_shadowing_when_the_occurrences_are_not_shared() {
    let outer = Rc::new(gt(var("k"), int(0)));
    let inner = Rc::new(gt(var("k"), int(0)));
    let body = gt(var("j"), int(0)).with_ty(refined(&inner));
    let mut e =
        TypedExpr::lambda("k", Type::Hole, body).with_ty(Type::fun(refined(&outer), Type::Hole));

    let s = Subst::then(
        &Subst::discharge("k", int(5)),
        &Subst::discharge("j", int(6)),
    );
    s.rewrite_expr(&mut e);

    let Type::Fun { domain, .. } = &e.ty else {
        panic!("function type preserved");
    };
    assert_eq!(**predicate_of(domain), gt(int(5), int(0)));
    let TypedExprNode::Lambda { body, .. } = &e.node else {
        panic!("lambda preserved");
    };
    assert_eq!(**predicate_of(&body.ty), gt(var("k"), int(0)));
}

// ---------------------------------------------------------------------------
// Finding 3 — `rewrite_expr_go` never rewrites binder-slot types, so a
// predicate riding `param.ty` is left stale against the same predicate on `ty`.
// ---------------------------------------------------------------------------

/// A lambda's domain refinement rides both `expr.ty`'s `Fun` domain and
/// `param.ty`, as two occurrences of one `Rc`. `rewrite_expr` rebuilds the
/// former and never visits the latter, so after the rewrite the two slots
/// disagree — the stale-copy defect this file exists to pin.
#[test]
fn rewrite_reaches_the_lambda_param_type_slot() {
    let shared = Rc::new(gt(var("k"), int(0)));
    let mut e = TypedExpr::lambda("x", refined(&shared), var("x"))
        .with_ty(Type::fun(refined(&shared), Type::Hole));

    Subst::discharge("k", int(5)).rewrite_expr(&mut e);

    let TypedExprNode::Lambda { param, .. } = &e.node else {
        panic!("lambda preserved");
    };
    assert_eq!(
        **predicate_of(&param.ty),
        gt(int(5), int(0)),
        "`param.ty` holds its own `Rc`, so the discharge must reach it too"
    );
}

// ---------------------------------------------------------------------------
// Finding 4 — `count_free`/`is_free` does not walk binder-slot types, while
// `walk_type_slots` does. Three "skip the work" fast paths gate on `is_free`.
// ---------------------------------------------------------------------------

/// `let y = 1 in unit` with `y : {_ | k > 0}` — `k` occurs *only* in the
/// predicate riding the `Let` binding's declared type.
///
/// `distinct_predicate_rcs` (i.e. `walk_type_slots`) sees that slot; `is_free`
/// does not. The asymmetry is load-bearing: `inline_in_type_predicates` now
/// returns early on `!is_free(name, pred)`, and `subst` skips both inert
/// subtrees and vacuous predicates the same way — so an occurrence only
/// `walk_type_slots` can see is silently left un-rewritten.
#[test]
fn is_free_sees_a_predicate_on_a_let_binding_slot() {
    let k = Name::raw("k");
    let mut e = Expr::let_bind(
        "y",
        Expr::lit(Lit::Int(1)).with_ty(refined(&Rc::new(gt(var("k"), int(0))))),
        Expr::lit(Lit::Unit),
    );
    // `let_bind` copies `bound_expr.ty` into `binding.ty`; clear the former so
    // the binder slot is the only place the predicate rides.
    if let TypedExprNode::Let { bound_expr, .. } = &mut e.node {
        bound_expr.ty = Type::Hole;
    }

    assert_eq!(
        distinct_predicate_rcs(&e),
        1,
        "walk_type_slots reaches the binding's declared type",
    );
    assert!(
        is_free(&k, &e),
        "`k` occurs free in `e` — in the predicate on the `Let` binding's type. \
         Every fast path that skips work on `!is_free` misses it.",
    );
}

// ---------------------------------------------------------------------------
// Finding 5 — the `changed` bit a callback returns cannot see the re-pointings
// a nested memo *reuse* performs, so reporting "unchanged" discards them.
// ---------------------------------------------------------------------------

/// A callback that recurses through the memo (which is why the combinator hands
/// it one) can have its copy mutated by a nested memo hit while having nothing
/// of its own to report. Reporting `false` then throws the copy away, so the
/// nested slot keeps a predicate the pass already rebuilt — and the outer
/// predicate is memoized as `origin ↦ origin`, fixing that staleness for every
/// later occurrence.
///
/// This is `simplify`'s exact shape: it returns `simplify_once(pred, memo).0`,
/// which reports only whether a *rule fired*.
#[test]
fn walk_preserves_a_repointing_made_by_a_nested_memo_hit() {
    let memo: PredMemo = PredMemo::new();

    // An inner predicate `q`, rebuilt through the memo by some earlier occurrence.
    let q = Rc::new(gt(var("a"), int(0)));
    let mut t_q = refined(&q);
    walk_refined_predicates_mut(&mut t_q, &memo, &(), &mut |pred, _| {
        *pred = gt(var("a"), int(1)); // a real rewrite
        true
    });
    let q_rebuilt = Rc::clone(predicate_of(&t_q));
    assert!(!Rc::ptr_eq(&q_rebuilt, &q), "q was rebuilt");

    // An outer predicate `p` carrying a second occurrence of `q` on its own type
    // slot. The transform has nothing to say about `p` itself.
    let p = Rc::new(int(1).with_ty(refined(&q)));
    let mut t_p = refined(&p);
    walk_refined_predicates_mut(&mut t_p, &memo, &(), &mut |pred, memo| {
        // Recurse into the predicate's own type slots, as every caller does.
        walk_refined_predicates_mut(&mut pred.ty, memo, &(), &mut |_, _| false);
        false // "no rule fired at this level"
    });

    assert!(
        Rc::ptr_eq(predicate_of(&predicate_of(&t_p).ty), &q_rebuilt),
        "the nested occurrence of `q` must end up at the single rebuild, not at \
         the stale origin the discarded copy was re-pointed away from",
    );
}

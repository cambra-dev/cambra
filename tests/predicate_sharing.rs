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
//! We measure at **post-inference** (cheap — milliseconds), which is where the
//! sharing is established and preserved; the downstream slowdown a regression
//! causes is in planning, but the *cause* is visible here as an inflated count.

use cambra::ccl::ccl_utils::distinct_predicate_rcs;
use cambra::ccl::infer::{TypeInferenceContext, infer};
use cambra::ccl::lower::{LoweringContext, lower_stmts};
use cambra::ccl::uniquify;
use cambra::chl_parser;

/// Parse → lower → uniquify → infer `code` (the pipeline prefix through type
/// inference; comprehensions over literals need no source registration), then
/// count the distinct refinement-predicate `Rc`s in the inferred tree.
fn distinct_rcs_post_infer(code: &str) -> usize {
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
    distinct_predicate_rcs(&expr)
}

/// A doubly-nested comprehension whose filtered domains ride many type slots.
/// Under the sharing bug this reached ~9 independent `Rc`s *per* structural
/// predicate (dozens total, multiplying downstream); with sharing preserved it
/// is one `Rc` per predicate the program actually contains — a small handful.
#[test]
fn nested_comprehension_shares_predicate_rcs() {
    let code = "[a + b
        for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
        for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
    if a != b]";
    let n = distinct_rcs_post_infer(code);
    assert!(
        n <= 8,
        "nested-comprehension predicate `Rc`s not shared: {n} distinct (expected one per \
         distinct predicate the program contains; a larger count means an inference pass \
         rebuilt predicates per-occurrence instead of preserving `Rc` sharing)"
    );
}

/// Sharing must not degrade *multiplicatively* with nesting depth: adding a
/// `for … if a_i == a_{i+1}` binder is a bounded, additive increment to the
/// distinct-`Rc` count, not a multiplicative blowup (the regression that made
/// planning superlinear).
#[test]
fn filtered_join_nesting_stays_additive() {
    let counts: Vec<usize> = (2..=6)
        .map(|n| {
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
            distinct_rcs_post_infer(&format!("[{sum} {fors} {conds}]"))
        })
        .collect();
    for w in counts.windows(2) {
        assert!(
            w[1] <= w[0] + 4,
            "distinct predicate `Rc`s grew multiplicatively across nesting depth: {counts:?} \
             (sharing lost — an inference pass is rebuilding predicates per-occurrence)"
        );
    }
}

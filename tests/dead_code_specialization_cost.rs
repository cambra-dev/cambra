//! Typechecking a never-called definition must not cost *more* than compiling the
//! same code live.
//!
//! A use inside a discarded subtree specializes like any other, and the memo is what
//! stops it re-cloning the callee. That memo is separate from the decision of what to
//! splice (`Specialization::referenced`), and conflating the two — declining to
//! register a specialization whose use is about to be dropped — silently reintroduces
//! a clone per dead call site, compounding through a call chain.
//!
//! Allocation count is the probe rather than wall-clock: it is deterministic, so the
//! guard can be a hard bound instead of a flaky timing threshold. The counter is
//! `tests/alloc_probe/mod.rs`. The chain `aᵢ = λx. aᵢ₋₁(x) + aᵢ₋₁(x)` is the shape
//! that makes re-cloning visible — every level doubles the call sites sharing must
//! collapse.

mod alloc_probe;

use alloc_probe::allocations;
use cambra::ccl::{
    infer::{TypeInferenceContext, infer},
    lower::{LoweringContext, lower_stmts},
};
use cambra::chl_parser;

/// `a1 … a{depth}`, each calling its predecessor twice, then `f` calling the last.
/// With `live`, `f` is applied; without, `f` is dead code.
fn chain(depth: usize, live: bool) -> String {
    let mut s = String::from("a1 = \\x -> x + 1\n");
    for i in 2..=depth {
        s.push_str(&format!("a{i} = \\x -> a{p}(x) + a{p}(x)\n", p = i - 1));
    }
    s.push_str(&format!("f = \\q -> a{depth}(q)\n"));
    if live {
        s.push_str("live = f(1)\n");
    }
    s.push_str("1\n");
    s
}

/// Allocations `infer` performs on this thread. Parsing and lowering are done first,
/// outside the window, so only inference is measured.
fn inference_allocations(code: &str) -> usize {
    let mut lctx = LoweringContext::default();
    let stmts = chl_parser::parse_module(code)
        .into_result()
        .expect("parse")
        .body;
    let mut expr = lower_stmts(&stmts, &mut lctx).into_result().expect("lower");
    let mut ictx = TypeInferenceContext::new();
    let mut typed = false;
    let allocs = allocations(|| typed = infer(&mut expr, &mut ictx).is_ok());
    assert!(typed, "the chain type-checks");
    allocs
}

#[test]
fn a_dead_call_chain_does_not_cost_more_than_a_live_one() {
    const DEPTH: usize = 4;
    let live = inference_allocations(&chain(DEPTH, true));
    let dead = inference_allocations(&chain(DEPTH, false));
    // Dead does the same specialization work as live and then splices none of it, so
    // it should come in *well* under. The factor is a calibrated guard rather than a
    // law — measured at this depth, sharing gives `dead ≈ 0.28 × live`, and a lost
    // memo gives `≈ 0.94 ×` (and exceeds `live` outright one level deeper). Halfway
    // between leaves room for ordinary drift while still catching the regression.
    assert!(
        dead * 2 <= live,
        "typechecking a never-called chain allocated {dead}, against {live} for the \
         same code live: the specialization memo is not being shared across uses \
         inside the discarded subtree"
    );
}

//! Typechecking a chain of `.extract()` calls on a value nested `n` deep must allocate no
//! faster than `n⁴`.
//!
//! Each call specializes `extract` at the next type down, and every specialization's pin
//! crosses the clones the ones before pinned, so compaction composes and copies
//! substitutions whose discharge payloads grow with the `let`s around them. Copies of a
//! substitution share their payloads rather than copying each term, and the walk carries
//! only the entries for the names below each variable. Measured here, doubling the depth
//! from 6 to 12 multiplies the allocations by about 6.8; copying each payload, and carrying
//! every entry, it multiplied them by about 26.
//!
//! Allocation count is the probe rather than wall-clock: it is deterministic, so the
//! guard can be a hard bound instead of a flaky timing threshold. The counter is
//! `tests/alloc_probe/mod.rs`. Comparing two depths of one program, rather than one
//! count against a fixed number, keeps the bound from moving with the inference cost
//! every program pays.

mod alloc_probe;

use alloc_probe::allocations;
use cambra::ccl::{
    comprehension,
    infer::{TypeInferenceContext, infer},
    lower::{LoweringContext, lower_stmts},
    opaque_output, uniquify,
};
use cambra::chl_parser;
use cambra::chl_parser::FileId;

/// A value nested `depth` deep in `One`, then a `.extract()` per level.
fn chain(depth: usize) -> String {
    let mut s = String::from("type One(T) = T\nc0 = 1\n");
    for i in 1..=depth {
        s.push_str(&format!("c{i} = One::new(c{})\n", i - 1));
    }
    s.push_str(&format!("c{depth}{}\n", ".extract()".repeat(depth)));
    s
}

/// Allocations `infer` performs on this thread. Parsing and lowering are done first,
/// outside the window, so only inference is measured.
fn inference_allocations(code: &str) -> usize {
    let mut lctx = LoweringContext::default();
    let module = chl_parser::parse_module(FileId::ROOT, code)
        .into_result()
        .expect("parse");
    let expr = lower_stmts(&module, &mut lctx)
        .into_result()
        .expect("lower");
    // The pre-inference phases run outside the window, as the pipeline runs them before
    // `infer`.
    let mut expr = opaque_output::run(comprehension::run(uniquify::run(expr), lctx.shared_holes()));
    let mut ictx = TypeInferenceContext::new();
    let mut typed = false;
    let allocs = allocations(|| typed = infer(&mut expr, &mut ictx).is_ok());
    assert!(typed, "the chain type-checks");
    allocs
}

#[test]
fn doubling_the_nesting_multiplies_the_allocations_by_less_than_sixteen() {
    let shallow = inference_allocations(&chain(6));
    let deep = inference_allocations(&chain(12));
    assert!(
        deep < 16 * shallow,
        "a chain twelve deep allocated {deep}, {:.1} times the {shallow} of one six deep: \
         faster than the fourth power of the depth",
        deep as f64 / shallow as f64
    );
}

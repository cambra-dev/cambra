//! Inline fan-out: a scalar UDF called at two sites *at the same type*.
//!
//! Monomorphization makes one specialization, then `inline` duplicates the body
//! per call site — one copy preserves the input ids, the other is a freshened
//! `Replicated` copy tagged `Derived { via: Inline }`. That duplication is what
//! makes the inspector's `post-inference → post-channelize` link window carry
//! genuine non-identity edges, asserted in `tests/inspector_goldens.rs`.

use super::common::expect_scalar;

#[test]
fn udf_fanout() {
    expect_scalar(include_str!("program.cambra"), "32");
}

//! A mutable accumulator whose loop body reads it at two sites
//! (`total + total`).
//!
//! The induction phase substitutes the read-your-writes value once per read, so
//! the copies — and the `step_view` scaffolding clones — must carry freshened,
//! unique `NodeId`s. `tests/inspector_goldens.rs` asserts that the resulting
//! dense channelize window fans one upstream node out to several downstream
//! ones.

use super::common::expect_scalar;

#[test]
fn mutation_loop() {
    // 0 → 0+0+1 = 1 → 1+1+2 = 4 → 4+4+3 = 11.
    expect_scalar(include_str!("program.cambra"), "11");
}

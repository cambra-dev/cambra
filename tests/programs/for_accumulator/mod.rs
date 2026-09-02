//! Sum 1..5 by accumulating into a loop-carried mutable variable — the
//! natural imperative shape for "fold".  The accumulator is introduced by
//! the `:=` mutation operator (`acc := 0`) and advanced with `acc := acc + i`;
//! a plain `=` inside a loop is an immutable per-iteration binding, not a
//! mutable write.
//!
//! Also the inspector corpus's `Letrec` program. The induction phase's
//! substituted read-your-writes values and the `step_view` scaffolding clones
//! carry freshened, unique `NodeId`s, which `tests/inspector_goldens.rs`
//! asserts as a dense `post-inference → post-channelize` window — so a change
//! to this program's shape re-targets that assertion.

use super::common::expect_scalar;

#[test]
fn for_accumulator_sums_to_15() {
    expect_scalar(include_str!("program.cambra"), "15");
}

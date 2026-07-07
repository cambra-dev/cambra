//! Sum 1..5 by accumulating into a loop-carried mutable variable — the
//! natural imperative shape for "fold".
//!
//! The reassignment of the pre-loop `acc` inside the for body is
//! recognised as a loop-carried accumulator and lowered to a CCL `Loop`
//! node (see `src/ccl/design/ir.md` → `Loop`).

use super::common::expect_scalar;

#[test]
fn for_accumulator_sums_to_15() {
    expect_scalar(include_str!("program.cambra"), "15");
}

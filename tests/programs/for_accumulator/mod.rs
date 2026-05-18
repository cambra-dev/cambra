//! Sum 1..5 by accumulating into a loop-carried mutable variable — the
//! natural imperative shape for "fold".
//!
//! Blocked on plan.md → Mutability → "for loop with loop-carried mutable
//! variables → iterate/recurse combinator".  Flip this test green by
//! switching to `expect_scalar(..., "15")` once the feature ships.

use super::common::expect_scalar;

#[test]
fn for_accumulator_currently_fails_at_lowering() {
    expect_scalar(include_str!("program.cambra"), "15");
}

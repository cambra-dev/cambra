//! Count up to 5 with a `while` loop — the smallest program that needs
//! unbounded time-domain lowering.
//!
//! Blocked on plan.md → Mutability → "while loop lowering (unbounded time
//! domain; defer termination checking)".  Flip green by switching to
//! `expect_scalar(..., "5")` once the feature ships.

use super::common::expect_compile_error;

#[test]
fn while_counter_currently_fails_at_lowering() {
    expect_compile_error(
        include_str!("program.cambra"),
        "Only assignment and function definition statements are supported",
    );
}

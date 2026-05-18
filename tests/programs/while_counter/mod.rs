//! Count up to 5 with a `while` loop — the smallest program that needs
//! unbounded time-domain lowering.
//!
//! Currently rejected by the new CHL parser before lowering even sees it
//! (`while` isn't a recognised statement keyword yet).  Blocked on
//! plan.md → Mutability → "while loop lowering (unbounded time domain;
//! defer termination checking)".  Flip green by switching to
//! `expect_scalar(..., "5")` once the feature ships.

use super::common::expect_compile_error;

#[test]
fn while_counter_currently_fails_to_parse() {
    expect_compile_error(include_str!("program.cambra"), "parse error");
}

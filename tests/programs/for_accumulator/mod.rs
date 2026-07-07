//! Sum 1..5 by accumulating into a loop-carried mutable variable — the
//! natural imperative shape for "fold".  The accumulator is introduced by
//! the `:=` mutation operator (`acc := 0`) and advanced with `acc := acc + i`;
//! a plain `=` inside a loop is an immutable per-iteration binding, not a
//! store write.

use super::common::expect_scalar;

#[test]
fn for_accumulator() {
    expect_scalar(include_str!("program.cambra"), "15");
}

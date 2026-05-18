//! Bind a variable, then use it in a second expression — smoke-test for
//! sequencing and reference resolution.

use super::common::expect_scalar;

#[test]
fn arithmetic() {
    expect_scalar(include_str!("program.cambra"), "20");
}

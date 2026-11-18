//! A function returns collection data read from its private Feed. The caller
//! combines that collection's total with contributions to its own Feed.

use super::common::expect_scalar;

#[test]
fn defer_lift() {
    expect_scalar(include_str!("program.cambra"), "10");
}

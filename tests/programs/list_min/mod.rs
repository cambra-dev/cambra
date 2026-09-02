//! A bare list literal — the smallest program with a data collection in it.
//!
//! The second of the inspector's two full-wire canaries (fixture `list_min`):
//! being this small, its snapshot is the one to read when asking what the
//! payload looks like at all.

use super::common::expect_scalar;

#[test]
fn list_min() {
    expect_scalar(include_str!("program.cambra"), "Function [ 1, 2, 3, 4 ]");
}

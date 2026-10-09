//! An unfiltered comprehension over a list literal, used once.
//!
//! The inspector fixture `list_comp`: the only one carrying nodes the
//! comprehension phase mints (`via: "Comprehension"`). A comprehension bound
//! by a `let` is generalized and monomorphization re-tags its clone, so this
//! one is the program's value.

use super::common::expect_scalar;

#[test]
fn list_comp() {
    expect_scalar(include_str!("program.cambra"), "Function [ 2, 3 ]");
}

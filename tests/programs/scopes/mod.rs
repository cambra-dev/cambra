//! A `def` with several parameters plus an outer binding — the program that
//! exercises the inspector's scopes table and goto-definition, where every use
//! of `p`, `q`, `r` and `base` must resolve to its own binder.

use super::common::expect_scalar;

#[test]
fn scopes() {
    expect_scalar(include_str!("program.cambra"), "106");
}

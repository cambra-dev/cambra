//! SQL-style "select sum(score) from users where age >= 18" — filter a
//! let-bound list of records on one field, aggregate over another.
//!
//! **Currently buggy.**  Returns `345` (all four scores summed) instead of
//! `253` (alice + carol + dave; bob filtered out for age 17).  The bug:
//! when the comprehension source is a let-bound variable, the `if` clause
//! is silently dropped.  See `docs/demo-programs.md` → Known issues.
//!
//! Once fixed, swap `expect_scalar_currently_buggy` for
//! `expect_scalar(..., "253")` and rename the test.

use super::common::expect_scalar_currently_buggy;

#[test]
fn filter_and_aggregate_currently_buggy() {
    expect_scalar_currently_buggy(include_str!("program.cambra"), "345");
}

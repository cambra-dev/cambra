//! SQL-style "select sum(score) from users where age >= 18" — filter a
//! let-bound list of records on one field, aggregate over another.
//!
//! Regression guard for filter survival on a let-bound comprehension
//! source: the `if` clause must reach the iteration site, so the result is
//! the sum of the adults' scores (`253`), not the unfiltered total (`345`).
//! The filter rides a `Builtin::Cast` on the refined function type from
//! lowering through planning; this test goes red if a pass drops it at the
//! let-bound boundary.

use super::common::expect_scalar;

#[test]
fn filter_and_aggregate() {
    expect_scalar(include_str!("program.cambra"), "253");
}

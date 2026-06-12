//! SQL-style "select sum(score) from users where age >= 18" — filter a
//! let-bound list of records on one field, aggregate over another.

use super::common::expect_scalar;

#[test]
fn filter_and_aggregate() {
    expect_scalar(include_str!("program.cambra"), "253");
}

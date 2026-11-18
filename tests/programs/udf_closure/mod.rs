//! A UDF called once, closing over an outer binding — the smallest program in
//! which a call site and a free variable meet.
//!
//! The inspector's canary: the frontend's tests read its payload in most of
//! their cases (`dumped("udf_closure")` in `web/src/`), so a change to how its
//! literals or operators reach the wire shows there.

use super::common::expect_scalar;

#[test]
fn udf_closure() {
    expect_scalar(include_str!("program.cambra"), "13");
}

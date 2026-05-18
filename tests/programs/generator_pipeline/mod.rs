//! Compose two user-defined generators (filter to positives, then square)
//! and take the max — exercises UDF inlining all the way through to
//! operator conversion.

use super::common::expect_scalar;

#[test]
fn generator_pipeline() {
    expect_scalar(include_str!("program.cambra"), "25");
}

//! Compose two user-defined generators (filter to positives, then square)
//! and take the max — exercises UDF inlining all the way through to
//! operator conversion.

use super::common::expect_scalar;

// Composes `positives` (filter to > 0) then `squared`, and takes the max:
// `max(squared(positives([-3, 4, -1, 2, 5, -7])))` = 5² = 25. The filter in
// `positives` lowers to a refined-source channel whose domain carries the bare
// element predicate `__elem ▷ source ▷ (λ x → x > 0)`, which planning reifies
// into an `IterateExtent` + `Restrict` — so negatives are dropped before
// squaring. (Previously produced 49 = (-7)² because the filter was dropped.)
#[test]
fn generator_pipeline() {
    expect_scalar(include_str!("program.cambra"), "25");
}

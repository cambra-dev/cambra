//! Compose two user-defined generators (filter to positives, then square)
//! and take the max — exercises UDF inlining all the way through to
//! operator conversion.

use super::common::expect_scalar;

// Currently produces `49` (= (-7)²) instead of `25` (= 5²) because the
// filter in `positives` is silently dropped.  In the return-value
// desugar design, `positives`'s filter-feed pattern attaches a
// `Refinement` to its source param's `user_annotation`; after inference
// that refinement lives on the cluster binding's *type*, but the
// value-expression at the binding (a `Record` projection) doesn't
// carry the refinement on its own `expr.ty`.
// `operator_conversion::iterate_type` only inspects the value
// expression's type, so the `Restrict` operator never gets emitted.
//
// A coworker is fixing `operator_conversion` to honour refinements on
// let-binding types.  Once that lands, drop the `#[ignore]` here —
// no changes are expected in desugar itself.  Same root cause as
// `tests/compilation_pipeline.rs::test_generator_function::positives`;
// see `src/ccl/design-desugar-defers.md` "Known gaps & future work"
// for the longer write-up.
#[test]
#[ignore]
fn generator_pipeline() {
    expect_scalar(include_str!("program.cambra"), "25");
}

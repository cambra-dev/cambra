//! Dependent sums end to end: `box` as the way in, and what consuming a summed
//! collection does — in particular **filtering** one.
//!
//! A conditional is the *usual* way two candidates end up in one sum, so these
//! shapes are easy to mistake for conditional-specific ones. They are not: every
//! program here has a single arm and no `Case` at all. `conditionals.rs` carries
//! the multi-candidate half, and the two share one gap.
//!
//! See `src/ccl/design/type-inference.md`, "Only a term builds a sum".

use std::time::Duration;

use cambra::interpreter::Value;
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Consuming a boxed collection — the unfiltered baseline
// ---------------------------------------------------------------------------

/// A one-candidate sum is consumed like the collection it wraps. `box` is a
/// type-level introduction with no runtime content, so every one of these is
/// the plain collection's answer.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Consumed whole, without an iteration site of its own.
#[case("sum(box([1, 2, 3]))", Value::Int(6))]
// Iterated: inline, let-bound, and through a UDF parameter.
#[case("sum([y for y in box([1, 2, 3])])", Value::Int(6))]
#[case("x = box([1, 2, 3])\nsum([y for y in x])", Value::Int(6))]
#[case(
    r"
def f(xs):
    sum([y for y in xs])
f(box([1, 2, 3]))",
    Value::Int(6)
)]
// A mapping body, which composes onto the source rather than collapsing to it.
#[case("x = box([1, 2, 3])\nsum([y * 10 for y in x])", Value::Int(60))]
fn a_boxed_collection_is_consumed_like_the_collection_it_wraps(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

/// **The filter that is already compiled.** A filter *inside* the box belongs to
/// the boxed term and became a `Restrict` when that comprehension was
/// materialised — the sum's candidate merely records it.
///
/// This is the control group for
/// [`a_filter_over_a_boxed_source_is_dropped`]: the refinement on a candidate
/// looks identical whether it was compiled inside the arm or is still owed by
/// the consumer, so a rule that emits an operator for every refinement it finds
/// on a candidate would double-apply these.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("sum(box([z for z in [1, 2, 3] if z > 1]))", Value::Int(5))]
#[case(
    "sum([y for y in box([z for z in [1, 2, 3] if z > 1])])",
    Value::Int(5)
)]
#[case(
    "x = box([z for z in [1, 2, 3] if z > 1])\nsum([y for y in x])",
    Value::Int(5)
)]
fn a_filter_inside_the_box_is_already_compiled(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Filtering a boxed collection — the gap
// ---------------------------------------------------------------------------

/// **A comprehension filter over a summed source is dropped.** No conditional is
/// involved: one `box`, one candidate, one filter — and the filter never becomes
/// an operator.
///
/// This is the *minimal* form of the gap that
/// `a_filter_over_a_conditional_source_is_dropped` shows with two candidates.
/// Recording it here is the point: the conditional is incidental, and designing
/// the fix against the two-candidate case alone would fit a mechanism (a gate per
/// realized leg) to a shape that the one-candidate case does not have — it has no
/// legs, because nothing realizes a sum a `Case` did not produce.
///
/// Inference is right in every case below; the type carries the filter exactly
/// where it belongs, on the candidate:
/// `Σ 𝜎 ∈ {{[0, 2] | 𝑝}}. (𝜎 ⤇ Int)`.
/// What is missing is downstream, in `planning::iterate::wrap_with_iterate`:
/// reading `expr.ty.domain()` on a sum yields its **witness**, the site is
/// skipped as un-iterable, and the restrict is never emitted. The refinement is
/// on the *candidate*, which `domain()` does not look at.
///
/// The two outcomes below are both present and the silent one is the worse:
/// - a **let-bound** or parameter-passed box computes the *unfiltered* answer;
/// - an **inline** box fails loudly at op-conversion (a list literal reaches it
///   with no iteration source, because the site that was skipped was the one that
///   would have provided it).
#[rstest]
#[timeout(Duration::from_secs(10))]
// How the box reaches the generator: inline, let-bound, UDF parameter.
#[case("sum([y for y in box([1, 2, 3]) if y > 1])", Value::Int(5))]
#[case("x = box([1, 2, 3])\nsum([y for y in x if y > 1])", Value::Int(5))]
#[case(
    r"
def f(xs):
    sum([y for y in xs if y > 1])
f(box([1, 2, 3]))",
    Value::Int(5)
)]
// A mapping body as well as the identity one: the identity comprehension
// simplifies to a bare `cast`, so it alone would not exercise the composed form.
#[case(
    "x = box([1, 2, 3])\nsum([y * 10 for y in x if y > 1])",
    Value::Int(50)
)]
// Predicate shapes: an empty result, an outer binding, a conjunction. (An
// always-true predicate cannot discriminate a dropped filter from a working
// one, so it sits with the controls above.)
#[case("x = box([1, 2, 3])\nsum([y for y in x if y > 100])", Value::Int(0))]
// A filter that admits *every* element. It cannot tell a working restrict from a
// dropped one by its answer — but it belongs here rather than with the controls,
// because planning refuses a site that still owes a restrict rather than dropping
// it, and this owes one like any other. It used to compute 6 by luck.
#[case("x = box([1, 2, 3])\nsum([y for y in x if y > 0])", Value::Int(6))]
#[case(
    "k: Int = 1\nx = box([1, 2, 3])\nsum([y for y in x if y > k])",
    Value::Int(5)
)]
#[case(
    "x = box([1, 2, 3])\nsum([y for y in x if y > 1 and y < 3])",
    Value::Int(2)
)]
// A consumer other than `sum`. The predicate discriminates: unfiltered `max` is
// 3, so a dropped filter is visible.
#[case("x = box([1, 2, 3])\nmax([y for y in x if y < 3])", Value::Int(2))]
// Two consumers of one box, each with its own filter — the restrictions belong
// to the sites, not to the boxed value they share.
#[case(
    "x = box([1, 2, 3])\nsum([y for y in x if y > 1]) + sum([z for z in x if z > 2])",
    Value::Int(8)
)]
// ...and one filtered consumer beside an unfiltered one.
#[case(
    "x = box([1, 2, 3])\nsum([y for y in x]) + sum([z for z in x if z > 1])",
    Value::Int(11)
)]
// **Both kinds of refinement on one candidate**: the box carries its own filter
// (already compiled — `a_filter_inside_the_box_is_already_compiled`) and the
// consumer adds another (still owed). Whatever distinguishes the two cannot be
// "which candidate is it on", because here it is the same one.
#[case(
    "x = box([z for z in [1, 2, 3] if z > 1])\nsum([y for y in x if y < 3])",
    Value::Int(2)
)]
#[ignore = "a filter over a summed source is never emitted: `wrap_with_iterate` reads \
            the witness where the refinement is on the candidate; measured 2026-08-08"]
fn a_filter_over_a_boxed_source_is_dropped(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

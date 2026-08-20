//! Dependent sums end to end: `box` as the way in, and what consuming a summed
//! collection does — in particular **filtering** one.
//!
//! A conditional is the *usual* way two candidates end up in one sum, so these
//! shapes are easy to mistake for conditional-specific ones. They are not: every
//! program here has a single arm and no `Case` at all — the witness is
//! **determined**, and that is what lets it be erased rather than materialized.
//! `conditionals.rs` carries the undetermined half, which still needs an extent.
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
// The same mapping body over an **inline** box. Both halves are needed and neither
// implies the other: the body is what puts the `box` inside a point-free chain, and
// being inline is what leaves it there as an interior morphism — where `lambda_elim`
// re-types it as the sum's body, so the erasure has to read the type the introduction
// states rather than the one the node ended up with.
#[case("sum([y * 10 for y in box([1, 2, 3])])", Value::Int(60))]
#[case("sum([y * 10 for y in box([z for z in [1, 2, 3]])])", Value::Int(60))]
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
// Filtering a boxed collection
// ---------------------------------------------------------------------------

/// **A comprehension filter over a summed source.** No conditional is involved:
/// one `box`, one candidate, one filter.
///
/// A determined witness — one candidate — needs no runtime representation, which
/// is why `unbox` erases its introduction. What that erasure has to reach is
/// *both halves*: the term **and** every type still saying `Σ`. A type asserting
/// an indeterminacy the term no longer has presents a **witness** where the
/// consuming site expects a domain, and a witness has no extent, so planning
/// could build no iteration source and dropped the site's filter with it.
///
/// Two shapes made this reach further than the term walk:
/// - the mentions are scattered (the `Let`, the `Var`, the `cast`, the consumer's
///   own parameter), so instantiating the witness is a whole-tree type map rather
///   than a local rewrite;
/// - a filter's predicate carries **its own copy of the source** (`__elem ▷ src ▷
///   𝑓`), so with an inline `box` the introduction sits inside a *predicate* — a
///   term riding a type slot, which no term walk visits.
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
fn a_filter_over_a_boxed_source_is_applied(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The one shape above that still fails, and **not for a reason about sums**: a
/// let-bound *filtered* comprehension, filtered again, panics with `no entry found
/// for key`. The same program without a `box` fails identically on `main` —
/// `comprehensions.rs`, `filtered_comprehension_shapes_that_do_not_compile` — so
/// what the `box` contributes here is nothing.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[ignore = "pre-existing on main: a let-bound filtered comprehension, filtered again; \
            unrelated to sums; measured 2026-08-09"]
fn a_filter_over_a_box_that_already_carries_one() {
    check_scalar(
        "x = box([z for z in [1, 2, 3] if z > 1])\nsum([y for y in x if y < 3])",
        Value::Int(2),
    );
}

// ---------------------------------------------------------------------------
// Boxing a sum is the identity
// ---------------------------------------------------------------------------

/// **`box` is idempotent.** `Σ σ ∈ {𝑆}. σ` is `𝑆` when `𝑆` is itself a sum
/// ([`cambra::ccl::ty::SigmaType::into_type`]), so a second `box` introduces no
/// second witness: one value made one choice, and the outer sum's candidate list
/// contributes its own candidates rather than nesting inside it. That is the
/// one-candidate instance of the flattening a join already performs.
///
/// The law is about the *outer* sum, so the inner one's shape does not matter, and
/// the cases below are the three it can have: a kind listing one candidate, one
/// listing several, and one that describes them. Each answers what the singly-boxed
/// program answers.
#[rstest]
#[timeout(Duration::from_secs(10))]
// One candidate: the plain re-box, inline and through a binding.
#[case("sum([y for y in box(box([1, 2, 3]))])", Value::Int(6))]
#[case("x = box([1, 2, 3])\ny = box(x)\nsum([z for z in y])", Value::Int(6))]
// Idempotent rather than merely collapsing once: a third `box` adds nothing either.
#[case("sum([y for y in box(box(box([1, 2, 3])))])", Value::Int(6))]
// The re-boxed sum is still consumable — a filter over it lands.
#[case(
    "x = box([1, 2, 3])\ny = box(x)\nsum([z for z in y if z > 1])",
    Value::Int(5)
)]
// Several candidates: boxing a conditional collection, whose witness is undetermined.
// A second witness here would be a second choice for the one the conditional made.
#[case(
    "c: Bool = True\nzs = box([1, 2]) if c else box([1, 2, 3])\nws = box(zs)\nsum([y for y in ws])",
    Value::Int(3)
)]
// A described kind: `List(Int)` names one domain per length, so there is no candidate
// list to splice and the outer sum has to adopt the inner sum whole.
#[case(
    "xs: List(Int) = box([1, 2, 3])\nys = box(xs)\nsum([z for z in ys])",
    Value::Int(6)
)]
fn boxing_a_sum_is_the_identity(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

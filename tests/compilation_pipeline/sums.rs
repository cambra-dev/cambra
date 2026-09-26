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
use indoc::indoc;
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
// it, and this owes one like any other.
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

/// A `box` over a **filtered** comprehension, filtered again at the consumer. Recorded here
/// as failing with `no entry found for key`, which was never a fact about sums: the same
/// program without the `box` failed identically, and both compile now
/// (`comprehensions.rs`, `test_refiltered_let_bound_comprehension` is the unboxed pair).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_filter_over_a_box_that_already_carries_one() {
    check_scalar(
        "x = box([z for z in [1, 2, 3] if z > 1])\nsum([y for y in x if y < 3])",
        Value::Int(2),
    );
}

// ---------------------------------------------------------------------------
// A jagged nested collection — the witness the value carries
// ---------------------------------------------------------------------------

/// **Elements at differing domains, joined into one element position.** Each `box` states the
/// single candidate it is and the join binds a witness over both, so the witness is neither
/// determined nor a branch's to pick: the value is what says which domain each element has.
///
/// **The aggregates are chosen to distinguish a per-row fold from a flattened one.** `sum` over
/// `sum` is blind here — `sum([sum(r) for r in xs])` and `sum(flatten(xs))` agree on every
/// input — so a wrong answer would read as right. `sum` over `max` does not: over rows `[1, 2]`
/// and `[3, 4, 5]` it answers 7, where flattening answers 5 or 15. One `sum`/`sum` case is kept
/// as the plain reading.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[case("sum([max(r) for r in [box([1, 2]), box([3, 4, 5])]])", Value::Int(7))]
#[case("sum([sum(r) for r in [box([1, 2]), box([3, 4, 5])]])", Value::Int(15))]
// The other order, so neither aggregate is the one that could be folding both levels.
#[case("max([sum(r) for r in [box([1, 2]), box([3, 4, 5])]])", Value::Int(12))]
#[case(
    "sum([max(r) for r in box([box([1, 2]), box([3, 4, 5])])])",
    Value::Int(7)
)]
// The outer box is determined — one candidate — so its own introduction still erases while
// the inner ones stand.
#[case(
    indoc! {r"
        x = box([box([1, 2]), box([3, 4, 5])])
        sum([max(r) for r in x])
    "},
    Value::Int(7)
)]
// Three elements, so the join names three candidates and no two rows share a length.
#[case(
    "sum([max(r) for r in [box([1]), box([2, 3]), box([4, 5, 6])]])",
    Value::Int(10)
)]
// A rectangular literal forms no sum at all: the element domains agree, so the join needs no
// `box` and the elements are plain collections.
#[case("sum([max(r) for r in [[1, 2], [3, 4]]])", Value::Int(6))]
// **Through a copair.** `++` decomposes each operand's own sum into a variant tag, but merges
// the operands' *codomains* into one variable — so where the elements are collections that
// merge is a sum, and an arm's elements stand at it exactly as a literal's do.
#[case(
    "sum([max(r) for r in ([box([1, 2])] ++ [box([3, 4, 5])])])",
    Value::Int(7)
)]
// Jagged within one arm as well as across the two, so both merges carry candidates.
#[case(
    "sum([max(r) for r in ([box([1, 2]), box([3, 4, 5])] ++ [box([6])])])",
    Value::Int(13)
)]
// An empty row is a candidate like any other. `max` over the row sums answers 3, where
// flattening answers 2.
#[case("max([sum(r) for r in [box([]), box([1, 2])]])", Value::Int(3))]
// A single row is a join over one candidate, so the witness is determined and erases.
#[case("sum([max(r) for r in [box([1, 2])]])", Value::Int(2))]
// **A filter over the outer collection** reads the collection at the index inside its
// predicate, so the predicate holds its own copy of each `box`. That copy stands at the same
// element position as the term's and is kept with it.
#[case(
    "sum([max(r) for r in [box([1, 2]), box([3, 4, 5])] if max(r) > 2])",
    Value::Int(5)
)]
// **Inside a tuple**, whose fields are each handed their own element type, and so as the
// values of a `map`, which takes its entries as a list of pairs.
#[case(
    r#"sum([max(p.1) for p in [("a", box([1])), ("b", box([2, 3]))]])"#,
    Value::Int(4)
)]
#[case(
    indoc! {r#"
        m = map([("a", box([1])), ("b", box([2, 3]))])
        sum([max(r) for r in m])
    "#},
    Value::Int(4)
)]
// **Through a mutable variable and a feed**, which merge their writes into one variable. Each
// write here is a whole list literal, so its elements stand at the literal's element position.
#[case(
    indoc! {r"
        xs := [box([1])]
        xs = [box([1]), box([2, 3])]
        sum([max(r) for r in xs])
    "},
    Value::Int(4)
)]
#[case(
    indoc! {r"
        x = defer()
        x <<= [box([1]), box([2, 3])]
        sum([max(r) for r in x])
    "},
    Value::Int(4)
)]
// **A filter over each row**, whose refinement reads the row and so narrows each row's own
// domain, which is a candidate of the element position's witness. Unfiltered, these answer 15
// and 7.
#[case(
    "sum([sum([v for v in r if v > 1]) for r in [box([1, 2]), box([3, 4, 5])]])",
    Value::Int(14)
)]
#[case(
    "sum([max([v for v in r if v < 4]) for r in [box([1, 2]), box([3, 4, 5])]])",
    Value::Int(5)
)]
fn a_jagged_nested_collection_is_consumed_at_each_rows_own_domain(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

/// **A comprehension over a collection whose domain is the witness composes with it.** A
/// `List(List(𝑇))` annotation binds a described kind at both levels, so the outer collection's
/// domain is a witness rather than an extent. The comprehension needs no iteration source over
/// that domain: its generator is the collection composed with the element function
/// (`src/ccl/design/optimization.md`, "A generator over a sum composes with its source").
#[test]
fn a_comprehension_over_a_witness_domained_collection_composes_with_it() {
    check_scalar(
        indoc! {r"
            def f(xs: List(List(Int))):
                sum([sum(r) for r in xs])
            f(box([box([1,2]), box([3,4,5])]))
        "},
        Value::Int(15),
    );
}

/// A correlated comprehension over a witness-domained collection: the inner comprehension
/// iterates the outer row and reads it again, so each row's collection is composed with a
/// function of that row. `[1, 2]` gives `3 + 4` and `[3, 4, 5]` gives `8 + 9 + 10`.
#[test]
fn a_correlated_comprehension_over_a_witness_domained_collection() {
    check_scalar(
        indoc! {r"
            def f(xs: List(List(Int))):
                sum([sum([v + max(r) for v in r]) for r in xs])
            f(box([box([1,2]), box([3,4,5])]))
        "},
        Value::Int(34),
    );
}

/// **A `let`-bound row reaches a jagged position written in place.** Inlining moves a
/// `let`-bound list element into the literal that reads it, so the `box` stands where the row
/// is merged and planning keeps it there. Through a list literal and through a copair arm:
/// `2 + 5`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(indoc! {r"
    x = box([1, 2])
    sum([max(r) for r in [x, box([3, 4, 5])]])
"})]
#[case(indoc! {r"
    x = box([1, 2])
    sum([max(r) for r in [x] ++ [box([3, 4, 5])]])
"})]
fn a_let_bound_row_at_a_jagged_position_is_read_in_place(#[case] code: &str) {
    check_scalar(code, Value::Int(7));
}

/// **A row read from a mutable variable is rejected by name** at a jagged position. Its `box`
/// is erased where the variable is introduced, while the position merging it keeps the sum, so
/// the row stands fixed before it reaches the list.
#[test]
fn a_row_read_from_a_mutable_variable_at_a_jagged_position_is_unsupported() {
    check_compile_error(
        indoc! {r"
            x := box([1, 2])
            y = x
            sum([max(r) for r in [y, box([3, 4, 5])]])
        "},
        "a row bound or computed elsewhere",
    );
}

/// **Rows at differing domains merged by two appends or by a keyed write do not compile.**
/// Neither site hands its rows a demand the way a list literal does
/// (`src/ccl/planning/conditionals.rs`, `child_demand`). These pin the failures as they stand:
/// two `<<` appends fail the free-witness check in a debug build and the post-planning type
/// check in a release one, and the keyed write fails group-by recognition's type check.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::two_appends(
    indoc! {r"
        x = defer()
        x << box([1])
        x << box([2, 3])
        sum([sum(r) for r in x])
    "},
    if cfg!(debug_assertions) { "free witness reference" } else { "post-planning produced an invalid tree" }
)]
#[case::keyed_write(
    indoc! {r#"
        m: Mut(Map(String, List(Int)), Txn) := box(map([("a", box([1]))]))
        with begin():
            m["b"] := box([2, 3])
        sum([max(r) for r in await_final(m)])
    "#},
    "Bad group expr"
)]
fn jagged_rows_merged_by_appends_or_a_keyed_write_do_not_compile(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle);
}

/// **A `for` loop over a collection whose type is a sum is rejected by name**, in every build.
///
/// A loop's history is a function over its source's domain, and a sum's domain is the witness
/// the sum binds, so the history would name a witness outside its binder
/// (`src/ccl/design/collections.md`, "Compiling a conditional collection"). The first case's
/// outer domain is an undetermined witness, the `UIntRanges` a `List(𝑇)` annotation binds. The
/// second's is determined: planning would erase it, but only after the loop's history is
/// typed.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(indoc! {r"
    xs: List(List(Int)) = box([box([1]), box([2, 3])])
    total := 0
    for r in xs:
        total += 1
    total
"})]
#[case(indoc! {r"
    total := 0
    for x in box([1, 2]):
        total += x
    total
"})]
fn a_loop_over_a_sum_is_unsupported(#[case] code: &str) {
    check_compile_error(
        code,
        "a `for` loop over a collection whose type is a sum is not supported yet",
    );
}

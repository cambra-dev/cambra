//! End-to-end sum compilation: boxed collections, filtering, materialized
//! jagged rows, witness-domained comprehensions and unsupported storage/loop shapes.
//!
//! See `src/ccl/design/type-inference.md`, "Only a term builds a sum".

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::*;

// ---------------------------------------------------------------------------
// Consuming a boxed collection — the unfiltered baseline
// ---------------------------------------------------------------------------

/// One-candidate sums, consumed as the collections they wrap: `box` is the identity at runtime.
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
// `min` under the same filter: unfiltered `min` is 1, so only a filter that drops 1 is visible.
#[case("x = box([1, 2, 3])\nmin([y for y in x if y > 1])", Value::Int(2))]
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
        x: Feed(_)
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
/// function of that row, through `strength_over` (`src/ccl/design/optimization.md`, "A generator
/// over a sum composes with its source").
#[rstest]
#[timeout(Duration::from_secs(10))]
// `[1, 2]` gives `3 + 4` and `[3, 4, 5]` gives `8 + 9 + 10`.
#[case::rows(
    indoc! {r"
        def f(xs: List(List(Int))):
            sum([sum([v + max(r) for v in r]) for r in xs])
        f(box([box([1,2]), box([3,4,5])]))
    "},
    34
)]
// A row holding nothing pairs nothing, and its sum is the identity: `[1, 2]` gives
// `(1 + 3) + (2 + 3)` and `[]` gives 0.
#[case::an_empty_row(
    indoc! {r"
        def f(xs: List(List(Int))):
            sum([sum([v + sum(r) for v in r]) for r in xs])
        f(box([box([1,2]), box([])]))
    "},
    9
)]
// Values that are collections of their own pair with their row whole. `[[1, 2], [3]]` gives
// `(3 + 3) + (3 + 3)` and `[[4]]` gives `4 + 4`.
#[case::values_holding_a_level(
    indoc! {r"
        def f(xs: List(List(List(Int)))):
            sum([sum([sum(v) + max([sum(u) for u in r]) for v in r]) for r in xs])
        f(box([box([box([1, 2]), box([3])]), box([box([4])])]))
    "},
    20
)]
fn a_correlated_comprehension_over_a_witness_domained_collection(
    #[case] code: &str,
    #[case] total: i64,
) {
    check_scalar(code, Value::Int(total));
}

/// **A `let`-bound row reaches a jagged position written in place.** Inlining moves a
/// `let`-bound list element into the literal that reads it, so the `box` stands where the row
/// is merged. Through a list literal and through a copair arm: `2 + 5`.
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

/// **A row read from a mutable variable does not compile at a jagged position.** The literal
/// holding it is converted as a constant, and op-conversion takes a collection-valued element
/// only written out as a list literal, which a read is not. Pinned on that failure.
#[test]
fn a_row_read_from_a_mutable_variable_at_a_jagged_position_is_unsupported() {
    check_compile_error(
        indoc! {r"
            x := box([1, 2])
            y = x
            sum([max(r) for r in [y, box([3, 4, 5])]])
        "},
        "a collection-valued list element must be written out as a list literal",
    );
}

/// **Rows at differing domains merged by two appends.** Each append's `box` stays, so each row
/// carries its own domain into the merged collection.
#[test]
fn jagged_rows_merged_by_two_appends() {
    check_scalar(
        indoc! {r"
            x: Feed(_)
            x << box([1])
            x << box([2, 3])
            sum([sum(r) for r in x])
        "},
        Value::Int(6),
    );
}

/// **Rows at differing domains merged by a keyed write.** Each row's `box` stays, so each row
/// carries its own domain into the map: `1 + 3`.
#[test]
fn jagged_rows_merged_by_a_keyed_write() {
    check_scalar(
        indoc! {r#"
            m: Mut(Map(String, List(Int)), Txn) := box(map([("a", box([1]))]))
            with begin():
                m["b"] := box([2, 3])
            sum([max(r) for r in await_final(m)])
        "#},
        Value::Int(4),
    );
}

/// **A filtered collection reaching a `List` position through a sum's candidate is refused.**
/// A filtered range has gaps, so it is not a `List` (`docs/chl-spec.md`, "7.4 `box`"). Here the
/// candidate is read through a substitution, so the kind is recorded on a suspension, which the
/// coalesce pass decides (`src/ccl/design/type-inference.md`, "Membership is decided at
/// materialization"): a conditional's arm passed inline, through a `let`, per row, or through an
/// unannotated `def`, bound by a `List` annotation, and written to a `Mut(List(…))`. Written
/// inside a loop whose variable the filter reads, the candidate widens to every subtype of its
/// range, which is not a `List` either.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::inline(indoc! {r"
    def f(c: List(Int)):
        sum(c)
    f(box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2]))
"}, "found {0..3 |")]
#[case::let_bound(indoc! {r"
    def f(c: List(Int)):
        sum(c)
    x = box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2])
    f(x)
"}, "found {0..3 |")]
#[case::per_row(indoc! {r"
    def f(c: List(Int)):
        sum(c)
    rows = [1, 2]
    [f(box([x for x in [1, 2, 3] if x > r]) if r > 1 else box([1])) for r in rows]
"}, "found {0..3 |")]
#[case::through_a_def(indoc! {r"
    def f(c: List(Int)):
        sum(c)
    def g(c):
        f(c)
    g(box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2]))
"}, "found {0..3 |")]
#[case::annotation(indoc! {r"
    xs: List(Int) = box([x for x in [1, 2, 3] if x > 1]) if True else box([1, 2])
    sum(xs)
"}, "found {0..3 |")]
#[case::mut_write(indoc! {r"
    xs: Mut(List(Int)) := box([1, 2])
    xs := box([x for x in [1, 2, 3] if x > 1])
    sum(xs)
"}, "found {0..3 |")]
#[case::mut_write_in_a_loop(indoc! {r"
    xs: Mut(List(Int)) := box([1, 2])
    for r in [1, 2]:
        xs := box([x for x in [1, 2, 3] if x > r])
    sum(xs)
"}, "found Σ (σ : SubtypesOf(0..3)). (σ ⤇ _)")]
fn a_filtered_candidate_reaching_a_list_position_is_refused(
    #[case] code: &str,
    #[case] found: &str,
) {
    let msg = compile_panic(code);
    let expected = format!(
        "Type mismatch for collection annotation: expected Σ (σ : UIntRanges). (σ ⤇ _), {found}"
    );
    assert!(
        msg.starts_with("compilation failed:") && msg.contains(&expected),
        "expected a compile error containing {expected:?}; got: {msg}"
    );
}

/// **A `for` loop over a sum ranges over the keys the sum's value holds.** Its history is
/// typed over the source's witness projected through the source, and its items are read from
/// the source unboxed (`src/ccl/design/collections.md`, "A `for` loop over a sum"). The first
/// case's witness is undetermined, the `UIntRanges` a `List(𝑇)` annotation binds, so the
/// positions come from the value. The second's is determined, so planning erases it to the
/// one candidate after the history was typed over its projection. The third reads a mutable
/// variable, whose seed keeps its `box` because the variable states the kind.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(indoc! {r"
    xs: List(List(Int)) = box([box([1]), box([2, 3])])
    total := 0
    for r in xs:
        total += 1
    total
"}, Value::Int(2))]
#[case(indoc! {r"
    total := 0
    for x in box([1, 2]):
        total += x
    total
"}, Value::Int(3))]
#[case(indoc! {r"
    xs: Mut(List(Int)) := box([1, 2, 3])
    total := 0
    for x in xs:
        total += x
    total
"}, Value::Int(6))]
fn a_loop_over_a_sum_ranges_over_its_keys(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// **A loop writing a mutable variable over a conditional ranges over the chosen arm's keys**,
/// the conditional written in place (its arms comprehensions too), bound by a `let`, returned by
/// a `def`, or chosen per row of an enclosing loop. The conditional is realized where it stands
/// and the loop reads it through `unbox` (`src/ccl/design/collections.md`, "A `for` loop over a
/// sum"). Chosen per row, the realized conditional is lambda-eliminated point-free, and the
/// projection its consumers' types quote reads back to it by normal form
/// (`src/ccl/design/type-inference.md`, "Predicates are compared by normal form").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::in_place(indoc! {r"
    c: Bool = True
    total := 0
    for x in (box([1, 2]) if c else box([1, 2, 3])):
        total += x
    total
"}, Value::Int(3))]
#[case::let_bound(indoc! {r"
    c: Bool = False
    xs = box([1, 2]) if c else box([1, 2, 3])
    total := 0
    for x in xs:
        total += x
    total
"}, Value::Int(6))]
#[case::returned_by_a_def(indoc! {r"
    def pick(c: Bool):
        box([1, 2]) if c else box([1, 2, 3])
    c: Bool = False
    total := 0
    for x in pick(c):
        total += x
    total
"}, Value::Int(6))]
#[case::two_loops_over_one(indoc! {r"
    c: Bool = False
    xs = box([1, 2]) if c else box([1, 2, 3])
    total := 0
    for x in xs:
        total += x
    n := 0
    for y in xs:
        n += 1
    total * 10 + n
"}, Value::Int(63))]
#[case::of_comprehensions(indoc! {r"
    c = 1 > 0
    total := 0
    for x in (box([v + 1 for v in [1, 2]]) if c else box([v * 2 for v in [1, 2, 3]])):
        total += x
    total
"}, Value::Int(5))]
#[case::nested(indoc! {r"
    c: Bool = True
    total := 0
    for x in (box([1]) if c else box([1, 2])):
        for y in (box([10]) if c else box([10, 20])):
            total += x * y
    total
"}, Value::Int(10))]
#[case::chosen_per_row(indoc! {r"
    total := 0
    for i in [1, 2]:
        for q in (box([1, 2]) if i > 1 else box([3, 4, 5])):
            total += q
    total
"}, Value::Int(15))]
#[case::chosen_per_row_among_three(indoc! {r"
    total := 0
    for i in [1, 2, 3]:
        for q in (box([1]) if i == 1 else box([1, 2]) if i == 2 else box([1, 2, 3])):
            total += q * i
    total
"}, Value::Int(25))]
fn a_loop_writing_over_a_conditional_ranges_over_the_chosen_keys(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

/// **A loop feeding a sink over a conditional chosen per row** is keyed by the row and the chosen
/// arm's keys. The realized conditional is bound as a collection over the enclosing positions,
/// a value `Case` fanned out over its input, and planning drives it with an `iterate` over those
/// positions (`crate::ccl::planning` `is_iteration_bearing`).
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::boxed(
    indoc! {r#"
        out = test_sink()
        for i in [1, 2]:
            for q in (box([1, 2]) if i > 1 else box([3, 4, 5])):
                out << q * 10
    "#},
    "[(_0: 0, _1: 0) -> 30, (_0: 0, _1: 1) -> 40, (_0: 0, _1: 2) -> 50, (_0: 1, _1: 0) -> 10, (_0: 1, _1: 1) -> 20]"
)]
#[case::same_domain(
    indoc! {r#"
        out = test_sink()
        for i in [1, 2]:
            for q in ([1, 2] if i > 1 else [3, 4]):
                out << q
    "#},
    "[(_0: 0, _1: 0) -> 3, (_0: 0, _1: 1) -> 4, (_0: 1, _1: 0) -> 1, (_0: 1, _1: 1) -> 2]"
)]
fn a_feed_over_a_conditional_chosen_per_row_is_keyed_by_its_arm(
    #[case] code: &str,
    #[case] expected: &str,
) {
    check_sink(code, expected);
}

/// **A loop over a comprehension over a sum is an ordinary loop**: the comprehension reads its
/// source through `unbox`, so it is a plain collection. Filtered, written in place or bound by a
/// `let`, or inside another loop and reading its element.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::mapped(indoc! {r"
    total := 0
    for x in [v + 1 for v in box([1, 2, 3])]:
        total += x
    total
"}, Value::Int(9))]
#[case::filtered(indoc! {r"
    xs: List(Int) = box([1, 2, 3])
    total := 0
    for x in [v for v in xs if v > 1]:
        total += x
    total
"}, Value::Int(5))]
#[case::filtered_let_bound(indoc! {r"
    xs: List(Int) = box([1, 2, 3])
    ys = [v for v in xs if v > 1]
    total := 0
    for x in ys:
        total += x
    total
"}, Value::Int(5))]
#[case::in_a_loop(indoc! {r"
    xs: List(Int) = box([1, 2])
    total := 0
    for r in [1, 2]:
        for x in [v + r for v in xs]:
            total += x
    total
"}, Value::Int(12))]
fn a_loop_over_a_comprehension_over_a_sum(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Not yet compiled: jagged rows summed inside a `def`. The same expression at top level
/// compiles (`a_jagged_nested_collection_is_consumed_at_each_rows_own_domain`), so the witness listing that comes out empty
/// is lost generalizing over the `def`, not in the comprehension. The generated grid's
/// `function_body/rows_sum` and `generator_yield/rows_sum` cells are this program.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "post-inference produced an invalid tree")]
fn a_def_body_summing_jagged_rows_does_not_compile() {
    check_scalar(
        indoc! {r"
            def f(n):
                sum([sum(r2) for r2 in [box([1, 2]), box([3])]])
            f(3)
        "},
        Value::Int(6),
    );
}

/// **A comprehension over a boxed collection is not boxed** (`docs/chl-spec.md`, "7.4 `box`"):
/// it is keyed like the box's collection, so two over one box join, and boxing it keeps the
/// alternatives the source ranges over, which is what lets it meet the source's annotation.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::comprehensions_over_one_box_join(indoc! {r"
    c: Bool = True
    d: Bool = False
    b = box([1, 2]) if c else box([1, 2, 3])
    ys = [x * 2 for x in b] if d else [x * 3 for x in b]
    sum(ys)
"}, Value::Int(9))]
#[case::a_boxed_comprehension_returns_as_its_sources_type(indoc! {r"
    def doubled(xs: List(Int)) => List(Int):
        box([x * 2 for x in xs])
    sum(doubled(box([1, 2, 3])))
"}, Value::Int(12))]
#[case::a_boxed_comprehension_binds_as_its_sources_type(indoc! {r"
    xs: List(Int) = box([1, 2, 3])
    ys: List(Int) = box([x * 2 for x in xs])
    sum(ys)
"}, Value::Int(12))]
#[case::boxed_branches_join(indoc! {r"
    c: Bool = False
    b1 = box([1, 2])
    b2 = box([1, 2, 3])
    sum(box([y for y in b1]) if c else box([z for z in b2]))
"}, Value::Int(6))]
#[case::a_filtered_box_is_a_collection(indoc! {r"
    xs = box([1, 2, 3])
    ys: Collection(Int) = box([x for x in xs if x > 1])
    sum(ys)
"}, Value::Int(5))]
#[case::a_boxed_comprehension_over_a_map_is_a_map(indoc! {r#"
    held = box(map([("btc", 2), ("eth", 1)]))
    qty: Mut(Map(String, Int), Txn) := box([q * 10000 for q in held])
    sum(await_final(qty))
"#}, Value::Int(30000))]
fn a_comprehension_over_a_box_is_keyed_like_it(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The two spellings §7.5 refuses: comprehensions over two different boxes are keyed
/// differently and do not join, and a filtered box has gaps, so it is no `List`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::comprehensions_over_two_boxes(indoc! {r"
    c: Bool = False
    b1 = box([1, 2])
    b2 = box([1, 2, 3])
    sum([y for y in b1] if c else [z for z in b2])
"}, "Wrap each arm in `box`")]
#[case::a_filtered_box_as_a_list(indoc! {r"
    xs = box([1, 2, 3])
    ys: List(Int) = box([x for x in xs if x > 1])
    sum(ys)
"}, "Type mismatch for collection annotation")]
fn a_comprehension_over_a_box_is_refused_where_its_keys_do_not_fit(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle);
}

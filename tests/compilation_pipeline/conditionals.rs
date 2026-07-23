//! Conditionals: value-selecting `Case` compilation via the literal
//! union-of-restricts forms (the C-form and the data-typed gate fan-out).
//!
//! See `src/ccl/design/mutability.md`, "Value-selecting `Case` and conditional induction writes (partially implemented)".

use std::time::Duration;

use cambra::interpreter::{ColumnValue, Tile, Value};
use rstest_log::rstest;

use crate::helpers::*;

/// Extract the codomain integers of a (possibly `Union`-domain) collection
/// result tile, sorted. A conditional-collection result is a tagged union whose
/// single non-empty variant carries the selected arm's elements.
fn codomain_ints(tile: &Tile) -> Vec<i64> {
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected a SealedFunction tile, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(v)) = codomain.as_ref() else {
        panic!("expected an Ints scalar codomain, got {codomain:?}");
    };
    let mut v = v.clone();
    v.sort_unstable();
    v
}

// ---------------------------------------------------------------------------
// Scalar / compute value selection — the C-form
//
// `x = e₁ if p else e₂` compiles to a union of gated one-shot lifts over the
// `UIntRange(1)` driver, extracted by `final_or_default`. The gates partition
// the driver by first-match (`πᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ`), so exactly one arm's
// element survives.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Basic ternary, both branches.
#[case("c: Bool = True\n1 if c else 2", Value::Int(1))]
#[case("c: Bool = False\n1 if c else 2", Value::Int(2))]
// Guard is a computed comparison, not a bare variable.
#[case("a: Int = 1\nb: Int = 2\n10 if a < b else 20", Value::Int(10))]
#[case("a: Int = 5\nb: Int = 2\n10 if a < b else 20", Value::Int(20))]
// The selected value is itself a computed expression over outer bindings.
#[case("a: Int = 5\nc: Bool = True\na * 2 if c else a - 1", Value::Int(10))]
#[case("a: Int = 5\nc: Bool = False\na * 2 if c else a - 1", Value::Int(4))]
// `elif` chain — first matching guard wins.
#[case(
    "n: Int = 1\n100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(100)
)]
#[case(
    "n: Int = 2\n100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(200)
)]
#[case(
    "n: Int = 9\n100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(300)
)]
// Ternary in an arithmetic context — the whole `Case` is a scalar `V`.
#[case("c: Bool = True\n(1 if c else 2) + 10", Value::Int(11))]
// Nested ternary in an arm.
#[case(
    "a: Int = 1\nb: Int = 1\n(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(100)
)]
#[case(
    "a: Int = 1\nb: Int = 9\n(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(101)
)]
#[case(
    "a: Int = 9\nb: Int = 1\n(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(200)
)]
// Degenerate constant guard folds to the first arm.
#[case("7 if True else 8", Value::Int(7))]
// String and bool arms — the C-form is value-agnostic.
#[case("c: Bool = False\n\"yes\" if c else \"no\"", Value::String("no".into()))]
#[case("c: Bool = True\nFalse if c else True", Value::Bool(false))]
fn test_value_ternary_scalar(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// The off-path arm is **not evaluated**: a guard-protected partial expression
// (`//` by a value the guard proves non-zero) must not fault on the path its
// guard excludes. The scalar C-form lifts each arm over a gated `Units(1)`
// driver, and `MapResultToConst` skips a false-gate arm's value entirely — so
// `10 // b` is never computed when `b == 0`. (Before the laziness fix this
// panicked with "attempt to divide by zero".)
#[rstest]
#[timeout(Duration::from_secs(10))]
// Off-path partial arm: guard false → the `10 // b` arm is skipped, not faulted.
#[case("b: Int = 0\n0 if b == 0 else 10 // b", Value::Int(0))]
// On-path partial arm still evaluates normally.
#[case("b: Int = 2\n10 // b if b != 0 else 0", Value::Int(5))]
// Guard true selects the safe arm; the partial `else` is skipped.
#[case("b: Int = 0\n99 if b == 0 else 10 // b", Value::Int(99))]
// The partial arm is the (excluded) `else` of an explicit guard.
#[case("b: Int = 0\n10 // b if b != 0 else 42", Value::Int(42))]
fn test_value_ternary_skips_partial_off_path_arm(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Data-collection value selection — the gate fan-out
//
// `zs = xs if c else ys` compiles to `⧺ᵢ (xsᵢ | π̂ᵢ)`: each arm's whole
// collection restricted by its constant gate, unioned. The result is the type the
// type system gave the `Case`; exactly one gated arm is non-empty, so consuming
// the union (here via `sum`) sees just that arm's elements.
//
// The union's tagged-`Variant` domain reconciles against the arms' joined data
// function by `is_index_partition_of`: every leg is that one domain under its own
// gate. Arms at *distinct* domains have no join to subtype against and are rejected
// at inference, so the fan-out is only built at one domain.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Two arms at one domain.
#[case("c: Bool = True\nsum([1, 2] if c else [3, 4])", Value::Int(3))]
#[case("c: Bool = False\nsum([1, 2] if c else [3, 4])", Value::Int(7))]
// Guard is a computed comparison.
#[case("n: Int = 2\nsum([10, 20] if n == 1 else [1, 2])", Value::Int(3))]
#[case("n: Int = 1\nsum([10, 20] if n == 1 else [1, 2])", Value::Int(30))]
// `elif` over collections — first matching arm's collection wins. **Three legs over
// one fiber**: the three arms all have domain `[0, 1)`, so the fan-out is a
// three-leg `Variant` whose payloads are all that one domain under different gates.
// This is exactly what `is_index_partition_of` must accept — a positional
// leg↔domain bijection would reject it — and what an `if`/`elif` accumulator write
// produces.
#[case(
    "n: Int = 1\nsum([1] if n == 1 else [2] if n == 2 else [3])",
    Value::Int(1)
)]
#[case(
    "n: Int = 2\nsum([1] if n == 1 else [2] if n == 2 else [3])",
    Value::Int(2)
)]
#[case(
    "n: Int = 9\nsum([1] if n == 1 else [2] if n == 2 else [3])",
    Value::Int(3)
)]
fn test_value_case_collection_sum(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional collection as the program result: the tagged union tile carries
// exactly the selected arm (the other legs are gated empty). This pins the tile
// shape, which the `sum` cases above only exercise through an aggregate.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_value_case_collection_result() {
    let result = run_pipeline("c: Bool = True\n[1, 2] if c else [3, 4]");
    assert_eq!(codomain_ints(&result), vec![1, 2]);
    let result = run_pipeline("c: Bool = False\n[1, 2] if c else [3, 4]");
    assert_eq!(codomain_ints(&result), vec![3, 4]);
}

// Consuming a conditional collection through a comprehension
// (`[f(x) for x in (xs if c else ys)]`) is exercised below by
// `test_comprehension_over_conditional`.

// ---------------------------------------------------------------------------
// Source-less conditional feeds
//
// `if c: d << v1 else: d << v2` (outside any loop) has no iteration source, so
// each feeding arm becomes a gated one-shot lift `λ __unused : {Unit | π̂ᵢ} → vᵢ`
// over the `Unit` driver. The channel union publishes exactly the selected arm's
// value (empty when no arm fires — a naturally-partial feed). A `defer()` read
// surfaces the channel.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// if/else — the selected arm's value is fed.
#[case("c: Bool = True\nx = defer()\nif c:\n    x << 1\nelse:\n    x << 2\nx", vec![1])]
#[case("c: Bool = False\nx = defer()\nif c:\n    x << 1\nelse:\n    x << 2\nx", vec![2])]
// elif — first matching arm's value.
#[case(
    "n: Int = 1\nx = defer()\nif n == 1:\n    x << 10\nelif n == 2:\n    x << 20\nelse:\n    x << 30\nx",
    vec![10]
)]
#[case(
    "n: Int = 2\nx = defer()\nif n == 1:\n    x << 10\nelif n == 2:\n    x << 20\nelse:\n    x << 30\nx",
    vec![20]
)]
#[case(
    "n: Int = 9\nx = defer()\nif n == 1:\n    x << 10\nelif n == 2:\n    x << 20\nelse:\n    x << 30\nx",
    vec![30]
)]
fn test_conditional_feed(#[case] code: &str, #[case] expected: Vec<i64>) {
    assert_eq!(codomain_ints(&run_pipeline(code)), expected);
}

// Off-path laziness for the source-less feed: each arm is a gated one-shot lift
// over the `Unit` driver, so only the fired arm's value is pulled — a
// guard-protected partial op in the *unfired* arm is never evaluated. `100 // n`
// must not fault at n = 0. (A non-lazy fan-out would divide by zero here.)
//
// Note: this laziness holds for the source-less feed (and the scalar C-form)
// because each arm is a distinct gated one-shot lift. It does NOT extend to a
// partial op inside a *filtered comprehension* body (`[100 // x for x in xs if
// x != 0]`), where the filter is a logical delete and the map still evaluates
// the deleted positions — a pre-existing limitation independent of conditionals.
#[rstest]
#[timeout(Duration::from_secs(10))]
// n=0 → else fires (42); the `100 // n` arm is not pulled.
#[case("n: Int = 0\nx = defer()\nif n != 0:\n    x << 100 // n\nelse:\n    x << 42\nx", vec![42])]
// n=5 → the partial arm fires and evaluates normally (100 // 5 = 20).
#[case("n: Int = 5\nx = defer()\nif n != 0:\n    x << 100 // n\nelse:\n    x << 42\nx", vec![20])]
fn test_conditional_feed_skips_partial_off_path_arm(
    #[case] code: &str,
    #[case] expected: Vec<i64>,
) {
    assert_eq!(codomain_ints(&run_pipeline(code)), expected);
}

// NOTE: a *source-less no-else* conditional feed (`if c: d << v`, a naturally
// partial feed) is blocked earlier, at lowering — a bare `if` with no `else` is
// rejected as a value-returning expression before channelize sees it. The source-less-feed path handles
// the feed extraction once lowering admits the shape; the if/else and elif forms
// above exercise it. A *scrutinee / pattern* feed stays rejected
// (`PartialFeedCaseUnsupported`): a pattern match cannot be gated by a boolean.

// ---------------------------------------------------------------------------
// Comprehension over a conditional collection
//
// `[f(x) for x in (xs if c else ys)]` floats the source `Case` out of the map
// (`lower::comprehension`) — `Case{gᵢ → [f(x) for x in srcᵢ]}` — with each arm
// built as a `Compose` (`src ≫ λx→body`) so it carries the source's *data* kind.
// The arms then join as collections and compile via the gate fan-out, rather than
// colliding as compute-kinded lambdas over their index domains.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Identity comprehension over a conditional collection.
#[case(
    "c: Bool = True\nsum([x for x in ([1, 2] if c else [3, 4])])",
    Value::Int(3)
)]
#[case(
    "c: Bool = False\nsum([x for x in ([1, 2] if c else [3, 4])])",
    Value::Int(7)
)]
// Mapping comprehension over a conditional collection.
#[case(
    "c: Bool = True\nsum([x * 10 for x in ([1, 2] if c else [3, 4])])",
    Value::Int(30)
)]
#[case(
    "c: Bool = False\nsum([x * 10 for x in ([1, 2] if c else [3, 4])])",
    Value::Int(70)
)]
// Nested conditional source (an `elif` in the iterable) floats per arm.
#[case(
    "n: Int = 2\nsum([x for x in ([1] if n == 1 else [2] if n == 2 else [3])])",
    Value::Int(2)
)]
#[case(
    "n: Int = 3\nsum([x for x in ([1] if n == 1 else [2] if n == 2 else [3])])",
    Value::Int(3)
)]
fn test_comprehension_over_conditional(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional *between* two standalone comprehensions
// (`([x for x in xs]) if c else ([y for y in ys])`). This is the case
// kind inference unblocks: a comprehension used as a
// value is a lambda whose kind var resolves to `Data` from its collection domain, so
// the two `Case` arms join as collections instead of colliding as compute meets.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "c: Bool = True\nsum(([x for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
    Value::Int(3)
)]
#[case(
    "c: Bool = False\nsum(([x for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
    Value::Int(7)
)]
#[case(
    "c: Bool = True\nsum(([x * 10 for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
    Value::Int(30)
)]
fn test_conditional_between_comprehensions(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Conditional element in a comprehension
//
// `[a if g(x) else b for x in xs]` — a per-element conditional — fans the source
// out by each arm's *element-dependent* first-match gate
// (`lower::comprehension::fan_out_element_case`): `⧺ᵢ [eᵢ for x in xs if π̂ᵢ]`.
// Each arm is a filtered map (source restricted by the gate, mapped by the arm
// value); the gates partition the source, so the `++`-union recombines the arms
// by position into the fully-mapped collection. A `CollectionUnion`, so the
// compute-kinded per-arm maps do not need to join.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// [1,2,3,4] with `x*10 if x>2 else 0` → [0,0,30,40].
#[case(
    "sum([(x * 10 if x > 2 else 0) for x in [1, 2, 3, 4]])",
    Value::Int(70)
)]
// Both arms reference the element.
#[case(
    "sum([(x * 2 if x > 2 else x + 100) for x in [1, 2, 3, 4]])",
    Value::Int(217)
)]
// Nested `elif` element flattens to a flat partition.
#[case(
    "sum([(100 if x == 1 else 200 if x == 2 else 300) for x in [1, 2, 3]])",
    Value::Int(600)
)]
// Degenerate gates: always-true / never-true.
#[case("sum([(x if x > 0 else 0) for x in [1, 2, 3]])", Value::Int(6))]
#[case("sum([(99 if x > 100 else x) for x in [1, 2, 3]])", Value::Int(6))]
fn test_conditional_element_comprehension(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// The conditional-element comprehension result is a tagged union — one variant
// per arm, each carrying the elements the arm mapped.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_conditional_element_result() {
    // x>2 → x*10 (positions 2,3 → 30,40); else 0 (positions 0,1 → 0,0).
    let result = run_pipeline("[(x * 10 if x > 2 else 0) for x in [1, 2, 3, 4]]");
    assert_eq!(codomain_ints(&result), vec![0, 0, 30, 40]);
}

// ---------------------------------------------------------------------------
// Conditional induction writes — `if p: acc += e` in a mutation loop.
//
// `lower_loop_body_chain` lowers the `if` to a statement-`Case`; `transform_chain`
// merges its branches into one writer decision — a single conditional write is
// `{commit: ĝ, writes: prev+e}` (a `!commit` position carries in the changelog).
// One writer over the full source → a single-writer `Transact` → the changelog
// `InductionStore`, read densely and reduced to the final accumulator.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Guard fires for 3, 4 → total = 3 + 4 = 7; positions 0, 1 carry.
#[case(
    "total := 0\nfor x in [1, 2, 3, 4]:\n    if x > 2:\n        total += x\ntotal",
    7
)]
// Guard fires for none → total stays at its init.
#[case(
    "total := 0\nfor x in [1, 2, 3]:\n    if x > 10:\n        total += x\ntotal",
    0
)]
// Guard fires for all → same as an unconditional accumulate (1+2+3 = 6).
#[case(
    "total := 0\nfor x in [1, 2, 3]:\n    if x > 0:\n        total += x\ntotal",
    6
)]
// A non-zero init the leading carries fold to (only 3 fires → 100 + 3 = 103).
#[case(
    "total := 100\nfor x in [1, 2, 3]:\n    if x == 3:\n        total += x\ntotal",
    103
)]
// Fire early, then an **all-carry tail**: x=3 (position 0) writes +3; x=1
// (position 1) carries. The last *change* is at position 0, but the final
// accumulator is at position 1 — so the scalar-final `ExtractLast` must read the
// carried tail, not stop at the last change tick. Pins the terminality/watermark
// decoupling (a sparse writer whose tail carries reads its true final value).
#[case(
    "total := 0\nfor x in [3, 1]:\n    if x > 2:\n        total += x\ntotal",
    3
)]
// A **partial op** (`//`) in the written value, guarded away from its bad input.
// The write value is compiled lazily (`filter_values(x != 0) ≫ (total // x)`), so
// `total // x` is evaluated only where `x != 0` — never at the `x == 0` position
// it would fault on. x=2 → 100 // 2 = 50; x=0 → guard false, carry → 50.
#[case(
    "total := 100\nfor x in [2, 0]:\n    if x != 0:\n        total := total // x\ntotal",
    50
)]
// An **absolute** conditional write (`total := 5`, a constant not reading the
// accumulator): the arm is `filter_values(x > 2) ≫ const(5)`. The filter routes
// the constant to the guard's positions only — `try_const_reduce` must not
// collapse `filter_values ≫ const` to a bare `const` (which would set 5 at every
// position). x=1,2 carry init 9; x=3,4 set 5 → final 5.
#[case(
    "total := 9\nfor x in [1, 2, 3, 4]:\n    if x > 2:\n        total := 5\ntotal",
    5
)]
// An **unconditional** write *before* a conditional write on the same accumulator.
// The unconditional `+= 1` applies at every position and must commit even where
// the guard fails — the guard change rides *on top* of it. x=1 → +1 (=1); x=2 →
// +1 then +10 (=12); x=3 → +1 then +10 (=23). A commit gate that only fired on the
// guard would drop the `+= 1` at x=1 (regressing to the prior value).
#[case(
    "x := 0\nfor i in [1, 2, 3]:\n    x := x + 1\n    if i > 1:\n        x := x + 10\nx",
    23
)]
// Same, with the unconditional write *after* the conditional (spliced into every
// path). x=1 → +1 (=1); x=2 → +10 then +1 (=12); x=3 → +10 then +1 (=23).
#[case(
    "x := 0\nfor i in [1, 2, 3]:\n    if i > 1:\n        x := x + 10\n    x := x + 1\nx",
    23
)]
// **Sibling** `if`s (not `elif`) writing the *same* accumulator: the write set is
// a nested value-`Case`, and `commit` is forced true wherever the carry differs
// from the entering value. i=1: +100 (=100); i=2: +2 then +100 (=202); i=3: +3
// (=205). Final 205.
#[case(
    "a := 0\nfor i in [1, 2, 3]:\n    if i > 1:\n        a := a + i\n    if i < 3:\n        a := a + 100\na",
    205
)]
fn test_conditional_induction_write(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

// Two **separate** accumulators in one loop — one unconditional, one conditional.
// `cnt` commits on every position (its carry always differs from the entering
// value); `total` rides its own conditional value-`Case`. cnt = 3 (all), total =
// 2+3 = 5. Encoded as `cnt * 10 + total` = 35 to pin both independently.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_conditional_induction_two_accumulators() {
    check_scalar(
        "cnt := 0\ntotal := 0\nfor i in [1, 2, 3]:\n    cnt := cnt + 1\n    if i > 1:\n        total := total + i\ncnt * 10 + total",
        Value::Int(35),
    );
}

// An `if`/`else` that writes the *same* accumulator on both arms: the write set
// is a per-position value-`Case` (`writes.total = Case[x>2 → prev+x; true →
// prev+1]`), compiled by the lazy value-preserving `filter_values`
// union-of-restricts inside the writer lambda (`⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`; each
// arm's value is evaluated only where its guard holds — no eager both-arm eval).
#[rstest]
#[timeout(Duration::from_secs(10))]
// x=1,2 → +1 (else); x=3,4 → +x. total = 1+1+3+4 = 9.
#[case(
    "total := 0\nfor x in [1, 2, 3, 4]:\n    if x > 2:\n        total += x\n    else:\n        total += 1\ntotal",
    9
)]
// elif chain, all arms write. x=1→+10, x=2→+20, x=3→+30. total = 60.
#[case(
    "total := 0\nfor x in [1, 2, 3]:\n    if x == 1:\n        total += 10\n    elif x == 2:\n        total += 20\n    else:\n        total += 30\ntotal",
    60
)]
fn test_conditional_induction_if_else_both_write(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

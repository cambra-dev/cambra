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
#[case(
    r"
c: Bool = True
1 if c else 2",
    Value::Int(1)
)]
#[case(
    r"
c: Bool = False
1 if c else 2",
    Value::Int(2)
)]
// Guard is a computed comparison, not a bare variable.
#[case(
    r"
a: Int = 1
b: Int = 2
10 if a < b else 20",
    Value::Int(10)
)]
#[case(
    r"
a: Int = 5
b: Int = 2
10 if a < b else 20",
    Value::Int(20)
)]
// The selected value is itself a computed expression over outer bindings.
#[case(
    r"
a: Int = 5
c: Bool = True
a * 2 if c else a - 1",
    Value::Int(10)
)]
#[case(
    r"
a: Int = 5
c: Bool = False
a * 2 if c else a - 1",
    Value::Int(4)
)]
// `elif` chain — first matching guard wins.
#[case(
    r"
n: Int = 1
100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(100)
)]
#[case(
    r"
n: Int = 2
100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(200)
)]
#[case(
    r"
n: Int = 9
100 if n == 1 else 200 if n == 2 else 300",
    Value::Int(300)
)]
// Ternary in an arithmetic context — the whole `Case` is a scalar `V`.
#[case(
    r"
c: Bool = True
(1 if c else 2) + 10",
    Value::Int(11)
)]
// Nested ternary in an arm.
#[case(
    r"
a: Int = 1
b: Int = 1
(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(100)
)]
#[case(
    r"
a: Int = 1
b: Int = 9
(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(101)
)]
#[case(
    r"
a: Int = 9
b: Int = 1
(100 if b == 1 else 101) if a == 1 else 200",
    Value::Int(200)
)]
// Degenerate constant guard folds to the first arm.
#[case("7 if True else 8", Value::Int(7))]
// String and bool arms — the C-form is value-agnostic.
#[case(r#"
c: Bool = False
"yes" if c else "no""#, Value::String("no".into()))]
#[case(
    r"
c: Bool = True
False if c else True",
    Value::Bool(false)
)]
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
#[case(
    r"
b: Int = 0
0 if b == 0 else 10 // b",
    Value::Int(0)
)]
// On-path partial arm still evaluates normally.
#[case(
    r"
b: Int = 2
10 // b if b != 0 else 0",
    Value::Int(5)
)]
// Guard true selects the safe arm; the partial `else` is skipped.
#[case(
    r"
b: Int = 0
99 if b == 0 else 10 // b",
    Value::Int(99)
)]
// The partial arm is the (excluded) `else` of an explicit guard.
#[case(
    r"
b: Int = 0
10 // b if b != 0 else 42",
    Value::Int(42)
)]
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
#[case(
    r"
c: Bool = True
sum([1, 2] if c else [3, 4])",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum([1, 2] if c else [3, 4])",
    Value::Int(7)
)]
// Guard is a computed comparison.
#[case(
    r"
n: Int = 2
sum([10, 20] if n == 1 else [1, 2])",
    Value::Int(3)
)]
#[case(
    r"
n: Int = 1
sum([10, 20] if n == 1 else [1, 2])",
    Value::Int(30)
)]
// `elif` over collections — first matching arm's collection wins. **Three legs over
// one fiber**: the three arms all have domain `[0, 1)`, so the fan-out is a
// three-leg `Variant` whose payloads are all that one domain under different gates.
// This is exactly what `is_index_partition_of` must accept — a positional
// leg↔domain bijection would reject it — and what an `if`/`elif` accumulator write
// produces.
#[case(
    r"
n: Int = 1
sum([1] if n == 1 else [2] if n == 2 else [3])",
    Value::Int(1)
)]
#[case(
    r"
n: Int = 2
sum([1] if n == 1 else [2] if n == 2 else [3])",
    Value::Int(2)
)]
#[case(
    r"
n: Int = 9
sum([1] if n == 1 else [2] if n == 2 else [3])",
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
    let result = run_pipeline(
        r"
c: Bool = True
[1, 2] if c else [3, 4]",
    );
    assert_eq!(codomain_ints(&result), vec![1, 2]);
    let result = run_pipeline(
        r"
c: Bool = False
[1, 2] if c else [3, 4]",
    );
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
#[case(r"
c: Bool = True
x = defer()
if c:
    x << 1
else:
    x << 2
x", vec![1])]
#[case(r"
c: Bool = False
x = defer()
if c:
    x << 1
else:
    x << 2
x", vec![2])]
// elif — first matching arm's value.
#[case(
    r"
n: Int = 1
x = defer()
if n == 1:
    x << 10
elif n == 2:
    x << 20
else:
    x << 30
x",
    vec![10]
)]
#[case(
    r"
n: Int = 2
x = defer()
if n == 1:
    x << 10
elif n == 2:
    x << 20
else:
    x << 30
x",
    vec![20]
)]
#[case(
    r"
n: Int = 9
x = defer()
if n == 1:
    x << 10
elif n == 2:
    x << 20
else:
    x << 30
x",
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
#[case(r"
n: Int = 0
x = defer()
if n != 0:
    x << 100 // n
else:
    x << 42
x", vec![42])]
// n=5 → the partial arm fires and evaluates normally (100 // 5 = 20).
#[case(r"
n: Int = 5
x = defer()
if n != 0:
    x << 100 // n
else:
    x << 42
x", vec![20])]
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
    r"
c: Bool = True
sum([x for x in ([1, 2] if c else [3, 4])])",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum([x for x in ([1, 2] if c else [3, 4])])",
    Value::Int(7)
)]
// Mapping comprehension over a conditional collection.
#[case(
    r"
c: Bool = True
sum([x * 10 for x in ([1, 2] if c else [3, 4])])",
    Value::Int(30)
)]
#[case(
    r"
c: Bool = False
sum([x * 10 for x in ([1, 2] if c else [3, 4])])",
    Value::Int(70)
)]
// Nested conditional source (an `elif` in the iterable) floats per arm.
#[case(
    r"
n: Int = 2
sum([x for x in ([1] if n == 1 else [2] if n == 2 else [3])])",
    Value::Int(2)
)]
#[case(
    r"
n: Int = 3
sum([x for x in ([1] if n == 1 else [2] if n == 2 else [3])])",
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
    r"
c: Bool = True
sum(([x for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum(([x for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
    Value::Int(7)
)]
#[case(
    r"
c: Bool = True
sum(([x * 10 for x in [1, 2]]) if c else ([y for y in [3, 4]]))",
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
// by position into the fully-mapped collection. A `Copair`, so the
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
    r"
total := 0
for x in [1, 2, 3, 4]:
    if x > 2:
        total += x
total",
    7
)]
// Guard fires for none → total stays at its init.
#[case(
    r"
total := 0
for x in [1, 2, 3]:
    if x > 10:
        total += x
total",
    0
)]
// Guard fires for all → same as an unconditional accumulate (1+2+3 = 6).
#[case(
    r"
total := 0
for x in [1, 2, 3]:
    if x > 0:
        total += x
total",
    6
)]
// A non-zero init the leading carries fold to (only 3 fires → 100 + 3 = 103).
#[case(
    r"
total := 100
for x in [1, 2, 3]:
    if x == 3:
        total += x
total",
    103
)]
// Fire early, then an **all-carry tail**: x=3 (position 0) writes +3; x=1
// (position 1) carries. The latest *change* is at position 0, but the final
// accumulator is at position 1 — so the scalar-final `ExtractFinal` must read the
// carried tail, not stop at the latest change tick. Pins the terminality/watermark
// decoupling (a sparse writer whose tail carries reads its true final value).
#[case(
    r"
total := 0
for x in [3, 1]:
    if x > 2:
        total += x
total",
    3
)]
// **Trailing carries**: writes then a carrying tail (`x < 3` fires at 1,2; the
// final three positions carry). The scalar-final read must fold to the latest
// *written* value (1+2 = 3), not undercount because the changelog's latest change
// tick sits below the position watermark — the terminality-vs-watermark fix.
#[case(
    r"
total := 0
for x in [1, 2, 3, 4, 5]:
    if x < 3:
        total += x
total",
    3
)]
// A **partial op** (`//`) in the written value, guarded away from its bad input.
// The write value is compiled lazily (`filter_values(x != 0) ≫ (total // x)`), so
// `total // x` is evaluated only where `x != 0` — never at the `x == 0` position
// it would fault on. x=2 → 100 // 2 = 50; x=0 → guard false, carry → 50.
#[case(
    r"
total := 100
for x in [2, 0]:
    if x != 0:
        total := total // x
total",
    50
)]
// An **absolute** conditional write (`total := 5`, a constant not reading the
// accumulator): the arm is `filter_values(x > 2) ≫ const(5)`. The filter routes
// the constant to the guard's positions only — `try_const_reduce` must not
// collapse `filter_values ≫ const` to a bare `const` (which would set 5 at every
// position). x=1,2 carry init 9; x=3,4 set 5 → final 5.
#[case(
    r"
total := 9
for x in [1, 2, 3, 4]:
    if x > 2:
        total := 5
total",
    5
)]
// An **unconditional** write *before* a conditional write on the same accumulator.
// The unconditional `+= 1` applies at every position and must commit even where
// the guard fails — the guard change rides *on top* of it. x=1 → +1 (=1); x=2 →
// +1 then +10 (=12); x=3 → +1 then +10 (=23). A commit gate that only fired on the
// guard would drop the `+= 1` at x=1 (regressing to the prior value).
#[case(
    r"
x := 0
for i in [1, 2, 3]:
    x := x + 1
    if i > 1:
        x := x + 10
x",
    23
)]
// Same, with the unconditional write *after* the conditional (spliced into every
// path). x=1 → +1 (=1); x=2 → +10 then +1 (=12); x=3 → +10 then +1 (=23).
#[case(
    r"
x := 0
for i in [1, 2, 3]:
    if i > 1:
        x := x + 10
    x := x + 1
x",
    23
)]
// **Sibling** `if`s (not `elif`) writing the *same* accumulator: the write set is
// a nested value-`Case`, and `commit` is forced true wherever the carry differs
// from the entering value. i=1: +100 (=100); i=2: +2 then +100 (=202); i=3: +3
// (=205). Final 205.
#[case(
    r"
a := 0
for i in [1, 2, 3]:
    if i > 1:
        a := a + i
    if i < 3:
        a := a + 100
a",
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
        r"
cnt := 0
total := 0
for i in [1, 2, 3]:
    cnt := cnt + 1
    if i > 1:
        total := total + i
cnt * 10 + total",
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
    r"
total := 0
for x in [1, 2, 3, 4]:
    if x > 2:
        total += x
    else:
        total += 1
total",
    9
)]
// elif chain, all arms write. x=1→+10, x=2→+20, x=3→+30. total = 60.
#[case(
    r"
total := 0
for x in [1, 2, 3]:
    if x == 1:
        total += 10
    elif x == 2:
        total += 20
    else:
        total += 30
total",
    60
)]
fn test_conditional_induction_if_else_both_write(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

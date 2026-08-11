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
// collection restricted by its constant gate, unioned. The result is the Σ the
// type system gave the `Case`; exactly one gated arm is non-empty, so consuming
// the union (here via `sum`) sees just that arm's elements.
//
// The union's tagged-`Variant` domain reconciles against the Σ by
// Σ-width (distinct domains → the compiled partition realizes the whole
// Σ; same-domain collapse → it subtypes the collapsed plain data fun).
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Distinct-domain arms — the `Case` types as a Σ; `sum` consumes it via `Σ <: Fun`.
#[case(
    r"
c: Bool = True
sum(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(6)
)]
// Same-domain arms — the Σ collapses to a plain data function.
#[case(
    r"
c: Bool = True
sum(box([1, 2]) if c else box([3, 4]))",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum(box([1, 2]) if c else box([3, 4]))",
    Value::Int(7)
)]
// Guard is a computed comparison.
#[case(
    r"
n: Int = 2
sum(box([10, 20]) if n == 1 else box([1, 2, 3, 4]))",
    Value::Int(10)
)]
// `elif` over collections — first matching arm's collection wins.
#[case(
    r"
n: Int = 2
sum(box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3]))",
    Value::Int(4)
)]
#[case(
    r"
n: Int = 3
sum(box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3]))",
    Value::Int(9)
)]
// **Repeated domain across branches.** `[1]` and `[2]` share domain `[0,1)`, so
// the Σ has *two* candidates (`{[0,1), [0,2)}`) but the fan-out has *three*
// legs. This is why leg↔candidate is a **surjection**: two legs realize the
// shared `[0,1)` candidate, their gates partitioning "branch a or b was taken".
// A rule demanding one leg per candidate would reject it.
#[case(
    r"
n: Int = 1
sum(box([1]) if n == 1 else box([2]) if n == 2 else box([3, 3]))",
    Value::Int(1)
)]
#[case(
    r"
n: Int = 2
sum(box([1]) if n == 1 else box([2]) if n == 2 else box([3, 3]))",
    Value::Int(2)
)]
#[case(
    r"
n: Int = 9
sum(box([1]) if n == 1 else box([2]) if n == 2 else box([3, 3]))",
    Value::Int(6)
)]
fn test_value_case_collection_sum(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Arms whose domains share a **base** but differ by a refinement: a filtered
/// comprehension beside an unfiltered collection over the same range. The Σ is
/// `Σ 𝐷 ∈ {{[0,2]|p}, [0,2]}. 𝐷` — two candidates, one base, distinguished by nothing
/// but their refinements.
///
/// That is what makes these the cases where a *deep* refinement strip is
/// indistinguishable from the right answer at the type level and catastrophic at the
/// value level: both candidates strip to `[0,2]`, so realization still builds two legs
/// over two apparently-fine domains — and the filtered leg silently iterates all three
/// elements, because the filter it lost was the only thing that was going to become a
/// `Restrict`. The wrong answer is the *unfiltered* sum, which is why the expected values
/// here differ by exactly the elements a missing filter would readmit.
///
/// Both branch orders are pinned: with a shared base, an asymmetry between the two is the
/// signature of a rule that reads the candidates positionally.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Filtered arm first (`c` true → the filtered arm, `[2, 3]`).
#[case(
    r"
c: Bool = True
sum(box([x for x in [1, 2, 3] if x > 1]) if c else box([1, 2, 3]))",
    Value::Int(5)
)]
// The same program with the arms swapped (`c` true → the unfiltered arm).
#[case(
    r"
c: Bool = True
sum(box([1, 2, 3]) if c else box([x for x in [1, 2, 3] if x > 1]))",
    Value::Int(6)
)]
// Off-path selection through the shared base: `c` false takes the second arm.
#[case(
    r"
c: Bool = False
sum(box([x for x in [1, 2, 3] if x > 1]) if c else box([1, 2, 3]))",
    Value::Int(6)
)]
// Both arms filtered, by *different* predicates — two distinct refined
// candidates over one base, so neither leg subtypes the other's candidate.
#[case(
    r"
c: Bool = True
sum(box([x for x in [1,2,3] if x > 1]) if c else box([y for y in [1,2,3] if y > 2]))",
    Value::Int(5)
)]
fn test_value_case_arms_sharing_a_domain_base(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional collection used directly as the program result: the tagged
// union tile carries exactly the selected arm (the other variant is empty).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_value_case_collection_result() {
    // `True` arm: the surviving variant holds `[1, 2]`.
    let result = run_pipeline(
        r"
c: Bool = True
box([1, 2]) if c else box([1, 2, 3])",
    );
    assert_eq!(codomain_ints(&result), vec![1, 2]);
    // `False` arm: the surviving variant holds `[1, 2, 3]`.
    let result = run_pipeline(
        r"
c: Bool = False
box([1, 2]) if c else box([1, 2, 3])",
    );
    assert_eq!(codomain_ints(&result), vec![1, 2, 3]);
}

// Same-domain arms as a program result: the Σ collapses to a plain data
// function, not a Σ, but the runtime still selects the right arm. This pins the
// tile shape of the collapse, which the `sum` cases above only exercise through
// an aggregate.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_value_case_same_domain_collection_result() {
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
// The arms then `sigma_join` into the Σ and compile via the gate fan-out,
// rather than colliding as compute-kinded lambdas over distinct index domains.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Identity comprehension over a conditional collection.
#[case(
    r"
c: Bool = True
sum([x for x in (box([1, 2]) if c else box([1, 2, 3]))])",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum([x for x in (box([1, 2]) if c else box([1, 2, 3]))])",
    Value::Int(6)
)]
// Mapping comprehension over a conditional collection.
#[case(
    r"
c: Bool = True
sum([x * 10 for x in (box([1, 2]) if c else box([1, 2, 3]))])",
    Value::Int(30)
)]
#[case(
    r"
c: Bool = False
sum([x * 10 for x in (box([1, 2]) if c else box([1, 2, 3]))])",
    Value::Int(60)
)]
// Nested conditional source: an `elif` in the iterable is one N-choice sum.
#[case(
    r"
n: Int = 2
sum([x for x in (box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3]))])",
    Value::Int(4)
)]
#[case(
    r"
n: Int = 3
sum([x for x in (box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3]))])",
    Value::Int(9)
)]
fn test_comprehension_over_conditional(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// **The source need not be a literal `Case`.** Consuming a conditional collection goes
/// through one rule, so what matters is the *type* at the generator, not the syntax that
/// put it there — a binding, a parameter, or a filter in between are all the same rule.
///
/// Each case here is a shape the retired source-`Case` float could not reach: it pattern
/// -matched a `Case` sitting literally in the generator, so a let-bound or parameter-passed
/// conditional fell through to a path that could not name the witness consistently. They
/// type-checked and failed to compile. Cases 1-2 of `test_comprehension_over_conditional`
/// stay as the literal-source form, which the float *did* handle — keeping both is what
/// shows the general path subsumes it rather than replacing one gap with another.
#[rstest]
#[timeout(Duration::from_secs(30))]
// Let-bound: the conditional is named, then iterated.
#[case(
    r"
c: Bool = True
x = box([1, 2]) if c else box([1, 2, 3])
sum([y for y in x])",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
x = box([1, 2]) if c else box([1, 2, 3])
sum([y * 10 for y in x])",
    Value::Int(60)
)]
// Through a UDF parameter: the sum arrives at the call, not the definition.
#[case(
    r"
def f(xs):
    sum([y for y in xs])
c: Bool = True
f(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(3)
)]
// **One collection, two consumers.** Both comprehensions range over whichever domain the
// same conditional took, so they share a witness — the half of witness identity that
// `two_conditional_sources_keep_their_witnesses_apart` does not cover, since it is about
// keeping *different* witnesses apart.
#[case(
    r"
c: Bool = True
x = box([1, 2]) if c else box([1, 2, 3])
sum([y for y in x]) + sum([z for z in x])",
    Value::Int(6)
)]
fn a_conditional_source_compiles_however_it_reaches_the_generator(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
}

/// **A comprehension filter over a conditional source is not emitted yet.**
///
/// The conditional-free half of this now works (`sums.rs`,
/// `a_filter_over_a_boxed_source_is_applied`): a **determined** witness — one candidate — is
/// erased by `unbox` in the term and instantiated in the types, so the consuming site is left
/// with an ordinary refined domain and the existing iterate-then-restricts chain compiles it.
///
/// These are the cases where the witness is *not* determined, so nothing erases it. The sum
/// has two or more candidates (or one candidate over two realized legs — the same-domain
/// pair below), and the site's domain stays `{𝜎 | 𝑝}` with 𝜎 a real witness. Inference is
/// right throughout; the comprehension types as
/// `Σ 𝜎 ∈ {[0, 1], [0, 2]}. ({𝜎 | 𝑝} ⤇ Int)`,
/// the restriction on the witness exactly as
/// `src/ccl/design/type-inference.md`, "Consuming a sum: naming the witness" says.
///
/// **What is owed is an extent for that witness**, and it is right there: realization has
/// already materialized this sum as the gated union below the site, whose extent *is* the
/// selected domain because the unselected legs are empty. Planning does not consult it — it
/// reads the domain off the type, finds a witness, and refuses.
///
/// Planning refuses rather than dropping, so these fail to compile instead of computing the
/// unfiltered answer. That distinction matters here: two of the cases below have filters that
/// are no-ops on the arm they select, so a dropped filter would leave them *passing*.
#[rstest]
#[timeout(Duration::from_secs(30))]
// Both arms of the two-candidate sum. Only the `else` arm was pinned before, which cannot
// distinguish a rule that reads the candidate list positionally.
#[case(
    r"
c: Bool = True
sum([y for y in (box([1, 2]) if c else box([1, 2, 3])) if y > 1])",
    Value::Int(2)
)]
#[case(
    r"
c: Bool = False
sum([y for y in (box([1, 2]) if c else box([1, 2, 3])) if y > 1])",
    Value::Int(5)
)]
// How the conditional reaches the generator — the same three routes
// `a_conditional_source_compiles_however_it_reaches_the_generator` pins unfiltered.
#[case(
    r"
def f(xs):
    sum([y for y in xs if y > 1])
c: Bool = False
f(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(5)
)]
#[case(
    r"
c: Bool = False
sum([y for y in (box([x for x in [1, 2]]) if c else box([x for x in [1, 2, 3]])) if y > 1])",
    Value::Int(5)
)]
// A **mapping** body. The identity comprehension above simplifies to a bare `cast`, so the
// `Case` still carries the sum when realization reaches it; composing a map onto the site
// opens the sum, leaving the `Case` typed by the *arrow view* `σ ⤇ Int`. Both spellings name
// the same witness and owe the same restriction.
#[case(
    r"
c: Bool = False
sum([y * 10 for y in (box([1, 2]) if c else box([1, 2, 3])) if y > 1])",
    Value::Int(50)
)]
// Three arms: more legs than the two the union shape is usually reasoned about with.
#[case(
    r"
n: Int = 2
sum([y for y in (box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3])) if y > 1])",
    Value::Int(4)
)]
#[case(
    r"
n: Int = 3
sum([y for y in (box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3])) if y > 1])",
    Value::Int(9)
)]
// ...including one whose selected arm the filter empties.
#[case(
    r"
n: Int = 1
sum([y for y in (box([1]) if n == 1 else box([2, 2]) if n == 2 else box([3, 3, 3])) if y > 1])",
    Value::Int(0)
)]
// **Same-domain arms**: two legs, but the sum collapses to *one* candidate, so this sits
// between the single-`box` shape and the two-candidate one — a filter that must reach two
// legs through a sum that no longer distinguishes them. Both predicates discriminate; an
// unfiltered answer would be 6 and 7.
#[case(
    r"
c: Bool = True
sum([y for y in (box([1, 5]) if c else box([3, 4])) if y > 2])",
    Value::Int(5)
)]
#[case(
    r"
c: Bool = False
sum([y for y in (box([1, 5]) if c else box([3, 4])) if y > 3])",
    Value::Int(4)
)]
// **Two consumers, each with its own conditional.** A restriction is discharged into the
// arms, so arms cannot be shared between consumers that restrict differently — spelled
// inline, each consumer has its own `Case` and there is nothing to share. These are the
// controls for the let-bound pair below, which is the same program with one binding.
#[case(
    r"
c: Bool = False
sum([y for y in (box([1, 2]) if c else box([1, 2, 3])) if y > 1]) + sum([z for z in (box([1, 2]) if c else box([1, 2, 3])) if z > 2])",
    Value::Int(8)
)]
// ...including one consumer that restricts nothing, which owes the arms *no* gate.
#[case(
    r"
c: Bool = False
sum([y for y in (box([1, 2]) if c else box([1, 2, 3]))]) + sum([z for z in (box([1, 2]) if c else box([1, 2, 3])) if z > 1])",
    Value::Int(11)
)]
// **Let-bound**, the same three programs with the conditional shared through a binding.
// The legs carry the consumer's filter, so a shared conditional is inlined at each consumer
// before realization — which is also what puts the `Case` back below the site that restricts
// it, where the binding had placed it above.
#[case(
    r"
c: Bool = False
x = box([1, 2]) if c else box([1, 2, 3])
sum([y for y in x if y > 1])",
    Value::Int(5)
)]
#[case(
    r"
c: Bool = False
x = box([1, 2]) if c else box([1, 2, 3])
sum([y for y in x if y > 1]) + sum([z for z in x if z > 2])",
    Value::Int(8)
)]
#[case(
    r"
c: Bool = False
x = box([1, 2]) if c else box([1, 2, 3])
sum([y for y in x]) + sum([z for z in x if z > 1])",
    Value::Int(11)
)]
fn a_filter_over_a_conditional_source_is_applied(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional *between* two standalone comprehensions
// (`([x for x in xs]) if c else ([y for y in ys])`). This is the case
// kind inference unblocks: a comprehension used as a
// value is a lambda whose kind var resolves to `Data` from its collection domain, so
// the two `Case` arms `sigma_join` into the Σ instead of colliding as
// compute meets. (`sum` consumes the Σ via `Σ <: Fun`.)
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
c: Bool = True
sum(box([x for x in [1, 2]]) if c else box([y for y in [1, 2, 3]]))",
    Value::Int(3)
)]
#[case(
    r"
c: Bool = False
sum(box([x for x in [1, 2]]) if c else box([y for y in [1, 2, 3]]))",
    Value::Int(6)
)]
#[case(
    r"
c: Bool = True
sum(box([x * 10 for x in [1, 2]]) if c else box([y for y in [1, 2, 3]]))",
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
/// A `box`ed conditional collection, end to end.
///
/// Two arms only: a three-arm `elif` chain currently fails in *inference*, on literal
/// singleton element types rather than on anything about sums
/// (`expected 2, found {2 | __elem == 3}`), so it is a separate gap and not covered here. Both arms enter the sum explicitly, the
/// join keeps both candidates, and `planning` realizes the Σ as the gated union — which
/// happens after inference, so no subtyping rule ever relates the two.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "c: Bool = True\nsum(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(3)
)]
#[case(
    "c: Bool = False\nsum(box([1, 2]) if c else box([1, 2, 3]))",
    Value::Int(6)
)]
#[case(
    "n: Int = 2\nsum(box([1]) if n == 1 else box([2]) if n == 2 else box([3, 3]))",
    Value::Int(2)
)]
fn test_boxed_conditional_collection(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// **Two witnesses live at once, end to end.** A comprehension over two conditional
/// collections opens both sums while typing one body. It types correctly and keeps the
/// witnesses apart (`two_conditional_sources_keep_their_witnesses_apart`, in
/// `tests/type_check.rs`); what it does not yet do is compile.
///
/// Two generators nest two sums — `Σ σ₄ ∈ 𝐾₄. Σ σ₇ ∈ 𝐾₇. ((σ₄, σ₇) ⤇ Int)` — and what
/// each blocker has in common is that **a nested sum has no settled rule**, not that a case
/// is missing. Measured in order, each one reached by getting past the last:
///
/// 1. `SigmaType::body_residue` hits its `unreachable!`: the body is a `Sigma`, and the
///    witness-independent residue of a sum inside a sum is not defined. Returning the inner
///    sum's residue gets past it and is probably right, but it is a *guess* until width says
///    what a nested sum's search covers.
/// 2. Consumption (`Σ <: Fun`) then places a range demand from **one** witness on the
///    consumer's whole domain, which here is the tuple `(σ₄, σ₇)`. Two witnesses index two
///    tuple components; one demand cannot say that.
/// 3. `Proj` on that tuple fails with `expected [0, 1], found σ` — projecting a component
///    resolves against a concrete candidate where a witness stands.
///
/// The question under all three is whether nesting means one sum over the **product** kind
/// (candidates `𝐾₄ × 𝐾₇`, one witness, everything downstream unchanged, n×m candidates) or
/// two binders peeled in turn (no explosion, but width, consumption and projection each
/// need a rule for *which* witness a position names). That is a type-system decision, so it
/// is not made here.
///
/// It is **not** the copair/disjoint-join split, which this test was previously ignored
/// for: that diagnosis predates the witness-identity work and does not survive it. The
/// failure has moved four times under measurement (a sum in a domain position reaching
/// `extent_of`, then a free witness on the index, then an unresolved variable, then
/// `[0, 1] <: σ` at `constrain_go`'s witness arm), so the reasons above are what a run says
/// today and nothing more — re-measure before trusting them.
#[rstest]
#[timeout(Duration::from_secs(30))]
#[ignore = "two generators nest two sums, and a nested sum has no width, consumption or \
            projection rule; measured 2026-08-11"]
fn two_conditional_sources_compile() {
    check_scalar(
        r"
c: Bool = True
d: Bool = False
sum([x + y for x in (box([1, 2]) if c else box([1, 2, 3])) for y in (box([10, 20]) if d else box([10, 20, 30]))])",
        Value::Int(3 + 60 + 3 * 60 - 60),
    );
}

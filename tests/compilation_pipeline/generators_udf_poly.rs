//! User-defined functions (`def` and `lambda`), generator functions, and
//! polymorphic UDF chains (monomorphization through wrappers, diamonds, and
//! triple chains), plus nested generator functions.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Regular function definitions — def f(x): body; f(arg)
// ---------------------------------------------------------------------------

// Scalar `def` calls (single- and multi-arg) work end-to-end via the
// uncurried definition/call shape and the inline pass for scalar UDFs.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("def inc(x):\n    x + 1\ninc(4)", Value::Int(5))]
#[case("def add(x, y):\n    x + y\nadd(3, 4)", Value::Int(7))]
fn test_function_def_scalar(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A polymorphic UDF applied at two *distinct* argument types in the same
// program, end-to-end. `x == x` is `∀α. α → Bool`, so the two calls have
// incompatible domains (Int vs String) — under a monomorphic `let` they would
// collide (`IncompatibleBounds`). Let-generalization + use-site monomorphization
// must specialize each call independently. `x == x` is deliberately *not* the
// identity (which lowering β-reduces away before inference), so a real `let f`
// survives to the solver and exercises the splice path. Both results are `Bool`,
// so they combine to a checkable scalar.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_function_def_polymorphic_used_at_two_types() {
    let code = "f = lambda x: x == x\nf(1) and f(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// ---------------------------------------------------------------------------
// Generator functions — def f(xs): for x in xs: yield expr
// ---------------------------------------------------------------------------

// End-to-end tests for calling list-producing user-defined functions (generator
// `def`s). Lowering is covered by unit tests in `src/ccl/lower.rs`; these check
// that inference, pre-lambda-elim inline
// (`ccl::inline::inline_non_iterable_lambdas`), lambda elimination, and operator
// conversion all compose correctly.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Simple map: yield x * 2
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\ndoubles([1, 2, 3])",
    make_int_list(&[2, 4, 6])
)]
// Same generator, but its result is *bound* to a variable before use
// (`y = doubles(...)` then `y`) rather than called inline. `inline` expands
// the call to `let y = (let __result = defer in … __result) in y`, and
// `channelize::try_lift_defer` lifts the inner result-defer scope out so the
// feeds land on `y`. The inline form above never reaches that path, so this
// case is its regression guard.
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\ny = doubles([1, 2, 3])\ny",
    make_int_list(&[2, 4, 6])
)]
// A UDF that binds another generator's result to a local and returns it
// (`def wrap(xs): z = doubles(xs); z`). After inlining, `y = wrap(...)`
// becomes `let y = (let z = <doubles inlined> in z) in y` — the inner
// bound-expr contains a defer but is not itself `Defer`, so
// `channelize`'s defer-returning-let *collapse* fires (surfacing the inner
// defer for a subsequent `try_lift_defer`). Regression guard for that path.
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\ndef wrap(xs):\n    z = doubles(xs)\n    z\ny = wrap([1, 2, 3])\ny",
    make_int_list(&[2, 4, 6])
)]
// Map with captured parameter
#[case(
    "def add_to(xs, n):\n    for x in xs:\n        yield x + n\nadd_to([1, 2, 3], 10)",
    make_int_list(&[11, 12, 13])
)]
// Filter via if-guard. The generator body's filter-feed lowers to a
// refined-source channel whose domain carries the bare element predicate
// `__elem ▷ source ▷ (λ x → x > n)` (the same form a filtered comprehension
// builds), so planning reifies it into an `IterateExtent` + `Restrict` and
// only guard-passing elements are yielded.
#[case(
    r#"
def positives(xs):
    n = 0
    for x in xs:
        if x > n:
            yield x
positives([-1, 2, -3, 4])"#,
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1, 3]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 4]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_generator_function(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Brainstorm §4b — generator with loop-carried mutable state.  The body
// mutates a pre-loop variable (`total += item`) and yields its updated
// value each iteration, producing a running-total stream.  This routes
// through the guarded `LetRec` the unified phase emits (recognized onto the
// `Transact` carrier, then `Recurse`), with the yield-defer hoisted out as a
// `to_*` feed field on the history record.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r#"
def running_totals(items):
    total := 0
    for item in items:
        total += item
        yield total
running_totals([1, 2, 3, 4])"#,
    make_int_list(&[1, 3, 6, 10])
)]
fn test_generator_with_loop_carried_mutation(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Generator function composed with aggregate: sum(doubles([1, 2, 3])) == 12
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\nsum(doubles([1, 2, 3]))",
    Value::Int(12)
)]
fn test_generator_function_with_aggregate(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// F2 (PR #227) — a generator UDF that is *polymorphic over its element type*
// (`yield 1` ignores the element, so `ones : ∀α. [α] ⇒ [Int]`), applied at two
// *distinct* element types in one program. The old generator carve-out kept
// such UDFs monomorphic and shared, so the `Int`-list and `String`-list calls
// collided into one parameter (`IncompatibleBounds`) and the program failed to
// compile. Per-type monomorphization specializes the generator once per element
// type — and because its domain is iterable, `inline` leaves each specialization
// *cached* rather than duplicating it — so both calls compile and run. Summing
// the two `[Int]` results (3 ones + 2 ones) gives a single checkable scalar.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_generator_polymorphic_over_element_type() {
    let code = "def ones(xs):\n    for x in xs:\n        yield 1\nsum(ones([1, 2, 3])) + sum(ones([\"a\", \"b\"]))";
    check_scalar(code, Value::Int(5));
}

// ---------------------------------------------------------------------------
// Chained monomorphization — a polymorphic UDF used only inside another
// polymorphic UDF's definition. Such a use becomes concrete only inside the
// wrapper's per-type clones, so it specializes during each clone's re-entrant
// coalesce, against the inner binding's still-in-scope frame. The wrapper
// bodies below are structural (a real call, not a bare variable), so no
// pre-inference beta-reduction rescues the chain.
// ---------------------------------------------------------------------------

// Scalar poly-calls-poly at two concrete use types — the chained variant of
// `test_function_def_polymorphic_used_at_two_types`.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_calls_poly_at_two_types() {
    let code = "f = lambda x: x == x\ng = lambda y: f(y)\ng(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// List-producing body chained through a poly wrapper, single concrete use
// type. The lone `f` use sits inside `g`'s (generalized) definition, so it is
// only ever reached through `g`'s clone — one concrete use type suffices to
// exercise the chain.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_calls_poly_list_body() {
    let code = "f = lambda x: [x, x]\ng = lambda y: f(y)\nsum(g(5))";
    check_scalar(code, Value::Int(10));
}

// Collection (comprehension) UDF chained through a poly wrapper at one
// element type.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_collection_udf_through_poly_wrapper() {
    let code = "f = lambda xs: [x for x in xs]\ng = lambda ys: f(ys)\ng([1, 2, 3])";
    check_tile(code, make_int_list(&[1, 2, 3]));
}

// Collection UDF chained through a poly wrapper at two element types — the
// `inline`-keeps-shared path: one cached specialization per element type.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_collection_udf_through_poly_wrapper_two_element_types() {
    let code = "f = lambda xs: [1 for x in xs]\ng = lambda ys: f(ys)\nsum(g([1, 2, 3])) + sum(g([\"a\", \"b\"]))";
    check_scalar(code, Value::Int(5));
}

// Generator `def` chained through a poly wrapper at two element types — the
// chained variant of `test_generator_polymorphic_over_element_type`.
//
// **Currently ignored** — pre-existing `channelize` bug, independent of
// monomorphization: a yield-based generator `def` *invoked inside a lambda
// body* desugars to `λ ys → λ __floated___floated_chain_0 → ()` — the
// generator's body is lost and the wrapper returns unit, so inference rejects
// `sum(wrap(...))` with "Type mismatch for Aggregate: expected (), found
// Int". The defer/feed plumbing assumes a generator call's result is
// consumed at the statement level, not captured under a binder. Tracked in
// the `defer-generator-call-inside-lambda` vault issue.
#[ignore = "channelize drops a generator def's body when the call sits inside a lambda"]
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_generator_def_through_poly_wrapper_two_element_types() {
    let code = "def ones(xs):\n    for x in xs:\n        yield 1\nwrap = lambda ys: ones(ys)\nsum(wrap([1, 2, 3])) + sum(wrap([\"a\", \"b\"]))";
    check_scalar(code, Value::Int(5));
}

// Triple chain (poly → poly → poly) with a concrete leaf use.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_triple_poly_chain_collection() {
    let code = "f = lambda xs: [x for x in xs]\ng = lambda ys: f(ys)\nh = lambda zs: g(zs)\nsum(h([1, 2, 3]))";
    check_scalar(code, Value::Int(6));
}

// Triple chain at two concrete leaf types: every layer specializes twice.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_triple_poly_chain_at_two_types() {
    let code = "f = lambda x: x == x\ng = lambda y: f(y)\nh = lambda z: g(z)\nh(1) and h(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// Diamond: two poly wrappers over one poly base, each used at a different
// type. The base's specializations are demanded from two *distinct* freshly
// minted wrapper clones, sharing one memo.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_diamond() {
    let code = "f = lambda x: x == x\ng = lambda y: f(y)\nh = lambda z: f(z)\ng(1) and h(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// The inner UDF used both directly (concrete in the main walk) and through a
// poly wrapper (concrete only inside the wrapper's clone).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_used_directly_and_through_wrapper() {
    let code = "f = lambda x: x == x\ng = lambda y: f(y)\nf(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// N outer × M inner: the wrapper uses the inner UDF twice (param-dependent
// and concrete), and is itself used at two types. The four interior `f` uses
// collapse onto two specializations (Int, String).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_fanout_inside_wrapper() {
    let code = "f = lambda x: x == x\ng = lambda y: f(y) and f(\"z\")\ng(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// Chained variant of `test_udf_containing_filter`: the inner generalized
// definition anchors a cast-target refinement, so the wrapper-driven
// specialization exercises predicate-cell de-aliasing through *two* layers of
// cloning (the `CellRemap` retirement chains).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_filter_udf_through_poly_wrapper() {
    let code = "f = lambda xs: [x for x in xs if x > 1]\ng = lambda ys: f(ys)\ng([1, 2, 3])";
    check_tile(
        code,
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// Chained variant of `test_udf_used_inside_filter_predicate`: the generalized
// predicate UDF's only use lives inside a refinement predicate anchored in
// *another* generalized definition — the coalesce walk reaches it through the
// wrapper clone's cast-target predicate.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_predicate_udf_used_inside_poly_wrapper_filter() {
    let code = "p = lambda x: x > 1\ng = lambda ys: [y for y in ys if p(y)]\ng([1, 2, 3])";
    check_tile(
        code,
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// A multi-arg poly wrapper around a collection UDF (uncurrying composes with
// chaining).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_chain_with_extra_param() {
    let code = "f = lambda xs: [x for x in xs]\ng = lambda ys, n: sum(f(ys)) + n\ng([1, 2], 10)";
    check_scalar(code, Value::Int(13));
}

// A generalized definition the program never exercises at a concrete type is
// an *ambiguous program*: residual inference variables reach the post-infer
// typecheck wall, which must surface a rendered diagnostic — not panic.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_unexercised_generic_definition_is_an_error_not_a_panic() {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, "f = lambda x: [x, x]\nf", consumer);
    assert!(
        result.is_err(),
        "ambiguous (never-exercised) generic must fail with a diagnostic"
    );
}

// Nested generator calls: one generator feeds into another.
// Exercises the ANF lift for defer-returning Compose sources introduced when
// `For` was replaced with `Compose+Lambda`.
#[rstest]
#[timeout(Duration::from_secs(10))]
// doubles(add_one([1,2,3])) == [4, 6, 8]
#[case(
    r#"def add_one(xs):
    for x in xs:
        yield x + 1
def doubles(xs):
    for x in xs:
        yield x * 2
doubles(add_one([1, 2, 3]))"#,
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 6, 8]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
// sum(doubles(add_one([1,2,3]))) == 18
#[case(
    r#"def add_one(xs):
    for x in xs:
        yield x + 1
def doubles(xs):
    for x in xs:
        yield x * 2
sum(doubles(add_one([1, 2, 3])))"#,
    Tile::Scalar(ColumnValue::Ints(vec![18]))
)]
fn test_nested_generator_functions(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

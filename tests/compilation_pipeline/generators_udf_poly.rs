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
    let code = "f = \\x -> x == x\nf(1) and f(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// Two calls at the same *base* types but different argument literals. Every
// literal carries its own singleton, so the two uses instantiate the UDF at
// genuinely different refined types and must not share a specialization — the
// clone's interior is resolved against the argument that pinned it, so a shared
// clone would carry one call's argument type at the other's call site.
//
// These are regression guards for a specialization memo keyed on a *resolved
// type*: because a domain resolves from its upper bounds, an argument's refinement
// (a lower bound) was invisible in the key exactly where the definition body
// supplied something concrete, so a difference confined to such a position keyed
// equal. `\a, b -> a + b` at `(1, 2)` and `(1, 5)` both keyed on
// `((1, Int) ⇒ Int)`, shared a clone typing `.1` as `2`, and the post-inline
// consistency wall then panicked ("Type mismatch for Apply: expected 5, found
// 2"). `SpecKey` reads both bound directions, so the two key apart.
//
// The controls matter as much as the cases: a difference in the *first* argument
// always keyed apart (its refinement reached the key), and two identical calls must
// still **share** — the fix must not degrade into cloning per call site.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Differs only in the second argument — the position the old key could not see.
#[case("h = \\a, b -> a + b\nh(1, 2) + h(1, 5)", Value::Int(9))]
// Differs in the first argument: keyed apart even before the fix.
#[case("h = \\a, b -> a + b\nh(2, 1) + h(5, 1)", Value::Int(9))]
// Three call sites, two of them differing only in an invisible position.
#[case("h = \\a, b -> a + b\nh(1, 2) + h(1, 5) + h(1, 9)", Value::Int(19))]
// Identical calls: one specialization, shared.
#[case("h = \\a, b -> a + b\nh(1, 2) + h(1, 2)", Value::Int(6))]
// A single-argument UDF, where the shared clone's body carried the first call's
// singleton on its parameter reference (`λ x : Int → x:<1> + 1`). That happened
// to compile to the right answer, so this case pins the *result* while the
// unit-level `SpecKey` tests pin the keying.
#[case("f = \\x -> x + 1\nf(1) + f(2)", Value::Int(5))]
fn test_polymorphic_udf_calls_differing_only_in_a_literal(
    #[case] code: &str,
    #[case] expected: Value,
) {
    check_scalar(code, expected);
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
// A list-returning UDF over a *literal* argument, with a body that imposes
// nothing on that parameter (`yield k`, not `yield x + k`). The UDF is
// therefore generalized in `k`, so use-site monomorphization specializes its
// domain to the type actually flowing in — a literal's singleton,
// `{Int | __elem == 10}` — and coalesce's `refresh_lambda_param_slot` copies
// that refinement into the outer lambda's `param.ty`. This is what makes the
// refined-outer-parameter branch of `ccl::inline::inline_and_beta_reduce`
// (and its hard, release-mode `assert!`) live on an ordinary call path: the
// assert passes only because the argument's own type carries the very
// refinement the parameter demands, so beta-reduction *discharges* the
// precondition instead of dropping it. Contrast `add_to` above, where
// `x + n` forces `n` to plain `Int` and the parameter is unrefined.
#[case(
    "def rep(k):\n    for x in [1, 2, 3]:\n        yield k\nrep(10)",
    make_int_list(&[10, 10, 10])
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

// Mutability design notes, §4b — generator with loop-carried mutable state.  The body
// mutates a pre-loop variable (`total += item`) and yields its updated
// value each iteration, producing a running-total stream.  This routes
// through the causal `LetRec` the unified phase emits (recognized onto the
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
    let code = "f = \\x -> x == x\ng = \\y -> f(y)\ng(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// List-producing body chained through a poly wrapper, single concrete use
// type. The lone `f` use sits inside `g`'s (generalized) definition, so it is
// only ever reached through `g`'s clone — one concrete use type suffices to
// exercise the chain.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_calls_poly_list_body() {
    let code = "f = \\x -> [x, x]\ng = \\y -> f(y)\nsum(g(5))";
    check_scalar(code, Value::Int(10));
}

// Collection (comprehension) UDF chained through a poly wrapper at one
// element type.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_collection_udf_through_poly_wrapper() {
    let code = "f = \\xs -> [x for x in xs]\ng = \\ys -> f(ys)\ng([1, 2, 3])";
    check_tile(code, make_int_list(&[1, 2, 3]));
}

// Collection UDF chained through a poly wrapper at two element types — the
// `inline`-keeps-shared path: one cached specialization per element type.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_collection_udf_through_poly_wrapper_two_element_types() {
    let code = "f = \\xs -> [1 for x in xs]\ng = \\ys -> f(ys)\nsum(g([1, 2, 3])) + sum(g([\"a\", \"b\"]))";
    check_scalar(code, Value::Int(5));
}

// Generator `def` chained through a poly wrapper at two element types — the
// chained variant of `test_generator_polymorphic_over_element_type`.
//
// The generator call sits *inside a lambda body* rather than at the statement level, so
// the defer/feed plumbing has to carry the generator's body across a binder. `channelize`
// once dropped it there — the wrapper desugared to `λ ys → λ __floated___floated_chain_0 →
// ()`, returning unit, and inference rejected `sum(wrap(...))`.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_generator_def_through_poly_wrapper_two_element_types() {
    let code = "def ones(xs):\n    for x in xs:\n        yield 1\nwrap = \\ys -> ones(ys)\nsum(wrap([1, 2, 3])) + sum(wrap([\"a\", \"b\"]))";
    check_scalar(code, Value::Int(5));
}

// Triple chain (poly → poly → poly) with a concrete leaf use.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_triple_poly_chain_collection() {
    let code =
        "f = \\xs -> [x for x in xs]\ng = \\ys -> f(ys)\nh = \\zs -> g(zs)\nsum(h([1, 2, 3]))";
    check_scalar(code, Value::Int(6));
}

// Triple chain at two concrete leaf types: every layer specializes twice.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_triple_poly_chain_at_two_types() {
    let code = "f = \\x -> x == x\ng = \\y -> f(y)\nh = \\z -> g(z)\nh(1) and h(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// Diamond: two poly wrappers over one poly base, each used at a different
// type. The base's specializations are demanded from two *distinct* freshly
// minted wrapper clones, sharing one memo.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_diamond() {
    let code = "f = \\x -> x == x\ng = \\y -> f(y)\nh = \\z -> f(z)\ng(1) and h(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// The inner UDF used both directly (concrete in the main walk) and through a
// poly wrapper (concrete only inside the wrapper's clone).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_used_directly_and_through_wrapper() {
    let code = "f = \\x -> x == x\ng = \\y -> f(y)\nf(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// N outer × M inner: the wrapper uses the inner UDF twice (param-dependent
// and concrete), and is itself used at two types. The four interior `f` uses
// collapse onto two specializations (Int, String).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_poly_fanout_inside_wrapper() {
    let code = "f = \\x -> x == x\ng = \\y -> f(y) and f(\"z\")\ng(1) and g(\"foo\")";
    check_scalar(code, Value::Bool(true));
}

// Chained variant of `test_udf_containing_filter`: the inner generalized
// definition anchors a cast-target refinement, so the wrapper-driven
// specialization exercises predicate-cell de-aliasing through *two* layers of
// cloning (the `CellRemap` retirement chains).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_filter_udf_through_poly_wrapper() {
    let code = "f = \\xs -> [x for x in xs if x > 1]\ng = \\ys -> f(ys)\ng([1, 2, 3])";
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
    let code = "p = \\x -> x > 1\ng = \\ys -> [y for y in ys if p(y)]\ng([1, 2, 3])";
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
    let code = "f = \\xs -> [x for x in xs]\ng = \\ys, n -> sum(f(ys)) + n\ng([1, 2], 10)";
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
    let result = compile_program(&mut ctx, "f = \\x -> [x, x]\nf", consumer);
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

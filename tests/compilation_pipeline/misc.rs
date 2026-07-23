//! Miscellaneous: operator-graph fan-out absence, scalar UDFs via lambda
//! (inline pass), multi-arg UDFs, and dependent group-by lookups.

use std::time::Duration;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{Tile, Value};
use cambra::pretty_graph::pretty_tile_operator;
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Operator-graph shape: no spurious fan-outs for simple binops
// ---------------------------------------------------------------------------

// Test that we don't have splits in the operator graph for simple binops
#[rstest]
#[case("[1 + x + 1 for x in [1,2,3]]")]
#[case("[(x, x).0 + 2 for x in [1,2,3]]")]
#[case("[(x, 0) for x in [1,2,3]]")]
#[case("[x for x in [1,2,3] if x + 1 < 2]")]
#[case("1 + 2 + 3")]
fn test_no_fan_outs(#[case] code: &str) {
    let compiled = compile_program(&mut GlobalContext::default(), code, Box::new(|| {}))
        .unwrap_or_render("<test>", code);
    let op = &compiled.main().unwrap().op;
    let op_str = pretty_tile_operator(op.as_ref());
    assert!(!op_str.contains("FanOut#"), "found fan-out in {op_str}");
}
// ---------------------------------------------------------------------------
// User-defined functions (scalar UDFs via lambda)
//
// These tests validate the inline pass: scalar-typed `Let` bindings introduced
// by lambda elimination are substituted at their call sites before operator
// conversion, avoiding the "Attempted to iterate on infinite Extent" panic.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("inc = \\x -> x + 1\ninc(4)", Value::Int(5))]
#[case("double = \\x -> x * 2\ndouble(7)", Value::Int(14))]
#[case("neg = \\x -> -x\nneg(3)", Value::Int(-3))]
#[case("identity = \\x -> x\nidentity(42)", Value::Int(42))]
fn test_scalar_udf(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("is_pos = \\x -> x > 0\nis_pos(5)", Value::Bool(true))]
#[case("is_pos = \\x -> x > 0\nis_pos(-1)", Value::Bool(false))]
fn test_udf_bool_codomain(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// UDF called twice: body is duplicated at each call site (acceptable trade-off).
#[case("f = \\x -> x + 1\nf(3) + f(4)", Value::Int(9))]
fn test_udf_called_multiple_times(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
// Nested call: f(f(3)) → f(6) → 12
#[case("f = \\x -> x * 2\nf(f(3))", Value::Int(12))]
fn test_udf_nested_calls(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// Regression: collection and scalar lets should remain unaffected by the
// inlining pass.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("x = 4\nx + 1", Value::Int(5))]
fn test_scalar_let_unaffected(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("xs = [1, 2, 3]\n[x * 2 for x in xs]", make_int_list(&[2, 4, 6]))]
fn test_collection_let_unaffected(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Multi-arg UDFs: lowering uncurries syntactic multi-arg lambdas into a
// single tupled-domain function, and multi-arg calls into a single Apply on
// a tupled argument. This keeps `curry` out of the tree for the common case.
// The n-arm zip arm in operator_conversion dispatches between `ScalarFanIn`
// (scalar upstream) and `FanIn` (function upstream), so bodies with nested
// BinOps also compile cleanly under scalar call sites. Explicit currying
// (`\\x -> \\y -> ...` or explicit `curry(f)`) is still tracked as
// follow-up work.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("add = \\x, y -> x + y\nadd(3, 4)", Value::Int(7))]
#[case("combine = \\a, b -> a * b + 1\ncombine(3, 4)", Value::Int(13))]
#[case("add3 = \\x, y, z -> x + y + z\nadd3(1, 2, 3)", Value::Int(6))]
#[case("mix = \\x, y, z -> x * y - z\nmix(4, 5, 2)", Value::Int(18))]
fn test_multi_arg_udf(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A comprehension filter that references an enclosing multi-arg lambda's
// parameter lowers the filter into the comprehension's `Cast::target`
// predicate with that parameter free in it. The uniform substitution engine
// rewrites type-carried predicates along with the term spine, so uncurrying
// reaches the filter and the program compiles and runs (this used to be
// `substitute_param_in_body`'s fail-loud guard).
#[test]
fn test_multi_arg_param_in_filter_predicate() {
    let code = "data = [1, 2, 30]\n\
                pick = \\lo, hi -> sum([x for x in data if x >= lo])\n\
                pick(8, 0)";
    check_scalar(code, Value::Int(30));
}

// Dependent application end-to-end: a single-key group-by lookup `g(k)` filters
// the collection by the key-discharged partition predicate at the iteration
// boundary, exercising the dependent type through to runtime values.
//
// DEFERRED: `groupby` infers the honest keyed type `{K | __elem ▷ keydom#id} ⤇ group`
// (see `src/ccl/design/collections.md`, "`groupby` is a `Map`"), so a direct lookup
// `g(k)` at a plain key demands proving the key is in *that* key domain — the
// discharge described in `src/ccl/design/collections.md`, "Lookup: membership
// discharge", which will re-enable these as discharged / `Option` lookups. They
// passed before only because the old total-function type was too loose (any key
// admitted, absent → empty group).
#[rstest]
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(1))", Value::Int(2))] // {1,1}
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(2))", Value::Int(4))] // {2,2}
#[case("g = groupby([1,1,2,2,3], \\x -> x)\nsum(g(3))", Value::Int(3))] // {3}
#[case("g = groupby([1,2,3,4,5], \\x -> x // 2)\nsum(g(0))", Value::Int(1))] // {1}
#[case("g = groupby([1,2,3,4,5], \\x -> x // 2)\nsum(g(1))", Value::Int(5))] // {2,3}
#[case("g = groupby([1,2,3,4,5], \\x -> x // 2)\nsum(g(2))", Value::Int(9))] // {4,5}
#[ignore = "regression: a bare key cannot prove membership until the lookup discharge lands (see the comment above)"]
fn test_dependent_groupby_lookup(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

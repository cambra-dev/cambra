//! Miscellaneous: operator-graph fan-out absence, scalar UDFs via lambda
//! (inline pass), multi-arg UDFs, and dependent group-by lookups.

use std::time::Duration;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{Tile, Value};
use cambra::pretty_graph::pretty_tile_operator;
use indoc::indoc;
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

// ---------------------------------------------------------------------------
// `pass`
//
// A statement that contributes nothing (`docs/chl-spec.md`, "4.7 `pass`"). Each of the
// blocks below has its own statement grammar and its own answer for "no statement": a
// value block drops it and rejects it as the terminal, a loop body drops it and takes
// `unit` as the terminal, and a `with begin():` block drops it and leaves the block
// with no footprint for the transaction rule to reject.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Before a value block's terminal, and before a function body's.
#[case("pass\n1 + 1", Value::Int(2))]
#[case("def f(x):\n    pass\n    x + 1\nf(1)", Value::Int(2))]
// A loop body with no accumulator: as a `match` arm that does nothing, which is the
// case an `if` can express by omitting its `else` and a `match` cannot.
#[case(
    indoc! {r#"
        good = defer()
        for m in [`a(2), `b(3)]:
            match m:
                case `a(n):
                    good << n
                case `b(k):
                    pass
        sum(good)
    "#},
    Value::Int(2)
)]
// The same arm in a loop body that carries an accumulator, which is lowered by the
// other of the two loop-body grammars.
#[case(
    indoc! {r#"
        acc := 0
        for m in [`a(2), `b(3)]:
            match m:
                case `a(n):
                    acc += n
                case `b(k):
                    pass
        acc
    "#},
    Value::Int(2)
)]
// As a loop body's whole content: a loop that does nothing.
#[case("for i in [1, 2]:\n    pass\nsum([1, 2])", Value::Int(3))]
// Before an accumulator write, so the drop leaves the write as the body.
#[case(
    "acc := 0\nfor i in [1, 2]:\n    pass\n    acc += i\nacc",
    Value::Int(3)
)]
fn pass_contributes_no_statement(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A block whose value is used cannot end in `pass`, a function body included — the
// spec's own example of what is rejected.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("pass")]
#[case("def todo(x):\n    pass\ntodo(1)")]
#[case("x = 1\npass")]
fn pass_cannot_end_a_block_whose_value_is_used(#[case] code: &str) {
    check_compile_error(code, "`pass` cannot end a block whose value is used");
}

// A `with begin():` block of nothing but `pass` has no footprint, which the
// transaction rule reports rather than the statement grammar.
#[test]
fn a_transaction_of_nothing_but_pass_has_no_footprint() {
    check_compile_error(
        indoc! {r#"
            b: Mut(Int, Txn) := 0
            for i in [1, 2]:
                with begin():
                    pass
            await_final(b)
        "#},
        "must do something",
    );
}

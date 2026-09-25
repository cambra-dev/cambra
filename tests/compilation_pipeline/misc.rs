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
// These tests validate pre-lambda-elimination inlining of compute-function
// bindings at their call sites. Leaving a scalar-domain function as a value
// would require iteration over a non-enumerable extent during compilation.
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
// BinOps also compile cleanly under scalar call sites. Nested lambdas that
// leave an internal `curry` in the tree remain unsupported; see
// src/ccl/design/optimization.md "Limitations".
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
// A statement that contributes nothing (`docs/chl-spec.md`, "4.7 `pass`"). Every block
// walker drops it on entry (`contributing_stmts`), so it reaches no statement grammar at
// any position, and each block is left with the one question its own shape answers: what
// a block that contributes nothing is. A value block rejects it, a `for`-loop body is
// `unit`, and a `with begin():` block has no footprint for the transaction rule.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Before a value block's terminal, and before a function body's.
#[case(
    indoc! {r#"
        pass
        1 + 1
    "#},
    Value::Int(2)
)]
#[case(
    indoc! {r#"
        def f(x):
            pass
            x + 1
        f(1)
    "#},
    Value::Int(2)
)]
// A loop body with no accumulator: as a `match` arm that does nothing, which is the
// case an `if` can express by omitting its `else` and a `match` cannot. The feeding arm
// carries a trailing one, the position that takes the terminal away from the feed if a
// grammar splits its last statement off before dropping `pass`.
#[case(
    indoc! {r#"
        good = defer()
        for m in [`a(2), `b(3)]:
            match m:
                case `a(n):
                    good << n
                    pass
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
// As a loop body's whole content: the loop runs, and its body has no effect.
#[case(
    indoc! {r#"
        for i in [1, 2]:
            pass
        sum([1, 2])
    "#},
    Value::Int(3)
)]
// Before an accumulator write, so the drop leaves the write as the body.
#[case(
    indoc! {r#"
        acc := 0
        for i in [1, 2]:
            pass
            acc += i
        acc
    "#},
    Value::Int(3)
)]
// After a feed, so the drop leaves the feed as the body.
#[case(
    indoc! {r#"
        g = defer()
        for i in [1, 2]:
            g << i
            pass
        sum(g)
    "#},
    Value::Int(3)
)]
// Inside a `with begin():` block, as the arm of a `match` whose other arm writes.
#[case(
    indoc! {r#"
        b: Mut(Int, Txn) := 0
        for m in [`a(2), `b(3)]:
            with begin():
                match m:
                    case `a(n):
                        b := b + n
                    case `b(k):
                        pass
        await_final(b)
    "#},
    Value::Int(2)
)]
// And as the body of an `if` in one, beside a spine write that commits every iteration.
#[case(
    indoc! {r#"
        b: Mut(Int, Txn) := 0
        for i in [1, 2]:
            with begin():
                b := b + i
                if i > 1:
                    pass
        await_final(b)
    "#},
    Value::Int(3)
)]
fn pass_contributes_no_statement(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A block whose value is used needs a statement to be it, and a block of nothing but
// `pass` has none — the spec's own example of what is rejected, and a function body
// reaching the same rule.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("pass")]
#[case(
    indoc! {r#"
        def todo(x):
            pass
        todo(1)
    "#}
)]
fn a_block_of_nothing_but_pass_has_no_value(#[case] code: &str) {
    check_compile_error(code, "`pass` cannot be all of a block whose value is used");
}

// A trailing `pass` is dropped like any other, so the statement above it is the block's
// value and answers for itself. An assignment is not a value at that position, and the
// rejection names the assignment rather than the `pass` below it.
#[test]
fn a_trailing_pass_leaves_the_statement_above_it_as_the_value() {
    check_compile_error(
        indoc! {r#"
            x = 1
            pass
        "#},
        "last statement must be a bare expression",
    );
}

// A `with begin():` block of nothing but `pass` has no footprint, which the transaction
// rule reports rather than the statement grammar — as a loop body's transaction, and
// standing alone.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {r#"
        b: Mut(Int, Txn) := 0
        for i in [1, 2]:
            with begin():
                pass
        await_final(b)
    "#}
)]
#[case(
    indoc! {r#"
        b: Mut(Int, Txn) := 0
        with begin():
            pass
        await_final(b)
    "#}
)]
fn a_transaction_of_nothing_but_pass_has_no_footprint(#[case] code: &str) {
    check_compile_error(code, "must do something");
}

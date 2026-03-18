//! End-to-end pipeline tests: Python source → CCL lower → infer → compile → eval.
//!
//! Currently these exist as parity tests (Python → direct-lowering vs. CCL pipeline)
//! as we're still suporting parallel implementations. Eventually the direct lowering
//! will be removed, leaving only the full compilation stack:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates Lambda param_ty)
//!   → compile_ccl   (CCL Expr → dataflow operators)
//!   → subscribe()   (operator evaluation)
//! ```
//!
//! Every test case in this file runs through the **direct** lowering path
//! (`lower_let_stmt_block`).  Cases tagged [`Both`] additionally run through
//! the full CCL pipeline (Python → `ccl::lower` → `ccl::infer` → `compile_ccl`
//! → subscribe → get) and assert the same result.
//!
//! Cases tagged [`DirectOnly`] skip the pipeline assertion and include a comment
//! explaining which feature is missing.  Changing a tag from `DirectOnly` to
//! `Both` is the self-documenting way to mark a feature as pipeline-complete.
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use cambra::ccl::context::GlobalContext;
use cambra::ccl::infer::infer;
use cambra::ccl::lower::{lower_expr, lower_stmts};
use cambra::ccl::symbolic::symbolic;
use cambra::interpreter::compile_ccl::{compile, CompileContext};
use cambra::interpreter::{
    tuple_field, BaseType, ColumnValue, Consumer, Extent, FuncBinding, Guard, Scheduler, Value,
};
use cambra::lowering::{lower_let_stmt_block, LoweringContext};
use cambra::pretty_graph::pretty_operator;
use log::debug;
use rstest_log::rstest;
use rustpython_parser::{ast as pyast, parser};

// ---------------------------------------------------------------------------
// Pipeline flag
// ---------------------------------------------------------------------------

/// Whether the CCL pipeline path is exercised for this test case.
#[derive(Copy, Clone, Debug, PartialEq)]
enum Pipeline {
    /// Both the direct and CCL pipeline paths are asserted.
    Both,
    /// Only the direct path is asserted; pipeline support is pending.
    DirectOnly,
}
use Pipeline::{Both, DirectOnly};

// ---------------------------------------------------------------------------
// Helpers — direct path
// ---------------------------------------------------------------------------

/// Parse `code` as a Python module, lower via `lower_let_stmt_block`, subscribe,
/// and return the resulting [`ColumnValue`].
fn run_direct(code: &str) -> ColumnValue {
    let result =
        parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse Python module");
    let stmts = match result {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("expected Module, got {other:?}"),
    };
    let mut scheduler = Scheduler::new();
    let (mut op, scope) =
        lower_let_stmt_block(&mut LoweringContext::default(), &stmts, &mut scheduler)
            .expect("direct lowering failed");

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
    scheduler.check_for_notifications();
    assert!(*notified.borrow(), "expected notification (direct path)");
    producer.get().column_value
}

// ---------------------------------------------------------------------------
// Helpers — CCL pipeline path
// ---------------------------------------------------------------------------

/// Lower `code` through the CCL pipeline (parse → `ccl::lower` → `ccl::infer`
/// → `compile_ccl` → subscribe → get) and return the resulting [`ColumnValue`].
fn run_pipeline(code: &str) -> ColumnValue {
    let mut ctx = GlobalContext::default();
    let mut expr = if code.contains(';') || code.contains('=') {
        let result = parser::parse(code, parser::Mode::Module, "<test>")
            .expect("Failed to parse Python module");
        let stmts = match result {
            pyast::Mod::Module { body, .. } => body,
            other => panic!("expected Module, got {other:?}"),
        };
        lower_stmts(&stmts, ctx.lowering_ctx()).expect("ccl lowering failed")
    } else {
        let result = parser::parse(code, parser::Mode::Expression, "<test>")
            .expect("Failed to parse Python expression");
        let ast_expr = match result {
            pyast::Mod::Expression { body } => *body,
            other => panic!("expected Expression, got {other:?}"),
        };
        lower_expr(&ast_expr, ctx.lowering_ctx()).expect("ccl lowering failed")
    };

    debug!("Lowered:\n{}", symbolic(&expr));

    let ictx = ctx.inference_ctx();
    infer(&mut expr, ictx).expect("type inference failed");
    cambra::ccl::unify::resolve(&mut expr, &mut ictx.table);

    debug!("Inferred:\n{}", symbolic(&expr));

    let mut scheduler = Scheduler::new();
    let mut op =
        compile(&expr, &mut CompileContext::new(), &mut scheduler).expect("compile failed");

    debug!("Operators:\n{}", pretty_operator(op.as_ref()));

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut producer = op.subscribe(Guard::universal(), consumer, None, &mut scheduler);
    scheduler.check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
    producer.get().column_value
}

// ---------------------------------------------------------------------------
// Parity assertion helpers
// ---------------------------------------------------------------------------

/// Assert `code` produces `expected` via the direct path; additionally assert
/// the pipeline path if `pipeline == Both`.
fn parity(code: &str, expected: ColumnValue, pipeline: Pipeline) {
    assert_eq!(run_direct(code), expected, "direct path");
    if pipeline == Both {
        assert_eq!(run_pipeline(code), expected, "pipeline path");
    }
}

/// Scalar variant of [`parity`]: unwraps the result via [`ColumnValue::as_single`]
/// before comparing.
fn parity_scalar(code: &str, expected: Value, pipeline: Pipeline) {
    let direct = run_direct(code);
    assert_eq!(
        direct.as_single().unwrap(),
        expected,
        "direct path (scalar)"
    );
    if pipeline == Both {
        let pipe = run_pipeline(code);
        assert_eq!(
            pipe.as_single().unwrap(),
            expected,
            "pipeline path (scalar)"
        );
    }
}

// ---------------------------------------------------------------------------
// Value constructors
// ---------------------------------------------------------------------------

fn make_int_list(v: &[i64]) -> ColumnValue {
    ColumnValue::function_bindings(
        ColumnValue::UInts((0..v.len()).collect()),
        ColumnValue::Ints(v.into()),
    )
}

fn make_tuple(v: &[Value]) -> Value {
    let mut map = HashMap::new();
    for (i, elem) in v.iter().enumerate() {
        map.insert(tuple_field(i), elem.clone());
    }
    Value::Record(map)
}

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

#[rstest]
#[case("2", Value::Int(2))]
#[case(r#""hello""#, Value::String("hello".to_string()))]
#[case("True", Value::Bool(true))]
#[case("[]", Value::Function(vec![]))]
#[case("[1, 2]", Value::Function(vec![
    FuncBinding { input: Value::Int(0), output: Value::Int(1) },
    FuncBinding { input: Value::Int(1), output: Value::Int(2) },
]))]
fn test_literals(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[case("2 + 3", Value::Int(5))]
#[case("4 * 5", Value::Int(20))]
#[case("4 - 5", Value::Int(-1))]
#[case("1 + 2 - 3 * 4", Value::Int(-9))]
#[case("1 + 2 * 3 - 4", Value::Int(3))]
#[case("1 + 2 * (3 - 4)", Value::Int(-1))]
#[case("7 // 2", Value::Int(3))]
fn test_arithmetic(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Comparisons
// ---------------------------------------------------------------------------
//
// TODO: `ccl::lower` does not yet support `Compare` expressions.

#[rstest]
#[case("1 == 1", Value::Bool(true))]
#[case("'a' == 'b'", Value::Bool(false))]
#[case("1 != 1", Value::Bool(false))]
#[case("'a' != 'b'", Value::Bool(true))]
#[case("2 > 1", Value::Bool(true))]
#[case("'a' < 'b'", Value::Bool(true))]
#[case("True != False", Value::Bool(true))]
#[case("True == True", Value::Bool(true))]
fn test_compare(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, DirectOnly);
}

// ---------------------------------------------------------------------------
// Boolean operations
// ---------------------------------------------------------------------------
//
// TODO: `ccl::lower` does not yet support bitwise-as-boolean ops or `BoolOp`.

#[rstest]
#[case("True & True", Value::Bool(true))]
#[case("True | False", Value::Bool(true))]
#[case("True ^ True", Value::Bool(false))]
#[case("True and False", Value::Bool(false))]
#[case("True or False", Value::Bool(true))]
fn test_bool_ops(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Let bindings
// ---------------------------------------------------------------------------
//
#[rstest]
#[case("x = 2; x", Value::Int(2))]
#[case("x = 2; y = x; y", Value::Int(2))]
#[case("x = 2; y = x; y + x + 1", Value::Int(5))]
fn test_let_bindings(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, Both);
}

// ---------------------------------------------------------------------------
// More Let bindings
// ---------------------------------------------------------------------------
#[rstest]
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
#[ignore = "need first class functions for this let"]
fn test_let_nonscalar(#[case] code: &str, #[case] expected: ColumnValue) {
    parity(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Tuples / record fields
// ---------------------------------------------------------------------------
#[rstest]
#[case(
    "('a', 1)",
    make_tuple(&[Value::String("a".to_string()), Value::Int(1)])
)]
#[case("('a', 1)[0]", Value::String("a".to_string()))]
#[case("x = ('a', 1); x[0]", Value::String("a".to_string()))]
fn test_tuples(#[case] code: &str, #[case] expected: Value) {
    parity_scalar(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Basic list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[case("[x for x in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[42 for x in [10, 20]]", make_int_list(&[42, 42]))]
#[case("[y for y in [x for x in [10, 20]]]", make_int_list(&[10, 20]))]
#[case("[x + 2 for x in [10, 20]]", make_int_list(&[12, 22]))]
fn test_comprehensions(#[case] code: &str, #[case] expected: ColumnValue) {
    parity(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Comprehensions with let capture
// ---------------------------------------------------------------------------
//
#[rstest]
#[case("y = 5; [x + y for x in [10, 20]]", make_int_list(&[15, 25]))]
fn test_comprehensions_let_capture(#[case] code: &str, #[case] expected: ColumnValue) {
    parity(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Comprehensions with tuple body
// ---------------------------------------------------------------------------

#[rstest]
#[case("[(y, y)[1] for y in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[y[0] for y in [(10, 'a'), (20, 'b')]]", make_int_list(&[10, 20]))]
#[case(
    "[(y, 100) for y in [(10, 'a'), (20, 'b')]]",
    ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts(vec![0, 1])),
        outputs: Box::new(ColumnValue::Records(HashMap::from([
            (
                String::from("_0"),
                ColumnValue::Records(HashMap::from([
                    (String::from("_0"), ColumnValue::Ints(vec![10, 20])),
                    (
                        String::from("_1"),
                        ColumnValue::Strings(vec![
                            String::from("a"),
                            String::from("b"),
                        ]),
                    ),
                ])),
            ),
            (String::from("_1"), ColumnValue::Ints(vec![100, 100])),
        ]))),
    }
)]
fn test_comprehensions_tuple_body(#[case] code: &str, #[case] expected: ColumnValue) {
    parity(code, expected, Both);
}

// ---------------------------------------------------------------------------
// Filtered comprehensions
// ---------------------------------------------------------------------------
//
// TODO: `ccl::lower` does not yet support `if` clauses in comprehensions.

#[rstest]
#[case("[x for x in [1, 2, 3] if x < 0]", make_int_list(&[]))]
#[case("[x for x in [1, 2, 3] if x > 0]", make_int_list(&[1, 2, 3]))]
#[case("[x for x in [1, 2, 3] if x > 10]", make_int_list(&[]))]
#[case(
    "[x for x in [1, 2, 3] if x == 2]",
    ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts(vec![1])),
        outputs: Box::new(ColumnValue::Ints(vec![2])),
    }
)]
#[case(
    "[x for x in [1, 2, 3, 4, 5] if x > 1 if x < 5]",
    ColumnValue::FunctionBindings {
        inputs: Box::new(ColumnValue::UInts(vec![1, 2, 3])),
        outputs: Box::new(ColumnValue::Ints(vec![2, 3, 4])),
    }
)]
fn test_comprehensions_filtered(#[case] code: &str, #[case] expected: ColumnValue) {
    parity(code, expected, DirectOnly);
}

// ---------------------------------------------------------------------------
// Multi-generator comprehensions / joins
// ---------------------------------------------------------------------------
//
// TODO: `ccl::lower` does not yet support multiple generators.
//
// The join tests check only the `outputs` of the resulting `FunctionBindings`
// because the input key domain (cross-product indices) is an implementation
// detail.

#[rstest]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]",
    ColumnValue::strings(&["ac", "ad", "ae", "bc", "bd", "be"])
)]
#[case(
    "[x + '_' for x in ['a', 'b'] for y in [True, False]]",
    ColumnValue::strings(&["a_", "a_", "b_", "b_"])
)]
#[case(
    "[x + z + y for x in ['a', 'b'] for y in ['c', 'd'] for z in ['e', 'f']]",
    ColumnValue::strings(&["aec", "afc", "aed", "afd", "bec", "bfc", "bed", "bfd"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'e'] if x == y]",
    ColumnValue::strings(&["bb", "cc"])
)]
// Loop join with non-equality predicate involving both generators
#[case(
    "[x + y for x in [1, 1] for y in [2, 2, 3] if x + 1 == y]",
    ColumnValue::Ints(vec![3, 3, 3, 3])
)]
#[case(
    "[x for x in [y for y in ['a', 'b', 'c', 'd'] if y != 'b'] if x < 'c']",
    ColumnValue::strings(&["a"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'd'] if x < y]",
    ColumnValue::strings(&["ab", "ac", "ad", "bc", "bd", "cd"])
)]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd'] if x == y]",
    ColumnValue::strings(&[])
)]
#[case(
    "[x + y + z for x in ['a', 'b'] for y in ['b', 'c'] for z in ['b', 'c'] if x != y if y == z]",
    ColumnValue::strings(&["abb", "acc", "bcc"])
)]
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['a', 'b', 'c'] if x == y if x < 'c']",
    ColumnValue::strings(&["aa", "bb"])
)]
#[case(
    "y = 'b'; [x for x in ['a', 'b', 'c'] for z in ['b', 'c'] if x == y]",
    ColumnValue::strings(&["b", "b"])
)]
#[case(
    "[a + b
        for a in [c + d for c in ['a'] for d in ['b', 'c'] if c < d]
        for b in [e + f for e in ['d', 'e'] for f in ['f'] if e < f]
    if a != b]",
    ColumnValue::strings(&["abdf", "abef", "acdf", "acef"])
)]
fn test_joins(#[case] code: &str, #[case] expected: ColumnValue) {
    let results = &[run_direct(code), run_pipeline(code)];
    for result in results.iter() {
        match result {
            ColumnValue::FunctionBindings { outputs, .. } => {
                assert_eq!(**outputs, expected);
            }
            other => panic!("expected FunctionBindings, got: {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Data-source injection tests
// TODO: direct path only — CCL pipeline needs design work
//
// These tests inject a `TestDataSource` or `StdinDataSource` into the lowering
// context, which has no CCL pipeline equivalent yet.  Tracked as `DirectOnly`
// until a source-injection mechanism is designed for the pipeline.
// ---------------------------------------------------------------------------

#[rstest]
#[case("[x for x in testsource1()]")]
#[case("[x + '' for x in testsource1()]")]
#[case("['' + x for x in testsource1()]")]
#[case("y = ''; [y + x for x in testsource1()]")]
#[case("[(x, 0)[0] for x in testsource1()]")]
#[case("[(x, 0)[0] for x in testsource1() if True]")]
fn test_test_source(#[case] code: &str) {
    let mut ctx = LoweringContext::default();
    let data_source = ctx.inject_test_source("testsource1", Extent::Base(BaseType::String));
    let result =
        parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse Python module");
    let stmts = match result {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("expected Module, got {other:?}"),
    };
    let mut scheduler = Scheduler::new();
    let (mut op, scope) =
        lower_let_stmt_block(&mut ctx, &stmts, &mut scheduler).expect("direct lowering failed");

    data_source.borrow_mut().add_data(&[
        (Value::UInt(10), Value::String("foo".to_string())),
        (Value::UInt(20), Value::String("bar".to_string())),
    ]);
    data_source.borrow_mut().set_has_data(true);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
    scheduler.check_for_notifications();
    assert!(*notified.borrow());

    let get_result = producer.get();
    *notified.borrow_mut() = false;
    assert_eq!(
        get_result.column_value.sort_by_inputs(),
        ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::UInts(vec![10, 20])),
            outputs: Box::new(ColumnValue::Strings(vec![
                "foo".to_string(),
                "bar".to_string()
            ]))
        }
    );

    data_source.borrow_mut().set_yield_guard(Guard::Universal);
    scheduler.check_for_notifications();
    assert!(!*notified.borrow());
}

/// Test a join between two data sources, including incremental data addition
/// and region release.
#[rstest]
#[case("[(x._0, x._1, y._1) for x in testsource1() for y in testsource2() if x._0 == y._0]")]
#[case(
    "[(x._0, x._1, y._1) for x in testsource1() for y in testsource2() if x._0 == y._0 and True]"
)]
fn test_inner_join(#[case] code: &str) {
    let mut ctx = LoweringContext::default();
    let record_extent = Extent::record(HashMap::from([
        (String::from("_0"), Extent::Base(BaseType::Int)),
        (String::from("_1"), Extent::Base(BaseType::String)),
    ]));
    let data_source1 = ctx.inject_test_source("testsource1", record_extent.clone());
    let data_source2 = ctx.inject_test_source("testsource2", record_extent);
    let result =
        parser::parse(code, parser::Mode::Module, "<test>").expect("Failed to parse Python module");
    let stmts = match result {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("expected Module, got {other:?}"),
    };
    let mut scheduler = Scheduler::new();
    let (mut op, scope) =
        lower_let_stmt_block(&mut ctx, &stmts, &mut scheduler).expect("direct lowering failed");

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(10),
        Value::Record(HashMap::from([
            (String::from("_0"), Value::Int(100)),
            (String::from("_1"), Value::String("a1".to_string())),
        ])),
    )]);
    data_source1.borrow_mut().set_has_data(true);

    data_source2.borrow_mut().add_data(&[(
        Value::UInt(10),
        Value::Record(HashMap::from([
            (String::from("_0"), Value::Int(100)),
            (String::from("_1"), Value::String("b1".to_string())),
        ])),
    )]);
    data_source2.borrow_mut().set_has_data(true);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let mut producer = op.subscribe(Guard::universal(), consumer, scope, &mut scheduler);
    scheduler.check_for_notifications();
    assert!(*notified.borrow());

    let get_result = producer.get();
    *notified.borrow_mut() = false;
    assert_eq!(
        get_result.column_value.sort_by_inputs(),
        ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::UInts(vec![10])),
                ("_1".to_string(), ColumnValue::UInts(vec![10]))
            ]))),
            outputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::Ints(vec![100])),
                (
                    "_1".to_string(),
                    ColumnValue::Strings(vec!["a1".to_string()])
                ),
                (
                    "_2".to_string(),
                    ColumnValue::Strings(vec!["b1".to_string()])
                )
            ])))
        }
    );

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (String::from("_0"), Value::Int(200)),
            (String::from("_1"), Value::String("a2".to_string())),
        ])),
    )]);
    data_source1.borrow_mut().set_has_data(true);

    data_source2.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (String::from("_0"), Value::Int(100)),
            (String::from("_1"), Value::String("b2".to_string())),
        ])),
    )]);
    data_source2.borrow_mut().set_has_data(true);

    scheduler.check_for_notifications();
    assert!(*notified.borrow());
    let get_result = producer.get();
    *notified.borrow_mut() = false;
    assert_eq!(
        get_result.column_value.sort_by_inputs(),
        ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::UInts(vec![10, 10])),
                ("_1".to_string(), ColumnValue::UInts(vec![10, 20]))
            ]))),
            outputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::Ints(vec![100, 100])),
                (
                    "_1".to_string(),
                    ColumnValue::Strings(vec!["a1".to_string(), "a1".to_string()])
                ),
                (
                    "_2".to_string(),
                    ColumnValue::Strings(vec!["b1".to_string(), "b2".to_string()])
                )
            ])))
        }
    );

    producer.release(Guard::Domain(Box::new(Guard::Record(HashMap::from([
        ("_0".to_string(), Guard::LessThanOrEq(Value::UInt(10))),
        ("_1".to_string(), Guard::LessThanOrEq(Value::UInt(10))),
    ])))));

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(30),
        Value::Record(HashMap::from([
            (String::from("_0"), Value::Int(100)),
            (String::from("_1"), Value::String("a3".to_string())),
        ])),
    )]);
    data_source1.borrow_mut().set_has_data(true);

    scheduler.check_for_notifications();
    assert!(*notified.borrow());
    let get_result = producer.get();
    *notified.borrow_mut() = false;
    assert_eq!(
        get_result.column_value.sort_by_inputs(),
        ColumnValue::FunctionBindings {
            inputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::UInts(vec![30])),
                ("_1".to_string(), ColumnValue::UInts(vec![20]))
            ]))),
            outputs: Box::new(ColumnValue::Records(HashMap::from([
                ("_0".to_string(), ColumnValue::Ints(vec![100])),
                (
                    "_1".to_string(),
                    ColumnValue::Strings(vec!["a3".to_string()])
                ),
                (
                    "_2".to_string(),
                    ColumnValue::Strings(vec!["b2".to_string()])
                )
            ])))
        }
    );
}

//! End-to-end pipeline tests: Python source → CCL lower → infer → compile → eval.
//!
//! All tests run through the full CCL pipeline via [`GlobalContext::compile_program`]:
//!
//! ```text
//! Python source
//!   → ccl::lower    (Python AST → CCL Expr)
//!   → ccl::infer    (type inference; annotates Lambda param_ty)
//!   → compile_ccl   (CCL Expr → dataflow operators)
//!   → subscribe()   (operator evaluation)
//! ```
//!
//! Unlike the unit tests in each module, these tests validate the composition
//! of all passes together.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use cambra::ccl::{context::GlobalContext, Type};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    tuple_field, BaseType, ColumnValue, Consumer, Extent, FuncBinding, Predicate,
    SealedFunctionGuard, TestDataSource, Tile, TileGuard, Value,
};
use rstest_log::rstest;

// ---------------------------------------------------------------------------
// Helpers — CCL pipeline path
// ---------------------------------------------------------------------------

/// Lower `code` through the CCL pipeline (parse → `ccl::lower` → `ccl::infer`
/// → `compile_ccl` → subscribe → get) and return the resulting [`ColumnValue`].
fn run_pipeline(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut producer = ctx.compile_program(code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
    producer.get(producer.tiling().universal_guard())
}

// ---------------------------------------------------------------------------
// Parity assertion helpers
// ---------------------------------------------------------------------------

/// Assert `code` produces `expected` via the direct path; additionally assert
/// the pipeline path if `pipeline == Both`.
fn check_tile(code: &str, expected: Tile) {
    assert_eq!(run_pipeline(code), expected, "pipeline path");
}

/// Scalar variant of [`parity`]: unwraps the result via [`ColumnValue::as_single`]
/// before comparing.
fn check_scalar(code: &str, expected: Value) {
    let result = run_pipeline(code);
    let scalar = scalar_tile_to_column_value(result);
    assert_eq!(scalar.as_single().unwrap(), expected);
}

// ---------------------------------------------------------------------------
// Value constructors
// ---------------------------------------------------------------------------

fn make_int_list(v: &[i64]) -> Tile {
    Tile::SealedFunction {
        domain: ColumnValue::UInts((0..v.len()).collect()),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(v.into()))),
        domain_predicate: Predicate::True,
    }
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
    FuncBinding { input: Value::UInt(0), output: Value::Int(1) },
    FuncBinding { input: Value::UInt(1), output: Value::Int(2) },
]))]
fn test_literals(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
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
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Comparisons
// ---------------------------------------------------------------------------

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
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Boolean operations
// ---------------------------------------------------------------------------

#[rstest]
#[case("True & True", Value::Bool(true))]
#[case("True | False", Value::Bool(true))]
#[case("True ^ True", Value::Bool(false))]
#[case("True and False", Value::Bool(false))]
#[case("True or False", Value::Bool(true))]
fn test_bool_ops(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
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
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// More Let bindings
// ---------------------------------------------------------------------------
#[rstest]
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
#[ignore = "need first class functions for this let"]
fn test_let_nonscalar(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
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
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Basic list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[case("[x for x in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[42 for x in [10, 20]]", make_int_list(&[42, 42]))]
#[case("[y for y in [x for x in [10, 20]]]", make_int_list(&[10, 20]))]
#[case("[x + 2 for x in [10, 20]]", make_int_list(&[12, 22]))]
fn test_comprehensions(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Comprehensions with let capture
// ---------------------------------------------------------------------------
//
#[rstest]
#[case("y = 5; [x + y for x in [10, 20]]", make_int_list(&[15, 25]))]
fn test_comprehensions_let_capture(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Comprehensions with tuple body
// ---------------------------------------------------------------------------

#[rstest]
#[case("[(y, y)[1] for y in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[y[0] for y in [(10, 'a'), (20, 'b')]]", make_int_list(&[10, 20]))]
#[case(
    "[(y, 100) for y in [(10, 'a'), (20, 'b')]]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1]),
        codomain: Box::new(Tile::Record(HashMap::from([
            (
                tuple_field(0),
                Tile::Scalar(ColumnValue::Records(HashMap::from([
                    (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                    (
                        tuple_field(1),
                        ColumnValue::Strings(vec![
                            String::from("a"),
                            String::from("b"),
                        ]),
                    ),
                ]))),
            ),
            (tuple_field(1), Tile::Scalar(ColumnValue::Ints(vec![100, 100]))),
        ]))),
        domain_predicate: Predicate::True,
    }
)]
fn test_comprehensions_tuple_body(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
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
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
        domain_predicate: Predicate::True,
    }
)]
#[case(
    "[x for x in [1, 2, 3, 4, 5] if x > 1 if x < 5]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1, 2, 3]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
        domain_predicate: Predicate::True,
    }
)]
fn test_comprehensions_filtered(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
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
// TODO turn back to hash join
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'e'] if x == y and True]",
    ColumnValue::strings(&["bb", "cc"])
)]
// Loop join with non-equality predicate involving both generators
// TODO turn back to hash join
#[case(
    "[x + y for x in [1, 1] for y in [2, 2, 3] if x + 1 == y and True]",
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
// TODO turn back to hash join
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd'] if x == y and True]",
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
    let result = run_pipeline(code);
    match result {
        Tile::SealedFunction { codomain, .. } => {
            assert_eq!(scalar_tile_to_column_value(*codomain), expected);
        }
        other => panic!("expected FunctionBindings, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Data-source injection tests
// ---------------------------------------------------------------------------

/// Verify that a single-generator comprehension over a `TestDataSource` compiles
/// and evaluates correctly through the CCL pipeline.
///
/// All six code variants project or transform the string elements of `testsource1`
/// and should produce the same sorted key→value mapping: `{10 → "foo", 20 → "bar"}`.
///
/// Also confirms that updating the yield guard without adding new data does not
/// trigger a spurious notification.
#[rstest]
#[case("testsource1()")]
#[case("[x for x in testsource1()]")]
#[case("[x + '' for x in testsource1()]")]
#[case("['' + x for x in testsource1()]")]
#[case("y = ''; [y + x for x in testsource1()]")]
#[case("[(x, 0)[0] for x in testsource1()]")]
#[case("[(x, 0)[0] for x in testsource1() if True]")]
fn test_test_source(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let data_source = Rc::new(RefCell::new(TestDataSource::new(
        "testsource1",
        Type::Base(BaseType::String),
        Extent::Base(BaseType::String),
    )));
    ctx.register_test_source(data_source.clone());

    data_source.borrow_mut().add_data(&[
        (Value::UInt(10), Value::String("foo".to_string())),
        (Value::UInt(20), Value::String("bar".to_string())),
    ]);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let mut producer = ctx.compile_program(code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());

    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // Extract domain and codomain; sort by domain key for deterministic comparison.
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        panic!("expected SealedFunction tile");
    };
    let Tile::Scalar(codomain_cv) = *codomain else {
        panic!("expected Scalar codomain");
    };
    let keys = match domain {
        ColumnValue::UInts(v) => v,
        other => panic!("expected UInts domain, got {other:?}"),
    };
    let vals = match codomain_cv {
        ColumnValue::Strings(v) => v,
        other => panic!("expected Strings codomain, got {other:?}"),
    };
    let mut pairs: Vec<(usize, String)> = keys.into_iter().zip(vals).collect();
    pairs.sort_by_key(|(k, _)| *k);
    assert_eq!(
        pairs,
        vec![(10, "foo".to_string()), (20, "bar".to_string())]
    );

    // Changing the yield guard without adding new data must not notify.
    data_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();
    assert!(!*notified.borrow());
}

/// Test a join between two data sources, including incremental data addition
/// and region release.
#[rstest]
#[case(
    "[(x[0], x[1], y[1]) for x in testsource1() for y in testsource2() if x[0] == y[0] and True]"
)]
fn test_inner_join(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let record_type = Type::Record(vec![
        (tuple_field(0), Type::Base(BaseType::Int)),
        (tuple_field(1), Type::Base(BaseType::String)),
    ]);
    let record_extent = Extent::record(HashMap::from([
        (tuple_field(0), Extent::Base(BaseType::Int)),
        (tuple_field(1), Extent::Base(BaseType::String)),
    ]));
    let data_source1 = Rc::new(RefCell::new(TestDataSource::new(
        "testsource1",
        record_type.clone(),
        record_extent.clone(),
    )));
    let data_source2 = Rc::new(RefCell::new(TestDataSource::new(
        "testsource2",
        record_type,
        record_extent,
    )));
    ctx.register_test_source(data_source1.clone());
    ctx.register_test_source(data_source2.clone());

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(10),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("a1".to_string())),
        ])),
    )]);
    data_source2.borrow_mut().add_data(&[(
        Value::UInt(10),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("b1".to_string())),
        ])),
    )]);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let mut producer = ctx.compile_program(code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());

    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // Extract rows from a SealedFunction tile where:
    //   domain   = Records { _0: UInts (src1 key), _1: UInts (src2 key) }
    //   codomain = Record { _0: Scalar(Ints), _1: Scalar(Strings), _2: Scalar(Strings) }
    // Returns pairs sorted by (domain._0, domain._1) for deterministic comparison.
    type DomainKey = (usize, usize);
    type JoinOutput = (i64, String, String);
    fn extract_join_rows(tile: Tile) -> Vec<(DomainKey, JoinOutput)> {
        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction tile, got {tile:?}");
        };
        // domain  = Records { _0: UInts (src1 key), _1: UInts (src2 key) }
        // codomain = Record { _0: Scalar(Ints), _1: Scalar(Strings), _2: Scalar(Strings) }
        let ColumnValue::Records(mut domain_fields) = domain else {
            panic!("expected Records domain, got {domain:?}");
        };
        let Tile::Record(mut codomain_fields) = *codomain else {
            panic!("expected Record codomain, got {codomain:?}");
        };
        let ColumnValue::UInts(d0) = domain_fields.remove("_0").expect("domain._0") else {
            panic!(
                "expected UInts in domain._0, got {:?}",
                domain_fields.get("_0")
            );
        };
        let ColumnValue::UInts(d1) = domain_fields.remove("_1").expect("domain._1") else {
            panic!(
                "expected UInts in domain._1, got {:?}",
                domain_fields.get("_1")
            );
        };
        let Tile::Scalar(ColumnValue::Ints(o0)) =
            codomain_fields.remove("_0").expect("codomain._0")
        else {
            panic!(
                "expected Scalar(Ints) in codomain._0, got {:?}",
                codomain_fields.get("_0")
            );
        };
        let Tile::Scalar(ColumnValue::Strings(o1)) =
            codomain_fields.remove("_1").expect("codomain._1")
        else {
            panic!(
                "expected Scalar(Strings) in codomain._1, got {:?}",
                codomain_fields.get("_1")
            );
        };
        let Tile::Scalar(ColumnValue::Strings(o2)) =
            codomain_fields.remove("_2").expect("codomain._2")
        else {
            panic!(
                "expected Scalar(Strings) in codomain._2, got {:?}",
                codomain_fields.get("_2")
            );
        };
        let mut rows: Vec<(DomainKey, JoinOutput)> = d0
            .into_iter()
            .zip(d1)
            .zip(o0.into_iter().zip(o1).zip(o2))
            .map(|((k0, k1), ((v0, v1), v2))| ((k0, k1), (v0, v1, v2)))
            .collect();
        rows.sort_by_key(|(k, _)| *k);
        rows
    }

    assert_eq!(
        extract_join_rows(tile),
        vec![((10, 10), (100, "a1".to_string(), "b1".to_string()))]
    );

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(200)),
            (tuple_field(1), Value::String("a2".to_string())),
        ])),
    )]);
    data_source2.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("b2".to_string())),
        ])),
    )]);

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // After second batch: (10,10)→(100,"a1","b1") and (10,20)→(100,"a1","b2").
    // src1[20] (_0=200) does not match any src2 row via the x._0==y._0 filter.
    assert_eq!(
        extract_join_rows(tile),
        vec![
            ((10, 10), (100, "a1".to_string(), "b1".to_string())),
            ((10, 20), (100, "a1".to_string(), "b2".to_string())),
        ]
    );

    producer.release(TileGuard::SealedFunction(SealedFunctionGuard::Domain(
        Predicate::Record(HashMap::from([
            (tuple_field(0), Predicate::True),
            (tuple_field(1), Predicate::LessThanEq(Value::UInt(10))),
        ])),
    )));
    producer.release(TileGuard::SealedFunction(SealedFunctionGuard::Domain(
        Predicate::Record(HashMap::from([
            (tuple_field(0), Predicate::LessThanEq(Value::UInt(10))),
            (tuple_field(1), Predicate::True),
        ])),
    )));

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(30),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("a3".to_string())),
        ])),
    )]);

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // After release {_0:≤10, _1:≤10}: each source releases its bound independently.
    // src1 releases key 10; src2 releases key 10.  The remaining cross-products
    // are src1={20,30} × src2={20} = {(20,20),(30,20)}.  After the join filter
    // x[0]==y[0]: src1[20]._0=200 ≠ src2[20]._0=100 (filtered out); src1[30]._0=100
    // == src2[20]._0=100 (kept).
    assert_eq!(
        extract_join_rows(tile),
        vec![((30, 20), (100, "a3".to_string(), "b2".to_string()))]
    );
}

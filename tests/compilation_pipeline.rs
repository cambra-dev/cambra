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
use std::time::Duration;

use bit_set::BitSet;
use bit_vec::BitVec;
use cambra::ccl::context::compile_program;
use cambra::ccl::Expr;
use cambra::ccl::{context::GlobalContext, Type};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    sort_sealed_function_by_domain, tuple_field, BaseType, ColumnValue, Consumer, Extent,
    Predicate, TestDataSource, Tile, Value,
};
use cambra::pretty_graph::pretty_tile_operator;
use rstest_log::rstest;
use smol_str::SmolStr;

// ---------------------------------------------------------------------------
// Helpers — CCL pipeline path
// ---------------------------------------------------------------------------

/// Lower `code` through the CCL pipeline (parse → `ccl::lower` → `ccl::infer`
/// → `compile_ccl` → subscribe → get) and return the resulting [`ColumnValue`].
fn run_pipeline(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    run_pipeline_with_ctx(&mut ctx, code).1
}

fn run_pipeline_with_ctx(ctx: &mut GlobalContext, code: &str) -> (Expr, Tile) {
    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let (ccl, _, mut producer) = compile_program(ctx, code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
    let mut result = producer.get(producer.tiling().universal_guard());
    result.compact();
    (ccl, result)
}

// ---------------------------------------------------------------------------
// Parity assertion helpers
// ---------------------------------------------------------------------------

/// Assert `code` produces `expected` via the direct path; additionally assert
/// the pipeline path if `pipeline == Both`.
fn check_tile(code: &str, expected: Tile) {
    assert_eq!(
        sort_sealed_function_by_domain(run_pipeline(code)),
        sort_sealed_function_by_domain(expected),
        "pipeline path"
    );
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
        deleted: BitSet::new(),
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
#[timeout(Duration::from_secs(1))]
#[case("2", Value::Int(2))]
#[case(r#""hello""#, Value::String("hello".into()))]
#[case("True", Value::Bool(true))]
fn test_literals(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("[]", Tile::SealedFunction { domain: ColumnValue::UInts(vec![]), codomain: Box::new(Tile::Scalar(ColumnValue::Units(0))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case("[1, 2]", make_int_list(&[1, 2]))]
fn test_list_literals(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
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
#[timeout(Duration::from_secs(1))]
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
#[timeout(Duration::from_secs(1))]
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
#[timeout(Duration::from_secs(1))]
#[case("x = 2; x", Value::Int(2))]
#[case("x = 2; y = x; y", Value::Int(2))]
#[case("x = 2; y = x; y + x + 1", Value::Int(5))]
fn test_let_bindings(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Augmented assignment
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("x = 0\nx += 1\nx", Value::Int(1))]
#[case("x = 10\nx -= 3\nx", Value::Int(7))]
#[case("x = 2\nx *= 5\nx", Value::Int(10))]
#[case("x = 7\nx //= 2\nx", Value::Int(3))]
// Chained augmented assignments accumulate correctly.
#[case("x = 0\nx += 1\nx += 2\nx", Value::Int(3))]
// Mix of plain and augmented assignment.
#[case("x = 1\ny = x\nx += 4\ny", Value::Int(1))]
fn test_augmented_assignment(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// More Let bindings
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
#[ignore = "need first class functions for this let"]
fn test_let_nonscalar(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Tuples / record fields
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    "('a', 1)",
    make_tuple(&[Value::String("a".into()), Value::Int(1)])
)]
#[case("('a', 1)[0]", Value::String("a".into()))]
#[case("('a', 1)[1]", Value::Int(1))]
#[case("x = ('a', 1); x[0]", Value::String("a".into()))]
fn test_tuples(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Basic list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
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
#[timeout(Duration::from_secs(1))]
#[case("y = 5; [x + y for x in [10, 20]]", make_int_list(&[15, 25]))]
#[case("y = 1; z = [1,2,3]; [x + y for x in z]", make_int_list(&[2, 3, 4]))]
#[case("y = 1; z = [(1, 'a'),(2, 'b'),(3, 'c')]; [x[0] + y for x in z]", make_int_list(&[2, 3, 4]))]
fn test_comprehensions_let_capture(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Comprehensions with tuple body
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
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
                            "a".into(),
                            "b".into(),
                        ]),
                    ),
                ]))),
            ),
            (tuple_field(1), Tile::Scalar(ColumnValue::Ints(vec![100, 100]))),
        ]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_comprehensions_tuple_body(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Filtered comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("[x for x in [1, 2, 3] if x < 0]", make_int_list(&[]))]
#[case("[x for x in [1, 2, 3] if x > 0]", make_int_list(&[1, 2, 3]))]
#[case("[x for x in [1, 2, 3] if x > 10]", make_int_list(&[]))]
#[case(
    "[x for x in [1, 2, 3] if x == 2]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x for x in [1, 2, 3, 4, 5] if x > 1 if x < 5]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1, 2, 3]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_comprehensions_filtered(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Multi-generator comprehensions / joins
// ---------------------------------------------------------------------------
//
// The join tests check only the `outputs` of the resulting `FunctionBindings`
// because the input key domain (cross-product indices) is an implementation
// detail.

#[rstest]
#[timeout(Duration::from_secs(1))]
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
    ColumnValue::strings(&["cc", "bb"])
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
    ColumnValue::strings(&["ab", "ac", "ad","cd", "bc", "bd"])
)]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd'] if x == y]",
    ColumnValue::strings(&[])
)]
#[case(
    "[x + y + z for x in ['a', 'b'] for y in ['b', 'c'] for z in ['b', 'c'] if x != y if y == z]",
    ColumnValue::strings(&["abb", "bcc", "acc"])
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
#[case(
    "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b]",
    ColumnValue::Ints(vec![11, 21, 12, 22])
)]
#[case(
    "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b if x == y // 10 and True]",
    ColumnValue::Ints(vec![11, 22])
)]
fn test_joins(#[case] code: &str, #[case] expected: ColumnValue) {
    let result = sort_sealed_function_by_domain(run_pipeline(code));
    match result {
        Tile::SealedFunction { codomain, .. } => {
            assert_eq!(scalar_tile_to_column_value(*codomain), expected);
        }
        other => panic!("expected FunctionBindings, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Aggregates
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("sum([1,2,3])", Value::Int(6))]
#[case("max([x + 1 for x in [1,2,3]])", Value::Int(4))]
#[case("max([x + sum([1,2,3]) for x in [1,2,3]])", Value::Int(9))]
fn test_aggregates(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Groupby
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    "[sum(x) for x in groupby([2,3,4,5], lambda x: x // 2)]",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 9]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], lambda x: x // 2)]",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![6, 7]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![25, 29]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_groupby(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
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
#[timeout(Duration::from_secs(1))]
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
        (Value::UInt(10), Value::String("foo".into())),
        (Value::UInt(20), Value::String("bar".into())),
    ]);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let (_, _, mut producer) = compile_program(&mut ctx, code, consumer);
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
    let mut pairs: Vec<(usize, SmolStr)> = keys.into_iter().zip(vals).collect();
    pairs.sort_by_key(|(k, _)| *k);
    assert_eq!(pairs, vec![(10, "foo".into()), (20, "bar".into())]);

    // Changing the yield guard without adding new data must not notify.
    data_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();
    assert!(!*notified.borrow());
}

/// Filtering a data source while in non-terminal state: only elements that
/// satisfy the predicate appear in the codomain; the domain reflects all
/// received source keys and the domain predicate remains `False` (not done).
#[test]
fn test_source_filter_nonterminal() {
    let mut ctx = GlobalContext::default();
    let test_source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    test_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
    ]);
    ctx.register_test_source(test_source.clone());

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let code = "[s for s in source1() if s < 15]";
    let (_, _, mut producer) = compile_program(&mut ctx, code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());

    let mut tile = producer.get(producer.tiling().universal_guard());
    tile.compact();
    assert_eq!(
        sort_sealed_function_by_domain(tile),
        sort_sealed_function_by_domain(Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        })
    );
}

/// Test a join between two data sources, including incremental data addition
/// and region release.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("[(x[0], x[1], y[1]) for x in testsource1() for y in testsource2() if x[0] == y[0]]")]
#[case(
    "[(x[0], x[1], y[1]) for x in testsource1() for y in testsource2() if x[0] == y[0] and True]"
)]
fn test_inner_join(#[case] code: &str) {
    let mut ctx = GlobalContext::default();
    let record_type = Type::Tuple(vec![
        Type::Base(BaseType::Int),
        Type::Base(BaseType::String),
    ]);
    let record_extent = Extent::Record(HashMap::from([
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
            (tuple_field(1), Value::String("a1".into())),
        ])),
    )]);
    data_source1
        .borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(10usize)));
    data_source2.borrow_mut().add_data(&[(
        Value::UInt(10),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("b1".into())),
        ])),
    )]);
    data_source2
        .borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(10usize)));

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    // let mut producer = ctx.compile_program(code, consumer);
    let mut producer = compile_program(&mut ctx, code, consumer).2;
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());

    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // Extract rows from a SealedFunction tile where:
    //   domain   = Records { _0: UInts (src1 key), _1: UInts (src2 key) }
    //   codomain = Record { _0: Scalar(Ints), _1: Scalar(Strings), _2: Scalar(Strings) }
    // Returns pairs sorted by (domain._0, domain._1) for deterministic comparison.
    type DomainKey = (usize, usize);
    type JoinOutput = (i64, SmolStr, SmolStr);
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
        vec![((10, 10), (100, "a1".into(), "b1".into()))]
    );

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(200)),
            (tuple_field(1), Value::String("a2".into())),
        ])),
    )]);
    data_source1
        .borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(20usize)));
    data_source2.borrow_mut().add_data(&[(
        Value::UInt(20),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("b2".into())),
        ])),
    )]);
    data_source2
        .borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(20usize)));

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // After second batch: (10,10)→(100,"a1","b1") and (10,20)→(100,"a1","b2").
    // src1[20] (_0=200) does not match any src2 row via the x._0==y._0 filter.
    assert_eq!(
        extract_join_rows(tile),
        vec![
            ((10, 10), (100, "a1".into(), "b1".into())),
            ((10, 20), (100, "a1".into(), "b2".into())),
        ]
    );

    data_source1.borrow_mut().add_data(&[(
        Value::UInt(30),
        Value::Record(HashMap::from([
            (tuple_field(0), Value::Int(100)),
            (tuple_field(1), Value::String("a3".into())),
        ])),
    )]);
    data_source1
        .borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(30usize)));

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    assert_eq!(
        extract_join_rows(tile),
        vec![
            ((10, 10), (100, "a1".into(), "b1".into())),
            ((10, 20), (100, "a1".into(), "b2".into())),
            ((30, 10), (100, "a3".into(), "b1".into())),
            ((30, 20), (100, "a3".into(), "b2".into()))
        ]
    );
}

/// Simpler version of test_inner_join to make it easier to debug.
#[rstest]
#[case("[x + y for x in source1() for y in source2() if x == y]")]
#[case("[x + y for x in source1() for y in source2() if x == y and True]")]
fn test_incremental_join_simple(#[case] code: &str) {
    let mut ctx = GlobalContext::default();

    let src1 = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    let src2 = Rc::new(RefCell::new(TestDataSource::new(
        "source2",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_test_source(src1.clone());
    ctx.register_test_source(src2.clone());

    src1.borrow_mut()
        .add_data(&[(Value::UInt(1), Value::Int(100))]);
    src1.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(1usize)));
    src2.borrow_mut()
        .add_data(&[(Value::UInt(10), Value::Int(100))]);
    src2.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(10usize)));

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let (_, _, mut producer) = compile_program(&mut ctx, code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());
    *notified.borrow_mut() = false;

    // Unpack SealedFunction where:
    //   domain   = Records { _0: UInts (src1 domain key), _1: UInts (src2 domain key) }
    //   codomain = Record  { _0: Scalar(Ints src1 value), _1: Scalar(Ints src2 value) }
    fn extract_rows(tile: Tile) -> Vec<((usize, usize), i64)> {
        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction, got {tile:?}");
        };
        let ColumnValue::Records(mut df) = domain else {
            panic!("expected Records domain, got {domain:?}");
        };
        let Tile::Scalar(ColumnValue::Ints(codomain)) = *codomain else {
            panic!("expected Ints codomain");
        };
        let ColumnValue::UInts(d0) = df.remove("_0").unwrap() else {
            panic!("domain._0 not UInts");
        };
        let ColumnValue::UInts(d1) = df.remove("_1").unwrap() else {
            panic!("domain._1 not UInts");
        };
        let mut rows: Vec<((usize, usize), i64)> = d0.into_iter().zip(d1).zip(codomain).collect();
        rows.sort_by_key(|(k, _)| *k);
        rows
    }

    assert_eq!(extract_rows(tile), vec![((1, 10), 200)]);

    // Phase 2: extend src1 with a second element; src2 is unchanged.
    src2.borrow_mut()
        .add_data(&[(Value::UInt(20), Value::Int(100))]);
    src2.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(20usize)));

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());

    // Cross-product of src1={10, 30} × src2={20}: two pairs.
    assert_eq!(extract_rows(tile), vec![((1, 10), 200), ((1, 20), 200)]);

    // Phase 3: extend src2 with a second element; src1 is unchanged.
    src1.borrow_mut()
        .add_data(&[(Value::UInt(2), Value::Int(100))]);
    src1.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(2usize)));

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());
    let tile = producer.get(producer.tiling().universal_guard());

    // Cross-product of src1={10, 30} × src2={20}: two pairs.
    assert_eq!(
        extract_rows(tile),
        vec![
            ((1, 10), 200),
            ((1, 20), 200),
            ((2, 10), 200),
            ((2, 20), 200)
        ]
    );
}

/// `sum(source1())` accumulates values across batches and emits the final sum only
/// once the data source signals that it is done producing output.
#[test_log::test]
fn test_incremental_global_aggregate() {
    let code = "sum(source1())";
    let mut ctx = GlobalContext::default();

    let test_source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_test_source(test_source.clone());
    let (_, _, mut producer) = compile_program(&mut ctx, code, Box::new(|| {}));

    // First batch: 10 + 20 = 30 accumulated so far, but source is not done.
    test_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
    ]);
    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![])),
        "should produce no output before source is done (after first batch)"
    );

    // Second batch: adds 30 more; running total 60, still not terminal.
    test_source
        .borrow_mut()
        .add_data(&[(Value::UInt(2), Value::Int(30))]);
    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![])),
        "should produce no output before source is done (after second batch)"
    );

    // Signal that the source is exhausted; the accumulated sum should now be emitted.
    test_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![60])),
        "should emit final sum once source is terminal"
    );

    assert_eq!(
        test_source.borrow().get_released_predicate(),
        Predicate::True
    );
}

#[test_log::test]
fn test_incremental_aggregates() {
    let code = "[sum(x) for x in groupby(source1(), lambda x: x // 10)]";
    let mut ctx = GlobalContext::default();

    let test_source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_test_source(test_source.clone());

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let (_, _, mut producer) = compile_program(&mut ctx, code, consumer);

    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
    *notified.borrow_mut() = false;

    test_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
    ]);

    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        result,
        Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        }
    );

    test_source.borrow_mut().add_data(&[
        (Value::UInt(2), Value::Int(10)),
        (Value::UInt(3), Value::Int(30)),
    ]);
    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        result,
        Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        }
    );

    test_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);

    let result = producer.get(producer.tiling().universal_guard());
    assert_eq!(
        sort_sealed_function_by_domain(result),
        sort_sealed_function_by_domain(Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![1, 2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![20, 20, 30]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        })
    );

    assert_eq!(
        test_source.borrow().get_released_predicate(),
        Predicate::True
    );
}

// Test that we don't have splits in the operator graph for simple binops
#[rstest]
#[case("[1 + x + 1 for x in [1,2,3]]")]
#[case("[(x, x)[0] + 2 for x in [1,2,3]]")]
#[case("[(x, 0) for x in [1,2,3]]")]
#[case("[x for x in [1,2,3] if x + 1 < 2]")]
#[case("1 + 2 + 3")]
fn test_no_splits(#[case] code: &str) {
    let op = compile_program(&mut GlobalContext::default(), code, Box::new(|| {})).1;
    let op_str = pretty_tile_operator(op.as_ref());
    assert!(!op_str.contains("Split#"), "found split in {op_str}");
}

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("1", "1:Int", Tile::Scalar(ColumnValue::Ints(vec![1])))]
#[case("1 + 2", "(1, 2) ▷ add:Int", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case(
    "1 + 2 - 3 * 4",
    "((1, 2) ▷ add, (3, 4) ▷ mul) ▷ sub:Int",
    Tile::Scalar(ColumnValue::Ints(vec![-9]))
)]
#[case(
    "[1,2,3]",
    "[1, 2, 3]:([0, 2] ⇒ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "x = [1,2,3]; x",
    "let x : ([0, 2] ⇒ Int) = [1, 2, 3]\nin x:([0, 2] ⇒ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "x = [1,2,3]; [y + 10 for y in x]",
    "let x : ([0, 2] ⇒ Int) = [1, 2, 3]\nin x ≫ (id, 10 ▷ const) ▷ zip ≫ add:([0, 2] ⇒ Int)",
    make_int_list(&[11,12,13])
)]
#[case(
    "[x + 10 + x for x in [1,2,3]]",
    "[1, 2, 3] ≫ ((id, 10 ▷ const) ▷ zip ≫ add, id) ▷ zip ≫ add:([0, 2] ⇒ Int)",
    make_int_list(&[12,14,16])
)]
#[case(
    "y = 10; [x + y for x in [1,2,3]]",
    "let y : Int = 10\nin [1, 2, 3] ≫ (id, y ▷ const) ▷ zip ≫ add:([0, 2] ⇒ Int)",
    make_int_list(&[11,12,13])
)]
#[case(
    "[x for x in [False,True] if x]",
    "[false, true]:({[0, 1] | Refined([false, true])} ⇒ Bool)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Bools(BitVec::from_elem(1, true)))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    },
)]
#[case(
    "[x + 10 for x in [1,2,3] if x == 2]",
    "[1, 2, 3] ≫ (id, 10 ▷ const) ▷ zip ≫ add:({[0, 2] | Refined([1, 2, 3] ≫ (id, 2 ▷ const) ▷ zip ≫ eq)} ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![12]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    },
)]
#[case(
    "[x + y for x in [1,2,3] for y in [10,20]]",
    "(.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip ≫ add:(([0, 2], [0, 1]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![11, 21, 12, 22, 13, 23]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[(x, y) for x in [1,2,3] for y in [10,20]]",
    "(.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip:(([0, 2], [0, 1]) ⇒ (Int, Int))",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new( Tile::Record(HashMap::from([
            ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![10, 20, 10, 20, 10, 20]))),
            ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 2, 3, 3]))),
        ]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x for x in [1,2,3] for y in [10,20]]",
    ".0 ≫ [1, 2, 3]:(([0, 2], [0, 1]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 1, 1, 2, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 2, 3, 3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [1,2,3] if x == 2 for y in [10,20] if y == 10]",
    "(.0 ≫ [1, 2, 3], .1 ≫ [10, 20]) ▷ zip ≫ add:({([0, 2], [0, 1]) | Refined(((.0 ≫ [1, 2, 3], 2 ▷ const) ▷ zip ≫ eq, (.1 ≫ [10, 20], 10 ▷ const) ▷ zip ≫ eq) ▷ zip ≫ and)} ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![12]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x for x in [x for x in [x for x in [1,2,3]]]]",
    "[1, 2, 3]:([0, 2] ⇒ Int)",
    make_int_list(&[1,2,3])
)]
#[case(
    "[x for x in [y for y in [1,2,3] if y < 3] if x < 2]",
    "[1, 2, 3]:({{[0, 2] | Refined([1, 2, 3] ≫ (id, 3 ▷ const) ▷ zip ≫ lt)} | Refined([1, 2, 3] ≫ (id, 2 ▷ const) ▷ zip ≫ lt)} ⇒ Int)",
    make_int_list(&[1])
)]
#[case(
    "[(x, x) for x in [(x, x) for x in [1,2,3]]]",
    "[1, 2, 3] ≫ (id, id) ▷ zip ≫ (id, id) ▷ zip:([0, 2] ⇒ ((Int, Int), (Int, Int)))",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1, 2]),
        codomain: Box::new(Tile::Record(HashMap::from([
            ("_1".into(), Tile::Record(HashMap::from([
                ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            ]))),
            ("_0".into(), Tile::Record(HashMap::from([
                ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            ]))),
        ]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]",
    "(.0 ≫ [\"a\", \"b\"], .1 ≫ [\"c\", \"d\", \"e\"]) ▷ zip ≫ concat:(([0, 1], [0, 2]) ⇒ String)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0, 0, 0, 1, 1, 1])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1, 2, 0, 1, 2])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::strings(&["ac", "ad", "ae", "bc", "bd", "be"]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + 10 for x in testsource1() if x < 15]",
    "source(testsource1) ≫ (id, 10 ▷ const) ▷ zip ≫ add:({source(testsource1) | Refined(source(testsource1) ≫ (id, 15 ▷ const) ▷ zip ≫ lt)} ⇒ Int)",
    make_int_list(&[10, 20])
)]
#[case("sum([1,2,3])", "[1, 2, 3] ▷ sum:Int", Tile::Scalar(ColumnValue::Ints(vec![6])))]
#[case(
    "[sum(x) for x in groupby([1,2,3,4], lambda y: y // 2)]",
    "([1, 2, 3, 4] ≫ (id, 2 ▷ const) ▷ zip ≫ floor_div) ▷ converse ≫ [1, 2, 3, 4] ▷ map ≫ sum:(Int ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Ints(vec![0, 1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 5, 4]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    })]
#[case(
    "[x + y for x in [1,2,3] for y in [2,3,4,5] if x == y]",
    "([1, 2, 3] ≫ [2, 3, 4, 5] ▷ converse) ▷ uncurry ▷ map_domain ≫ (.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add:(([0, 2], [0, 3]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 6]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [1,2,3] for y in [2,3,4,5] if y == x]",
    "([1, 2, 3] ≫ [2, 3, 4, 5] ▷ converse) ▷ uncurry ▷ map_domain ≫ (.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add:(([0, 2], [0, 3]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![1, 2])),
            ("_1".into(), ColumnValue::UInts(vec![0, 1])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 6]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + 1 for x in [1,2,3] for y in [2,3,4,5] if y - 2 == x + 2]",
    "(([1, 2, 3], 2 ▷ const) ▷ zip ≫ add ≫ (([2, 3, 4, 5], 2 ▷ const) ▷ zip ≫ sub) ▷ converse) ▷ uncurry ▷ map_domain ≫ ((.0 ≫ [1, 2, 3], .1 ≫ [2, 3, 4, 5]) ▷ zip ≫ add, 1 ▷ const) ▷ zip ≫ add:(([0, 2], [0, 3]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![3])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
fn test_new_compile(#[case] code: &str, #[case] expected_ccl: &str, #[case] expected_result: Tile) {
    use cambra::ccl::symbolic::symbolic;

    let mut ctx = GlobalContext::default();

    // Register testsource1 for source-based test cases.
    let data_source = Rc::new(RefCell::new(TestDataSource::new(
        "testsource1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    data_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(0)),
        (Value::UInt(1), Value::Int(10)),
        (Value::UInt(2), Value::Int(20)),
    ]);
    data_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.register_test_source(data_source);

    let (expr, result) = run_pipeline_with_ctx(&mut ctx, code);
    assert_eq!(format!("{}:{}", symbolic(&expr), expr.ty), expected_ccl);
    assert_eq!(
        sort_sealed_function_by_domain(result),
        sort_sealed_function_by_domain(expected_result)
    );
}

// ---------------------------------------------------------------------------
// User-defined functions (scalar UDFs via lambda)
//
// These tests validate the inline pass: scalar-typed `Let` bindings introduced
// by lambda elimination are substituted at their call sites before operator
// conversion, avoiding the "Attempted to iterate on infinite Extent" panic.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("inc = lambda x: x + 1\ninc(4)", Value::Int(5))]
#[case("double = lambda x: x * 2\ndouble(7)", Value::Int(14))]
#[case("neg = lambda x: -x\nneg(3)", Value::Int(-3))]
#[case("identity = lambda x: x\nidentity(42)", Value::Int(42))]
fn test_scalar_udf(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("is_pos = lambda x: x > 0\nis_pos(5)", Value::Bool(true))]
#[case("is_pos = lambda x: x > 0\nis_pos(-1)", Value::Bool(false))]
fn test_udf_bool_codomain(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(1))]
// UDF called twice: body is duplicated at each call site (acceptable trade-off).
#[case("f = lambda x: x + 1\nf(3) + f(4)", Value::Int(9))]
fn test_udf_called_multiple_times(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(1))]
// Nested call: f(f(3)) → f(6) → 12
#[case("f = lambda x: x * 2\nf(f(3))", Value::Int(12))]
fn test_udf_nested_calls(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// Regression: collection and scalar lets should remain unaffected by the
// inlining pass.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("x = 4\nx + 1", Value::Int(5))]
fn test_scalar_let_unaffected(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("xs = [1, 2, 3]\n[x * 2 for x in xs]", make_int_list(&[2, 4, 6]))]
fn test_collection_let_unaffected(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Multi-arg UDFs: lowering uncurries syntactic multi-arg lambdas into a
// single tupled-domain function, and multi-arg calls into a single Apply on
// a tupled argument. This keeps `curry` out of the tree for the common case.
// The n-arm zip arm in operator_conversion dispatches between `ScalarTuple`
// (scalar upstream) and `Zip` (function upstream), so bodies with nested
// BinOps also compile cleanly under scalar call sites. Explicit currying
// (`lambda x: lambda y: ...` or explicit `curry(f)`) is still tracked as
// follow-up work.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("add = lambda x, y: x + y\nadd(3, 4)", Value::Int(7))]
#[case("combine = lambda a, b: a * b + 1\ncombine(3, 4)", Value::Int(13))]
#[case("add3 = lambda x, y, z: x + y + z\nadd3(1, 2, 3)", Value::Int(6))]
#[case("mix = lambda x, y, z: x * y - z\nmix(4, 5, 2)", Value::Int(18))]
fn test_multi_arg_udf(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

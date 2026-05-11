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
use cambra::ccl::Expr;
use cambra::ccl::context::compile_program;
use cambra::ccl::{Type, context::GlobalContext};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, Predicate, TestDataSource, Tile, Value,
    sort_sealed_function_by_domain, tuple_field,
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
    let mut compiled = compile_program(ctx, code, consumer);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "expected notification (pipeline path)");
    let producer = compiled
        .main_mut()
        .and_then(|o| o.producer.as_mut())
        .expect("pipeline test expects a `main` output");
    let mut result = producer.get(producer.tiling().universal_guard());
    result.compact();
    (compiled.ast, result)
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
// Collection union (`@`)
// ---------------------------------------------------------------------------

/// `[1, 2, 3] @ [4, 5]` produces a SealedFunction with a discriminated-union
/// domain and the concatenated integer codomains.
#[rstest]
#[case(
    "[1, 2, 3] @ [4, 5]",
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 1, 1],
            variants: vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; x @ x @ x",
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 1, 1, 2, 2],
            variants: vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; y = x @ x @ x; y",
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 1, 1, 2, 2],
            variants: vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
fn test_unions(#[case] code: &str, #[case] expected: Tile) {
    let result = run_pipeline(code);
    assert_eq!(result, expected);
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
// Records
// ---------------------------------------------------------------------------

fn make_record(fields: &[(&str, Value)]) -> Value {
    Value::Record(
        fields
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect(),
    )
}

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    "{x: 1, y: 2}",
    make_record(&[("x", Value::Int(1)), ("y", Value::Int(2))])
)]
#[case(
    r#"{name: "alice", age: 30}"#,
    make_record(&[("name", Value::String("alice".into())), ("age", Value::Int(30))])
)]
#[case("{x: 1, y: 2}.x", Value::Int(1))]
#[case("{x: 1, y: 2}.y", Value::Int(2))]
#[case(r#"r = {name: "bob", score: 99}; r.score"#, Value::Int(99))]
#[case(r#"r = {name: "bob", score: 99}; r.name"#, Value::String("bob".into()))]
fn test_records(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Records — computed fields and arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("{x: 1 + 2, y: 3 * 4}", make_record(&[("x", Value::Int(3)), ("y", Value::Int(12))]))]
#[case(r#"r = {x: 10, y: 3}; r.x - r.y"#, Value::Int(7))]
#[case(r#"r = {x: 10, y: 3}; r.x * r.y"#, Value::Int(30))]
fn test_records_computed(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Records — list comprehensions
// ---------------------------------------------------------------------------

/// Extract a single named field from the record codomain of a SealedFunction tile.
fn extract_record_field(tile: Tile, field: &str) -> ColumnValue {
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected SealedFunction, got {tile:?}");
    };
    let Tile::Record(mut fields) = *codomain else {
        panic!("expected Record codomain");
    };
    scalar_tile_to_column_value(fields.remove(field).unwrap_or_else(|| {
        panic!(
            "field {field:?} not found; available: {:?}",
            fields.keys().collect::<Vec<_>>()
        )
    }))
}

/// Project a field from an inline record literal in a list comprehension body.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("[{n: x, doubled: x * 2}.n for x in [1, 2, 3]]", make_int_list(&[1, 2, 3]))]
#[case("[{n: x, doubled: x * 2}.doubled for x in [1, 2, 3]]", make_int_list(&[2, 4, 6]))]
fn test_record_field_in_comp_body(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// List comp producing records as elements.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_comp_with_record_body() {
    let tile =
        sort_sealed_function_by_domain(run_pipeline("[{n: x, doubled: x * 2} for x in [1, 2, 3]]"));
    assert_eq!(
        extract_record_field(tile.clone(), "n"),
        ColumnValue::Ints(vec![1, 2, 3]),
    );
    assert_eq!(
        extract_record_field(tile, "doubled"),
        ColumnValue::Ints(vec![2, 4, 6]),
    );
}

/// List comp over an inline list of record literals — field access on the iteration variable.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    r#"[r.x for r in [{x: 1, y: "a"}, {x: 2, y: "b"}, {x: 3, y: "c"}]]"#,
    make_int_list(&[1, 2, 3])
)]
#[case(
    r#"[r.y for r in [{x: 1, y: "a"}, {x: 2, y: "b"}, {x: 3, y: "c"}]]"#,
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Strings(vec![
            "a".into(),
            "b".into(),
            "c".into(),
        ]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_comp_over_record_list(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// Filter on a record field inside a list comprehension.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_comp_filter_on_record_field() {
    let tile = sort_sealed_function_by_domain(run_pipeline(
        r#"[r.name for r in [{name: "alice", age: 30}, {name: "bob", age: 17}, {name: "carol", age: 25}] if r.age >= 18]"#,
    ));
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected SealedFunction");
    };
    assert_eq!(
        scalar_tile_to_column_value(*codomain),
        ColumnValue::strings(&["alice", "carol"])
    );
}

/// Aggregate over a field extracted from a list of record literals.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_aggregate_over_record_field() {
    check_scalar(
        r#"sum([r.score for r in [{score: 10}, {score: 20}, {score: 30}]])"#,
        Value::Int(60),
    );
}

// ---------------------------------------------------------------------------
// Records — joins
// ---------------------------------------------------------------------------

/// Cross-product join producing records with fields from both sides.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_join_with_record_body() {
    let tile = run_pipeline("[{a: x, b: y} for x in [1, 2] for y in [3, 4] if x + y == 5]");
    // (1,4) and (2,3) are the only pairs summing to 5.
    // Output order is determined by join domain — sort both fields together by "a" to compare.
    let ColumnValue::Ints(a_vals) = extract_record_field(tile.clone(), "a") else {
        panic!("expected Ints for field a")
    };
    let ColumnValue::Ints(b_vals) = extract_record_field(tile, "b") else {
        panic!("expected Ints for field b")
    };
    let mut pairs: Vec<(i64, i64)> = a_vals.into_iter().zip(b_vals).collect();
    pairs.sort();
    let (sorted_a, sorted_b): (Vec<i64>, Vec<i64>) = pairs.into_iter().unzip();
    assert_eq!(sorted_a, vec![1, 2]);
    assert_eq!(sorted_b, vec![4, 3]);
}

/// Hash-join (equality filter) producing a record output.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_hash_join_record_body() {
    let tile = sort_sealed_function_by_domain(run_pipeline(
        "[{left: x, right: y} for x in [1, 2, 3] for y in [2, 3, 4] if x == y]",
    ));
    // matched pairs: (2,2) and (3,3)
    assert_eq!(
        extract_record_field(tile.clone(), "left"),
        ColumnValue::Ints(vec![2, 3])
    );
    assert_eq!(
        extract_record_field(tile, "right"),
        ColumnValue::Ints(vec![2, 3])
    );
}

/// Join two data sources with named Record fields, access fields by name in the query.
#[rstest]
#[timeout(Duration::from_secs(1))]
fn test_datasource_named_record_join() {
    let mut ctx = GlobalContext::default();
    let record_type = Type::Record(vec![
        ("id".to_string(), Type::Base(BaseType::Int)),
        ("label".to_string(), Type::Base(BaseType::String)),
    ]);
    let record_extent = Extent::Record(HashMap::from([
        ("id".to_string(), Extent::Base(BaseType::Int)),
        ("label".to_string(), Extent::Base(BaseType::String)),
    ]));
    let src1 = Rc::new(RefCell::new(TestDataSource::new(
        "src1",
        record_type.clone(),
        record_extent.clone(),
    )));
    let src2 = Rc::new(RefCell::new(TestDataSource::new(
        "src2",
        record_type,
        record_extent,
    )));
    ctx.register_source(src1.clone());
    ctx.register_source(src2.clone());

    src1.borrow_mut().add_data(&[
        (
            Value::UInt(0),
            Value::Record(HashMap::from([
                ("id".to_string(), Value::Int(1)),
                ("label".to_string(), Value::String("a".into())),
            ])),
        ),
        (
            Value::UInt(1),
            Value::Record(HashMap::from([
                ("id".to_string(), Value::Int(2)),
                ("label".to_string(), Value::String("b".into())),
            ])),
        ),
    ]);
    src1.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(1usize)));

    src2.borrow_mut().add_data(&[
        (
            Value::UInt(0),
            Value::Record(HashMap::from([
                ("id".to_string(), Value::Int(1)),
                ("label".to_string(), Value::String("x".into())),
            ])),
        ),
        (
            Value::UInt(1),
            Value::Record(HashMap::from([
                ("id".to_string(), Value::Int(3)),
                ("label".to_string(), Value::String("y".into())),
            ])),
        ),
    ]);
    src2.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(1usize)));

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut compiled = compile_program(
        &mut ctx,
        "[(x.label, y.label) for x in src1() for y in src2() if x.id == y.id]",
        consumer,
    );
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow());

    let tile = sort_sealed_function_by_domain(producer.get(producer.tiling().universal_guard()));
    // Only (id=1, "a") × (id=1, "x") should match
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected SealedFunction, got {tile:?}");
    };
    let Tile::Record(mut fields) = *codomain else {
        panic!("expected Record codomain");
    };
    assert_eq!(
        scalar_tile_to_column_value(fields.remove(&tuple_field(0)).unwrap()),
        ColumnValue::strings(&["a"]),
    );
    assert_eq!(
        scalar_tile_to_column_value(fields.remove(&tuple_field(1)).unwrap()),
        ColumnValue::strings(&["x"]),
    );
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

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("x = defer(); x <<= 1; x", Tile::Scalar(ColumnValue::Ints(vec![1])))]
#[case("x = defer(); y = defer(); x <<= 1; y <<= 2; x + y", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case("x = defer(); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case("x = defer(); x << 1; x", Tile::SealedFunction { domain: ColumnValue::Units(1), codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case("x = defer(); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case(
r#"x = defer()
for i in [1,2,3]:
  x << i
x"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"x = defer()
for i in [0,1,2,3]:
  if i // 2 == 0:
    x << i
x"#, make_int_list(&[0, 1]))]
#[case(
r#"x = defer()
y = defer()
x <<= y
y <<= [0, 1]
x"#, make_int_list(&[0, 1]))]
#[case(
r#"x = defer()
y = defer()
x <<= [0, 1]
y <<= x
y"#, make_int_list(&[0, 1]))]
#[case(
r#"x = defer()
x << 1
x << 2
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
r#"x = defer()
x << 1
for i in [1, 2, 3]:
    x << i
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
// Three feed sites: locks down N-ary union construction beyond N=2.
#[case(
r#"x = defer()
x << 1
x << 2
x << 3
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
// Identical feed values still produce distinct variant tags.
#[case(
r#"x = defer()
x << 1
x << 1
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
r#"
x = defer()
y = x
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"
x = defer()
y = x
z = y
for i in [1,2,3]:
  z << i
z"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"
def f(n):
  x = defer()
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"
def f(x):
  x
x = defer()
for i in [1,2,3]:
  y = f(f(x))
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"
x = defer()
for i in [1,2,3]:
  y = x
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case(
r#"
def f(n):
  x = defer()
  x << n
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
r#"
def f(n):
  x = defer()
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y"#, Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 2, 2, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
r#"
def f(n):
  x = defer()
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y @ y"#, Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
            variants: vec![
                ColumnValue::Union {
                    tags: vec![0, 1, 2, 2, 2],
                    variants: vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ],
                },
                ColumnValue::Union {
                    tags: vec![0, 1, 2, 2, 2],
                    variants: vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ],
                },
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3, 10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![
            Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
            Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        ]),
        deleted: BitSet::new(),
    })]
fn test_feed_and_define_operators(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Generator expressions — equivalent to list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("(x for x in [10, 20])", make_int_list(&[10, 20]))]
#[case("(x + 2 for x in [10, 20])", make_int_list(&[12, 22]))]
fn test_generator_expressions(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Filtered generator expression — parity with filtered list comp.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    "(x for x in [1, 2, 3, 4, 5] if x > 2)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![2, 3, 4]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3, 4, 5]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_generator_expression_filtered(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Regular function definitions — def f(x): body; f(arg)
// ---------------------------------------------------------------------------

// Scalar `def` calls (single- and multi-arg) work end-to-end via the
// uncurried definition/call shape and the inline pass for scalar UDFs.
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case("def inc(x):\n    x + 1\ninc(4)", Value::Int(5))]
#[case("def add(x, y):\n    x + y\nadd(3, 4)", Value::Int(7))]
fn test_function_def_scalar(#[case] code: &str, #[case] expected: Value) {
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
#[timeout(Duration::from_secs(1))]
// Simple map: yield x * 2
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\ndoubles([1, 2, 3])",
    make_int_list(&[2, 4, 6])
)]
// Map with captured parameter
#[case(
    "def add_to(xs, n):\n    for x in xs:\n        yield x + n\nadd_to([1, 2, 3], 10)",
    make_int_list(&[11, 12, 13])
)]
// Filter via if-guard
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

// Generator function composed with aggregate: sum(doubles([1, 2, 3])) == 12
#[rstest]
#[timeout(Duration::from_secs(1))]
#[case(
    "def doubles(xs):\n    for x in xs:\n        yield x * 2\nsum(doubles([1, 2, 3]))",
    Value::Int(12)
)]
fn test_generator_function_with_aggregate(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// Nested generator calls: one generator feeds into another.
// Exercises the ANF lift for defer-returning Compose sources introduced when
// `For` was replaced with `Compose+Lambda`.
#[rstest]
#[timeout(Duration::from_secs(1))]
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
#[case(
    "[x + y for x in ['a', 'b', 'c'] for y in ['b', 'c', 'e', 'f'] if x == y]",
    ColumnValue::strings(&["bb", "cc"])
)]
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
    "a = [1,2]; b = [10, 20]; [x + y for x in a for y in b if x == y // 10]",
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
    ctx.register_source(data_source.clone());

    data_source.borrow_mut().add_data(&[
        (Value::UInt(10), Value::String("foo".into())),
        (Value::UInt(20), Value::String("bar".into())),
    ]);

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });

    let mut compiled = compile_program(&mut ctx, code, consumer);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
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
    ctx.register_source(test_source.clone());

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let code = "[s for s in source1() if s < 15]";
    let mut compiled = compile_program(&mut ctx, code, consumer);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
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
    "[(x[0], x[1], y[1]) for x in testsource1() for y in testsource2() if x[0] <= y[0] and x[0] >= y[0]]"
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
    ctx.register_source(data_source1.clone());
    ctx.register_source(data_source2.clone());

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
    let mut compiled = compile_program(&mut ctx, code, consumer);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
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
#[case("[x + y for x in source1() for y in source2() if x <= y and x >= y]")]
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
    ctx.register_source(src1.clone());
    ctx.register_source(src2.clone());

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
    let mut compiled = compile_program(&mut ctx, code, consumer);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
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
    ctx.register_source(test_source.clone());
    let mut compiled = compile_program(&mut ctx, code, Box::new(|| {}));
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();

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
    ctx.register_source(test_source.clone());

    let notified = Rc::new(RefCell::new(false));
    let notified_clone = notified.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || {
        *notified_clone.borrow_mut() = true;
    });
    let mut compiled = compile_program(&mut ctx, code, consumer);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();

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
fn test_no_fan_outs(#[case] code: &str) {
    let compiled = compile_program(&mut GlobalContext::default(), code, Box::new(|| {}));
    let op = &compiled.main().unwrap().op;
    let op_str = pretty_tile_operator(op.as_ref());
    assert!(!op_str.contains("FanOut#"), "found fan-out in {op_str}");
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
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == y and y == z]",
    "([1] ≫ (([1, 2] ≫ [1, 2, 3] ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ≫ ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add:(([0, 0], [0, 1], [0, 2]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
// x==z precedes y==z, so BFS visits z (arm 2) before y (arm 1), producing arm_order=[0,2,1].
// The permute_domain step in convert_loop_join restores canonical domain order.
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z]",
    "([1] ≫ (([1, 2, 3] ≫ [1, 2] ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add:(([0, 0], [0, 1], [0, 2]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y for x in [2] for y in [a + b for a in [1, 2] for b in [1, 2, 3] if a == b] if x == y]",
    "([2] ≫ (([1, 2] ≫ [1, 2, 3] ▷ converse) ▷ uncurry ▷ map_domain ≫ (.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ add) ▷ converse) ▷ uncurry ▷ map_domain ≫ (.0 ≫ [2], .1 ≫ (.0 ≫ [1, 2], .1 ≫ [1, 2, 3]) ▷ zip ≫ add) ▷ zip ≫ add:(([0, 0], ([0, 1], [0, 2])) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::Records(HashMap::from([
                ("_0".into(), ColumnValue::UInts(vec![0])),
                ("_1".into(), ColumnValue::UInts(vec![0])),
            ]))),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![4]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and x + 1 == y]",
    "((([1] ≫ [1, 2, 3] ▷ converse) ▷ uncurry ▷ map_domain ≫ .1 ≫ [1, 2, 3] ≫ [1, 2] ▷ converse) ▷ uncurry ▷ ([0] ▷ flatten_domain) ▷ map_domain ≫ (.0 ≫ ([1], 1 ▷ const) ▷ zip ≫ add, .2 ≫ [1, 2]) ▷ zip ≫ eq) ▷ restrict ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add:(([0, 0], [0, 1], [0, 2]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![])),
            ("_1".into(), ColumnValue::UInts(vec![])),
            ("_2".into(), ColumnValue::UInts(vec![])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and y < 2]",
    "([1] ≫ (([1, 2, 3] ≫ ((([1, 2], 2 ▷ const) ▷ zip ≫ lt) ▷ restrict ≫ [1, 2]) ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ [1, 2, 3]) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add:(([0, 0], [0, 1], [0, 2]) ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x + y + z for x in [1] for y in [1, 2] for z in [1, 2, 3] if x == z and y == z and x + y == z + 1]",
    "((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, .2 ≫ [1, 2, 3]) ▷ zip ≫ add:({([0, 0], [0, 1], [0, 2]) | Refined((((.0 ≫ [1], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq, (.1 ≫ [1, 2], .2 ≫ [1, 2, 3]) ▷ zip ≫ eq) ▷ zip ≫ and, ((.0 ≫ [1], .1 ≫ [1, 2]) ▷ zip ≫ add, (.2 ≫ [1, 2, 3], 1 ▷ const) ▷ zip ≫ add) ▷ zip ≫ eq) ▷ zip ≫ and)} ⇒ Int)",
    Tile::SealedFunction {
        domain: ColumnValue::Records(HashMap::from([
            ("_0".into(), ColumnValue::UInts(vec![0])),
            ("_1".into(), ColumnValue::UInts(vec![0])),
            ("_2".into(), ColumnValue::UInts(vec![0])),
        ])),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
        domain_predicate: Predicate::Record(HashMap::from([
            ("_0".into(), Predicate::True),
            ("_1".into(), Predicate::True),
            ("_2".into(), Predicate::True),
        ])),
        deleted: BitSet::new(),
    }
)]
// TODO add a more realistic join case like below.  Currently, our type inference isn't good enough.
// [(x, z) for x in [1,2,3] for y in [(3, 30), (2, 20), (1, 10)] for z in [20, 10, 30] if z == y[1] and y[2] == x]
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
    ctx.register_source(data_source);

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
// The n-arm zip arm in operator_conversion dispatches between `ScalarFanIn`
// (scalar upstream) and `FanIn` (function upstream), so bodies with nested
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

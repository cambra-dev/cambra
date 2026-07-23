//! Records: literals, computed fields, field access, records inside list
//! comprehensions, and joins producing record outputs.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::Type;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
use cambra::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, Predicate, TestDataSource, Tile, Value,
    sort_sealed_function_by_domain, tuple_field,
};
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Records
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "(x=1, y=2)",
    make_record(&[("x", Value::Int(1)), ("y", Value::Int(2))])
)]
#[case(
    r#"(name="alice", age=30)"#,
    make_record(&[("name", Value::String("alice".into())), ("age", Value::Int(30))])
)]
#[case("(x=1, y=2).x", Value::Int(1))]
#[case("(x=1, y=2).y", Value::Int(2))]
#[case(r#"r = (name="bob", score=99); r.score"#, Value::Int(99))]
#[case(r#"r = (name="bob", score=99); r.name"#, Value::String("bob".into()))]
fn test_records(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Records — computed fields and arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("(x=1 + 2, y=3 * 4)", make_record(&[("x", Value::Int(3)), ("y", Value::Int(12))]))]
#[case(r#"r = (x=10, y=3); r.x - r.y"#, Value::Int(7))]
#[case(r#"r = (x=10, y=3); r.x * r.y"#, Value::Int(30))]
fn test_records_computed(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Records — list comprehensions
// ---------------------------------------------------------------------------

/// Project a field from an inline record literal in a list comprehension body.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[(n=x, doubled=x * 2).n for x in [1, 2, 3]]", make_int_list(&[1, 2, 3]))]
#[case("[(n=x, doubled=x * 2).doubled for x in [1, 2, 3]]", make_int_list(&[2, 4, 6]))]
fn test_record_field_in_comp_body(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// List comp producing records as elements.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_comp_with_record_body() {
    let tile =
        sort_sealed_function_by_domain(run_pipeline("[(n=x, doubled=x * 2) for x in [1, 2, 3]]"));
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
#[timeout(Duration::from_secs(10))]
#[case(
    r#"[r.x for r in [(x=1, y="a"), (x=2, y="b"), (x=3, y="c")]]"#,
    make_int_list(&[1, 2, 3])
)]
#[case(
    r#"[r.y for r in [(x=1, y="a"), (x=2, y="b"), (x=3, y="c")]]"#,
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
#[timeout(Duration::from_secs(10))]
fn test_comp_filter_on_record_field() {
    let tile = sort_sealed_function_by_domain(run_pipeline(
        r#"[r.name for r in [(name="alice", age=30), (name="bob", age=17), (name="carol", age=25)] if r.age >= 18]"#,
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
#[timeout(Duration::from_secs(10))]
fn test_aggregate_over_record_field() {
    check_scalar(
        r#"sum([r.score for r in [(score=10), (score=20), (score=30)]])"#,
        Value::Int(60),
    );
}

// ---------------------------------------------------------------------------
// Records — joins
// ---------------------------------------------------------------------------

/// Cross-product join producing records with fields from both sides.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_join_with_record_body() {
    let tile = run_pipeline("[(a=x, b=y) for x in [1, 2] for y in [3, 4] if x + y == 5]");
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
#[timeout(Duration::from_secs(10))]
fn test_hash_join_record_body() {
    let tile = sort_sealed_function_by_domain(run_pipeline(
        "[(left=x, right=y) for x in [1, 2, 3] for y in [2, 3, 4] if x == y]",
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
#[timeout(Duration::from_secs(10))]
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
    let code = "[(x.label, y.label) for x in src1() for y in src2() if x.id == y.id]";
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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

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
    sort_function_by_domain, tuple_field,
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
    let tile = sort_function_by_domain(run_pipeline("[(n=x, doubled=x * 2) for x in [1, 2, 3]]"));
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
    Tile::data_function(ColumnValue::UInts(vec![0, 1, 2]), Box::new(Tile::Scalar(ColumnValue::Strings(vec![
            "a".into(),
            "b".into(),
            "c".into(),
        ]))), Predicate::True, BitSet::new())
)]
fn test_comp_over_record_list(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// Filter on a record field inside a list comprehension.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_comp_filter_on_record_field() {
    let tile = sort_function_by_domain(run_pipeline(
        r#"[r.name for r in [(name="alice", age=30), (name="bob", age=17), (name="carol", age=25)] if r.age >= 18]"#,
    ));
    let Tile::DataFunction { codomain, .. } = tile else {
        panic!("expected Function");
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
    let tile = sort_function_by_domain(run_pipeline(
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

    let tile = sort_function_by_domain(producer.get(producer.tiling().universal_guard()));
    // Only (id=1, "a") × (id=1, "x") should match
    let Tile::DataFunction { codomain, .. } = tile else {
        panic!("expected Function, got {tile:?}");
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

/// A conditional whose arms are records of **different width**.
///
/// The arms' join is a record-width one — `{a: Int, b: Int} ⊔ {a: Int}` is
/// `{a: Int}`, fields intersecting — and inference computes it, which is why
/// `r.a` typechecks. Taking the union's codomain from that type rather than
/// re-deriving one from the arms' extents gets the *declaration* right: the old
/// derivation answered the positional sum `{`0{a: Int, b: Int} | `1{a: Int}}`, a
/// shape no row holds and nothing downstream can project.
///
/// **Ignored**: the declaration is now right and the remaining gap is the merge
/// itself. Each arm arrives as a struct-of-arrays `Tile::Record`, and
/// `UnionProducer`'s heterogeneous path handles only `Tile::Scalar` arms — it
/// materialises one `Value` per row into a `Variants` column, which a record
/// column is not. Narrowing a wide arm's record column to the declared field set
/// is the operation the merge does not have, and whether the merge should narrow
/// at all (or the tile may stay wider than its tiling) is the open question —
/// the same one `MapResult`'s `Extent::includes` assert asks from the other side.
#[rstest]
#[timeout(Duration::from_secs(10))]
// The wide arm is taken; the narrow arm's field set is what survives in the type.
#[case("c = True\nr = (a=1, b=2) if c else (a=3)\nr.a", 1)]
// The narrow arm is taken.
#[case("c = False\nr = (a=1, b=2) if c else (a=3)\nr.a", 3)]
// Three arms, narrowing twice.
#[case(
    "c = False\nd = True\nr = (a=1, b=2) if c else ((a=3, x=9) if d else (a=4))\nr.a",
    3
)]
#[ignore = "UnionProducer cannot merge Tile::Record arms; needs record-width narrowing"]
fn test_conditional_arms_at_different_record_widths(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

// ---------------------------------------------------------------------------
// Products holding a collection
// ---------------------------------------------------------------------------

/// A collection component is handed back by `SelectField` as the collection it is.
///
/// The components' domains are unrelated, which is what separates a product of
/// collections from a collection of products: assembling one as the other needs
/// them to agree.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("r = (cash=10, lines=[1, 2, 3]); r.lines", &[1, 2, 3])]
#[case("r = (cash=10, lines=[1, 2, 3]); [x * 2 for x in r.lines]", &[2, 4, 6])]
#[case("t = (10, [4, 5, 6]); t.1", &[4, 5, 6])]
#[case("r = (a=[1, 2], b=[4, 5, 6]); r.a", &[1, 2])]
#[case("r = (a=[1, 2], b=[4, 5, 6]); r.b", &[4, 5, 6])]
#[case("xs = [7, 8]; r = (n=1, held=xs); r.held", &[7, 8])]
#[case("r = (n=1, inner=(k=2, deep=[7, 8])); r.inner.deep", &[7, 8])]
fn test_collection_component_of_a_product(#[case] code: &str, #[case] expected: &[i64]) {
    check_tile(code, make_int_list(expected));
}

/// The scalar components of such a product are untouched, and an aggregate over
/// a projected collection component reads it as any other collection.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("r = (cash=10, lines=[1, 2, 3]); r.cash", Value::Int(10))]
#[case("t = (10, [4, 5, 6]); t.0", Value::Int(10))]
#[case("r = (cash=10, lines=[1, 2, 3]); sum(r.lines)", Value::Int(6))]
#[case("t = (10, [4, 5, 6]); sum(t.1)", Value::Int(15))]
#[case(
    "r = (n=1, inner=(k=2, deep=[7, 8])); sum(r.inner.deep)",
    Value::Int(15)
)]
fn test_scalar_component_beside_a_collection(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The whole product value. `a` holds two elements where `b` holds three, which a
/// product of collections can and a collection of products cannot.
#[test]
fn test_product_of_collections_is_a_record_of_tables() {
    check_collection_tile(
        "r = (a=[1, 2], b=[4, 5, 6]); r",
        Tile::Record(
            [
                ("a".to_string(), make_int_list(&[1, 2])),
                ("b".to_string(), make_int_list(&[4, 5, 6])),
            ]
            .into_iter()
            .collect(),
        ),
    );
}

/// A record with a collection field is a constant, so a list of them is one too:
/// `expr_to_value` reaches the nested list and builds its table.
///
/// A list literal's elements are whole `Value`s, so the record rides one column
/// boxed (`Scalar(Records)`) rather than as the struct-of-arrays a record
/// literal compiles to, and each `b` cell carries its own table.
#[test]
fn test_list_of_records_holding_collections() {
    check_tile(
        "xs = [(a=1, b=[1, 2]), (a=3, b=[4, 5])]; xs",
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Records(
                [
                    ("a".to_string(), ColumnValue::Ints(vec![1, 3])),
                    (
                        "b".to_string(),
                        ColumnValue::Variants(vec![
                            make_int_collection(&[1, 2]),
                            make_int_collection(&[4, 5]),
                        ]),
                    ),
                ]
                .into_iter()
                .collect(),
            ))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// A component that is computed rather than written out. Holding a collection
/// means collecting one, and collecting needs something to collect, so planning
/// marks a computed component as an iteration site even though the component
/// position itself is not iterated (`planning::iterate`'s
/// `mark_component_source`). A list literal is the exception at both ends: its
/// table is built directly, with no iteration in between.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::record_comprehension("r = (n=1, xs=[y * 2 for y in [1, 2, 3]]); sum(r.xs)", Value::Int(12))]
#[case::record_filtered(
    "r = (n=1, xs=[y for y in [1, 2, 3] if y > 2]); sum(r.xs)",
    Value::Int(3)
)]
#[case::record_scalar_beside("r = (n=1, xs=[y * 2 for y in [1, 2, 3]]); r.n", Value::Int(1))]
#[case::tuple_comprehension("t = ([y * 2 for y in [1, 2, 3]], 1); sum(t.0)", Value::Int(12))]
#[case::tuple_filtered("t = ([y for y in [1, 2, 3] if y > 2], 1); sum(t.0)", Value::Int(3))]
fn test_computed_collection_component(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A partition is a component like any other. Every key of one holds a further
/// collection, so it tiles as two levels, and the component keeps both.
///
/// Held rather than read back: reading a partition's entries takes
/// `for k -> v in g`, which this version does not lower. What is pinned is that
/// holding one compiles and leaves its siblings readable.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::record_field(r"r = (n=1, g=groupby([1, 1, 2], \x -> x)); r.n", Value::Int(1))]
#[case::tuple_component(r"t = (groupby([1, 1, 2], \x -> x), 7); t.1", Value::Int(7))]
fn a_partition_is_a_product_component_like_any_other(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A `let`-bound partition held as a component reaches a `subst` defect.
///
/// The inline case above compiles, so a product can hold a two-level collection. What
/// this one trips is the key binder `groupby` mints, which `subst` reports as
/// escaping its scope when the `let` is substituted through — a defect in
/// substitution rather than in how a product holds a component.
///
/// Pinned rather than ignored, so the error it reaches is a ledger entry: whoever
/// fixes `subst` sees this case turn from a pinned panic into a passing one.
#[test]
#[should_panic(expected = "Barendregt violation: substitution range mentions binder")]
fn a_let_bound_partition_component_reaches_a_subst_defect() {
    check_scalar(
        r"g = groupby([1, 1, 2], \x -> x); t = (g, 7); t.1",
        Value::Int(7),
    );
}

/// A filtered component keeps the domain it binds rather than the extent it was
/// filtered from: index `2` survives `y > 2` and indices `0` and `1` do not, so the
/// field's tile is keyed by `2` alone.
///
/// Boxed into a cell, the collection would have to be read back out against something,
/// and the extent is the only thing available to read it against — which would ask
/// for keys this collection does not bind.
#[test]
fn test_a_filtered_component_keeps_the_domain_it_binds() {
    check_collection_tile(
        "r = (n=1, xs=[y for y in [1, 2, 3] if y > 2]); r",
        Tile::Record(
            [
                ("n".to_string(), Tile::Scalar(ColumnValue::Ints(vec![1]))),
                (
                    "xs".to_string(),
                    Tile::data_function(
                        ColumnValue::UInts(vec![2]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![3]))),
                        Predicate::True,
                        BitSet::new(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        ),
    );
}

/// A **filter** over a projected collection component, the shape a map over one
/// does not reach.
///
/// A filter plans as `iterate ▷ (𝑠 ≫ 𝑝) ▷ restrict ≫ 𝑠`, naming its source twice:
/// once inside the predicate and once as the composition stage that reads the
/// surviving domain. That second occurrence puts the projection in function
/// position with an input, where a map leaves it at the head with none, and
/// op-conversion's `Apply` arm answers the input by looking the collection up.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::record(
    "r = (n=1, xs=[1, 2, 3, 4]); sum([z for z in r.xs if z < 4])",
    Value::Int(6)
)]
#[case::tuple("t = ([1, 2, 3, 4], 1); sum([z for z in t.0 if z < 4])", Value::Int(6))]
#[case::filtered_component(
    "r = (n=1, xs=[y for y in [1, 2, 3, 4] if y > 1]); sum([z for z in r.xs if z < 4])",
    Value::Int(5)
)]
#[case::filter_and_map(
    "r = (n=1, xs=[1, 2, 3, 4]); sum([z * 2 for z in r.xs if z < 4])",
    Value::Int(12)
)]
#[case::nothing_survives(
    "r = (n=1, xs=[1, 2, 3]); sum([z for z in r.xs if z > 99])",
    Value::Int(0)
)]
#[case::everything_survives(
    "r = (n=1, xs=[1, 2, 3]); sum([z for z in r.xs if z > 0])",
    Value::Int(6)
)]
#[case::nested_projection(
    "r = (a=(b=[1, 2, 3, 4])); sum([z for z in r.a.b if z < 3])",
    Value::Int(3)
)]
// Two filters over one component: the projection is read at two different domains.
#[case::two_filters(
    "r = (n=1, xs=[1, 2, 3, 4]); sum([z for z in r.xs if z < 4]) + sum([w for w in r.xs if w > 2])",
    Value::Int(13)
)]
fn test_filter_over_a_projected_component(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A record built per element with a collection component does not compile yet.
///
/// A product value holds a collection, but a record inside a comprehension's body is a
/// component per element. A constant list component there reaches op-conversion with no
/// iteration planned for it.
///
/// Pinned rather than ignored, so the error it reaches is a ledger entry: whoever fixes
/// it sees this case turn from a pinned panic into a passing one.
#[test]
#[should_panic(expected = "list literal reached op-conversion without an input")]
fn a_per_element_record_holding_a_list_literal_is_not_yet_planned() {
    run_pipeline("xs = [1, 2]; ys = [(a=l, b=[1, 2]) for l in xs]; ys");
}

/// A record built per element whose collection component reads the element fails the
/// type check after `lambda_elim`, on the lowered component `[id, id]`. Pinned for the
/// reason [`a_per_element_record_holding_a_list_literal_is_not_yet_planned`] gives.
#[test]
#[should_panic(expected = "post-lambda-elim produced an invalid tree")]
fn a_per_element_record_holding_a_computed_list_fails_the_post_lambda_elim_check() {
    run_pipeline("xs = [1, 2]; ys = [(a=x, b=[x, x]) for x in xs]; ys");
}

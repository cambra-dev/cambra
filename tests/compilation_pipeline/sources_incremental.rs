//! Data-source injection and incremental evaluation: single-source
//! comprehensions, non-terminal filtering, inner joins with incremental batches,
//! incremental global aggregate, mutation loop over a source, and incremental
//! group-by aggregates.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::Type;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, Predicate, TestDataSource, Tile, Value,
    sort_sealed_function_by_domain, tuple_field,
};
use rstest_log::rstest;
use smol_str::SmolStr;

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
#[timeout(Duration::from_secs(10))]
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

    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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
// 30s: the original flake site; one of the heaviest compiles, ~9.5s wall on a slow CI VM.
#[rstest]
#[timeout(Duration::from_secs(30))]
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

    // let mut producer = ctx.compile_program(code, consumer).unwrap_or_render("<test>", code);
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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
    let mut compiled =
        compile_program(&mut ctx, code, Box::new(|| {})).unwrap_or_render("<test>", code);
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

/// Mutation loop summing values from an incremental source, semantically
/// equivalent to `sum(source1())` but exercising `Recurse` instead of
/// A *conditional* induction write over an async source: `if i > 15: x := x + i`.
/// An async (`DataSourceDomain`) extent routes to the dense `Recurse` path, which
/// cycles on `.writes` (not `.commit`). The writer decision is *carry-complete*
/// (`writes.x = Case[i > 15 → x + i; true → x]`), so a rejected position carries the
/// previous accumulator rather than accumulating unconditionally — the guard is
/// honored by the value, not silently dropped. Source `[10, 20, 30]`, guard `> 15`:
/// only 20 and 30 accumulate, so the final `x = 50` (a dropped guard would give 60).
#[test_log::test]
fn test_incremental_conditional_mutation_loop() {
    let code = "\
x := 0
for i in source1():
    if i > 15:
        x := x + i
x";
    let mut ctx = GlobalContext::default();
    let test_source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(test_source.clone());

    let consumer: Box<dyn Consumer> = Box::new(move || {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();

    test_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
        (Value::UInt(2), Value::Int(30)),
    ]);
    test_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();

    let empty = Tile::Scalar(ColumnValue::Ints(vec![]));
    let mut result = empty.clone();
    for _ in 0..4 {
        result = producer.get(producer.tiling().universal_guard());
        if result != empty {
            break;
        }
    }
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![50])),
        "conditional induction over an async source must honor the guard (20 + 30), not sum all (60)"
    );
}

/// `MapAggregate`.  Verifies that `Recurse` correctly:
/// - Re-reads its `domain` input as the source grows in batches.
/// - Holds back the final emission until the source signals it's done.
/// - Fires notifications when each batch arrives and again on terminal.
/// - Releases positions back through `recursive_input` so the source is
///   marked as fully consumed at the end.
#[test_log::test]
fn test_incremental_mutation_loop() {
    let code = "\
x := 0
for i in source1():
    x := x + i
x";
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
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();

    // Pull a few times between batches to verify the loop doesn't emit
    // anything before the source is terminal.  Done with a fixed cap
    // rather than a single pull because the cycle's pull granularity is
    // an internal detail — what we care about is "no premature output",
    // which any number of pre-terminal pulls should satisfy.
    let empty = Tile::Scalar(ColumnValue::Ints(vec![]));

    // First batch: 10 + 20 = 30 accumulated so far, but source is not done.
    test_source.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(10)),
        (Value::UInt(1), Value::Int(20)),
    ]);
    ctx.scheduler().check_for_notifications();
    assert!(*notified.borrow(), "first batch should fire a notification");
    for _ in 0..3 {
        let result = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            result, empty,
            "after first batch: should produce no output yet"
        );
    }
    *notified.borrow_mut() = false;

    // Second batch: adds 30; running total 60, still not terminal.
    test_source
        .borrow_mut()
        .add_data(&[(Value::UInt(2), Value::Int(30))]);
    ctx.scheduler().check_for_notifications();
    assert!(
        *notified.borrow(),
        "second batch should fire a notification"
    );
    for _ in 0..3 {
        let result = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            result, empty,
            "after second batch: should produce no output yet"
        );
    }
    *notified.borrow_mut() = false;

    // Signal that the source is exhausted; the loop's final accumulator
    // (10 + 20 + 30 = 60) should now be emitted.  Pull until the cycle
    // converges to a non-empty scalar (capped to catch regressions).
    test_source
        .borrow_mut()
        .set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();
    let mut result = empty.clone();
    for _ in 0..3 {
        result = producer.get(producer.tiling().universal_guard());
        if result != empty {
            break;
        }
    }
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![60])),
        "should emit final accumulator once source is terminal"
    );

    // The mutation loop should have released every position back to the
    // source by the end, mirroring `sum(source1())`'s release behaviour.
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
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
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

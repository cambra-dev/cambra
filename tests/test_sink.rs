//! `test_sink()`: what a program writes to a sink, read back as a value.
//!
//! Every program here observes through a sink rather than through a trailing bare
//! expression, so it compiles down the record-of-sinks path
//! (`convert_record_fields_to_operators`) that only the HTTP demos reached before.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::Type;
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{
    BaseType, Consumer, Extent, Predicate, SinkReadError, TestDataSource, Value,
};
use indoc::indoc;

/// Run `source` to completion and answer what it wrote to each named sink.
///
/// The drive loop is capped so a program that never completes fails the test rather than
/// hanging it — the same bound `tests/cli_driver_convergence.rs` puts on the same loop.
fn observe(source: &str, names: &[&str]) -> Vec<Result<Value, SinkReadError>> {
    const CAP: usize = 10_000;

    let mut ctx = GlobalContext::default();
    let sinks: Vec<_> = names.iter().map(|n| ctx.register_test_sink(*n)).collect();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = match compile_program(&mut ctx, source, consumer) {
        Ok(p) => p,
        Err(e) => panic!("compile failed: {e:?}"),
    };

    let mut completed = false;
    for _ in 0..CAP {
        ctx.scheduler().check_for_notifications();
        if program.done.try_recv().is_ok() {
            completed = true;
            break;
        }
    }
    assert!(completed, "sinks did not all complete within {CAP} pulls");

    sinks.iter().map(|s| s.value()).collect()
}

/// Compile `source`, expecting it to fail, and render the errors.
fn compile_error(source: &str) -> String {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    match compile_program(&mut ctx, source, consumer) {
        Ok(_) => String::new(),
        Err(errs) => format!("{errs:?}"),
    }
}

/// One sink, one scalar.
fn observe_one(source: &str) -> Result<Value, SinkReadError> {
    observe(source, &["out"]).remove(0)
}

/// A sink observes the channel's contributions, never a bare value: one feed from a
/// site that does not iterate is one contribution, keyed by unit.
#[test]
fn a_scalar_feed_is_one_contribution_keyed_by_unit() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << 1 + 2
    "#});
    assert_eq!(format!("{}", v.expect("a value")), "Function [ () -> 3 ]");
}

/// Feeding a collection contributes its elements, so the channel carries three
/// positionally-keyed entries rather than one entry holding a collection — the contrast
/// with the scalar feed above.
#[test]
fn a_collection_feed_contributes_its_elements() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << [x * 2 for x in [1, 2, 3]]
    "#});
    assert_eq!(format!("{}", v.expect("a value")), "Function [ 2, 4, 6 ]");
}

#[test]
fn two_sinks_are_observed_independently() {
    let vs = observe(
        indoc! {r#"
            left = test_sink()
            right = test_sink()
            left << 1
            right << 2
        "#},
        &["left", "right"],
    );
    let rendered: Vec<String> = vs
        .into_iter()
        .map(|v| format!("{}", v.expect("a value")))
        .collect();
    assert_eq!(rendered, ["Function [ () -> 1 ]", "Function [ () -> 2 ]"]);
}

#[test]
fn an_unwritten_sink_says_so_rather_than_answering_empty() {
    // A sink nobody wrote and an empty collection must not read alike.
    let sink = {
        let mut ctx = GlobalContext::default();
        ctx.register_test_sink("out")
    };
    assert_eq!(sink.value(), Err(SinkReadError::NothingWritten));
}

/// Filtering preserves a collection's keys: the survivors keep the positions they had,
/// rather than being renumbered densely. Nothing reindexes today, and anything that ever
/// does will be an explicit program-level construct.
#[test]
fn a_filtered_collection_keeps_the_keys_of_its_survivors() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << [x for x in [1, 2, 3, 4] if x > 2]
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ u2 -> 3, u3 -> 4 ]"
    );
}

// ---------------------------------------------------------------------------
// Value shapes: one case per tile the reader walks.
// ---------------------------------------------------------------------------

#[test]
fn a_record_feed() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << (a=1, b=2)
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ () -> {a: 1, b: 2} ]"
    );
}

#[test]
fn a_collection_of_records() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << [(id=x, sq=x * x) for x in [1, 2]]
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ {id: 1, sq: 1}, {id: 2, sq: 4} ]"
    );
}

/// A record whose components differ in depth — one a collection, one a scalar — does not
/// compile: `FanIn::new_at` requires every operand to be a collection at the ambient level
/// and panics otherwise. Pinned at the panic it reaches so the case is a ledger entry
/// rather than an absence.
#[test]
#[should_panic(expected = "FanIn pairs collections over")]
fn a_record_holding_a_collection_does_not_compile() {
    observe_one(indoc! {r#"
        out = test_sink()
        out << (xs=[1, 2], n=3)
    "#})
    .expect("a value");
}

/// A comprehension whose elements are themselves collections does not convert. Pinned at
/// the error it reaches; the reader's recursion into a nested `Function` has no other way
/// to be reached from source yet.
#[test]
fn a_collection_of_collections_does_not_compile() {
    let err = compile_error(indoc! {r#"
        out = test_sink()
        out << [[y * x for y in [1, 2]] for x in [1, 2]]
    "#});
    assert!(
        err.contains("non-combinator curry"),
        "expected the curry conversion error, got: {err}"
    );
}

/// An empty collection is a complete value, and must not read as `NothingWritten`.
#[test]
fn an_empty_collection_is_a_value() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << [x for x in [1, 2] if x > 5]
    "#});
    assert_eq!(format!("{}", v.expect("a value")), "Function [  ]");
}

#[test]
fn a_string_feed() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << "hi"
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        r#"Function [ () -> "hi" ]"#
    );
}

#[test]
fn a_bool_feed() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << 1 < 2
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ () -> true ]"
    );
}

/// One contribution per iteration, keyed by the loop's index — the shape a handler loop
/// produces, and the one the HTTP sink relies on to pair a reply with its request.
#[test]
fn a_loop_contributes_once_per_iteration() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            out << x * 10
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ 10, 20, 30 ]"
    );
}

#[test]
fn a_variant_feed() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        out << `some(1)
    "#});
    assert_eq!(
        format!("{}", v.expect("a value")),
        "Function [ () -> `some(1) ]"
    );
}

// ---------------------------------------------------------------------------
// The statement form.
// ---------------------------------------------------------------------------

/// A sink is a program output, so it is declared where the program's outputs are.
#[test]
fn test_sink_outside_the_top_level_is_rejected() {
    let err = compile_error(indoc! {r#"
        def f(x):
            out = test_sink()
            x

        f(1)
    "#});
    assert!(
        err.contains("top level"),
        "expected a top-level restriction, got: {err}"
    );
}

/// The form takes no arguments; anything else is an ordinary call to a name nothing binds.
#[test]
fn test_sink_with_an_argument_is_not_the_sink_form() {
    let err = compile_error(indoc! {r#"
        out = test_sink(1)
        out << 2
    "#});
    assert!(!err.is_empty(), "expected a compile error");
}

/// Declaring a sink and never writing to it is rejected by channelization, which should
/// instead observe the empty channel it is. Pinned at the error it reaches; a program that
/// writes to a sink only under some condition hits the same defect.
#[test]
fn a_sink_that_is_never_fed_is_rejected_which_is_a_defect() {
    let err = compile_error(indoc! {r#"
        out = test_sink()
        other = test_sink()
        other << 1
    "#});
    assert!(
        err.contains("NoFeedOrDefine"),
        "expected channelization to reject the unfed sink, got: {err}"
    );
}

/// Keys that are not integers: a group-by result is keyed by the group key, so the reader
/// walks a `Strings` key column rather than a `UInts` one.
#[test]
fn a_collection_keyed_by_strings() {
    let v = observe_one(indoc! {r#"
        sales = [
            (region="east", amount=1),
            (region="west", amount=2),
            (region="east", amount=3),
        ]
        out = test_sink()
        out << [sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)]
    "#});
    let rendered = format!("{}", v.expect("a value"));
    assert!(
        rendered.contains("\"east\" -> 4") && rendered.contains("\"west\" -> 2"),
        "expected both group totals, got: {rendered}"
    );
}

/// Successive tiles carry disjoint parts of one value, so the sink accumulates rather than
/// keeping the last. Two deliveries from one source is the only way to reach that path: a
/// literal source hands everything over at once.
#[test]
fn a_sink_accumulates_across_two_deliveries() {
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "nums",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let sink = ctx.register_test_sink("out");

    src.borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(1))]);
    src.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::UInt(0)));

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let code = indoc! {r#"
        out = test_sink()
        for x in nums():
            out << x * 10
    "#};
    let program = match compile_program(&mut ctx, code, consumer) {
        Ok(p) => p,
        Err(e) => panic!("compile failed: {e:?}"),
    };

    for _ in 0..200 {
        ctx.scheduler().check_for_notifications();
    }
    assert_eq!(
        sink.value(),
        Err(SinkReadError::Incomplete),
        "the first delivery is not the whole value"
    );

    src.borrow_mut()
        .add_data(&[(Value::UInt(1), Value::Int(2))]);
    src.borrow_mut().set_yield_predicate(Predicate::True);
    for _ in 0..200 {
        ctx.scheduler().check_for_notifications();
        if program.done.try_recv().is_ok() {
            break;
        }
    }

    assert_eq!(
        format!("{}", sink.value().expect("a value")),
        "Function [ 10, 20 ]",
        "both deliveries are in the accumulated value"
    );
}

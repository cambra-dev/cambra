//! `test_sink()`: what a program writes to a sink, read back as a value.
//!
//! Every program here observes through a sink rather than through a trailing bare
//! expression, so it compiles down the sink-record path (`convert_record_fields_to_operators`),
//! which a program otherwise reaches only through `http_serve`.

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
/// hanging it.
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

/// Compile `source` with a test sink registered under each of `names`, expecting it to
/// fail, and render the errors.
fn compile_error(source: &str, names: &[&str]) -> String {
    let mut ctx = GlobalContext::default();
    for name in names {
        ctx.register_test_sink(*name);
    }
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

/// A collection fed at a site that does not iterate lands flat: the channel takes the
/// collection's own keys (`keys: UInts([0, 1, 2])`) rather than one unit-keyed contribution
/// holding it, `() -> [2, 4, 6]`, which `docs/chl-spec.md`, "3.7 Feed operator `<<`" makes
/// it. Pinned as observed.
#[test]
fn a_collection_feed_lands_flat_rather_than_nesting() {
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

/// A sink nobody wrote and an empty collection must not read alike: a registered sink the
/// program never declares still says nothing was written once the program completes.
#[test]
fn an_unwritten_sink_says_so_rather_than_answering_empty() {
    let observed = observe(
        indoc! {r#"
            other = test_sink()
            other << [x for x in [1, 2] if x > 5]
        "#},
        &["out", "other"],
    );
    assert_eq!(observed[0], Err(SinkReadError::NothingWritten));
    assert_eq!(
        format!("{}", observed[1].clone().expect("a value")),
        "Function [  ]"
    );
}

/// Filtering preserves a collection's keys: the survivors keep the positions they had,
/// rather than being renumbered densely.
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
// Value shapes reachable from source. The reader's unit tests in
// `src/interpreter/test_sink.rs` build the rest directly.
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
/// and panics otherwise. Pinned at the panic it reaches.
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
/// the error it reaches; the reader's recursion into a nested `DataFunction` has no other way
/// to be reached from source.
#[test]
fn a_collection_of_collections_does_not_compile() {
    let err = compile_error(
        indoc! {r#"
        out = test_sink()
        out << [[y * x for y in [1, 2]] for x in [1, 2]]
    "#},
        &["out"],
    );
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
    let err = compile_error(
        indoc! {r#"
        def f(x):
            out = test_sink()
            x

        f(1)
    "#},
        &["out"],
    );
    assert!(
        err.contains("top level"),
        "expected a top-level restriction, got: {err}"
    );
}

/// A loop body and a `with` block lower their statements apart from the top level, and
/// refuse the form the same way.
#[rstest::rstest]
#[case::loop_body(indoc! {r#"
    for x in [1, 2]:
        out = test_sink()
        out << x
    0
"#})]
#[case::with_block(indoc! {r#"
    pool: Mut(Int, Txn) := 0
    for x in [1, 2]:
        with begin():
            out = test_sink()
            pool := x
    0
"#})]
fn test_sink_in_a_loop_or_block_is_rejected(#[case] source: &str) {
    let err = compile_error(source, &["out"]);
    assert!(
        err.contains("only supported at the top level"),
        "expected a top-level restriction, got: {err}"
    );
}

/// The form takes no arguments; anything else is an ordinary call to a name nothing binds.
#[test]
fn test_sink_with_an_argument_is_not_the_sink_form() {
    let err = compile_error(
        indoc! {r#"
        out = test_sink(1)
        out << 2
    "#},
        &["out"],
    );
    assert!(
        err.contains("Unbound variable: 'test_sink'"),
        "expected an unbound call, got: {err}"
    );
}

/// A sink nothing registered has no reader, so the program is refused rather than run
/// against a sink whose output nobody can observe.
#[test]
fn an_unregistered_test_sink_is_rejected() {
    let err = compile_error(
        indoc! {r#"
        out = test_sink()
        out << 2
    "#},
        &[],
    );
    assert!(
        err.contains("no test sink is registered under `out`"),
        "expected an unregistered-sink refusal, got: {err}"
    );
}

/// A second declaration of one sink would leave the first's writes with no reader.
#[test]
fn a_sink_declared_twice_is_rejected() {
    let err = compile_error(
        indoc! {r#"
            out = test_sink()
            out << 1
            out = test_sink()
            out << 2
        "#},
        &["out"],
    );
    assert!(
        err.contains("`out` is already declared as a sink"),
        "expected a duplicate-sink refusal, got: {err}"
    );
}

/// The sink record reads the innermost binding of a sink's name, so a later plain binding
/// would reach the sink in place of every write made through the declaration.
#[test]
fn a_sink_name_bound_again_is_rejected() {
    let err = compile_error(
        indoc! {r#"
            out = test_sink()
            out << 1
            out = [5]
            0
        "#},
        &["out"],
    );
    assert!(
        err.contains("`out` is a sink, so it cannot be bound again"),
        "expected a sink-rebinding refusal, got: {err}"
    );
}

/// The refusal lands on the rebinding, wherever it sits relative to the declaration.
#[test]
fn a_sink_name_bound_before_its_declaration_is_rejected_there() {
    let source = indoc! {r#"
        out = [5]
        out = test_sink()
        out << 1
        0
    "#};
    let err = compile_error(source, &["out"]);
    assert!(
        err.contains("`out` is a sink, so it cannot be bound again")
            && err.contains("span: Span { start: 0, end: 9 }"),
        "expected the refusal at `out = [5]`, got: {err}"
    );
}

/// A sink written only under a condition that does not hold observes the empty channel.
#[test]
fn a_sink_fed_only_under_a_false_condition_is_empty() {
    let v = observe_one(indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            if x > 5:
                out << x
    "#});
    assert_eq!(format!("{}", v.expect("a value")), "Function [  ]");
}

/// Declaring a sink and never writing to it is rejected by channelization, which should
/// instead observe the empty channel it is. Pinned at the error it reaches.
#[test]
fn a_sink_that_is_never_fed_is_rejected_which_is_a_defect() {
    let err = compile_error(
        indoc! {r#"
        out = test_sink()
        other = test_sink()
        other << 1
    "#},
        &["out", "other"],
    );
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
    let Value::Function(bindings) = v.expect("a value") else {
        panic!("a collection");
    };
    // Compared as a set of bindings: the group order is not part of the value.
    let mut groups: Vec<(String, String)> = bindings
        .iter()
        .map(|b| (b.input.to_string(), b.output.to_string()))
        .collect();
    groups.sort();
    assert_eq!(
        groups,
        vec![
            ("\"east\"".to_string(), "4".to_string()),
            ("\"west\"".to_string(), "2".to_string()),
        ]
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
    let mut completed = false;
    for _ in 0..200 {
        ctx.scheduler().check_for_notifications();
        if program.done.try_recv().is_ok() {
            completed = true;
            break;
        }
    }
    assert!(completed, "the program did not complete within 200 pulls");

    assert_eq!(
        format!("{}", sink.value().expect("a value")),
        "Function [ 10, 20 ]",
        "both deliveries are in the accumulated value"
    );
}

/// Feeding a collection built from the loop variable, from inside the loop, does not compile:
/// a list whose elements vary with the binder needs a former that adds a level, which
/// `lambda_elim` states rather than building a tree its own post-pass check rejects. Not a
/// sink defect — the same program through a plain `defer()` and a trailing expression is
/// refused identically.
///
/// It leaves one feed case unmeasured — whether such a channel takes the loop's keys with a
/// collection under each, or splices the contributions into one flat domain — so nothing
/// downstream should assume either.
#[test]
fn a_collection_fed_from_inside_a_loop_does_not_compile() {
    let err = compile_error(indoc! {r#"
        out = test_sink()
        for x in [1, 2]:
            out << [x, x * 10]
    "#});
    assert!(
        err.contains("a list element that varies with the enclosing binder `x`"),
        "expected the list-former gap, got: {err}"
    );
}

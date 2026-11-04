//! Compiled programs run end to end through `crate::interpreter::dispatcher::run_program`: the
//! dispatcher drives every pipeline breaker in the sink's producer chain on one thread, and the
//! sink's own pipeline pulls its producer one package at a time. Each answer is checked against
//! a fixed expected value.

use indoc::indoc;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::Value;
use crate::interpreter::dispatcher::{Planned, Refused, run_program};

use super::TileProducer;

/// `source` compiled with a test sink `out` and its pipelines run through the dispatcher at
/// morsels of `rows`, the sink's among them: the value `out` receives, and what the run planned
/// for each pipeline.
fn dispatched(source: &str, rows: usize) -> (Value, Vec<Planned>) {
    let (mut values, planned) = dispatched_into(source, rows, &["out"]);
    (values.remove(0), planned)
}

/// `source` compiled with a test sink of each of `names` and its pipelines run through the
/// dispatcher at morsels of `rows`, the sinks' among them: the value each sink receives, in the
/// order of `names`, and what the run planned for each pipeline.
///
/// Each sink's producer is released whole by the run's end. A pull of each sink afterwards, in
/// pull mode, reaches no producer beneath a breaker, since the breakers answer from what they
/// consumed; it changes no sink's value, and it finds every sink done.
fn dispatched_into(source: &str, rows: usize, names: &[&str]) -> (Vec<Value>, Vec<Planned>) {
    dispatched_with(source, rows, names, |_| {})
}

/// [`dispatched_into`] with `setup` run on the context before `source` compiles, as a test
/// registers a source there.
fn dispatched_with(
    source: &str,
    rows: usize,
    names: &[&str],
    setup: impl FnOnce(&mut GlobalContext),
) -> (Vec<Value>, Vec<Planned>) {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    setup(&mut ctx);
    let sinks: Vec<_> = names
        .iter()
        .map(|name| ctx.register_test_sink(*name))
        .collect();
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    // The operators stay alive through the run: the map holds the fan-outs the chains share.
    let _operators = ctx.take_operator_map();
    let consumers: Vec<_> = names
        .iter()
        .map(|name| {
            program
                .outputs
                .iter()
                .find(|output| output.name == *name)
                .and_then(|output| output.sink_consumer.clone())
                .unwrap_or_else(|| panic!("{source} writes to sink {name}"))
        })
        .collect();
    let planned = run_program(&mut program, rows)
        .unwrap_or_else(|refused| panic!("{refused}"))
        .planned;
    assert!(
        program.done.try_recv().is_ok(),
        "{source}: the run's last pull of each sink finds every sink done"
    );
    let roots: Vec<_> = consumers
        .iter()
        .map(|consumer| consumer.borrow().producer_slot().clone())
        .collect();
    for (name, root) in names.iter().zip(&roots) {
        let root = root.borrow();
        let producer = root.as_ref().expect("a root holds its producer");
        assert!(
            producer.obsolete_guard().is_universal(),
            "{source}: the run releases sink {name}'s producer whole: {planned:?}"
        );
    }
    let values = |what: &str| -> Vec<Value> {
        sinks
            .iter()
            .zip(names)
            .map(|(sink, name)| {
                let written = sink
                    .value()
                    .unwrap_or_else(|error| panic!("{source}: sink {name} {what}: {error:?}"));
                let [binding] = written.as_function().as_slice() else {
                    panic!("{source} writes one value to {name}: {written:?}")
                };
                binding.output.clone()
            })
            .collect()
    };
    let delivered = values("holds a value once the run returns");
    let beneath = pulls_beneath_breakers(&roots);
    for consumer in &consumers {
        consumer.borrow().pull_now();
    }
    ctx.scheduler().check_for_notifications();
    assert_eq!(
        pulls_beneath_breakers(&roots),
        beneath,
        "{source}: a pull after the run stops at the breakers"
    );
    assert_eq!(values("holds a value after a later pull"), delivered);
    (delivered, planned)
}

/// The pulls of every producer beneath a pipeline breaker in the chains under `roots`: what the
/// breakers' inputs answered.
fn pulls_beneath_breakers(roots: &[crate::interpreter::sinks::ProducerSlot]) -> u64 {
    fn walk(producer: &mut dyn TileProducer, beneath: bool) -> u64 {
        let own = if beneath { producer.base().pulls } else { 0 };
        let breaker = beneath || producer.as_breaking_mut().is_some();
        let mut total = own;
        producer.visit_input_producers_mut(&mut |_, input| total += walk(input, breaker));
        total
    }
    roots
        .iter()
        .map(|root| {
            let mut root = root.borrow_mut();
            walk(
                root.as_mut().expect("a root holds its producer").as_mut(),
                false,
            )
        })
        .sum()
}

/// `source` answers the value rendered as `expected` through the dispatcher, at morsels of one
/// row, three, and one per guard, with a pipeline whose breaker's name starts with each of `kinds`.
fn answers(source: &str, expected: &str, kinds: &[&str]) {
    for rows in [1, 3, usize::MAX] {
        let (value, breakers) = dispatched(source, rows);
        assert_eq!(
            value.to_string(),
            expected,
            "{source} at morsels of {rows}: {breakers:?}"
        );
        for kind in kinds {
            assert!(
                breakers
                    .iter()
                    .any(|planned| planned.name.starts_with(kind)),
                "{source} runs a {kind} pipeline: {breakers:?}"
            );
        }
    }
}

/// A per-row sum whose rows carry a constant reads it through a `MapResultToConst` beneath the
/// `MapAggregate`, in the `MapAggregate`'s own chain: a zip with a constant arm, or a constant
/// element under a filter on the row.
#[rstest_log::rstest]
#[case::zipped_with_a_constant(indoc! {"
    out = test_sink()
    ys = [1, 2, 3, 4, 5]
    k = 10
    out << [sum([y * x + k for y in ys]) for x in [1, 2]]
"}, "Function [ 65, 80 ]")]
#[case::a_constant_under_a_filter(indoc! {"
    out = test_sink()
    ys = [1, 2, 3, 4, 5]
    out << [sum([10 for y in ys if y > x]) for x in [1, 2]]
"}, "Function [ 40, 30 ]")]
fn a_sum_over_rows_carrying_a_constant(#[case] source: &str, #[case] expected: &str) {
    assert!(
        kinds_beneath(&operator_graph(source, false), "MapAggregate")
            .is_some_and(|kinds| kinds.contains(&"MapResultToConst")),
        "{source}: the `MapAggregate` reads a `MapResultToConst` in its own chain"
    );
    answers(source, expected, &["MapAggregate"]);
}

/// A sum of the constant alone does not depend on the row: it is one `Aggregate`, and a
/// `MapResultToConst` gives its value to every row, with no `MapAggregate`.
#[test]
fn a_sum_of_a_constant_over_rows_is_one_aggregate() {
    let source = indoc! {"
        out = test_sink()
        ys = [1, 2, 3, 4, 5]
        out << [sum([10 for y in ys]) for x in [1, 2]]
    "};
    assert_eq!(
        kinds_beneath(&operator_graph(source, false), "MapAggregate"),
        None,
        "{source} compiles no `MapAggregate`"
    );
    answers(source, "Function [ 50, 50 ]", &["Aggregate"]);
}

/// The operator graph `source` compiles to, with `source1` registered where `live`.
fn operator_graph(source: &str, live: bool) -> crate::interpreter::operator_graph::OperatorGraph {
    let mut ctx = GlobalContext::default();
    if live {
        ctx.register_source(std::rc::Rc::new(std::cell::RefCell::new(
            crate::interpreter::TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
                crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
            ),
        )));
    }
    let _sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"))
        .operator_graph
}

/// The kinds of the operators beneath the first operator of `kind` in `graph`, down to the first
/// `Memo` or `FanOutSlot` on each path: the operators its own chain evaluates. `None` where no
/// operator is of `kind`.
fn kinds_beneath(
    graph: &crate::interpreter::operator_graph::OperatorGraph,
    kind: &str,
) -> Option<Vec<&'static str>> {
    use crate::interpreter::operator_graph::GraphNode;
    let operators: std::collections::HashMap<_, _> = graph
        .nodes()
        .iter()
        .filter_map(|node| match node {
            GraphNode::Operator {
                id, kind, inputs, ..
            } => Some((*id, (*kind, inputs))),
            GraphNode::Sink { .. } => None,
        })
        .collect();
    let (_, (_, inputs)) = operators.iter().find(|(_, (k, _))| *k == kind)?;
    let mut kinds = Vec::new();
    let mut stack: Vec<_> = inputs.iter().map(|edge| edge.subscribed).collect();
    while let Some(id) = stack.pop() {
        let (kind, inputs) = operators[&id];
        kinds.push(kind);
        if !matches!(kind, "Memo" | "FanOutSlot") {
            stack.extend(inputs.iter().map(|edge| edge.subscribed));
        }
    }
    Some(kinds)
}

#[test]
fn a_sum_over_a_let_bound_list() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([x * 2 for x in xs])
        "},
        "12",
        &["Memo", "Aggregate"],
    );
}

#[test]
fn a_max_over_a_mapped_list() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            out << max([x * 2 for x in xs])
        "},
        "8",
        &["Memo", "Aggregate", "ExtractAggregate"],
    );
}

#[test]
fn a_mapped_list() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << [x + 1 for x in xs]
        "},
        "Function [ 2, 3, 4 ]",
        &["Memo"],
    );
}

#[test]
fn a_sum_inside_an_expression() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [3, 1, 2]
            out << sum([x for x in xs]) + 1
        "},
        "7",
        &["Aggregate", "ExtractAggregate"],
    );
}

/// A filter reads its input's memo twice, as the values and as the predicate: the memo's push
/// reaches the sum along both, which queues it once.
#[test]
fn a_filtered_sum() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            out << sum([x for x in xs if x > 1])
        "},
        "9",
        &["Memo", "Aggregate"],
    );
}

/// A literal arm of a concatenation has no breaker beneath it, so no push names its keys: the
/// planner queues the region it brings for the sum at the start of the run.
#[test]
fn a_sum_over_a_list_concatenated_with_a_literal() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([x * 2 for x in xs] ++ [10, 20])
        "},
        "42",
        &["Memo", "Aggregate"],
    );
    let (_, planned) = dispatched(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([x * 2 for x in xs] ++ [10, 20])
        "},
        1,
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("Aggregate") && !plan.whole && plan.started),
        "the sum reads the memo's pushes and the literal's region: {planned:?}"
    );
}

/// The comprehension under the second arm of a concatenation: its pushes arrive under tag `1`,
/// and the literal's region under tag `0` is queued at the start.
#[test]
fn a_sum_over_a_union_with_the_comprehension_second() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([7, 8] ++ [x * 2 for x in xs])
        "},
        "27",
        &["Memo", "Aggregate"],
    );
}

/// A chain of concatenations compiles to one union of three arms: the comprehension's pushes
/// arrive under its tag, and both literal arms' regions are queued at the start.
#[test]
fn a_sum_over_a_chain_of_unions() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum(([x * 2 for x in xs] ++ [7]) ++ [8])
        "},
        "27",
        &["Memo", "Aggregate"],
    );
}

/// A union written out whole, read by the output's memo beneath a key of its own.
#[test]
fn a_union_written_out_whole() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << [x * 2 for x in xs] ++ [7, 8]
        "},
        "Function [ `0(u0) -> 2, `0(u1) -> 4, `0(u2) -> 6, `1(u0) -> 7, `1(u1) -> 8 ]",
        &["Memo"],
    );
}

/// Two aggregates of one binding both read its memo through fan-out slots, and the output's memo
/// reads both: each aggregate is one value, so either push names every key of the memo's input,
/// and the memo reads its input whole once both have finished.
#[test]
fn two_aggregates_of_one_binding() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [3, 1, 2]
            out << sum(xs) * 10 + max(xs)
        "},
        "63",
        &["Memo", "Aggregate"],
    );
}

/// A group-by's memo reads its input's memo and the `Converse` keying the groups, which reads
/// that memo too: the group-by's memo reads two pipelines. It reads the `Converse`'s pushes, and
/// the input memo's push reaches it widened, so it keeps open rows and reads them again there.
#[test]
fn a_group_by() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3, 4]
        g = groupby(xs, \\x -> x > 2)
        out << sum([sum(v) for v in g])
    "};
    answers(source, "10", &["Memo", "Converse"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("Memo") && !plan.whole && plan.open),
        "the group-by's memo keeps open rows: {planned:?}"
    );
}

/// The two arms of a concatenation of comprehensions push under their own tags, so the sum reads
/// both pipelines' pushes: two stream edges whose pushes name no key in common.
#[test]
fn a_sum_over_two_concatenated_comprehensions() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        ys = [4, 5]
        out << sum([x for x in xs] ++ [y for y in ys])
    "};
    answers(source, "15", &["Memo", "Aggregate"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned.iter().any(|plan| plan.name.starts_with("Aggregate")
            && !plan.whole
            && !plan.open
            && !plan.started),
        "the sum reads both arms' pushes: {planned:?}"
    );
}

/// A sum read inside another comprehension: the outer sum's pipeline reads the inner sum's and the
/// list's. The inner sum's push names every key of the outer sum's input, which the list's pushes
/// name too, so the outer sum keeps open rows: a row consumed at the list's push before the inner
/// sum is final is read again at the inner sum's push.
#[rstest_log::rstest]
fn a_comprehension_reading_a_sum(#[values(1, usize::MAX)] rows: usize) {
    answers(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            n = sum(ys)
            xs = [1, 2, 3]
            out << sum([x * n for x in xs])
        "},
        "18",
        &["Memo", "Aggregate"],
    );
    let (_, planned) = dispatched(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            n = sum(ys)
            xs = [1, 2, 3]
            out << sum([x * n for x in xs])
        "},
        rows,
    );
    assert!(
        planned.iter().any(|plan| plan.open) && !planned.iter().any(|plan| plan.whole),
        "the outer sum keeps open rows, and no pipeline reads its input whole: {planned:?}"
    );
}

/// A sink is a pipeline of its own that no pipeline reads: it reads the pushes of the output memo
/// of a value.
#[test]
fn a_sink_reads_the_pushes_of_a_values_output_memo() {
    let source = indoc! {"
        out = test_sink()
        out << 1 + 2
    "};
    answers(source, "3", &["Memo", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let sink = sink_of(&planned);
    assert!(!sink.whole && !sink.open, "{sink:?}");
}

/// The sink of a collection reads the pushes of the collection's output memo.
#[test]
fn a_sink_of_a_collection() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << [x + 1 for x in xs]
    "};
    answers(source, "Function [ 2, 3, 4 ]", &["Memo", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let sink = sink_of(&planned);
    assert!(!sink.whole && !sink.open, "{sink:?}");
}

/// Two sinks each run as a pipeline of their own, and the program is done once both are.
#[test]
fn two_sinks_each_run_as_a_pipeline_of_their_own() {
    let source = indoc! {"
        out = test_sink()
        other = test_sink()
        xs = [1, 2, 3]
        out << sum(xs)
        other << max(xs)
    "};
    for rows in [1, usize::MAX] {
        let (values, planned) = dispatched_into(source, rows, &["out", "other"]);
        assert_eq!(values, vec![Value::Int(6), Value::Int(3)], "{planned:?}");
        let sinks = planned
            .iter()
            .filter(|plan| plan.name.starts_with("SinkBreaker"))
            .count();
        assert_eq!(sinks, 2, "{planned:?}");
    }
}

/// The plan of the one sink's pipeline.
fn sink_of(planned: &[Planned]) -> &Planned {
    let [sink] = planned
        .iter()
        .filter(|plan| plan.name.starts_with("SinkBreaker"))
        .collect::<Vec<_>>()[..]
    else {
        panic!("one sink pipeline: {planned:?}")
    };
    sink
}

/// A loop's store is the breaker of a pipeline of its own: the loop over a literal is a source
/// pipeline, cut into morsels of positions, and the sink reads the store once it is terminal.
#[test]
fn a_loop_over_a_literal() {
    answers(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total
        "},
        "6",
        &["LoopScope", "SinkBreaker"],
    );
}

/// The inner pipelines of the one loop scope `planned` holds.
fn rounds(planned: &[Planned]) -> &[Planned] {
    let scopes: Vec<_> = planned
        .iter()
        .filter(|plan| plan.name.starts_with("LoopScope"))
        .collect();
    assert_eq!(scopes.len(), 1, "one loop scope: {planned:?}");
    &scopes[0].rounds
}

/// A guarded loop puts `Memo`s inside the store's cycle, which are inner pipelines of the loop's
/// scope, as the drive's is.
#[test]
fn a_guarded_loop() {
    let source = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            if x > 1:
                total += x
        out << total
    "};
    answers(source, "5", &["LoopScope", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let kinds = |planned: &[Planned], kind: &str| {
        rounds(planned)
            .iter()
            .filter(|plan| plan.name.starts_with(kind))
            .count()
    };
    let (_, unguarded) = dispatched(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total
        "},
        1,
    );
    assert_eq!(
        (
            kinds(&unguarded, "InductionDriver"),
            kinds(&unguarded, "Memo")
        ),
        (1, 0),
        "a plain loop's one inner pipeline is its drive's: {unguarded:?}"
    );
    assert!(
        kinds(&planned, "InductionDriver") == 1 && kinds(&planned, "Memo") >= 1,
        "the drive and the guard's `Memo`s are inner pipelines: {planned:?}"
    );
}

/// A loop over a filtered list runs a round per position its source delivers: the positions
/// the filter drops run none, and a loop whose source delivers none runs no round.
#[rstest_log::rstest]
#[case::keeping_the_last(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3] if x > 2]:
        total += x
    out << total
"}, "3")]
#[case::dropping_one_between(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3, 4] if x > 1 and x != 3]:
        total += x
    out << total
"}, "6")]
#[case::dropping_the_last(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3] if x < 3]:
        total += x
    out << total
"}, "3")]
#[case::dropping_every_one(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3] if x > 5]:
        total += x
    out << total
"}, "0")]
#[case::over_an_empty_list(indoc! {"
    out = test_sink()
    total := 0
    for i in []:
        total += 1
    out << total
"}, "0")]
fn a_loop_over_a_filtered_list(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// A loop over a let-bound list reads the list's memo, a pipeline beneath the store's cycle,
/// and its scope reads its input whole once that pipeline has finished.
#[test]
fn a_loop_over_a_let_bound_list() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        total := 0
        for x in xs:
            total += x
        out << total
    "};
    answers(source, "6", &["Memo", "LoopScope", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("LoopScope") && plan.whole),
        "the loop's scope reads the list's memo whole: {planned:?}"
    );
}

/// A loop's total and a sum both feed the sink.
#[test]
fn a_loop_beside_a_sum() {
    answers(
        indoc! {"
            out = test_sink()
            ys = [4, 5]
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total + sum(ys)
        "},
        "15",
        &["LoopScope", "Aggregate", "SinkBreaker"],
    );
}

/// The inner loop of a nested pair runs as a scope inside the outer loop's scope, which queues it
/// one row of its store per round of the outer loop.
#[test]
fn a_nested_loop() {
    let source = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            for y in [1, 2]:
                total += x * y
        out << total
    "};
    answers(source, "18", &["LoopScope", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        rounds(&planned).iter().any(
            |plan| plan.name.starts_with("LoopScope(InductionStore") && !plan.rounds.is_empty()
        ),
        "the inner loop is a scope inside the outer loop's scope: {planned:?}"
    );
}

/// The second loop's seed reads the first loop's store: a scope reads a scope.
#[test]
fn two_loops_in_sequence() {
    answers(
        indoc! {"
            out = test_sink()
            a := 0
            for x in [1, 2, 3]:
                a += x
            b := a
            for y in [1, 2]:
                b += y
            out << b
        "},
        "9",
        &["LoopScope", "SinkBreaker"],
    );
}

/// The inner loop's seed reads the outer loop's position, so the nested store's seed reads a
/// pipeline of the outer scope.
#[test]
fn a_nested_loop_seeded_from_the_outer_position() {
    answers(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                count := x
                for y in [1, 2]:
                    count += y
                total += count
            out << total
        "},
        "15",
        &["LoopScope", "SinkBreaker"],
    );
}

#[rstest_log::rstest]
#[case::over_let_bound_lists(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ys = [1, 2]
    total := 0
    for x in xs:
        for y in ys:
            total += x * y
    out << total
"}, "18")]
#[case::with_an_accumulator_of_its_own(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        count := 0
        for y in [1, 2]:
            count += y
        total += x * count
    out << total
"}, "18")]
#[case::over_rows_of_no_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        for y in [y for y in [1, 2] if y > 5]:
            total += x * y
    out << total
"}, "0")]
#[case::guarded(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        for y in [1, 2]:
            if x > y:
                total += x * y
    out << total
"}, "11")]
#[case::two_inner_loops_on_one_accumulator(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += x * y
        for y in [3, 4]:
            total += x + y
    out << total
"}, "29")]
#[case::nested_twice_over_one_let_bound_list(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in xs:
        for y in xs:
            for z in xs:
                total := total + x * y - z
    out << total
"}, "54")]
fn a_nested_loop_answers(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// A loop nested in a nested loop runs as a scope inside the scope of the loop around it, itself
/// inside the outermost loop's.
#[test]
fn a_loop_nested_twice() {
    answers(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [1, 2]:
                        total += x * y * z
            out << total
        "},
        "27",
        &["LoopScope", "SinkBreaker"],
    );
}

/// A nested loop whose body aggregates a map of the inner position pulls the `MapAggregate` at each
/// position's path, which it restates: every level of its output is a level of its input.
#[rstest_log::rstest]
#[case::a_sum(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([z * y for z in [1, 2]])
    out << total
"}, "18")]
#[case::a_max_beside_the_outer_position(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += max([z * y for z in xs]) + x
    out << total
"}, "24")]
fn a_nested_loop_aggregating_a_map_of_its_position(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// A nested loop with a condition in its body, on the inner and on the outer position, plans a
/// loop scope.
#[rstest_log::rstest]
#[case::on_the_inner_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            if y > 1:
                total += y
    out << total
"}, "4")]
#[case::on_the_outer_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            if x > 1:
                total += y
    out << total
"}, "3")]
fn a_nested_loop_with_a_condition(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// Nested-loop bodies of the shapes the cases name: each plans a loop scope.
#[rstest_log::rstest]
#[case::an_aggregate_of_a_list_outside_the_loops(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum(xs) * y
    out << total
"}, "36")]
#[case::a_record_of_two_aggregates(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += max([z for z in xs]) - min([w for w in ws]) + y
    out << total
"}, "2")]
#[case::a_tuple_of_the_positions(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            t = (x, y)
            total += t.0 * t.1
    out << total
"}, "9")]
#[case::two_generators(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([z * w * y for z in xs for w in ws])
    out << total
"}, "324")]
#[case::a_sum_of_sums(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([sum([z * w for w in ws]) for z in xs]) * y
    out << total
"}, "324")]
#[case::an_inner_loop_with_a_condition(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            acc := 0
            for z in xs:
                if z > y:
                    acc += z
            total += acc
    out << total
"}, "16")]
#[case::a_comprehension_of_tuples(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([q.0 for q in [(y, z) for z in xs] if q.1 > 1])
    out << total
"}, "12")]
fn a_nested_loop_body_reading(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// A loop nested over the rows of a list, the inner source being the outer element, so each
/// outer position has a domain of its own.
#[rstest_log::rstest]
#[case::reading_the_inner_position(indoc! {"
    out = test_sink()
    acc := 0
    for xs in [[1, 2], [3, 4]]:
        for x in xs:
            acc := acc + x
    out << acc
"}, "10")]
#[case::reading_nothing(indoc! {"
    out = test_sink()
    acc := 0
    for xs in [[1, 2], [3, 4]]:
        for x in xs:
            acc := acc + 7
    out << acc
"}, "28")]
fn a_loop_nested_over_rows(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// Why the planner refuses `source`, compiled with a test sink `out`.
fn refusal(source: &str) -> Refused {
    let loaded = LoadedProgram::test(source);
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    ctx.register_test_sink("out");
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    match run_program(&mut program, 1) {
        Err(refused) => refused,
        Ok(_) => panic!("{source} is refused"),
    }
}

/// A condition on the inner position of a loop nested over rows. Its body selects a field of the
/// record the inner drive renders, at a path, and the selector releases the drive's other field
/// at every path. The drive's push names the paths under which a cell is still held
/// (`keys_released_whole`), so the reader takes each path's selected field
/// (`src/interpreter/design-path-projections.md`, "Differences of nested guards").
#[rstest_log::rstest]
#[case::reading_the_inner_position(indoc! {"
    out = test_sink()
    acc := 0
    for xs in [[1, 2], [3, 4]]:
        for x in xs:
            acc := acc + (x if x > 1 else 0)
    out << acc
"}, "9")]
#[case::reading_a_sum_over_the_inner_position(indoc! {"
    out = test_sink()
    acc := 0
    for xs in [[1, 2], [3, 4]]:
        for x in xs:
            acc := acc + sum([z * x for z in [1, 2]])
    out << acc
"}, "30")]
fn a_condition_in_a_loop_nested_over_rows(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["LoopScope", "SinkBreaker"]);
}

/// A store per row of a comprehension, from a function whose loop runs once per row, runs in no
/// loop's scope, so the planner refuses it.
#[test]
fn a_store_per_row_of_a_comprehension_is_refused() {
    let source = indoc! {"
        def fold_by(items) => Int:
            n := 0
            for x in items:
                n := n + x
            n

        [fold_by(r) for r in [[1, 2], [3, 4]]]
    "};
    let refused = refusal(source);
    assert!(
        refused
            .to_string()
            .contains("runs in no pipeline outside its loop's scope"),
        "{refused}"
    );
}

/// A transaction store of one writer is the breaker of a pipeline of its own; its input is the
/// writer's source, cut into morsels of items, and the sink reads the store once it is terminal.
#[rstest_log::rstest]
#[case::a_counter(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20, 30]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "40")]
// The last item is denied: a deny commits nothing and progresses through the source's release.
#[case::a_grant_then_a_deny(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [70, 50]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"}, "30")]
// An item after the denied one, which the deny leaves the store unchanged for.
#[case::a_deny_then_an_item(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [50, 70, 10]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"}, "40")]
// No item reaches the writer.
#[case::over_no_item(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [r for r in [10, 20] if r > 50]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "100")]
fn a_transaction(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["Commit", "SinkBreaker"]);
}

/// A transaction store of several writers is the breaker of one pipeline per writer, each
/// consuming its writer's source.
#[rstest_log::rstest]
// Both writers contend for one key: the first commits and the second denies.
#[case::contending(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [60]:
        with begin():
            if pool >= r:
                pool := pool - r
    for r in [60]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"}, "40")]
// Writer 0 denies its second item at the pool its first item leaves, 20, which it decides
// before its first item commits: the deny stands only once decided again at that pool.
#[case::a_deny_decided_ahead_of_a_commit(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 10
    for r in [-10, 15]:
        with begin():
            if pool >= r:
                pool := pool - r
    for r in [0]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "5")]
// Three writers contend for one key.
#[case::three_writers(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [30, 30]:
        with begin():
            if pool >= r:
                pool := pool - r
    for r in [20]:
        with begin():
            if pool >= r:
                pool := pool - r
    for r in [r for r in [40, 5] if r > 10]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"}, "10")]
// Writer 0 reads its items from a let-bound list, whose memo is a pipeline its store's pipeline
// reads whole.
#[case::a_writer_over_a_pipeline(indoc! {"
    out = test_sink()
    rs = [10, 20]
    pool: Mut(Int, Txn) := 100
    for r in rs:
        with begin():
            pool := pool - r
    for r in [5]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "65")]
// Each writer writes a key of its own.
#[case::disjoint(indoc! {"
    out = test_sink()
    a: Mut(Int, Txn) := 0
    b: Mut(Int, Txn) := 0
    for r in [1, 2, 3]:
        with begin():
            a := a + r
    for r in [10, 20]:
        with begin():
            b := b + r
    out << await_final(a) + await_final(b)
"}, "36")]
fn a_transaction_store_of_several_writers(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["Commit", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let writers = source.matches("with begin()").count();
    assert_eq!(
        planned
            .iter()
            .filter(|plan| plan.name.starts_with("Commit"))
            .count(),
        writers,
        "the store is the breaker of one pipeline per writer: {planned:?}"
    );
}

/// Two writers over sources of different lengths, each feeding a sink of its own the pool after
/// its commit. The store commits in key order, (source position, writer): writer 0's item 0,
/// writer 1's item 0, then writer 0's items 1 and 2, so the ticks are 1, 2, 3 and 4 in that order.
#[rstest_log::rstest]
fn two_writers_over_sources_of_different_lengths_commit_in_key_order(
    #[values(1, 2, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        a = test_sink()
        b = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20, 30]:
            with begin():
                pool := pool - r
                a << pool
        for r in [1]:
            with begin():
                pool := pool - r
                b << pool
    "};
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let sinks = [ctx.register_test_sink("a"), ctx.register_test_sink("b")];
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    run_program(&mut program, rows).unwrap_or_else(|refused| panic!("{refused}"));
    assert!(program.done.try_recv().is_ok(), "both sinks are done");
    let written: Vec<Vec<(u64, i64)>> = sinks
        .iter()
        .map(|sink| keyed_ints(&sink.value().expect("the sink holds a value")))
        .collect();
    assert_eq!(
        written,
        vec![vec![(1, 90), (3, 69), (4, 39)], vec![(2, 89)]]
    );
}

/// A loop over a live source runs in a scope whose pipeline the run notifies of the positions each
/// delivery adds, and answers once the source yields everything. Each case's `expected` holds its
/// answers over [`deliveries`], in that order.
#[rstest_log::rstest]
#[case::flat(indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        total += x
    out << total
"}, [15, 55, 15])]
#[case::filtered(indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        if x > 2:
            total += x
    out << total
"}, [12, 52, 12])]
#[case::over_a_nested_loop(indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        for y in [1, 2]:
            total += x * y
    out << total
"}, [45, 165, 45])]
#[case::nested_over_the_source(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in source1():
            total += x * y
    out << total
"}, [45, 165, 45])]
fn a_loop_over_a_live_source(
    #[case] source: &str,
    #[case] expected: [i64; 3],
    #[values(1, usize::MAX)] rows: usize,
) {
    for ((delivery, batches), expected) in deliveries().into_iter().zip(expected) {
        let (value, planned) = dispatched_live(source, rows, batches);
        assert_eq!(value, Value::Int(expected), "over {delivery}");
        assert!(
            planned
                .iter()
                .any(|plan| plan.live && plan.name.starts_with("LoopScope")),
            "the loop's scope is the live source pipeline over {delivery}: {planned:?}"
        );
    }
}

/// The deliveries of `source1` a test runs each case over, each named by the function that makes
/// it.
fn deliveries() -> [(&'static str, Vec<Batch>); 3] {
    [
        ("two_batches()", two_batches()),
        ("one_key_batches(10)", one_key_batches(10)),
        (
            "with_an_empty_last_delivery()",
            with_an_empty_last_delivery(),
        ),
    ]
}

/// A loop or a transaction over a live source whose drive reads past positions it runs no round
/// or attempt at: positions a filter on the drive's source drops, and keys a delivery calls
/// complete and holds nothing at while more are to come. The drive states them complete, so the
/// store releases them in the epoch that delivered them.
#[rstest_log::rstest]
#[case::a_filter_on_the_drive_s_source(
    indoc! {"
        out = test_sink()
        total := 0
        for x in [y for y in source1() if y > 2]:
            total += x
        out << total
    "},
    one_key_batches(10),
    52,
)]
#[case::absent_keys_in_a_loop(
    indoc! {"
        out = test_sink()
        total := 0
        for x in source1():
            total += x
        out << total
    "},
    with_absent_keys(),
    19,
)]
#[case::absent_keys_in_a_transaction(
    indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in source1():
            with begin():
                pool := pool - r
        out << await_final(pool)
    "},
    with_absent_keys(),
    81,
)]
#[case::an_item_ahead_of_its_completion(
    indoc! {"
        out = test_sink()
        total := 0
        for x in source1():
            total += x
        out << total
    "},
    with_an_item_ahead_of_its_completion(),
    8,
)]
#[case::an_item_ahead_of_its_completion_in_a_transaction(
    indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in source1():
            with begin():
                pool := pool - r
        out << await_final(pool)
    "},
    with_an_item_ahead_of_its_completion(),
    92,
)]
fn a_drive_over_a_live_source_reads_past_empty_positions(
    #[case] source: &str,
    #[case] batches: Vec<Batch>,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, _) = dispatched_live(source, rows, batches);
    assert_eq!(value, Value::Int(expected));
}

/// A loop over a let-bound map of a live source reads the map's `Memo`, the pipeline the run
/// notifies of each delivery, whole once that pipeline has finished the last epoch.
#[rstest_log::rstest]
#[case::two_batches(two_batches(), 30)]
#[case::one_key_batches(one_key_batches(10), 110)]
fn a_loop_over_a_let_bound_map_of_a_live_source(
    #[case] batches: Vec<Batch>,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        ys = [x * 2 for x in source1()]
        total := 0
        for y in ys:
            total += y
        out << total
    "};
    let (value, planned) = dispatched_live(source, rows, batches);
    assert_eq!(value, Value::Int(expected));
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && plan.name.starts_with("Memo"))
            && planned
                .iter()
                .any(|plan| plan.whole && plan.name.starts_with("LoopScope")),
        "the map's `Memo` is the live pipeline, and the loop's scope reads it whole: {planned:?}"
    );
}

/// A transaction over a live source is a pipeline the run notifies of the items each delivery adds,
/// committed in order, and `await_final` answers once the source yields everything. Each case's
/// `expected` holds its answers over [`deliveries`], in that order.
#[rstest_log::rstest]
#[case::every_item(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in source1():
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, [85, 45, 85])]
#[case::with_denies(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 10
    for r in source1():
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"}, [0, 0, 0])]
fn a_transaction_over_a_live_source(
    #[case] source: &str,
    #[case] expected: [i64; 3],
    #[values(1, usize::MAX)] rows: usize,
) {
    for ((delivery, batches), expected) in deliveries().into_iter().zip(expected) {
        let (value, planned) = dispatched_live(source, rows, batches);
        assert_eq!(value, Value::Int(expected), "over {delivery}");
        assert!(
            planned
                .iter()
                .any(|plan| plan.live && plan.name.starts_with("Commit")),
            "the transaction store is the live source pipeline over {delivery}: {planned:?}"
        );
    }
}

/// Two writers of one transaction store over one live source: each writer's pipeline is a live
/// source pipeline the run notifies of the items each delivery adds. Neither writer denies, so the
/// store's final value is 1000 less three times the items' sum whatever the order of the commits.
#[rstest_log::rstest]
#[case::two_batches(two_batches(), 955)]
#[case::one_key_batches(one_key_batches(10), 835)]
#[case::with_an_empty_last_delivery(with_an_empty_last_delivery(), 955)]
fn two_writers_over_a_live_source(
    #[case] batches: Vec<Batch>,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 1000
        for r in source1():
            with begin():
                pool := pool - r
        for r in source1():
            with begin():
                pool := pool - 2 * r
        out << await_final(pool)
    "};
    let (value, planned) = dispatched_live(source, rows, batches);
    assert_eq!(value, Value::Int(expected));
    assert_eq!(
        planned
            .iter()
            .filter(|plan| plan.live && plan.name.starts_with("Commit"))
            .count(),
        2,
        "each writer's pipeline is a live source pipeline: {planned:?}"
    );
}

/// Two writers over one live source that deny once the pool runs short, so the order of the
/// commits decides the answer. Key order commits writer 0's item at each position, then writer
/// 1's: the items worth 1 to 4 commit for both writers, which leaves 0 of 20, and both writers deny
/// the item worth 5.
#[rstest_log::rstest]
fn two_writers_over_a_live_source_commit_in_key_order(
    #[values(two_batches(), one_key_batches(5))] batches: Vec<Batch>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 20
        for r in source1():
            with begin():
                if pool >= r:
                    pool := pool - r
                    out << pool
        for r in source1():
            with begin():
                if pool >= r:
                    pool := pool - r
                    out << pool
    "};
    let (written, _) = dispatched_live_written(source, rows, batches);
    // The sink holds a tagged union of its two feeds, each keyed by commit tick: the site each
    // tick's write came from, and the pool after it.
    let mut fed: Vec<(u64, String, i64)> = written
        .as_function()
        .iter()
        .map(|binding| match (&binding.input, &binding.output) {
            (Value::Union { tag, inner }, Value::Int(pool)) => match **inner {
                Value::UInt(tick) => (tick, tag.to_string(), *pool),
                ref other => panic!("a feed is keyed by commit tick: {other}"),
            },
            other => panic!("a sink fed from two sites holds a tagged union: {other:?}"),
        })
        .collect();
    fed.sort();
    let sites: Vec<&str> = fed.iter().map(|(_, site, _)| site.as_str()).collect();
    let pools: Vec<i64> = fed.iter().map(|(_, _, pool)| *pool).collect();
    assert_eq!(
        sites,
        ["0", "1", "0", "1", "0", "1", "0", "1"],
        "{written:?}"
    );
    assert_eq!(pools, [19, 18, 16, 14, 11, 8, 4, 0], "{written:?}");
}

/// A feed inside a transaction over a live source reads the store's decided stream, which the
/// store pushes as each consume decides it, so the sink holds part of the stream before the source
/// yields everything.
///
/// The sink holds the pool after each commit, keyed by the commit's time.
#[rstest_log::rstest]
#[case::two_batches(two_batches(), vec![(1, 99), (2, 97), (3, 94), (4, 90), (5, 85)])]
#[case::one_key_batches(
    one_key_batches(10),
    vec![(1, 99), (2, 97), (3, 94), (4, 90), (5, 85), (6, 79), (7, 72), (8, 64), (9, 55), (10, 45)],
)]
fn a_feed_inside_a_transaction_over_a_live_source(
    #[case] batches: Vec<Batch>,
    #[case] expected: Vec<(u64, i64)>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in source1():
            with begin():
                pool := pool - r
                out << pool
    "};
    let mut written_before_the_end = Vec::new();
    let (written, _) = dispatched_live_observed(source, rows, batches, |sink| {
        written_before_the_end
            .push(sink.value() == Err(crate::interpreter::SinkReadError::Incomplete));
    });
    assert_eq!(keyed_ints(&written), expected);
    assert!(
        written_before_the_end.first() == Some(&true),
        "the first delivery's commits reach the sink before the next: {written_before_the_end:?}"
    );
}

/// A transaction over a let-bound list reads the list's memo along two paths inside its cycle,
/// the writer's and the body's, and reads it once.
#[test]
fn a_transaction_over_a_let_bound_list() {
    answers(
        indoc! {"
            out = test_sink()
            rs = [10, 20, 30]
            pool: Mut(Int, Txn) := 100
            for r in rs:
                with begin():
                    pool := pool - r
            out << await_final(pool)
        "},
        "40",
        &["Memo", "Commit", "SinkBreaker"],
    );
}

/// A guarded loop over a let-bound list reads the list's memo along every path its filter reads
/// the drive by, and reads it once.
#[test]
fn a_guarded_loop_over_a_let_bound_list() {
    answers(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            total := 0
            for x in xs:
                if x > 1:
                    total += x
            out << total
        "},
        "5",
        &["Memo", "LoopScope", "SinkBreaker"],
    );
}

/// A sink fed from two sites holds a tagged union of its feeds, which the run hands it arm by
/// arm: the run's last pull closes the arms' statements over the union (`Tile::closed_over`),
/// so the sink is done and holds both arms.
#[rstest_log::rstest]
fn a_sink_fed_from_two_sites(#[values(1, usize::MAX)] rows: usize) {
    let source = indoc! {r#"
        m = map([("a", 1)])
        r = m["a"]
        s = m["b"]
        out = test_sink()
        out << r
        out << s
    "#};
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    run_program(&mut program, rows).unwrap_or_else(|refused| panic!("{refused}"));
    assert!(program.done.try_recv().is_ok(), "the sink is done");
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("the sink holds a value: {error:?}"));
    assert_eq!(written.as_function().len(), 2, "both feeds: {written:?}");
}

/// One delivery of a live source: the entries it adds, and the region it then calls complete.
type Batch = (Vec<(Value, Value)>, crate::interpreter::Predicate);

/// `source`, reading the live source `source1`, compiled with a test sink `out` and run through
/// the dispatcher at morsels of `rows`, the source fed `batches`: the first before the run, and
/// each next one when the run has nothing to do. The one value the sink holds, and what the run
/// planned.
fn dispatched_live(source: &str, rows: usize, batches: Vec<Batch>) -> (Value, Vec<Planned>) {
    let (written, planned) = dispatched_live_written(source, rows, batches);
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    (binding.output.clone(), planned)
}

/// [`dispatched_live`], answering everything the sink holds: a value under each site that feeds
/// it.
fn dispatched_live_written(
    source: &str,
    rows: usize,
    batches: Vec<Batch>,
) -> (Value, Vec<Planned>) {
    dispatched_live_observed(source, rows, batches, |_| {})
}

/// [`dispatched_live_written`] with `idle` handed the sink each time the run has nothing to do,
/// before the next delivery.
fn dispatched_live_observed(
    source: &str,
    rows: usize,
    batches: Vec<Batch>,
    mut idle: impl FnMut(&crate::interpreter::TestSink),
) -> (Value, Vec<Planned>) {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let feed = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
        ),
    ));
    ctx.register_source(feed.clone());
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let mut batches = batches.into_iter();
    let deliver = |batch: Option<Batch>| {
        let Some((entries, complete)) = batch else {
            panic!("{source}: the run waits after the last batch")
        };
        let mut feed = feed.borrow_mut();
        feed.add_data(&entries);
        feed.set_yield_predicate(complete);
    };
    deliver(batches.next());
    let planned =
        crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
            idle(&sink);
            deliver(batches.next())
        })
        .unwrap_or_else(|refused| panic!("{refused}"))
        .planned;
    assert!(
        program.done.try_recv().is_ok(),
        "{source}: the run's last pull of the sink finds it done"
    );
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    (written, planned)
}

/// The entries of `value`, a collection of `Int` keyed by `UInt`s, a source's keys or commit
/// times, in key order.
fn keyed_ints(value: &Value) -> Vec<(u64, i64)> {
    let mut pairs: Vec<(u64, i64)> = value
        .as_function()
        .iter()
        .map(|binding| match (&binding.input, &binding.output) {
            (Value::UInt(key), Value::Int(value)) => (*key, *value),
            other => panic!("an `Int` keyed by a `UInt`: {other:?}"),
        })
        .collect();
    pairs.sort();
    pairs
}

/// Two deliveries of `source1`: keys 0 to 2 with everything through 4 called complete, so keys 3
/// and 4 never arrive, then keys 5 and 6 and the rest; each valued one more than the key.
fn with_absent_keys() -> Vec<Batch> {
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    vec![
        (
            entries(0..3),
            crate::interpreter::Predicate::at_or_below(Value::UInt(4)),
        ),
        (entries(5..7), crate::interpreter::Predicate::True),
    ]
}

/// Three deliveries of `source1`, one key each: key 0 with it complete; key 2 with only keys
/// through 1 complete, so key 1 never arrives and the drive holds key 2 past the delivery's
/// package; then key 3 and the rest. Each valued one more than the key.
fn with_an_item_ahead_of_its_completion() -> Vec<Batch> {
    let one = |key: u64| vec![(Value::UInt(key), Value::Int(key as i64 + 1))];
    vec![
        (
            one(0),
            crate::interpreter::Predicate::at_or_below(Value::UInt(0)),
        ),
        (
            one(2),
            crate::interpreter::Predicate::at_or_below(Value::UInt(1)),
        ),
        (one(3), crate::interpreter::Predicate::True),
    ]
}

/// [`two_batches`] with a third delivery that adds no key and calls the source complete.
fn with_an_empty_last_delivery() -> Vec<Batch> {
    let mut batches = two_batches();
    batches[1].1 = crate::interpreter::Predicate::at_or_below(Value::UInt(4));
    batches.push((Vec::new(), crate::interpreter::Predicate::True));
    batches
}

/// Two deliveries of `source1`: keys 0 to 2, then 3 and 4, valued one more than the key.
fn two_batches() -> Vec<Batch> {
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    vec![
        (
            entries(0..3),
            crate::interpreter::Predicate::at_or_below(Value::UInt(2)),
        ),
        (entries(3..5), crate::interpreter::Predicate::True),
    ]
}

/// A sum over a live source runs in a source pipeline the run notifies of each delivery, and
/// answers once the source yields everything.
#[rstest_log::rstest]
fn a_sum_over_a_live_source(#[values(1, 2, usize::MAX)] rows: usize) {
    let (value, planned) = dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum(source1())
        "},
        rows,
        two_batches(),
    );
    assert_eq!(value, Value::Int(15));
    assert!(
        planned.iter().any(|plan| plan.live),
        "a source pipeline over the live source: {planned:?}"
    );
}

/// The entries of `value`, a collection keyed by `UInt`s, each value rendered, in key order.
fn entries_by_key(value: &Value) -> Vec<(u64, String)> {
    let mut entries: Vec<(u64, String)> = value
        .as_function()
        .iter()
        .map(|binding| match &binding.input {
            Value::UInt(key) => (*key, binding.output.to_string()),
            other => panic!("a collection keyed by a `UInt`: {other:?}"),
        })
        .collect();
    entries.sort();
    entries
}

/// A lookup into a map built over a live source. The map groups the source's keys by value
/// through a `Converse`, whose groups stay open until the source is complete, and its push of a
/// region beneath the values reaches the per-group `sole` through `MapResultWithSource`, which
/// restates every level.
#[rstest_log::rstest]
#[case::one_key(indoc! {"
    out = test_sink()
    m = map([(x, x) for x in source1()])
    out << m[1]
"}, &[])]
#[case::a_key_per_row(indoc! {"
    out = test_sink()
    m = map([(x, x * 10) for x in source1()])
    out << [m[x] for x in source1()]
"}, &[(0, "`some(10)"), (1, "`some(20)"), (2, "`some(30)"), (3, "`some(40)"), (4, "`some(50)")])]
fn a_lookup_into_a_map_over_a_live_source(
    #[case] source: &str,
    #[case] per_key: &[(u64, &str)],
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, _) = dispatched_live(source, rows, two_batches());
    match per_key {
        [] => assert_eq!(value.to_string(), "`some(1)", "{source}"),
        per_key => assert_eq!(
            entries_by_key(&value),
            per_key
                .iter()
                .map(|(key, value)| (*key, value.to_string()))
                .collect::<Vec<_>>(),
            "{source}"
        ),
    }
}

/// A collection per row of a live source, at the `main` output, over two deliveries: each row's
/// value reads a static collection.
#[rstest_log::rstest]
#[case::pairs_per_row(
    "[(x, [y * x for y in [1, 2]]) for x in source1()]",
    &[
        (0, "{1, Function [ 1, 2 ]}"),
        (1, "{2, Function [ 2, 4 ]}"),
        (2, "{3, Function [ 3, 6 ]}"),
        (3, "{4, Function [ 4, 8 ]}"),
        (4, "{5, Function [ 5, 10 ]}")
    ]
)]
#[case::sum_per_row(
    "[x + sum([y * x for y in [1, 2]]) for x in source1()]",
    &[(0, "4"), (1, "8"), (2, "12"), (3, "16"), (4, "20")]
)]
#[case::filter_on_a_sum(
    "[x for x in source1() if sum([y for y in [1, 2] if y == x]) > 0]",
    &[(0, "1"), (1, "2")]
)]
fn a_static_collection_per_row_of_a_live_source_at_main(
    #[case] source: &str,
    #[case] expected: &[(u64, &str)],
    #[values(1, usize::MAX)] rows: usize,
) {
    let live = dispatched_live_main(source, rows, two_batches());
    assert_eq!(
        entries_by_key(&live.value),
        expected
            .iter()
            .map(|(key, value)| (*key, value.to_string()))
            .collect::<Vec<_>>(),
        "{source}"
    );
}

/// A let-bound map over a live source is a `Memo` keyed by the source's keys, which the run
/// notifies of each delivery. The sink reads the map through its feed's `Memo`, which is keyed by
/// the sink's one row: that `Memo` keeps the row open and reads the row again at each of the map's
/// pushes.
#[rstest_log::rstest]
fn a_let_bound_map_over_a_live_source(#[values(1, usize::MAX)] rows: usize) {
    let (value, planned) = dispatched_live(
        indoc! {"
            out = test_sink()
            ys = [x * 2 for x in source1()]
            out << ys
        "},
        rows,
        two_batches(),
    );
    // A collection's entries are keyed, and their order says nothing.
    let mut pairs: Vec<(Value, Value)> = value
        .as_function()
        .iter()
        .map(|binding| (binding.input.clone(), binding.output.clone()))
        .collect();
    pairs.sort_by_key(|(key, _)| match key {
        Value::UInt(key) => *key,
        other => panic!("the map is keyed by the source's keys: {other:?}"),
    });
    assert_eq!(
        pairs,
        (0..5)
            .map(|key| (Value::UInt(key), Value::Int(2 * (key as i64 + 1))))
            .collect::<Vec<_>>()
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && plan.name.starts_with("Memo")),
        "the map's `Memo` is the live source pipeline: {planned:?}"
    );
    assert!(
        planned
            .iter()
            .any(|plan| !plan.live && !plan.whole && plan.open && plan.name.starts_with("Memo")),
        "the feed's `Memo` keeps open rows: {planned:?}"
    );
}

/// A feed of a map over a live source is keyed by the sink's one row, which holds the whole map, so
/// a delivery's keys reach the pipeline above the source widened. The pipeline reads its input
/// whole once the source yields everything.
#[rstest_log::rstest]
#[case::every_key(
    indoc! {"
        out = test_sink()
        out << [x * 2 for x in source1()]
    "},
    (0..5).map(|key| (key, 2 * (key as i64 + 1))).collect(),
)]
#[case::filtered(
    indoc! {"
        out = test_sink()
        out << [x * 2 for x in source1() if x > 2]
    "},
    (2..5).map(|key| (key, 2 * (key as i64 + 1))).collect(),
)]
fn a_feed_of_a_map_over_a_live_source(
    #[case] source: &str,
    #[case] expected: Vec<(u64, i64)>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), expected);
    assert!(
        planned.iter().any(|plan| plan.live && plan.whole),
        "a live pipeline reads its input whole: {planned:?}"
    );
}

/// A sink fed from two sites reads a union of the two feeds, one arm each, so each site's arrivals
/// reach the pipeline above the source widened under its own arm, and the pipeline reads both arms
/// whole.
#[rstest_log::rstest]
fn a_sink_fed_twice_over_a_live_source(#[values(1, usize::MAX)] rows: usize) {
    let (written, _) = dispatched_live_written(
        indoc! {"
            out = test_sink()
            out << [x * 2 for x in source1()]
            out << [x + 100 for x in source1()]
        "},
        rows,
        two_batches(),
    );
    let mut arms: Vec<Vec<(u64, i64)>> = written
        .as_function()
        .iter()
        .map(|arm| keyed_ints(&arm.output))
        .collect();
    arms.sort();
    assert_eq!(
        arms,
        [
            (0..5)
                .map(|key| (key, 2 * (key as i64 + 1)))
                .collect::<Vec<_>>(),
            (0..5).map(|key| (key, key as i64 + 101)).collect(),
        ]
    );
}

/// `batches` deliveries of `source1`, one key each, valued one more than the key.
fn one_key_batches(batches: u64) -> Vec<Batch> {
    (0..batches)
        .map(|key| {
            let complete = match key + 1 == batches {
                true => crate::interpreter::Predicate::True,
                false => crate::interpreter::Predicate::at_or_below(Value::UInt(key)),
            };
            (
                vec![(Value::UInt(key), Value::Int(key as i64 + 1))],
                complete,
            )
        })
        .collect()
}

/// A source delivering in more passes than the dispatcher keeps epochs in flight runs one epoch
/// per delivery, each finished before the next is sealed.
#[test]
fn a_sum_over_more_deliveries_than_epochs_in_flight() {
    let (value, _) = dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum(source1())
        "},
        1,
        one_key_batches(10),
    );
    assert_eq!(value, Value::Int(55));
}

/// Two pipelines over one source are each notified of every delivery.
#[test]
fn two_sums_over_one_live_source() {
    let (value, planned) = dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum(source1()) + sum([x * 2 for x in source1()])
        "},
        1,
        two_batches(),
    );
    assert_eq!(value, Value::Int(45));
    assert_eq!(
        planned.iter().filter(|plan| plan.live).count(),
        2,
        "two live source pipelines: {planned:?}"
    );
}

/// A cross product of a live source with itself is keyed by pairs of its positions, which no
/// notification of one source's positions names.
#[test]
#[should_panic(expected = "which is no one live source's positions")]
fn a_cross_product_of_live_sources_is_refused() {
    dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum([x * y for x in source1() for y in source1()])
        "},
        1,
        two_batches(),
    );
}
/// A reader whose build edge reads a pipeline with a live source beneath it reads its input whole
/// once every epoch has run, since that pipeline finishes epochs before its input is whole: a
/// lookup of a live store's final value, and of an aggregate over a live map.
#[rstest_log::rstest]
#[case::a_live_store(indoc! {"
    out = test_sink()
    ys = [1, 2]
    pool: Mut(Int, Txn) := 100
    for r in source1():
        with begin():
            pool := pool - r
    zs = [y + await_final(pool) for y in ys]
    out << sum(zs)
"}, 173)]
#[case::a_live_map(indoc! {"
    out = test_sink()
    ys = [1, 2]
    xs = [x * 2 for x in source1()]
    zs = [y + sum(xs) for y in ys]
    out << sum(zs)
"}, 63)]
fn a_reader_of_a_live_pipeline_through_a_build_edge(
    #[case] source: &str,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, _) = dispatched_live(source, rows, two_batches());
    assert_eq!(value, Value::Int(expected));
}

/// A breaker whose chain reads a live source and a pipeline takes the source's arrivals and keeps
/// open rows (`Dispatcher::take_arrivals`): each row adds the sum of `ys`, and a row consumed
/// before the sum is final is read again at its push.
#[rstest_log::rstest]
fn a_reader_of_a_live_source_and_a_pipeline(#[values(1, usize::MAX)] rows: usize) {
    let (value, planned) = dispatched_live(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            out << sum([x + sum(ys) for x in source1()])
        "},
        rows,
        two_batches(),
    );
    assert_eq!(value, Value::Int(30));
    assert!(
        planned.iter().any(|plan| plan.live && plan.open),
        "the pipeline over the source keeps open rows: {planned:?}"
    );
}

/// What a dispatched run hands a `main` output: it keeps each answer as a test sink does, counts
/// the outermost keys the answers have held, and lists the answers pull mode would print.
#[derive(Default)]
struct MainAnswers {
    kept: crate::interpreter::TestSink,
    keys: std::sync::atomic::AtomicUsize,
    printed: std::sync::Mutex<Vec<crate::interpreter::Tile>>,
}

/// Whether the driver prints `tile`, as `pull_main` and the dispatched run's printer decide: it
/// holds a key or a value, or it is terminal.
fn is_printed(tile: &crate::interpreter::Tile) -> bool {
    !tile.is_empty() || tile.is_terminal()
}

impl crate::interpreter::DataSink for MainAnswers {
    fn process(&self, tile: &crate::interpreter::Tile) {
        if let crate::interpreter::Tile::DataFunction {
            domain, deleted, ..
        } = tile
        {
            self.keys.fetch_add(
                domain.len() - deleted.len(),
                std::sync::atomic::Ordering::SeqCst,
            );
        }
        if is_printed(tile) {
            self.printed
                .lock()
                .expect("no answer panics")
                .push(tile.clone());
        }
        self.kept.process(tile);
    }
}

/// What [`dispatched_live_main`] observed of a run.
struct LiveMain {
    /// The `main` output's value.
    value: Value,
    /// What the run planned.
    planned: Vec<Planned>,
    /// The outermost keys the `main` output had been handed each time the run had nothing to do,
    /// before the next delivery.
    handed: Vec<usize>,
    /// The answers the driver prints ([`is_printed`]), in the order they were handed.
    printed: Vec<crate::interpreter::Tile>,
}

/// `source`, whose `main` output reads the live source `source1`, compiled and run through the
/// dispatcher at morsels of `rows`, the source fed `batches` as [`dispatched_live`] feeds them.
fn dispatched_live_main(source: &str, rows: usize, batches: Vec<Batch>) -> LiveMain {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let feed = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
        ),
    ));
    ctx.register_source(feed.clone());
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let mut batches = batches.into_iter();
    let deliver = |batch: Option<Batch>| {
        let Some((entries, complete)) = batch else {
            panic!("{source}: the run waits after the last batch")
        };
        let mut feed = feed.borrow_mut();
        feed.add_data(&entries);
        feed.set_yield_predicate(complete);
    };
    deliver(batches.next());
    let main = std::sync::Arc::new(MainAnswers::default());
    let mut handed = Vec::new();
    let planned = crate::interpreter::dispatcher::run_program_into(
        &mut program,
        rows,
        main.clone(),
        &mut || {
            handed.push(main.keys.load(std::sync::atomic::Ordering::SeqCst));
            deliver(batches.next())
        },
    )
    .unwrap_or_else(|refused| panic!("{refused}"));
    let producer = program
        .outputs
        .iter()
        .find(|output| output.is_main())
        .and_then(|output| output.producer.as_ref())
        .unwrap_or_else(|| panic!("{source}: the run hands the `main` output's producer back"));
    assert!(
        producer.obsolete_guard().is_universal(),
        "{source}: the run releases the `main` output's producer whole: {planned:?}"
    );
    let value = main
        .kept
        .value()
        .unwrap_or_else(|error| panic!("{source}: the `main` output: {error:?}"));
    let printed = std::mem::take(&mut *main.printed.lock().expect("no answer panics"));
    LiveMain {
        value,
        planned,
        handed,
        printed,
    }
}

/// `source`, whose `main` output reads the live source `source1`, compiled and run in pull mode,
/// the source fed `batches` one at a time, the `main` output pulled at the universal guard and
/// released at its answer once the scheduler has run out of work after each: the answers the
/// driver prints ([`is_printed`]).
fn pulled_live_main(source: &str, batches: Vec<Batch>) -> Vec<crate::interpreter::Tile> {
    let mut ctx = GlobalContext::default();
    let feed = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
        ),
    ));
    ctx.register_source(feed.clone());
    let mut program = compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let mut producer = program
        .outputs
        .iter_mut()
        .find(|output| output.is_main())
        .and_then(|output| output.producer.take())
        .unwrap_or_else(|| panic!("{source} has a `main` output"));
    let mut printed = Vec::new();
    for (entries, complete) in batches {
        feed.borrow_mut().add_data(&entries);
        feed.borrow_mut().set_yield_predicate(complete);
        for _ in 0..1000 {
            ctx.scheduler().check_for_notifications();
        }
        let tile = producer.get(producer.tiling().universal_guard());
        producer.release(tile.to_guard());
        if is_printed(&tile) {
            printed.push(tile);
        }
    }
    assert!(
        printed
            .last()
            .is_some_and(crate::interpreter::Tile::is_terminal),
        "{source}: pull mode's last pull answers a terminal tile"
    );
    printed
}

/// [`one_key_batches`] with a last delivery that adds no key and calls the source complete.
fn one_key_batches_then_empty(batches: u64) -> Vec<Batch> {
    let mut all = one_key_batches(batches);
    all[batches as usize - 1].1 =
        crate::interpreter::Predicate::at_or_below(Value::UInt(batches - 1));
    all.push((Vec::new(), crate::interpreter::Predicate::True));
    all
}

/// The `main` output is handed, one delivery at a time, the answers pull mode prints after each:
/// a key the filter drops and a delivery of no key hand an answer the driver does not print, a
/// sum is printed once its source is complete, and the last answer is terminal. A row that reads a
/// sum is answered once the sum is final: a sum over a literal before the first delivery's rows,
/// and a sum over the live source at the last delivery, whose epoch reads the earlier rows again
/// after its own, so that case compares the answers in key order.
#[rstest_log::rstest]
#[case::a_map("[x * 10 for x in source1()]", false)]
#[case::a_filter_dropping_a_key("[x for x in source1() if x != 2]", false)]
#[case::a_sum("sum(source1())", false)]
#[case::a_filter_reading_a_sum("[x for x in source1() if sum([1, 2, 3]) > 5]", false)]
#[case::a_map_reading_a_sum("[x + sum([1, 2]) for x in source1()]", false)]
#[case::a_filter_reading_a_live_sum("[x for x in source1() if sum(source1()) > 2]", true)]
fn the_main_output_prints_what_pull_mode_prints_per_delivery(
    #[case] source: &str,
    #[case] reads_again: bool,
    #[values(one_key_batches(3), one_key_batches_then_empty(3))] batches: Vec<Batch>,
    #[values(1, usize::MAX)] rows: usize,
) {
    // An epoch that reads rows again merges them after its own, so where a case does, the answers
    // are compared in key order.
    let in_key_order = |answers: Vec<crate::interpreter::Tile>| -> Vec<_> {
        match reads_again {
            true => answers
                .into_iter()
                .map(crate::interpreter::sort_function_by_domain)
                .collect(),
            false => answers,
        }
    };
    let pulled = pulled_live_main(source, batches.clone());
    let dispatched = dispatched_live_main(source, rows, batches);
    assert_eq!(in_key_order(dispatched.printed), in_key_order(pulled));
}

/// A map or a filter over a live source at the `main` output takes each delivery's keys as they
/// arrive: the run places the entry before the `main` output's consumer in the output's pipeline,
/// so a push of a delivery's keys reaches it restated, and the output is handed the first
/// delivery's keys before the second arrives.
#[rstest_log::rstest]
#[case::a_map(
    "[x * 10 for x in source1()]",
    (0..5).map(|key| (key, 10 * (key as i64 + 1))).collect(),
    3
)]
#[case::a_filter(
    "[x for x in source1() if x > 2]",
    (2..5).map(|key| (key, key as i64 + 1)).collect(),
    1
)]
fn a_map_over_a_live_source_at_main(
    #[case] source: &str,
    #[case] expected: Vec<(u64, i64)>,
    #[case] first: usize,
    #[values(1, usize::MAX)] rows: usize,
) {
    let LiveMain {
        value,
        planned,
        handed,
        ..
    } = dispatched_live_main(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), expected);
    assert_eq!(
        handed,
        [first],
        "the first delivery's keys reach the `main` output before the second delivery"
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && !plan.whole && plan.name.starts_with("SinkBreaker")),
        "the `main` output's pipeline is notified of each delivery: {planned:?}"
    );
}

/// A filter over a live source that reads a sum takes the source's arrivals and keeps open rows
/// (`Dispatcher::take_arrivals`). A sum over a literal is final in the first epoch, so the first
/// delivery's rows are answered in it, read again at the sum's push where they arrived before. A
/// sum over the live source is final only at the last delivery, so the first delivery's rows stay
/// open until then and are read again at its push.
#[rstest_log::rstest]
#[case::a_sum_over_a_literal("[x for x in source1() if sum([1, 2, 3]) > 5]", 3)]
#[case::a_sum_over_the_source("[x for x in source1() if sum(source1()) > 2]", 0)]
fn a_filter_over_a_live_source_reading_a_sum(
    #[case] source: &str,
    #[case] first: usize,
    #[values(1, usize::MAX)] rows: usize,
) {
    let LiveMain {
        value,
        planned,
        handed,
        ..
    } = dispatched_live_main(source, rows, two_batches());
    assert_eq!(
        keyed_ints(&value),
        (0..5).map(|key| (key, key as i64 + 1)).collect::<Vec<_>>()
    );
    assert_eq!(
        handed,
        [first],
        "the `main` output is handed the first delivery's rows once the sum is final"
    );
    assert!(
        planned.iter().any(|plan| plan.live
            && !plan.whole
            && plan.open
            && plan.name.starts_with("SinkBreaker")),
        "the `main` output's pipeline takes arrivals and keeps open rows: {planned:?}"
    );
}

/// The readers of a pipeline with a live source beneath it read no input whole: the inner
/// comprehension's memo, the per-row sum and the outer comprehension's memo each keep open rows,
/// and a push reads again the rows it names (`src/interpreter/design-operators.md`, "Reading rows
/// again").
#[rstest_log::rstest]
fn readers_over_a_live_pipeline_keep_open_rows(#[values(1, usize::MAX)] rows: usize) {
    let source = indoc! {"
        out = test_sink()
        ys = [y for y in source1()]
        out << [sum([y * x for y in ys]) for x in [1, 2]]
    "};
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), vec![(0, 15), (1, 30)]);
    assert!(
        !planned.iter().any(|plan| plan.whole),
        "no pipeline reads its input whole: {planned:?}"
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.open && plan.name.starts_with("MapAggregate")),
        "the per-row sum keeps open rows: {planned:?}"
    );
    assert_eq!(
        planned.iter().filter(|plan| plan.open).count(),
        3,
        "the two memos and the sum keep open rows: {planned:?}"
    );
}

/// The sums of `a_sum_over_rows_carrying_a_constant` over a live list. The sum's pipeline keeps
/// open rows and reads each row again at its outermost key, above the level the constant applies
/// at, where `MapResultToConst` panics on a pull at or beneath that level, so the values check it
/// (`src/interpreter/design-operators.md`, "Reading rows again").
#[rstest_log::rstest]
#[case::zipped_with_a_constant(
    indoc! {"
        out = test_sink()
        ys = [y for y in source1()]
        k = 10
        out << [sum([y * x + k for y in ys]) for x in [1, 2]]
    "},
    vec![(0, 65), (1, 80)],
)]
#[case::a_constant_under_a_filter(
    indoc! {"
        out = test_sink()
        ys = [y for y in source1()]
        out << [sum([10 for y in ys if y > x]) for x in [1, 2]]
    "},
    vec![(0, 40), (1, 30)],
)]
fn a_sum_over_rows_carrying_a_constant_reading_a_live_list(
    #[case] source: &str,
    #[case] expected: Vec<(u64, i64)>,
    #[values(1, usize::MAX)] rows: usize,
) {
    assert!(
        kinds_beneath(&operator_graph(source, true), "MapAggregate")
            .is_some_and(|kinds| kinds.contains(&"MapResultToConst")),
        "{source}: the `MapAggregate` reads a `MapResultToConst` in its own chain"
    );
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), expected);
    assert!(
        !planned.iter().any(|plan| plan.whole),
        "no pipeline reads its input whole: {planned:?}"
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.open && plan.name.starts_with("MapAggregate")),
        "the per-row sum keeps open rows: {planned:?}"
    );
}

/// The same sums with the source as the rows: the sum's input is keyed by the source's keys, which
/// reach it through the pushes of the live source's `Memo`.
#[rstest_log::rstest]
#[case::zipped_with_a_constant(
    indoc! {"
        out = test_sink()
        k = 10
        out << [sum([y * x + k for y in [1, 2, 3]]) for x in source1()]
    "},
    vec![(0, 36), (1, 42), (2, 48), (3, 54), (4, 60)],
)]
#[case::a_constant_under_a_filter(
    indoc! {"
        out = test_sink()
        out << [sum([10 for y in [1, 2, 3] if y > x]) for x in source1()]
    "},
    vec![(0, 20), (1, 10), (2, 0), (3, 0), (4, 0)],
)]
fn a_sum_over_live_rows_carrying_a_constant(
    #[case] source: &str,
    #[case] expected: Vec<(u64, i64)>,
    #[values(1, usize::MAX)] rows: usize,
) {
    assert!(
        kinds_beneath(&operator_graph(source, true), "MapAggregate")
            .is_some_and(|kinds| kinds.contains(&"MapResultToConst")),
        "{source}: the `MapAggregate` reads a `MapResultToConst` in its own chain"
    );
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), expected);
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && plan.name.starts_with("Memo")),
        "the source's `Memo` is the live pipeline: {planned:?}"
    );
    assert!(
        !planned.iter().any(|plan| plan.whole),
        "no pipeline reads its input whole: {planned:?}"
    );
}

/// The same filter fed to a sink. The comprehension is the constant of the `()` row above it, so
/// a delivery's keys reach the sink's pipeline widened, and that pipeline reads its input whole
/// once the source yields everything, keeping open rows for the sum's push.
#[rstest_log::rstest]
fn a_filter_over_a_live_source_reading_a_sum_into_a_sink(#[values(1, usize::MAX)] rows: usize) {
    let source = indoc! {"
        out = test_sink()
        out << [x for x in source1() if sum([1, 2, 3]) > 5]
    "};
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(
        keyed_ints(&value),
        (0..5).map(|key| (key, key as i64 + 1)).collect::<Vec<_>>()
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && plan.whole && plan.open),
        "a pipeline over the source reads it whole and keeps open rows: {planned:?}"
    );
}

/// A sum whose rows read a sum over the same live source: the outer sum's pipeline takes the
/// source's arrivals and is not ordered, so its open rows are read again when the inner sum is
/// final, at the last delivery.
#[rstest_log::rstest]
fn a_sum_over_a_live_source_reading_a_sum_over_it(#[values(1, usize::MAX)] rows: usize) {
    let (value, _) = dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum([x for x in source1() if sum(source1()) > 2])
        "},
        rows,
        two_batches(),
    );
    assert_eq!(value, Value::Int(15));
}

/// Why the planner refuses `source`, which reads the live source `source1`.
fn live_refusal(source: &str) -> Refused {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    ctx.register_source(std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
        ),
    )));
    ctx.register_test_sink("out");
    let mut program = compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let main = std::sync::Arc::new(MainAnswers::default());
    match crate::interpreter::dispatcher::run_program_into(&mut program, 1, main, &mut || {
        panic!("{source}: a refused run polls nothing")
    }) {
        Err(refused) => refused,
        Ok(planned) => panic!("{source} is refused: {planned:?}"),
    }
}

/// A pipeline notified of a live source's arrivals takes no other package, so the planner refuses
/// one whose input has rows no arrival names: a range no live source yields, as a static arm of a
/// concatenation, or a pipeline it reads whose pushes arrive as its own keys, as a let-bound arm or
/// a field of a let-bound record, whose memo holds one value.
#[rstest_log::rstest]
#[case::a_static_arm_reading_a_sum("[x for x in source1()] ++ [y + sum([10, 20]) for y in [0]]")]
#[case::a_sum_of_a_static_arm_reading_a_sum(
    "sum([x for x in source1()] ++ [y + sum([10, 20]) for y in [0]])"
)]
#[case::a_sum_of_an_arm_reading_a_sum(
    "sum([x + sum([10, 20]) for x in source1()] ++ [y for y in [100]])"
)]
#[case::a_sum_of_a_static_arm("sum([x for x in source1()] ++ [y * 2 for y in [10, 20]])")]
#[case::a_let_bound_arm(indoc! {"
    ys = [y * 10 for y in [1, 2]]
    [x for x in source1()] ++ ys
"})]
#[case::a_field_of_a_let_bound_record(indoc! {"
    r = (a=[y * 2 for y in [10, 20]], b=1)
    sum([x for x in source1()] ++ r.a) + r.b
"})]
fn a_pipeline_notified_of_arrivals_with_rows_no_arrival_names_is_refused(#[case] source: &str) {
    let refused = live_refusal(source);
    assert!(
        refused.to_string().contains("which no arrival names")
            || refused.to_string().contains("whose rows no arrival names"),
        "{refused}"
    );
}

/// A loop over a live source whose body reads a sum: the loop's scope reads the sum's pipeline
/// beside the source, and a scope takes no arrivals beside the pipelines it reads.
#[test]
fn a_loop_over_a_live_source_reading_a_pipeline_is_refused() {
    let refused = live_refusal(indoc! {"
        out = test_sink()
        ys = [1, 2]
        total := 0
        for x in source1():
            total += x + sum(ys)
        out << total
    "});
    assert!(
        refused.to_string().contains("as a store or a loop's scope"),
        "{refused}"
    );
}

/// A sum or a loop over a live source at the `main` output: the run notifies the aggregate's or
/// the loop's pipeline of each delivery, beneath the output's pipeline, and the output is handed
/// the scalar once the source yields everything.
#[rstest_log::rstest]
#[case::a_sum("sum(source1())", "Aggregate")]
#[case::a_loop(
    indoc! {"
        total := 0
        for x in source1():
            total += x
        total
    "},
    "LoopScope"
)]
fn a_sum_over_a_live_source_at_main(
    #[case] source: &str,
    #[case] live: &str,
    #[values(1, usize::MAX)] rows: usize,
) {
    let LiveMain { value, planned, .. } = dispatched_live_main(source, rows, two_batches());
    assert_eq!(value, Value::Int(15));
    assert!(
        planned
            .iter()
            .all(|plan| plan.live == plan.name.starts_with(live)),
        "the live source pipeline is the {live}'s alone: {planned:?}"
    );
}

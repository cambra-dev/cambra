//! Compiled programs run end to end through `crate::interpreter::dispatcher::run_program`: the
//! dispatcher drives every pipeline breaker in the sink's producer chain on one thread, and the
//! sink's own pipeline pulls its producer one package at a time. Each answer is checked against
//! a fixed expected value.

use indoc::{formatdoc, indoc};

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::Consumer;
use crate::interpreter::Value;
use crate::interpreter::dispatcher::{Planned, run_program};

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
        consumer
            .borrow_mut()
            .invalidate(&crate::interpreter::Projection::Everything);
    }
    ctx.source_registry().notify_changes();
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

/// A group-by's memo reads its input's memo and the `Converse` keying the groups, which reads that
/// memo too and is no breaker. The input memo's push reaches the group-by's memo widened, so it
/// parks its rows until that memo has decided them.
#[test]
fn a_group_by() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3, 4]
        g = groupby(xs, \\x -> x > 2)
        out << sum([sum(v) for v in g])
    "};
    answers(source, "10", &["Memo"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("Memo") && !plan.whole && plan.held),
        "the group-by's memo parks its rows: {planned:?}"
    );
}

/// The two arms of a concatenation of comprehensions push under their own tags, so the sum reads
/// both pipelines' pushes, parked until each arm has decided its rows, and no region at the start.
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
            && plan.held
            && !plan.started),
        "the sum reads both arms' pushes: {planned:?}"
    );
}

/// A sum read inside another comprehension: the outer sum's pipeline reads the inner sum's and the
/// list's. The inner sum's push names every key of the outer sum's input, which the list's pushes
/// name too, so the outer sum parks the rows the list's pushes bring until the inner sum is
/// decided, and reads each once.
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
        planned.iter().any(|plan| plan.held) && !planned.iter().any(|plan| plan.whole),
        "the outer sum parks its rows, and no pipeline reads its input whole: {planned:?}"
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
    assert!(!sink.whole && sink.held, "{sink:?}");
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
    assert!(!sink.whole && sink.held, "{sink:?}");
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
        &["InductionRequest", "SinkBreaker"],
    );
}

/// The inner pipelines of the one loop scope `planned` holds.
fn rounds(planned: &[Planned]) -> &[Planned] {
    let scopes: Vec<_> = planned
        .iter()
        .filter(|plan| plan.name.starts_with("InductionRequest"))
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
    answers(source, "5", &["InductionRequest", "SinkBreaker"]);
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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
    answers(source, "6", &["Memo", "InductionRequest", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("InductionRequest") && plan.whole),
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
        &["InductionRequest", "Aggregate", "SinkBreaker"],
    );
}

/// A reader inside a loop's scope whose pushes can name one row twice parks its rows until the
/// pipelines it reads have decided them, as one in the run's dispatcher does, and reads no input
/// whole in pull mode.
#[test]
fn a_reader_inside_a_loops_scope_parks() {
    let source = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            for y in [1, 2]:
                total += x * y
        out << total
    "};
    answers(source, "18", &["InductionRequest", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let inner = rounds(&planned);
    assert!(
        inner.iter().any(|plan| plan.held) && !inner.iter().any(|plan| plan.whole),
        "a reader in the outer loop's scope parks, and none reads whole: {planned:?}"
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
    answers(source, "18", &["InductionRequest", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        rounds(&planned).iter().any(|plan| plan
            .name
            .starts_with("InductionRequest(InductionStore")
            && !plan.rounds.is_empty()),
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
        &["InductionRequest", "SinkBreaker"],
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
        &["InductionRequest", "SinkBreaker"],
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
}

/// A loop nested twice over nested collections: each inner loop iterates the element of the loop
/// around it. The middle loop's store closes a row once the innermost store states that row
/// complete, which it does once its body states every position beneath the row complete.
#[test]
fn a_loop_nested_twice_over_nested_collections() {
    answers(
        indoc! {"
            out = test_sink()
            acc := 0
            for xss in [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]:
                for xs in xss:
                    for x in xs:
                        acc := acc + x
            out << acc
        "},
        "36",
        &["InductionRequest", "SinkBreaker"],
    );
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
        &["InductionRequest", "SinkBreaker"],
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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
#[case::an_inner_source_of_sums_over_the_outer_position(indoc! {"
    out = test_sink()
    ws = [1, 2, 3]
    qs = [1, 2]
    total := 0
    for x in [1, 2]:
        acc := 0
        for z in [sum([w * x * q for w in ws]) for q in qs]:
            acc += z
        total += acc
    out << total
"}, "54")]
fn a_nested_loop_body_reading(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
}

/// A store per row of a comprehension, from a function whose loop runs once per row, runs as a
/// loop's scope in the run's dispatcher, its rounds at the paths of the row and the position.
#[rstest_log::rstest]
#[case::one_loop(indoc! {"
    def fold_by(items) => Int:
        n := 0
        for x in items:
            n := n + x
        n

    [fold_by(r) for r in [[1, 2], [3, 4]]]
"}, "Function [ 3, 7 ]")]
#[case::a_nested_loop(indoc! {"
    def fold_by(items) => Int:
        n := 0
        for x in items:
            for y in [1, 2]:
                n := n + x * y
        n

    [fold_by(r) for r in [[1, 2], [3, 4]]]
"}, "Function [ 9, 21 ]")]
#[case::a_body_mapping_a_comprehension(indoc! {"
    def g(items) => Int:
        n := 0
        for x in items:
            n += sum([z * x for z in [1, 2]])
        n

    [g(r) for r in [[1, 2], [3, 4]]]
"}, "Function [ 9, 21 ]")]
fn a_store_per_row_of_a_comprehension(
    #[case] source: &str,
    #[case] expected: &str,
    #[values(1, 3, usize::MAX)] rows: usize,
) {
    let loaded = LoadedProgram::test(source);
    let mut ctx = GlobalContext::default();
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let run = run_program(&mut program, rows).unwrap_or_else(|refused| panic!("{refused}"));
    assert!(
        run.planned
            .iter()
            .any(|plan| plan.name.starts_with("InductionRequest")),
        "the store runs as a loop's scope: {:?}",
        run.planned
    );
    let sink = crate::interpreter::TestSink::default();
    crate::interpreter::DataSink::process(&sink, &run.main.expect("the run answers `main`"));
    let value = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(value.to_string(), expected, "{source} at morsels of {rows}");
}

/// Compilation subscribes sinks without running them; the dispatcher delivers their values.
#[test]
fn compiling_a_program_does_not_execute_its_sinks() {
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    let mut program = compile_program(
        &mut ctx,
        &LoadedProgram::test("out = test_sink()\nout << 3\n"),
        Box::new(|| {}),
    )
    .unwrap();
    assert!(matches!(
        sink.value(),
        Err(crate::interpreter::test_sink::SinkReadError::NothingWritten)
    ));
    run_program(&mut program, 1).unwrap();
    assert!(sink.value().is_ok());
}

/// Of two loops in one loop's body, the first runs in the scope of the second, which reads its
/// result as its seed. Its store has one row level above its positions, the outer loop's, so its
/// rounds pull its cycle at the keys of level 1, where the map over a comprehension restates them,
/// although its scope runs two deep.
#[rstest_log::rstest]
#[case::one_row(indoc! {"
    out = test_sink()
    acc := 0
    for r in [1]:
        for x in [1]:
            acc += sum([z * x for z in [1]])
        for y in [1]:
            acc += y
    out << acc
"}, "2")]
#[case::two_rows(indoc! {"
    out = test_sink()
    acc := 0
    for r in [1, 2]:
        for x in [1, 2]:
            acc += sum([z * x for z in [1, 2]])
        for y in [1, 2]:
            acc += y * r
    out << acc
"}, "27")]
fn a_map_in_the_first_of_two_inner_loops(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["InductionRequest", "SinkBreaker"]);
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

/// A transaction store whose seed reads a pipeline: a sum, and the final value of another
/// transaction store, as phase separation seeds one (`docs/chl-spec.md`, "8.6 `await_final`").
/// The store reads its seed by pull when it opens, so a push from the seed's pipeline stops in
/// front of the store, and the store's pipeline reads it.
#[rstest_log::rstest]
#[case::a_sum(indoc! {"
    out = test_sink()
    ys = [1, 2]
    pool: Mut(Int, Txn) := sum(ys)
    for r in [1, 2]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "0")]
#[case::another_stores_final_value(indoc! {"
    out = test_sink()
    a: Mut(Int, Txn) := 100
    for r in [1, 2]:
        with begin():
            a := a - r
    b: Mut(Int, Txn) := await_final(a)
    for s in [1, 2]:
        with begin():
            b := b + s
    out << await_final(b)
"}, "100")]
fn a_transaction_seeded_from_a_pipeline(#[case] source: &str, #[case] expected: &str) {
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
            pool := pool - r
    for r in [20]:
        with begin():
            pool := pool - r
    for r in [r for r in [40, 5] if r > 10]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "-20")]
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
#[case::seeded_from_a_pipeline(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum([y * 2 for y in [1, 2]]) + 100
    for r in [60]:
        with begin():
            pool := pool - r
    for r in [50]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "-4")]
#[case::seeded_from_a_sum(indoc! {"
    out = test_sink()
    ys = [1, 2]
    pool: Mut(Int, Txn) := sum(ys)
    for r in [1]:
        with begin():
            pool := pool - r
    for r in [1]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "1")]
#[case::a_writer_over_a_concatenation(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [1, 2] ++ [3]:
        with begin():
            pool := pool - r
    for r in [5]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "89")]
#[case::two_writers_over_concatenations(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [1] ++ [2, 3]:
        with begin():
            pool := pool - r
    for r in [10] ++ [20]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, "64")]
fn a_transaction_store_of_several_writers(#[case] source: &str, #[case] expected: &str) {
    answers(source, expected, &["Commit", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let writers = source.matches("with begin()").count();
    let stores = source.matches(", Txn) :=").count();
    assert_eq!(
        planned
            .iter()
            .filter(|plan| plan.name.starts_with("Commit"))
            .count(),
        writers + stores,
        "a store is the breaker of one pipeline per writer and one for its seeds: {planned:?}"
    );
}

/// Final balances admitted by serially attempting every withdrawal in any order.
fn serial_withdrawal_balances(
    balance: i64,
    remaining: &mut Vec<i64>,
    answers: &mut std::collections::BTreeSet<i64>,
) {
    if remaining.is_empty() {
        answers.insert(balance);
        return;
    }
    for at in 0..remaining.len() {
        let amount = remaining.remove(at);
        serial_withdrawal_balances(
            if amount <= balance {
                balance - amount
            } else {
                balance
            },
            remaining,
            answers,
        );
        remaining.insert(at, amount);
    }
}

/// Conflicting writers serialize without comparing their source domains. The result is one
/// admitted by a serial execution of all withdrawals, with no overdraft or lost transaction.
#[rstest_log::rstest]
#[case::a_uint_writer_beside_a_concatenation("", "[60] ++ [10]", "[50]")]
#[case::a_concatenation_beside_a_uint_writer("", "[50]", "[60] ++ [10]")]
#[case::two_concatenations("", "[60] ++ [10]", "[50] ++ [5]")]
#[case::uint_items_beside_a_concatenation("", "[60] ++ [10]", "[50, 30]")]
#[case::concatenations_of_different_depth("xs = [60] ++ [10]", "xs ++ [5]", "[50] ++ [20]")]
#[case::three_sides_beside_two("", "[60] ++ [10] ++ [5]", "[50] ++ [20]")]
#[case::record_beside_uint("", "[r + y for r in [60, 10] for y in [0]]", "[50]")]
#[case::uint_beside_record("", "[50]", "[r + y for r in [60, 10] for y in [0]]")]
#[case::two_records(
    "",
    "[r + y for r in [60, 10] for y in [0]]",
    "[r + y for r in [50, 5] for y in [0]]"
)]
#[case::records_of_different_widths(
    "",
    "[r + y for r in [60, 10] for y in [0]]",
    "[r + y for r in [50, 5] for y in [0, 0]]"
)]
#[case::record_beside_tagged("", "[r + y for r in [60, 10] for y in [0]]", "[50] ++ [5]")]
#[case::records_of_different_arities(
    "",
    "[r + y for r in [60, 10] for y in [0]]",
    "[r + y + z for r in [50, 5] for y in [0] for z in [0, 0]]"
)]
fn several_writers_serialize_ready_proposals(
    #[case] prelude: &str,
    #[case] first: &str,
    #[case] second: &str,
    #[values(1, 2, usize::MAX)] rows: usize,
) {
    let source = formatdoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        {prelude}
        for r in {first}:
            with begin():
                if pool >= r:
                    pool := pool - r
        for r in {second}:
            with begin():
                if pool >= r:
                    pool := pool - r
        out << await_final(pool)
    "};
    let amounts = |items: &str| {
        let pure = formatdoc! {r#"
            out = test_sink()
            {prelude}
            out << {items}
        "#};
        dispatched(&pure, rows)
            .0
            .as_function()
            .iter()
            .map(|binding| {
                let Value::Int(amount) = binding.output else {
                    panic!("integer withdrawal")
                };
                amount
            })
            .collect::<Vec<_>>()
    };
    let mut withdrawals = amounts(first);
    withdrawals.extend(amounts(second));
    let mut possible = std::collections::BTreeSet::new();
    serial_withdrawal_balances(100, &mut withdrawals, &mut possible);
    let actual = dispatched(&source, rows).0;
    let Value::Int(balance) = actual else {
        panic!("integer balance: {actual}")
    };
    assert!(
        possible.contains(&balance),
        "{source} at morsels of {rows}: {balance}, admitted {possible:?}"
    );
}

/// Writers of different lengths commit every withdrawal once in one serial history.
#[rstest_log::rstest]
fn two_ready_writers_over_sources_of_different_lengths(#[values(1, 2, usize::MAX)] rows: usize) {
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
    let mut commits: Vec<_> = written
        .iter()
        .enumerate()
        .flat_map(|(site, values)| values.iter().map(move |&(tick, pool)| (tick, site, pool)))
        .collect();
    commits.sort();
    let mut amounts = [Vec::new(), Vec::new()];
    let mut previous = 100;
    for (at, &(tick, site, pool)) in commits.iter().enumerate() {
        assert_eq!(tick, at as u64 + 1);
        amounts[site].push(previous - pool);
        previous = pool;
    }
    amounts[0].sort();
    assert_eq!(amounts, [vec![10, 20, 30], vec![1]]);
    assert_eq!(previous, 39);
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
                .any(|plan| plan.live && plan.name.starts_with("InductionRequest")),
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
/// store releases them in the pass that delivered them.
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
/// notifies of each delivery. The map's keys reach the loop's drive as its positions, so the loop's
/// scope is notified of each delivery as rounds too, and parks it until the `Memo` has decided it.
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
            .any(|plan| plan.live && plan.name.starts_with("Memo")),
        "the map's `Memo` is a live pipeline: {planned:?}"
    );
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("InductionRequest")
                && plan.live
                && !plan.whole
                && plan.held),
        "the loop's scope takes the deliveries as rounds, parked on the `Memo`: {planned:?}"
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

/// Check commit ticks, serial store reads and the multiset of each writer's withdrawals.
fn assert_serial_withdrawals(written: &Value, initial: i64, expected: &[Vec<i64>]) -> i64 {
    let mut fed: Vec<_> = written
        .as_function()
        .iter()
        .map(|binding| {
            let (Value::Union { tag, inner }, Value::Int(pool)) = (&binding.input, &binding.output)
            else {
                panic!("tagged commit feed: {binding:?}")
            };
            let Value::UInt(tick) = **inner else {
                panic!("commit tick")
            };
            (tick, tag.to_string().parse::<usize>().unwrap(), *pool)
        })
        .collect();
    fed.sort();
    let mut amounts = vec![Vec::new(); expected.len()];
    let mut previous = initial;
    for (at, &(tick, site, pool)) in fed.iter().enumerate() {
        assert_eq!(tick, at as u64 + 1);
        amounts[site].push(previous - pool);
        previous = pool;
    }
    for (mut actual, mut expected) in amounts.into_iter().zip(expected.iter().cloned()) {
        actual.sort();
        expected.sort();
        assert_eq!(actual, expected, "{written:?}");
    }
    previous
}

/// Both writers commit every arrived product row before the next source delivery. Commit
/// ticks form one serial history; each writer withdraws each delivered amount exactly once.
#[rstest_log::rstest]
#[case::uint("source1()", 1, 1)]
#[case::live_outer_product("[r + y for r in source1() for y in [0, 0]]", 2, 1)]
#[case::live_inner_product("[r + y for y in [0, 0] for r in source1()]", 2, 1)]
#[case::filtered_outer_product("[r + y for r in source1() for y in [0, 0] if r > 2]", 2, 3)]
#[case::filtered_inner_product("[r + y for y in [0, 0] for r in source1() if r > 2]", 2, 3)]
fn live_writers_commit_ready_product_rows(
    #[case] items: &str,
    #[case] multiplicity: usize,
    #[case] minimum: i64,
    #[values(two_batches(), one_key_batches(5))] batches: Vec<Batch>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = formatdoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 1000
        for r in {items}:
            with begin():
                pool := pool - r
                out << pool
        for r in {items}:
            with begin():
                pool := pool - r
                out << pool
    "};
    let mut delivered = 0;
    let partial_counts: Vec<_> = batches
        .iter()
        .map(|(entries, _)| {
            delivered += entries
                .iter()
                .filter(|(_, value)| matches!(value, Value::Int(amount) if *amount >= minimum))
                .count();
            delivered * multiplicity * 2
        })
        .collect();
    let mut idle = 0;
    let (written, _) = dispatched_live_observed(&source, rows, batches, |sink, _| {
        let partial = sink.written_so_far();
        let count = match &partial {
            Ok(value) => value.as_function().len(),
            Err(crate::interpreter::test_sink::SinkReadError::NothingWritten) => 0,
            Err(error) => panic!("valid partial feed: {error:?}"),
        };
        assert_eq!(count, partial_counts[idle], "delivery {idle}: {partial:?}");
        idle += 1;
    });
    let expected: Vec<_> = (minimum..=5)
        .flat_map(|r| std::iter::repeat_n(r, multiplicity))
        .collect();
    let final_balance = 1000 - expected.iter().sum::<i64>() * 2;
    assert_eq!(
        assert_serial_withdrawals(&written, 1000, &[expected.clone(), expected]),
        final_balance
    );
}

/// A ready writer progresses while its sibling waits for a product dimension. Subsequent
/// deliveries grow both dimensions without closing either source or replaying an old product row.
#[rstest_log::rstest]
fn a_live_product_writer_beside_an_independent_ready_writer(
    #[values(1, usize::MAX)] rows: usize,
    #[values(false, true)] close_left_first: bool,
) {
    use crate::interpreter::{BaseType, Extent, Predicate, TestDataSource};
    let mut ctx = GlobalContext::default();
    let feeds: Vec<_> = ["source1", "source2"]
        .into_iter()
        .map(|name| {
            let source = std::rc::Rc::new(std::cell::RefCell::new(TestDataSource::new(
                name,
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )));
            ctx.register_source(source.clone());
            source
        })
        .collect();
    let sink = ctx.register_test_sink("out");
    let text = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 1000
        for r in [x * y for x in source1() for y in source2()]:
            with begin():
                pool := pool - r
                out << pool
        for r in source1():
            with begin():
                pool := pool - r
                out << pool
    "};
    let loaded = LoadedProgram::test(text);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap();
    let _operators = ctx.take_operator_map();
    let deliver = |side: usize, key: u64, value: i64| {
        let mut source = feeds[side].borrow_mut();
        source.add_data(&[(Value::UInt(key), Value::Int(value))]);
        source.set_yield_predicate(Predicate::at_or_below(Value::UInt(key)));
    };
    deliver(0, 0, 2);
    let mut idle = 0;
    crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
        let partial = sink
            .written_so_far()
            .expect("ready commits before another source delivers");
        assert_eq!(
            partial.as_function().len(),
            [1, 2, 4, 6, 6][idle],
            "delivery {idle}: {partial:?}"
        );
        match idle {
            0 => deliver(1, 0, 3),
            1 => deliver(0, 1, 5),
            2 => deliver(1, 1, 7),
            3 => feeds[usize::from(!close_left_first)]
                .borrow_mut()
                .set_yield_predicate(Predicate::True),
            4 => feeds[usize::from(close_left_first)]
                .borrow_mut()
                .set_yield_predicate(Predicate::True),
            _ => panic!("run waits after both sources close"),
        }
        idle += 1;
    })
    .unwrap();
    assert_eq!(idle, 5);
    assert!(program.done.try_recv().is_ok());
    assert_eq!(
        assert_serial_withdrawals(
            &sink.value().unwrap(),
            1000,
            &[vec![6, 14, 15, 35], vec![2, 5]]
        ),
        923
    );
}

/// A concatenation writer progresses beside a live writer without comparing their keys.
#[rstest_log::rstest]
fn a_writer_over_a_concatenation_beside_one_over_a_live_source(
    #[values(two_batches(), one_key_batches(5))] batches: Vec<Batch>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in source1():
            with begin():
                pool := pool - r
                out << pool
        for r in [1] ++ [2]:
            with begin():
                pool := pool - r
                out << pool
    "};
    let (written, _) = dispatched_live_written(source, rows, batches);
    assert_eq!(
        assert_serial_withdrawals(&written, 100, &[vec![1, 2, 3, 4, 5], vec![1, 2]]),
        82
    );
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
    let expected_before_next_delivery: Vec<_> = batches
        .iter()
        .take(batches.len() - 1)
        .scan(0, |delivered, (entries, _)| {
            *delivered += entries.len();
            Some(expected[..*delivered].to_vec())
        })
        .collect();
    let mut written_before_next_delivery = Vec::new();
    let (written, _) = dispatched_live_observed(source, rows, batches, |sink, _| {
        assert_eq!(
            sink.value(),
            Err(crate::interpreter::SinkReadError::Incomplete),
            "the feed stays open until the source ends"
        );
        let partial = sink
            .written_so_far()
            .expect("the delivery's feed rows reach the sink before the next delivery");
        written_before_next_delivery.push(keyed_ints(&partial));
    });
    assert_eq!(keyed_ints(&written), expected);
    assert_eq!(
        written_before_next_delivery, expected_before_next_delivery,
        "each delivery's commits reach the sink before the next"
    );
}

/// A feed out of a loop over a live source reads the loop's store, which pushes the positions its
/// rounds decide, so the sink holds part of the feed before the source yields everything.
#[rstest_log::rstest]
#[case::two_batches(two_batches(), vec![(0, 1), (1, 3), (2, 6), (3, 10), (4, 15)])]
#[case::one_key_batches(one_key_batches(4), vec![(0, 1), (1, 3), (2, 6), (3, 10)])]
fn a_feed_out_of_a_loop_over_a_live_source(
    #[case] batches: Vec<Batch>,
    #[case] expected: Vec<(u64, i64)>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        n := 0
        for x in source1():
            n := n + x
            out << n
    "};
    let expected_before_next_delivery: Vec<_> = batches
        .iter()
        .take(batches.len() - 1)
        .scan(0, |delivered, (entries, _)| {
            *delivered += entries.len();
            Some(expected[..*delivered].to_vec())
        })
        .collect();
    let mut written_before_next_delivery = Vec::new();
    let (written, _) = dispatched_live_observed(source, rows, batches, |sink, _| {
        assert_eq!(
            sink.value(),
            Err(crate::interpreter::SinkReadError::Incomplete),
            "the feed stays open until the source ends"
        );
        let partial = sink
            .written_so_far()
            .expect("the delivery's feed rows reach the sink before the next delivery");
        written_before_next_delivery.push(keyed_ints(&partial));
    });
    assert_eq!(keyed_ints(&written), expected);
    assert_eq!(
        written_before_next_delivery, expected_before_next_delivery,
        "each delivery's positions reach the sink before the next"
    );
}

/// A loop over a let-bound list of a live source steps at each position the list has decided,
/// before the source yields everything: the list's memo pushes its decided keys, which the drive
/// reads by pull, and the entry in front of the drive's source records them at the loop's scope as
/// decided positions. What shows the steps is the store's decided region at each idle, which grows
/// a delivery at a time; the values it holds shrink where its readers release them.
#[rstest_log::rstest]
fn a_loop_over_a_let_bound_live_list_steps_before_the_source_ends(
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        xs = [x for x in source1()]
        n := 0
        for x in xs:
            n := n + x
            out << n
    "};
    fn decided_by_store(producer: &mut dyn TileProducer) -> Option<crate::interpreter::TileGuard> {
        if producer.name().starts_with("InductionStore") {
            return producer.as_breaking_mut().map(|store| store.decided());
        }
        let mut decided = None;
        producer.visit_input_producers_mut(&mut |_, input| {
            decided = decided.take().or_else(|| decided_by_store(input));
        });
        decided
    }
    let mut decided = Vec::new();
    let (value, _) = dispatched_live_observed(source, rows, one_key_batches(4), |_, root| {
        let mut root = root.borrow_mut();
        let producer = root.as_mut().expect("a root holds its producer");
        decided.push(decided_by_store(producer.as_mut()).expect("the sink reads the loop's store"));
    });
    assert_eq!(keyed_ints(&value), [(0, 1), (1, 3), (2, 6), (3, 10)]);
    assert!(
        decided.windows(2).all(|pair| {
            super::guard_minus(&pair[0], &pair[1]).is_empty()
                && !super::guard_minus(&pair[1], &pair[0]).is_empty()
        }),
        "the store steps at each delivery, before the source yields everything: {decided:?}"
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
        &["Memo", "InductionRequest", "SinkBreaker"],
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
    dispatched_live_observed(source, rows, batches, |_, _| {})
}

/// [`dispatched_live_written`] with `idle` handed the sink, and the slot of the producer the sink
/// reads, each time the run has nothing to do, before the next delivery.
fn dispatched_live_observed(
    source: &str,
    rows: usize,
    batches: Vec<Batch>,
    mut idle: impl FnMut(&crate::interpreter::TestSink, &crate::interpreter::sinks::ProducerSlot),
) -> (Value, Vec<Planned>) {
    let mut ctx = GlobalContext::default();
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
    let root = program
        .outputs
        .iter()
        .find(|output| output.name == "out")
        .and_then(|output| output.sink_consumer.clone())
        .unwrap_or_else(|| panic!("{source} writes to sink out"))
        .borrow()
        .producer_slot()
        .clone();
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
            idle(&sink, &root);
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

/// A group-by over a live source: its `Converse` restates the source's keys one level in, beneath
/// every value, so each delivery's arrivals reach the group-by's pipeline as a projection there.
#[rstest_log::rstest]
fn a_group_by_over_a_live_source(#[values(1, usize::MAX)] rows: usize) {
    let (value, _) = dispatched_live(
        indoc! {"
            out = test_sink()
            out << sum([sum(g) for g in groupby(source1(), \\x -> x > 2)])
        "},
        rows,
        two_batches(),
    );
    assert_eq!(value, Value::Int(15));
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
            .any(|plan| !plan.live && !plan.whole && plan.held && plan.name.starts_with("Memo")),
        "the feed's `Memo` parks its rows: {planned:?}"
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

/// A feed written in a loop over a live source, at the `main` output: the output is handed each
/// row once, and its value holds every row.
#[rstest_log::rstest]
fn a_feed_written_in_a_loop_over_a_live_source_at_main(#[values(1, usize::MAX)] rows: usize) {
    let live = dispatched_live_main(
        indoc! {"
            out: Feed(_)
            n := 0
            for x in source1():
                n := n + 1
                out << n
            out
        "},
        rows,
        two_batches(),
    );
    assert_eq!(
        keyed_ints(&live.value),
        (0..5).map(|key| (key, key as i64 + 1)).collect::<Vec<_>>()
    );
    let mut handed: Vec<u64> = live
        .printed
        .iter()
        .flat_map(|tile| tile.paths_at(crate::interpreter::CurryLevel::OUTERMOST))
        .map(|path| match path.as_slice() {
            [Value::UInt(key)] => *key,
            other => panic!("a row of the feed is a position: {other:?}"),
        })
        .collect();
    handed.sort_unstable();
    assert_eq!(
        handed,
        (0..5).collect::<Vec<_>>(),
        "each row is handed once"
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

/// A sum over a source delivering one key per pass, over ten passes.
#[test]
fn a_sum_over_ten_deliveries() {
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

#[rstest_log::rstest]
#[case::same_source(indoc! {"
    out = test_sink()
    out << sum([x * y for x in source1() for y in source1()])
"}, 225)]
#[case::static_inner(indoc! {"
    out = test_sink()
    out << sum([x * y for x in source1() for y in [10, 20]])
"}, 450)]
#[case::static_outer(indoc! {"
    out = test_sink()
    out << sum([x * y for x in [10, 20] for y in source1()])
"}, 450)]
#[case::empty_inner(indoc! {"
    out = test_sink()
    out << sum([x * y for x in source1() for y in [y for y in [10, 20] if y > 30]])
"}, 0)]
fn a_live_cartesian_product(
    #[case] source: &str,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
    #[values(two_batches(), one_key_batches(5))] batches: Vec<Batch>,
) {
    let (value, planned) = dispatched_live(source, rows, batches);
    assert!(
        planned
            .iter()
            .all(|pipeline| !pipeline.name.starts_with("IterateExtent#")),
        "iteration runs in its reader's pipeline: {planned:?}"
    );
    assert_eq!(value, Value::Int(expected));
}

#[rstest_log::rstest]
fn a_cartesian_product_of_two_live_sources(
    #[values(1, usize::MAX)] rows: usize,
    #[values(false, true)] together: bool,
    #[values(false, true)] close_left_first: bool,
) {
    use crate::interpreter::{BaseType, Extent, Predicate, TestDataSource};
    let mut ctx = GlobalContext::default();
    let feeds: Vec<_> = ["source1", "source2"]
        .into_iter()
        .map(|name| {
            let source = std::rc::Rc::new(std::cell::RefCell::new(TestDataSource::new(
                name,
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )));
            ctx.register_source(source.clone());
            source
        })
        .collect();
    let sink = ctx.register_test_sink("out");
    let text = indoc! {"
        out = test_sink()
        out << sum([x * y for x in source1() for y in source2()])
    "};
    let mut program = compile_program(&mut ctx, &LoadedProgram::test(text), Box::new(|| {}))
        .expect("the product compiles");
    let _operators = ctx.take_operator_map();
    let mut stages = vec![(vec![1], false, vec![10], false)];
    if together {
        stages.push((vec![2], false, vec![20], false));
    } else {
        stages.push((vec![2], false, vec![], false));
        stages.push((vec![], false, vec![20], false));
    }
    if close_left_first {
        stages.push((vec![3], true, vec![], false));
        stages.push((vec![], true, vec![], true));
    } else {
        stages.push((vec![], false, vec![], true));
        stages.push((vec![3], true, vec![], true));
    }
    let mut stages = stages.into_iter();
    let mut next = [0_u64; 2];
    let mut deliver = || {
        let (a, ac, b, bc) = stages
            .next()
            .expect("the product finishes after the last delivery");
        for (side, (values, closed)) in [(a, ac), (b, bc)].into_iter().enumerate() {
            let entries: Vec<_> = values
                .into_iter()
                .map(|value| {
                    let key = next[side];
                    next[side] += 1;
                    (Value::UInt(key), Value::Int(value))
                })
                .collect();
            let mut feed = feeds[side].borrow_mut();
            feed.add_data(&entries);
            let decided = if closed {
                Predicate::True
            } else if next[side] == 0 {
                Predicate::False
            } else {
                Predicate::at_or_below(Value::UInt(next[side] - 1))
            };
            feed.set_yield_predicate(decided);
        }
    };
    fn product_decided(producer: &mut dyn TileProducer) -> Option<crate::interpreter::TileGuard> {
        if producer.name().starts_with("IterateExtent#")
            && matches!(producer.tiling().domain_extent(), Some(Extent::Record(_)))
        {
            assert!(producer.as_breaking_mut().is_none());
            return Some(producer.get(producer.tiling().universal_guard()).to_guard());
        }
        let mut found = None;
        producer.visit_input_producers_mut(&mut |_, input| {
            if found.is_none() {
                found = product_decided(input);
            }
        });
        found
    }
    let root = program
        .outputs
        .iter()
        .find_map(|output| output.sink_consumer.as_ref())
        .expect("one sink")
        .borrow()
        .producer_slot()
        .clone();
    let mut boundaries = Vec::new();
    deliver();
    let mut next_delivery = || {
        let mut slot = root.borrow_mut();
        let decided = product_decided(slot.as_mut().expect("the sink owns its input").as_mut())
            .expect("the program has a Cartesian iterator");
        assert!(
            !decided.is_empty(),
            "the product progresses before either source closes"
        );
        boundaries.push(decided);
        drop(slot);
        deliver();
    };
    let planned =
        crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut next_delivery)
            .expect("the dispatcher supports both live product dimensions")
            .planned;
    let written = sink.value().expect("the result is final");
    assert_eq!(
        written.as_function()[0].output,
        Value::Int(180),
        "{planned:?}"
    );
    assert!(program.done.try_recv().is_ok());
    assert!(boundaries.len() >= 3);
    assert!(
        boundaries
            .windows(2)
            .all(|pair| super::guard_minus(&pair[0], &pair[1]).is_empty()),
        "product decisions survive output releases and grow at every source boundary"
    );
}

#[rstest_log::rstest]
#[case::live_outer("[(x, y) for x in source1() for y in [10, 20]]")]
#[case::live_inner("[(x, y) for x in [10, 20] for y in source1()]")]
fn a_live_product_as_a_loop_source(#[case] pairs: &str, #[values(1, usize::MAX)] rows: usize) {
    let source = format!(
        indoc! {"
        out = test_sink()
        total := 0
        for pair in {pairs}:
            total += pair.0 * pair.1
        out << total
    "},
        pairs = pairs
    );
    assert_eq!(
        dispatched_live(&source, rows, two_batches()).0,
        Value::Int(450)
    );
}

#[rstest_log::rstest]
fn a_loop_over_two_open_product_dimensions(#[values(1, usize::MAX)] rows: usize) {
    use crate::interpreter::{BaseType, Extent, Predicate};
    let mut ctx = GlobalContext::default();
    let a = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ),
    ));
    let b = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source2",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ),
    ));
    ctx.register_source(a.clone());
    ctx.register_source(b.clone());
    let sink = ctx.register_test_sink("out");
    let source = indoc! {"
        out = test_sink()
        total := 0
        for pair in [(x, y) for x in source1() for y in source2()]:
            total += pair.0 * pair.1
        out << total
    "};
    let mut program =
        compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
    a.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(1)),
        (Value::UInt(1), Value::Int(2)),
    ]);
    a.borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::UInt(1)));
    b.borrow_mut().add_data(&[(Value::UInt(0), Value::Int(10))]);
    b.borrow_mut()
        .set_yield_predicate(Predicate::at_or_below(Value::UInt(0)));
    let mut delivered = false;
    let mut next = || {
        assert!(!delivered, "the next delivery closes both sources");
        delivered = true;
        b.borrow_mut().add_data(&[(Value::UInt(1), Value::Int(20))]);
        a.borrow_mut().set_yield_predicate(Predicate::True);
        b.borrow_mut().set_yield_predicate(Predicate::True);
    };
    crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut next).unwrap();
    assert_eq!(
        sink.value().unwrap().as_function()[0].output,
        Value::Int(90)
    );
}

/// A reader of a pipeline with a live source beneath it takes the rows that pipeline reaches only
/// once it has decided them, which it does only once its input is whole: a lookup of a live
/// store's final value, and of an aggregate over a live map.
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

/// A breaker whose chain reads a live source and a pipeline takes the source's arrivals and parks
/// them (`Dispatcher::park`): each row adds the sum of `ys`, and a row arriving before the sum is
/// decided waits for it.
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
        planned.iter().any(|plan| plan.live && plan.held),
        "the pipeline over the source parks its rows: {planned:?}"
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

/// A run's observer that ends the run at its first drained boundary.
struct PauseAtOnce;

impl crate::interpreter::dispatcher::RunObserver for PauseAtOnce {
    fn drained(&mut self, _changed: bool) -> std::ops::ControlFlow<()> {
        std::ops::ControlFlow::Break(())
    }
}

/// A run ended at its first drained boundary leaves no entry placed, and a run started after it
/// over the same graph plans it afresh. The second delivery of `two_batches` comes between two
/// runs, and the `main` output holds each key once at the end.
#[rstest_log::rstest]
#[case::a_map(
    "[x * 10 for x in source1()]",
    "[u0 -> 10, u1 -> 20, u2 -> 30, u3 -> 40, u4 -> 50]"
)]
#[case::a_filter(
    "[x for x in source1() if x != 2]",
    "[u0 -> 1, u2 -> 3, u3 -> 4, u4 -> 5]"
)]
#[case::a_group_by("sum([sum(g) for g in groupby(source1(), \\x -> x > 2)])", "15")]
#[case::a_sum("sum(source1())", "15")]
#[case::a_live_product("sum([x * y for x in source1() for y in source1()])", "225")]
#[case::a_live_static_product("sum([x * y for x in source1() for y in [10, 20]])", "450")]
#[case::a_static_read(
    "[x + sum([1, 2]) for x in source1()]",
    "[u0 -> 4, u1 -> 5, u2 -> 6, u3 -> 7, u4 -> 8]"
)]
#[case::a_live_read(
    "[x + sum(source1()) for x in source1()]",
    "[u0 -> 16, u1 -> 17, u2 -> 18, u3 -> 19, u4 -> 20]"
)]
#[case::a_loop(indoc! {"
    total := 0
    for x in source1():
        total += x
    total
"}, "15")]
#[case::a_loop_over_a_binding(indoc! {"
    xs = source1()
    total := 0
    for x in xs:
        total += x
    total
"}, "15")]
#[case::a_transaction(indoc! {"
    pool: Mut(Int, Txn) := 100
    for x in source1():
        with begin():
            pool := pool - x
    await_final(pool)
"}, "85")]
fn a_run_paused_at_every_boundary_answers_each_arrival_once(
    #[case] source: &str,
    #[case] expected: &str,
    #[values(1, usize::MAX)] rows: usize,
) {
    use crate::interpreter::dispatcher::{Ended, Targets};
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
    let _operators = ctx.take_operator_map();
    let producer = program
        .main_mut()
        .and_then(|output| output.producer.take())
        .expect("a `main` output");
    let slot: crate::interpreter::sinks::ProducerSlot =
        std::rc::Rc::new(std::cell::RefCell::new(Some(producer)));
    let main = std::sync::Arc::new(MainAnswers::default());
    let mut targets = Targets::default();
    targets.add_main(&program, slot.clone(), main.clone());
    let placement = program
        .main()
        .and_then(|output| output.main_entry.clone())
        .expect("a `main` output's entry");
    let mut paused = 0;
    let mut done = false;
    for (entries, complete) in two_batches() {
        let mut feed = feed.borrow_mut();
        feed.add_data(&entries);
        feed.set_yield_predicate(complete);
        drop(feed);
        match targets
            .run(rows, &mut PauseAtOnce)
            .unwrap_or_else(|refused| panic!("{refused}"))
        {
            Ended::Paused(_) => {
                paused += 1;
                assert!(
                    placement.get().is_none(),
                    "a paused run leaves nothing placed"
                );
            }
            Ended::Done(_) => done = true,
        }
    }
    assert!(
        done,
        "the run finishes once the last delivery is complete: {source}"
    );
    assert_eq!(
        paused, 1,
        "the first delivery's run pauses, and the run after the last delivery ends"
    );
    let value = main.kept.value().expect("the `main` output's value");
    assert_eq!(rendered_in_key_order(&value), expected, "{source}");
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
            ctx.source_registry().notify_changes();
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

/// The answers the `main` output is handed add up to what pull mode prints, in key order, and the
/// last is terminal: a key the filter drops and a delivery of no key add nothing, a sum is handed
/// once its source is complete, and a row that reads a sum is answered once the sum is final. The
/// answers' boundaries are not compared: a run hands each package's answer as it consumes it,
/// where pull mode prints one answer per pull.
#[rstest_log::rstest]
#[case::a_map("[x * 10 for x in source1()]")]
#[case::a_filter_dropping_a_key("[x for x in source1() if x != 2]")]
#[case::a_sum("sum(source1())")]
#[case::a_filter_reading_a_sum("[x for x in source1() if sum([1, 2, 3]) > 5]")]
#[case::a_map_reading_a_sum("[x + sum([1, 2]) for x in source1()]")]
#[case::a_filter_reading_a_live_sum("[x for x in source1() if sum(source1()) > 2]")]
fn the_main_output_prints_what_pull_mode_prints(
    #[case] source: &str,
    #[values(one_key_batches(3), one_key_batches_then_empty(3))] batches: Vec<Batch>,
    #[values(1, usize::MAX)] rows: usize,
) {
    let merged = |answers: Vec<crate::interpreter::Tile>| {
        answers
            .into_iter()
            .reduce(|mut merged, answer| {
                merged.merge(answer);
                merged
            })
            .map(crate::interpreter::sort_function_by_domain)
    };
    let pulled = pulled_live_main(source, batches.clone());
    let dispatched = dispatched_live_main(source, rows, batches);
    assert!(
        dispatched
            .printed
            .last()
            .is_some_and(crate::interpreter::Tile::is_terminal)
            || merged(dispatched.printed.clone()).is_some_and(|merged| merged.is_terminal()),
        "{source}: the answers handed add up to a terminal one"
    );
    let value = |tile: Option<crate::interpreter::Tile>| {
        tile.map(|tile| rendered_in_key_order(&super::helpers::materialized_row(tile)))
    };
    assert_eq!(
        value(merged(dispatched.printed)),
        value(merged(pulled)),
        "{source}"
    );
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

/// An aggregate per row over a live source at the `main` output hands the first delivery's rows
/// before the second arrives: `MapAggregate` pushes only what `push_held` asks of it, which each
/// pass of a live run does once its claims run out (`drive_live`).
#[rstest_log::rstest]
fn an_aggregate_per_row_over_a_live_source_at_main(#[values(1, usize::MAX)] rows: usize) {
    let LiveMain { value, handed, .. } = dispatched_live_main(
        "[max([x * s for s in [1, 10]]) for x in source1()]",
        rows,
        two_batches(),
    );
    assert_eq!(
        keyed_ints(&value),
        (0..5)
            .map(|key| (key, 10 * (key as i64 + 1)))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        handed,
        [3],
        "the first delivery's rows reach the `main` output before the second delivery"
    );
}

/// A filter over a live source that reads a sum takes the source's arrivals and parks them
/// (`Dispatcher::park`). A sum over a literal is decided before the first delivery, so the first
/// delivery's rows are answered as they arrive. A sum over the live source is decided only at the
/// last delivery, so the first delivery's rows stay parked until then.
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
            && plan.held
            && plan.name.starts_with("SinkBreaker")),
        "the `main` output's pipeline takes arrivals and parks them: {planned:?}"
    );
}

/// The readers of a pipeline with a live source beneath it read no input whole: the inner
/// comprehension's memo, the per-row sum and the outer comprehension's memo each park their rows
/// until the pipelines they read have decided them (`src/interpreter/design-dispatcher.md`,
/// "Parking arrivals until a read is decided").
#[rstest_log::rstest]
fn readers_over_a_live_pipeline_park_their_rows(#[values(1, usize::MAX)] rows: usize) {
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
            .any(|plan| plan.held && plan.name.starts_with("MapAggregate")),
        "the per-row sum parks its rows: {planned:?}"
    );
    assert_eq!(
        planned
            .iter()
            .filter(|plan| plan.held && !plan.name.starts_with("SinkBreaker"))
            .count(),
        3,
        "the two memos and the sum park their rows: {planned:?}"
    );
}

/// The sums of `a_sum_over_rows_carrying_a_constant` over a live list. The sum's pipeline parks
/// each row until the constant is decided and reads it once at its outermost key, above the level
/// the constant applies at, where `MapResultToConst` panics on a pull at or beneath that level, so
/// the values check it (`src/interpreter/design-dispatcher.md`, "Parking arrivals until a read is
/// decided").
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
            .any(|plan| plan.held && plan.name.starts_with("MapAggregate")),
        "the per-row sum parks its rows: {planned:?}"
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
/// once the source yields everything, parked until the sum is decided.
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
            .any(|plan| plan.live && plan.whole && plan.held),
        "a pipeline over the source reads it whole and parks its rows: {planned:?}"
    );
}

/// A sum whose rows read a sum over the same live source: the outer sum's pipeline takes the
/// source's arrivals and parks them until the inner sum is decided, at the last delivery.
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

/// A pipeline notified of a live source's arrivals takes the rows no arrival names: a range no live
/// source yields, as a static arm of a concatenation, with the first notification, and the rows a
/// pipeline it reads pushes as its own keys, as a let-bound arm or a field of a let-bound record,
/// from that pipeline's pushes.
#[rstest_log::rstest]
#[case::a_static_arm_reading_a_sum(
    "[x for x in source1()] ++ [y + sum([10, 20]) for y in [0]]",
    "[`0(u0) -> 1, `0(u1) -> 2, `0(u2) -> 3, `0(u3) -> 4, `0(u4) -> 5, `1(u0) -> 30]"
)]
#[case::a_sum_of_a_static_arm_reading_a_sum(
    "sum([x for x in source1()] ++ [y + sum([10, 20]) for y in [0]])",
    "45"
)]
#[case::a_sum_of_an_arm_reading_a_sum(
    "sum([x + sum([10, 20]) for x in source1()] ++ [y for y in [100]])",
    "265"
)]
#[case::a_sum_of_a_static_arm("sum([x for x in source1()] ++ [y * 2 for y in [10, 20]])", "75")]
#[case::a_let_bound_arm(
    indoc! {"
        ys = [y * 10 for y in [1, 2]]
        [x for x in source1()] ++ ys
    "},
    "[`0(u0) -> 1, `0(u1) -> 2, `0(u2) -> 3, `0(u3) -> 4, `0(u4) -> 5, `1(u0) -> 10, `1(u1) -> 20]"
)]
#[case::a_field_of_a_let_bound_record(
    indoc! {"
        r = (a=[y * 2 for y in [10, 20]], b=1)
        sum([x for x in source1()] ++ r.a) + r.b
    "},
    "76"
)]
fn a_pipeline_notified_of_arrivals_takes_rows_no_arrival_names(
    #[case] source: &str,
    #[case] expected: &str,
    #[values(1, usize::MAX)] rows: usize,
) {
    let live = dispatched_live_main(source, rows, two_batches());
    assert_eq!(rendered_in_key_order(&live.value), expected, "{source}");
}

/// `value` rendered, a collection's entries in the order of their rendered keys.
fn rendered_in_key_order(value: &Value) -> String {
    match value {
        Value::Function(_) => {
            let mut entries: Vec<(String, String)> = value
                .as_function()
                .iter()
                .map(|binding| (binding.input.to_string(), binding.output.to_string()))
                .collect();
            entries.sort();
            let entries: Vec<String> = entries
                .into_iter()
                .map(|(key, value)| format!("{key} -> {value}"))
                .collect();
            format!("[{}]", entries.join(", "))
        }
        other => other.to_string(),
    }
}

/// A loop or a transaction over a live source whose body or seed reads a pipeline: the scope or
/// the store takes each delivery once the pipelines it reads have decided it. Where one of them is
/// final only once a live source yields everything, the scope or the store holds its
/// deliveries until then, or reads its input whole where it takes no delivery's keys. `plans`
/// says how each live scope or store in plan order takes its deliveries.
#[rstest_log::rstest]
#[case::a_loop_reading_a_sum(indoc! {"
    out = test_sink()
    ys = [1, 2]
    total := 0
    for x in source1():
        total += x + sum(ys)
    out << total
"}, Value::Int(30), &["held"])]
#[case::a_transaction_reading_a_sum(indoc! {"
    out = test_sink()
    ys = [1, 2]
    pool: Mut(Int, Txn) := 100
    for x in source1():
        with begin():
            pool := pool - x - sum(ys)
    out << await_final(pool)
"}, Value::Int(70), &["held"])]
#[case::a_loop_seeded_from_a_sum(indoc! {"
    out = test_sink()
    last := sum([1, 2])
    for x in source1():
        last := x
    out << last
"}, Value::Int(5), &["held"])]
#[case::a_transaction_seeded_from_a_sum(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum([60, 40])
    for x in source1():
        with begin():
            pool := pool - x
    out << await_final(pool)
"}, Value::Int(85), &["held"])]
#[case::two_loops_seeded_from_a_sum(indoc! {"
    out = test_sink()
    total := sum([1, 2])
    for x in source1():
        total += x
    for y in source1():
        total += y * 10
    out << total
"}, Value::Int(168), &["held", "held"])]
#[case::a_loop_reading_a_sum_of_the_source(indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        total += x + sum(source1())
    out << total
"}, Value::Int(90), &["held"])]
#[case::a_loop_reading_a_sum_of_a_map_of_the_source(indoc! {"
    out = test_sink()
    ys = [y * 10 for y in source1()]
    total := 0
    for x in source1():
        total += x + sum(ys)
    out << total
"}, Value::Int(765), &["held"])]
#[case::a_transaction_reading_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for x in source1():
        with begin():
            pool := pool - sum(source1())
    out << await_final(pool)
"}, Value::Int(25), &["held"])]
#[case::a_transaction_seeded_from_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum(source1())
    for x in source1():
        with begin():
            pool := pool - x
    out << await_final(pool)
"}, Value::Int(0), &["held"])]
#[case::a_loop_seeded_from_a_transaction(indoc! {"
    out = test_sink()
    rs = [10, 20]
    a: Mut(Int, Txn) := 100
    for r in rs:
        with begin():
            a := a - r
    last := await_final(a)
    for x in source1():
        last := last + x
    out << last
"}, Value::Int(85), &["held"])]
#[case::two_writers_seeded_from_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum(source1())
    for x in source1():
        with begin():
            pool := pool - x
    for y in source1():
        with begin():
            pool := pool - y
    out << await_final(pool)
"}, Value::Int(-15), &["held", "held"])]
#[case::a_transaction_over_a_concatenation_seeded_from_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum(source1())
    for r in [x for x in source1()] ++ [5]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, Value::Int(-5), &["whole"])]
#[case::a_loop_over_a_concatenation_reading_a_sum_of_the_source(indoc! {"
    out = test_sink()
    total := 0
    for r in [x for x in source1()] ++ [5]:
        total += r + sum(source1())
    out << total
"}, Value::Int(110), &["whole"])]
#[case::two_writers_one_reading_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for x in source1():
        with begin():
            pool := pool - sum(source1())
    for y in source1():
        with begin():
            pool := pool - y
    out << await_final(pool)
"}, Value::Int(10), &["held", "held"])]
#[case::a_writer_over_a_list_seeded_from_a_sum_of_the_source(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := sum(source1())
    for r in [1, 2]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"}, Value::Int(12), &[])]
fn a_store_over_a_live_source_reading_a_pipeline(
    #[case] source: &str,
    #[case] expected: Value,
    #[case] plans: &[&str],
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, planned) = dispatched_live(source, rows, two_batches());
    assert_eq!(value, expected, "{source}");
    let following: Vec<_> = planned
        .iter()
        .filter(|plan| {
            plan.live
                && (plan.name.starts_with("Commit") || plan.name.starts_with("InductionRequest"))
        })
        .collect();
    assert_eq!(
        following
            .iter()
            .map(|plan| match (plan.whole, plan.held) {
                (true, _) => "whole",
                (false, true) => "held",
                (false, false) => "held",
            })
            .collect::<Vec<_>>(),
        plans,
        "how each live store or scope takes its deliveries: {planned:?}"
    );
}

/// A transaction store's pipeline is notified of a delivery's keys as the items of its writer's
/// source, which holds only where that source is the live source itself. A writer over a
/// concatenation of the live source and a list has positions tagged by the side they come from,
/// which no delivery names, so the store takes its input whole once the source yields everything:
/// 100 less the five items and 5.
#[rstest_log::rstest]
fn a_writer_over_a_concatenation_with_a_live_source(#[values(1, usize::MAX)] rows: usize) {
    let (value, planned) = dispatched_live(
        indoc! {"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [x for x in source1()] ++ [5]:
                with begin():
                    pool := pool - r
            out << await_final(pool)
        "},
        rows,
        two_batches(),
    );
    assert_eq!(value, Value::Int(100 - 15 - 5));
    assert!(
        planned
            .iter()
            .any(|plan| plan.live && plan.whole && plan.name.starts_with("Commit")),
        "the store takes its input whole: {planned:?}"
    );
}

/// A pipeline notified of a live source's arrivals reads the rows of another pipeline as keys of
/// its own, which no arrival names, from that pipeline's pushes: a let-bound map over the live
/// source pushes the keys each delivery adds, and each push queues the rows it names.
#[rstest_log::rstest]
#[case::in_a_sum(indoc! {"
    out = test_sink()
    ys = [y * 10 for y in source1()]
    out << sum([x for x in source1()] ++ ys)
"}, "165")]
#[case::a_sum_beside_a_constant(indoc! {"
    out = test_sink()
    s = sum(source1())
    out << sum([x + s for x in source1()] ++ [7])
"}, "97")]
#[case::at_main(indoc! {"
    ys = [y * 10 for y in source1()]
    [x for x in source1()] ++ ys
"}, "[`0(u0) -> 1, `0(u1) -> 2, `0(u2) -> 3, `0(u3) -> 4, `0(u4) -> 5, `1(u0) -> 10, `1(u1) -> 20, `1(u2) -> 30, `1(u3) -> 40, `1(u4) -> 50]")]
fn an_arm_of_a_live_concatenation_reading_a_live_map(
    #[case] source: &str,
    #[case] expected: &str,
    #[values(1, usize::MAX)] rows: usize,
) {
    let value = match source.starts_with("out") {
        true => dispatched_live(source, rows, two_batches()).0,
        false => dispatched_live_main(source, rows, two_batches()).value,
    };
    assert_eq!(rendered_in_key_order(&value), expected, "{source}");
}

/// A loop or a transaction over a live source whose body reads a sum of a second live source,
/// which yields everything only after the first does: the scope or the store is notified of its
/// whole input once the second also yields everything, when the sum is final.
#[rstest_log::rstest]
#[case::a_loop(indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        total += x + sum(source2())
    out << total
"}, 6 + 3 * 10)]
#[case::a_transaction(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for x in source1():
        with begin():
            pool := pool - x - sum(source2())
    out << await_final(pool)
"}, 100 - 6 - 3 * 10)]
fn a_store_over_a_live_source_reading_a_sum_of_another(
    #[case] source: &str,
    #[case] expected: i64,
    #[values(1, usize::MAX)] rows: usize,
) {
    let mut ctx = GlobalContext::default();
    let feed = |name: &str| {
        std::rc::Rc::new(std::cell::RefCell::new(
            crate::interpreter::TestDataSource::new(
                name,
                crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
                crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
            ),
        ))
    };
    let (first, second) = (feed("source1"), feed("source2"));
    ctx.register_source(first.clone());
    ctx.register_source(second.clone());
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    first.borrow_mut().add_data(&entries(0..3));
    first
        .borrow_mut()
        .set_yield_predicate(crate::interpreter::Predicate::True);
    second.borrow_mut().add_data(&entries(0..2));
    second
        .borrow_mut()
        .set_yield_predicate(crate::interpreter::Predicate::at_or_below(Value::UInt(1)));
    let mut rest = Some(entries(2..4));
    let planned =
        crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
            let entries = rest
                .take()
                .expect("the run waits only for the second batch");
            second.borrow_mut().add_data(&entries);
            second
                .borrow_mut()
                .set_yield_predicate(crate::interpreter::Predicate::True);
        })
        .unwrap_or_else(|refused| panic!("{refused}"))
        .planned;
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    assert_eq!(binding.output, Value::Int(expected), "{planned:?}");
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
    "InductionRequest"
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

/// A transaction over a live source seeded from a sum of a second live source, which yields
/// everything while the first is still delivering: the store holds the deliveries that arrive
/// before the seed is final, takes them once the second source yields everything, and takes each
/// later delivery as it arrives, before the first source yields everything.
#[rstest_log::rstest]
fn a_transaction_takes_each_delivery_once_its_seed_is_final(#[values(1, usize::MAX)] rows: usize) {
    let source = indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := sum(source2())
        for x in source1():
            with begin():
                pool := pool + x
        out << await_final(pool)
    "};
    let mut ctx = GlobalContext::default();
    let feed = |name: &str| {
        std::rc::Rc::new(std::cell::RefCell::new(
            crate::interpreter::TestDataSource::new(
                name,
                crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
                crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
            ),
        ))
    };
    let (items, seed) = (feed("source1"), feed("source2"));
    ctx.register_source(items.clone());
    ctx.register_source(seed.clone());
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    let up_to = |key: u64| crate::interpreter::Predicate::at_or_below(Value::UInt(key));
    items.borrow_mut().add_data(&entries(0..2));
    items.borrow_mut().set_yield_predicate(up_to(1));
    seed.borrow_mut().add_data(&entries(0..2));
    seed.borrow_mut().set_yield_predicate(up_to(1));
    let mut idle = 0;
    let mut released = Vec::new();
    crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
        idle += 1;
        released.push(items.borrow().get_released_predicate());
        match idle {
            1 => {
                seed.borrow_mut().add_data(&entries(2..4));
                seed.borrow_mut()
                    .set_yield_predicate(crate::interpreter::Predicate::True);
            }
            2 => {
                items.borrow_mut().add_data(&entries(2..4));
                items.borrow_mut().set_yield_predicate(up_to(3));
            }
            3 => items
                .borrow_mut()
                .set_yield_predicate(crate::interpreter::Predicate::True),
            _ => panic!("{source}: the run waits only for its three batches"),
        }
    })
    .unwrap_or_else(|refused| panic!("{refused}"));
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    assert_eq!(binding.output, Value::Int(10 + 10));
    assert_eq!(
        released,
        [crate::interpreter::Predicate::False, up_to(1), up_to(3)],
        "the store releases nothing while its seed is open, the held deliveries once it is \
         final, and each later delivery as it arrives"
    );
}

/// A loop over a live source seeded from the final value of a transaction store over a let-bound
/// list: the store reads the list's pipeline whole, nothing live is beneath it, so it reads its
/// input at the start, and the loop takes each delivery as it arrives, before its source yields
/// everything.
#[rstest_log::rstest]
fn a_loop_seeded_from_a_static_store_takes_each_delivery(#[values(1, usize::MAX)] rows: usize) {
    let source = indoc! {"
        out = test_sink()
        rs = [10, 20]
        a: Mut(Int, Txn) := 100
        for r in rs:
            with begin():
                a := a - r
        last := await_final(a)
        for x in source1():
            last := last + x
        out << last
    "};
    let mut ctx = GlobalContext::default();
    let items = std::rc::Rc::new(std::cell::RefCell::new(
        crate::interpreter::TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
            crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
        ),
    ));
    ctx.register_source(items.clone());
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let mut program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    let up_to = |key: u64| crate::interpreter::Predicate::at_or_below(Value::UInt(key));
    items.borrow_mut().add_data(&entries(0..2));
    items.borrow_mut().set_yield_predicate(up_to(1));
    let mut idle = 0;
    let mut released = Vec::new();
    crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
        idle += 1;
        released.push(items.borrow().get_released_predicate());
        match idle {
            1 => {
                items.borrow_mut().add_data(&entries(2..4));
                items.borrow_mut().set_yield_predicate(up_to(3));
            }
            2 => items
                .borrow_mut()
                .set_yield_predicate(crate::interpreter::Predicate::True),
            _ => panic!("{source}: the run waits only for its two batches"),
        }
    })
    .unwrap_or_else(|refused| panic!("{refused}"));
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    assert_eq!(binding.output, Value::Int(70 + 1 + 2 + 3 + 4));
    assert_eq!(
        released,
        [up_to(1), up_to(3)],
        "the loop takes each delivery before its source yields everything"
    );
}

/// A comprehension over a live source whose rows read a value another pipeline decides: a
/// transaction store's final value, a sum, a loop's final value. Each delivery's rows park until
/// that pipeline has decided it, whether its push reaches the comprehension or the comprehension
/// reads it by pull.
#[rstest_log::rstest]
#[case::a_store_s_final_value(indoc! {"
    out = test_sink()
    rs = [10, 20]
    a: Mut(Int, Txn) := 100
    for r in rs:
        with begin():
            a := a - r
    out << [x + await_final(a) for x in source1()]
"}, &[(0, 71), (1, 72), (2, 73), (3, 74), (4, 75)])]
#[case::a_sum_in_a_filter(indoc! {"
    out = test_sink()
    ys = [1, 2]
    out << [x for x in source1() if x > sum(ys)]
"}, &[(3, 4), (4, 5)])]
#[case::a_loop_s_final_value(indoc! {"
    out = test_sink()
    t := 0
    for y in [1, 2]:
        t += y
    out << [x + t for x in source1()]
"}, &[(0, 4), (1, 5), (2, 6), (3, 7), (4, 8)])]
fn a_live_comprehension_reading_a_decided_value(
    #[case] source: &str,
    #[case] expected: &[(u64, i64)],
    #[values(1, usize::MAX)] rows: usize,
) {
    let (value, _) = dispatched_live(source, rows, two_batches());
    assert_eq!(keyed_ints(&value), expected, "{source}");
}

/// A sum whose rows read a live list and a sum over a second live source that becomes decided
/// between the list's two deliveries. Each row the list brings parks until the sum is decided; the
/// sum's decided push brings no row the list's already brought, so the outer sum reads each once.
#[rstest_log::rstest]
#[case::a_sum_in_the_row(indoc! {"
    out = test_sink()
    xs = [x for x in source1()]
    out << sum([x * sum(source2()) for x in xs])
"})]
#[case::a_let_bound_sum(indoc! {"
    out = test_sink()
    xs = [x for x in source1()]
    n = sum(source2())
    out << sum([x * n for x in xs])
"})]
fn a_reader_of_two_pipelines_decided_apart(
    #[case] source: &str,
    #[values(1, usize::MAX)] rows: usize,
) {
    let mut ctx = GlobalContext::default();
    let feed = |name: &str| {
        std::rc::Rc::new(std::cell::RefCell::new(
            crate::interpreter::TestDataSource::new(
                name,
                crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
                crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
            ),
        ))
    };
    let (list, summed) = (feed("source1"), feed("source2"));
    ctx.register_source(list.clone());
    ctx.register_source(summed.clone());
    let sink = ctx.register_test_sink("out");
    let mut program = compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let _operators = ctx.take_operator_map();
    let entries = |keys: std::ops::Range<u64>| {
        keys.map(|key| (Value::UInt(key), Value::Int(key as i64 + 1)))
            .collect::<Vec<_>>()
    };
    let up_to = |key: u64| crate::interpreter::Predicate::at_or_below(Value::UInt(key));
    list.borrow_mut().add_data(&entries(0..2));
    list.borrow_mut().set_yield_predicate(up_to(1));
    summed.borrow_mut().add_data(&entries(0..1));
    summed.borrow_mut().set_yield_predicate(up_to(0));
    let mut idle = 0;
    crate::interpreter::dispatcher::run_program_polling(&mut program, rows, &mut || {
        idle += 1;
        let (fed, keys) = match idle {
            1 => (&summed, 1..4),
            2 => (&list, 2..5),
            _ => panic!("{source}: the run waits only for its two batches"),
        };
        fed.borrow_mut().add_data(&entries(keys));
        fed.borrow_mut()
            .set_yield_predicate(crate::interpreter::Predicate::True);
    })
    .unwrap_or_else(|refused| panic!("{source}: {refused}"));
    let written = sink
        .value()
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    // sum(x) over 1..=5 is 15 and sum(source2()) over 1..=4 is 10.
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    assert_eq!(binding.output, Value::Int(150), "{source}");
}

/// A feed out of a loop over a let-bound filter of a live source: a delivery decides a position at
/// which the loop writes nothing, the key the filter drops, and the read of the feed states it
/// decided and absent, so the pipeline that consumed the store's push of it releases it.
#[rstest_log::rstest]
fn a_feed_out_of_a_loop_over_a_let_bound_filter_of_a_live_source(
    #[values(1, usize::MAX)] rows: usize,
) {
    let source = indoc! {"
        out = test_sink()
        ys = [x for x in source1() if x != 2]
        n := 0
        for y in ys:
            n := n + y
            out << n
    "};
    let (written, _) = dispatched_live_written(source, rows, one_key_batches(4));
    assert_eq!(keyed_ints(&written), [(0, 1), (2, 4), (3, 8)]);
}

#[rstest::rstest]
#[case::materialized_map(indoc! {r#"
    out = test_sink()
    mm = map([("a", [1, 2]), ("b", [3, 4])])
    out << sum([sum([v for v in vs]) for vs in mm])
"#}, 10)]
#[case::jagged_map(indoc! {r#"
    out = test_sink()
    m = map([("a", box([1])), ("b", box([2, 3]))])
    out << sum([max(r) for r in m])
"#}, 4)]
#[case::filtered_group(indoc! {r#"
    out = test_sink()
    out << sum([sum([sum(s.xs) for s in g if s.q > 1]) for g in groupby([(k=a > 1, q=a, xs=[a * j for j in [1, 2]]) for a in [1, 2, 3]], \x -> x.k)])
"#}, 15)]
#[case::nominal_group_key(indoc! {r#"
    type Money = Int
    instance Equatable(Money, Money)
    instance Orderable(Money, Money)

    g = groupby([1, 2, 3, 4], \x -> Money::new(x + (x if x > 1 else 0)))
    out = test_sink()
    out << sum([max(grp) for grp in g])
"#}, 10)]
fn small_morsels_preserve_nested_collection_values(
    #[case] source: &str,
    #[case] expected: i64,
    #[values(1, 2, usize::MAX)] rows: usize,
) {
    assert_eq!(dispatched(source, rows).0, Value::Int(expected));
}

#[rstest::rstest]
#[case::accumulator(indoc! {r#"
    out = test_sink()
    store: Mut(Int, Txn) := 0
    cnt: Mut(Int) := 0
    for r in [10, 20, 30]:
        cnt := cnt + 1
        with begin():
            store := store + cnt
    out << await_final(store)
"#}, Value::Int(6))]
#[case::carried_read(indoc! {r#"
    out = test_sink()
    cnt := 0
    a: Mut(Int, Txn) := 0
    for x in [1, 2, 3, 4]:
        if x > 2:
            cnt := cnt + 1
        with begin():
            a := a + cnt
    out << await_final(a)
"#}, Value::Int(3))]
#[case::second_store(indoc! {r#"
    out = test_sink()
    cnt := 0
    a: Mut(Int, Txn) := 0
    b: Mut(Int, Txn) := 0
    for x in [1, 2]:
        cnt := cnt + 1
        with begin():
            a := a + cnt
    for y in [10, 20]:
        with begin():
            b := b + y
    out << (await_final(a), await_final(b))
"#}, Value::Record(std::collections::HashMap::from([
    ("_0".into(), Value::Int(3)), ("_1".into(), Value::Int(30))
])))]
#[case::ordered_replies(indoc! {r#"
    out = test_sink()
    resps: Feed(_)
    store: Mut(Int, Txn) := 0
    cnt: Mut(Int) := 0
    for r in [10, 20, 30]:
        cnt := cnt + 1
        with begin():
            store := store + r
            resps << cnt
    out << resps
"#}, Value::Function(vec![
    crate::interpreter::FuncBinding { input: Value::UInt(1), output: Value::Int(1) },
    crate::interpreter::FuncBinding { input: Value::UInt(2), output: Value::Int(2) },
    crate::interpreter::FuncBinding { input: Value::UInt(3), output: Value::Int(3) },
]))]
#[case::gated_replies(indoc! {r#"
    out = test_sink()
    resps: Feed(_)
    pool: Mut(Int, Txn) := 100
    cnt: Mut(Int) := 0
    for r in [70, 50, 20]:
        cnt := cnt + 1
        with begin():
            if pool >= r:
                pool := pool - r
                resps << cnt
    out << resps
"#}, Value::Function(vec![
    crate::interpreter::FuncBinding { input: Value::UInt(1), output: Value::Int(1) },
    crate::interpreter::FuncBinding { input: Value::UInt(2), output: Value::Int(3) },
]))]
fn small_morsels_refresh_transaction_sources(
    #[case] source: &str,
    #[case] expected: Value,
    #[values(1, 2, usize::MAX)] rows: usize,
) {
    assert_eq!(dispatched(source, rows).0, expected);
}

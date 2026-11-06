//! Compiled programs run end to end through `crate::interpreter::dispatcher::run_program`: the
//! dispatcher drives every pipeline breaker in the sink's producer chain on one thread, and the
//! sink's own pipeline pulls its producer one package at a time. Each answer is checked against
//! the program's pull-mode answer.

use indoc::indoc;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::dispatcher::{Planned, run_program};
use crate::interpreter::{DataSink, Value};

use std::sync::Arc;

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
    let program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
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
    let targets: Vec<(_, Arc<dyn DataSink>)> = consumers
        .iter()
        .zip(&sinks)
        .map(|(consumer, sink)| (consumer.clone(), sink.clone() as Arc<dyn DataSink>))
        .collect();
    let planned = run_program(&targets, rows);
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
    assert!(
        program.done.try_recv().is_ok(),
        "{source}: a pull after the run finds every sink done"
    );
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

/// `source` answers through the dispatcher what it answers in pull mode, at morsels of one row,
/// three, and one per guard, with a pipeline whose breaker's name starts with each of `kinds`.
fn answers_as_pull_mode_does(source: &str, kinds: &[&str]) {
    let expected = pulled(source);
    for rows in [1, 3, usize::MAX] {
        let (value, breakers) = dispatched(source, rows);
        assert_eq!(
            value, expected,
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

#[test]
fn a_sum_over_a_let_bound_list() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([x * 2 for x in xs])
        "},
        &["Memo", "Aggregate"],
    );
}

#[test]
fn a_max_over_a_mapped_list() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            out << max([x * 2 for x in xs])
        "},
        &["Memo", "Aggregate", "ExtractAggregate"],
    );
}

#[test]
fn a_mapped_list() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << [x + 1 for x in xs]
        "},
        &["Memo"],
    );
}

#[test]
fn a_sum_inside_an_expression() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [3, 1, 2]
            out << sum([x for x in xs]) + 1
        "},
        &["Aggregate", "ExtractAggregate"],
    );
}

/// A filter reads its input's memo twice, as the values and as the predicate: the memo's push
/// reaches the sum along both, which queues it once.
#[test]
fn a_filtered_sum() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            out << sum([x for x in xs if x > 1])
        "},
        &["Memo", "Aggregate"],
    );
}

/// A literal arm of a concatenation has no breaker beneath it, so no push names its keys: the
/// planner queues the region it brings for the sum at the start of the run.
#[test]
fn a_sum_over_a_list_concatenated_with_a_literal() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([x * 2 for x in xs] ++ [10, 20])
        "},
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
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum([7, 8] ++ [x * 2 for x in xs])
        "},
        &["Memo", "Aggregate"],
    );
}

/// A chain of concatenations compiles to one union of three arms: the comprehension's pushes
/// arrive under its tag, and both literal arms' regions are queued at the start.
#[test]
fn a_sum_over_a_chain_of_unions() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << sum(([x * 2 for x in xs] ++ [7]) ++ [8])
        "},
        &["Memo", "Aggregate"],
    );
}

/// A union written out whole, read by the output's memo beneath a key of its own.
#[test]
fn a_union_written_out_whole() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            out << [x * 2 for x in xs] ++ [7, 8]
        "},
        &["Memo"],
    );
}

/// Two aggregates of one binding both read its memo through fan-out slots, and the output's memo
/// reads both: each aggregate is one value, so either push names every key of the memo's input,
/// and the memo reads its input whole once both have finished.
#[test]
fn two_aggregates_of_one_binding() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [3, 1, 2]
            out << sum(xs) * 10 + max(xs)
        "},
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
    answers_as_pull_mode_does(source, &["Memo"]);
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
    answers_as_pull_mode_does(source, &["Memo", "Aggregate"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("Aggregate") && !plan.whole && !plan.started),
        "the sum reads both arms' pushes: {planned:?}"
    );
}

/// A sum read inside another comprehension: the outer sum's pipeline reads the inner sum's and the
/// list's. The inner sum's push names every key of the outer sum's input, which the list's pushes
/// name too, so the outer sum parks the rows the list's pushes bring until the inner sum is
/// decided, and reads each once.
#[test]
fn a_comprehension_reading_a_sum() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            n = sum(ys)
            xs = [1, 2, 3]
            out << sum([x * n for x in xs])
        "},
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
        1,
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
    answers_as_pull_mode_does(source, &["Memo", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let sink = sink_of(&planned);
    assert!(!sink.whole, "{sink:?}");
}

/// The sink of a collection reads the pushes of the collection's output memo.
#[test]
fn a_sink_of_a_collection() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << [x + 1 for x in xs]
    "};
    answers_as_pull_mode_does(source, &["Memo", "SinkBreaker"]);
    let (_, planned) = dispatched(source, 1);
    let sink = sink_of(&planned);
    assert!(!sink.whole, "{sink:?}");
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

/// The answer `source`, compiled with a test sink `out`, writes in pull mode.
fn pulled(source: &str) -> Value {
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let completed = (0..1000).any(|_| {
        ctx.scheduler().check_for_notifications();
        program.done.try_recv().is_ok()
    });
    assert!(completed, "{source} completes in pull mode");
    let written = sink.value().expect("the sink holds a value");
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    binding.output.clone()
}

/// A loop's store is the breaker of a pipeline of its own: the loop over a literal is a source
/// pipeline, cut into morsels of positions, and the sink reads the store once it is terminal.
#[test]
fn a_loop_over_a_literal() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total
        "},
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
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
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
"})]
#[case::dropping_one_between(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3, 4] if x > 1 and x != 3]:
        total += x
    out << total
"})]
#[case::dropping_the_last(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3] if x < 3]:
        total += x
    out << total
"})]
#[case::dropping_every_one(indoc! {"
    out = test_sink()
    total := 0
    for x in [x for x in [1, 2, 3] if x > 5]:
        total += x
    out << total
"})]
#[case::over_an_empty_list(indoc! {"
    out = test_sink()
    total := 0
    for i in []:
        total += 1
    out << total
"})]
fn a_loop_over_a_filtered_list(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
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
    answers_as_pull_mode_does(source, &["Memo", "InductionRequest", "SinkBreaker"]);
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
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            ys = [4, 5]
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total + sum(ys)
        "},
        &["InductionRequest", "Aggregate", "SinkBreaker"],
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
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
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
    answers_as_pull_mode_does(
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
        &["InductionRequest", "SinkBreaker"],
    );
}

/// The inner loop's seed reads the outer loop's position, so the nested store's seed reads a
/// pipeline of the outer scope.
#[test]
fn a_nested_loop_seeded_from_the_outer_position() {
    answers_as_pull_mode_does(
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
"})]
#[case::with_an_accumulator_of_its_own(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        count := 0
        for y in [1, 2]:
            count += y
        total += x * count
    out << total
"})]
#[case::over_rows_of_no_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        for y in [y for y in [1, 2] if y > 5]:
            total += x * y
    out << total
"})]
#[case::guarded(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        for y in [1, 2]:
            if x > y:
                total += x * y
    out << total
"})]
#[case::two_inner_loops_on_one_accumulator(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += x * y
        for y in [3, 4]:
            total += x + y
    out << total
"})]
#[case::nested_twice_over_one_let_bound_list(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in xs:
        for y in xs:
            for z in xs:
                total := total + x * y - z
    out << total
"})]
fn a_nested_loop_answers_as_pull_mode_does(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
}

/// A loop nested in a nested loop runs as a scope inside the scope of the loop around it, itself
/// inside the outermost loop's.
#[test]
fn a_loop_nested_twice() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [1, 2]:
                        total += x * y * z
            out << total
        "},
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
"})]
#[case::a_max_beside_the_outer_position(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += max([z * y for z in xs]) + x
    out << total
"})]
fn a_nested_loop_aggregating_a_map_of_its_position(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
}

/// A nested loop with a condition in its body, on the inner and on the outer position, plans a
/// loop scope and answers as pull mode does.
#[rstest_log::rstest]
#[case::on_the_inner_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            if y > 1:
                total += y
    out << total
"})]
#[case::on_the_outer_position(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            if x > 1:
                total += y
    out << total
"})]
fn a_nested_loop_with_a_condition(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
}

/// Nested-loop bodies of the shapes the cases name: each plans a loop scope and answers as pull
/// mode does.
#[rstest_log::rstest]
#[case::an_aggregate_of_a_list_outside_the_loops(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum(xs) * y
    out << total
"})]
#[case::a_record_of_two_aggregates(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += max([z for z in xs]) - min([w for w in ws]) + y
    out << total
"})]
#[case::a_tuple_of_the_positions(indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            t = (x, y)
            total += t.0 * t.1
    out << total
"})]
#[case::two_generators(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([z * w * y for z in xs for w in ws])
    out << total
"})]
#[case::a_sum_of_sums(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    ws = [4, 5]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([sum([z * w for w in ws]) for z in xs]) * y
    out << total
"})]
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
"})]
#[case::a_comprehension_of_tuples(indoc! {"
    out = test_sink()
    xs = [1, 2, 3]
    total := 0
    for x in [1, 2]:
        for y in [1, 2]:
            total += sum([q.0 for q in [(y, z) for z in xs] if q.1 > 1])
    out << total
"})]
fn a_nested_loop_body_reading(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
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
"})]
#[case::reading_nothing(indoc! {"
    out = test_sink()
    acc := 0
    for xs in [[1, 2], [3, 4]]:
        for x in xs:
            acc := acc + 7
    out << acc
"})]
fn a_loop_nested_over_rows(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["InductionRequest", "SinkBreaker"]);
}

/// A transaction store is the breaker of a pipeline of its own; its input is its one writer's
/// source, cut into morsels of items, and the sink reads the store once it is terminal.
#[rstest_log::rstest]
#[case::a_counter(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20, 30]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"})]
// The last item is denied: a deny commits nothing and progresses through the source's release.
#[case::a_grant_then_a_deny(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [70, 50]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"})]
// An item after the denied one, which the deny leaves the store unchanged for.
#[case::a_deny_then_an_item(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [50, 70, 10]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"})]
// No item reaches the writer.
#[case::over_no_item(indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [r for r in [10, 20] if r > 50]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"})]
fn a_transaction(#[case] source: &str) {
    answers_as_pull_mode_does(source, &["Commit", "SinkBreaker"]);
}

/// A store of two writers has no consuming mode: a morsel names positions of one source.
#[test]
#[should_panic(expected = "a transaction store of 2 writers has no consuming mode")]
fn a_transaction_store_of_two_writers_is_refused() {
    dispatched(
        indoc! {"
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
        "},
        1,
    );
}

/// A loop over a live source runs in no pipeline: no run notifies the source's arrivals.
#[test]
#[should_panic(expected = "a store over a live source")]
fn a_loop_over_a_live_source_is_refused() {
    dispatched_with(
        indoc! {"
            out = test_sink()
            total := 0
            for x in source1():
                total += x
            out << total
        "},
        1,
        &["out"],
        |ctx| {
            ctx.register_source(std::rc::Rc::new(std::cell::RefCell::new(
                crate::interpreter::TestDataSource::new(
                    "source1",
                    crate::ccl::Type::Base(crate::interpreter::BaseType::Int),
                    crate::interpreter::Extent::Base(crate::interpreter::BaseType::Int),
                ),
            )));
        },
    );
}

/// A transaction over a let-bound list reads the list's memo along two paths inside its cycle,
/// the writer's and the body's, and reads it once.
#[test]
fn a_transaction_over_a_let_bound_list() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            rs = [10, 20, 30]
            pool: Mut(Int, Txn) := 100
            for r in rs:
                with begin():
                    pool := pool - r
            out << await_final(pool)
        "},
        &["Memo", "Commit", "SinkBreaker"],
    );
}

/// A guarded loop over a let-bound list reads the list's memo along every path its filter reads
/// the drive by, and reads it once.
#[test]
fn a_guarded_loop_over_a_let_bound_list() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3]
            total := 0
            for x in xs:
                if x > 1:
                    total += x
            out << total
        "},
        &["Memo", "InductionRequest", "SinkBreaker"],
    );
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

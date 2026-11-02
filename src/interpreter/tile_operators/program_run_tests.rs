//! Compiled programs run end to end through `crate::interpreter::dispatcher::run_program`: the
//! dispatcher drives every pipeline breaker in the sink's producer chain on one thread, and the
//! sink's own pipeline pulls its producer one package at a time. Each answer is checked against
//! the program's pull-mode answer.

use indoc::indoc;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
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

/// A group-by's memo reads its input's memo and the `Converse` keying the groups, which reads
/// that memo too: the group-by's memo reads two pipelines. It reads the `Converse`'s pushes and
/// waits for the input's memo to finish, taking no push of it.
#[test]
fn a_group_by() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3, 4]
        g = groupby(xs, \\x -> x > 2)
        out << sum([sum(v) for v in g])
    "};
    answers_as_pull_mode_does(source, &["Memo", "Converse"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned
            .iter()
            .any(|plan| plan.name.starts_with("Memo") && !plan.whole && !plan.builds.is_empty()),
        "the group-by's memo has a build edge: {planned:?}"
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
    answers_as_pull_mode_does(source, &["Memo", "Aggregate"]);
    let (_, planned) = dispatched(source, 1);
    assert!(
        planned.iter().any(|plan| plan.name.starts_with("Aggregate")
            && !plan.whole
            && plan.builds.is_empty()
            && !plan.started),
        "the sum reads both arms' pushes: {planned:?}"
    );
}

/// A sum read inside another comprehension: the outer sum's pipeline reads the inner sum's and the
/// list's. The inner sum's push names every key of the outer sum's input, which the list's pushes
/// name too, so the outer sum reads its input whole once both have finished.
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
        planned.iter().any(|plan| plan.whole),
        "a pipeline reads its input whole: {planned:?}"
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
    assert!(!sink.whole && sink.builds.is_empty(), "{sink:?}");
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
    assert!(!sink.whole && sink.builds.is_empty(), "{sink:?}");
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
    answers_as_pull_mode_does(source, &["LoopScope", "SinkBreaker"]);
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
    answers_as_pull_mode_does(source, &["LoopScope", "SinkBreaker"]);
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
    answers_as_pull_mode_does(source, &["Memo", "LoopScope", "SinkBreaker"]);
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
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            ys = [4, 5]
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total + sum(ys)
        "},
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
    answers_as_pull_mode_does(source, &["LoopScope", "SinkBreaker"]);
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
        &["LoopScope", "SinkBreaker"],
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
    answers_as_pull_mode_does(source, &["LoopScope", "SinkBreaker"]);
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
    answers_as_pull_mode_does(source, &["LoopScope", "SinkBreaker"]);
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

/// A loop over a live source runs in no pipeline: no round takes the source's arrivals.
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
        r = m["a"]?
        s = m["b"]?
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
/// each next one when the run has nothing to do. What the sink holds, and what the run planned.
fn dispatched_live(source: &str, rows: usize, batches: Vec<Batch>) -> (Value, Vec<Planned>) {
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
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    (binding.output.clone(), planned)
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

/// A let-bound map over a live source is a `Memo` keyed by the source's keys, which the run
/// notifies of each delivery. The sink reads the `Memo` through its feed, which is keyed by the
/// sink's one row, so it takes the `Memo`'s pushes as a build edge.
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
}

/// A feed of a map over a live source is keyed by the sink's one row, so a push of a delivery's
/// keys is widened on its way to the pipeline above the source, which no package names.
#[test]
#[should_panic(expected = "widened, so no package names them")]
fn a_feed_of_a_map_over_a_live_source_is_refused() {
    dispatched_live(
        indoc! {"
            out = test_sink()
            out << [x * 2 for x in source1()]
        "},
        1,
        two_batches(),
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
/// A breaker whose chain reads a live source and a pipeline takes the pipeline's pushes, and no
/// package a source's delivery names.
#[test]
#[should_panic(expected = "reads pushes and a live source")]
fn a_reader_of_pushes_over_a_live_source_is_refused() {
    dispatched_live(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            out << sum([x + sum(ys) for x in source1()])
        "},
        1,
        two_batches(),
    );
}

//! Compiled programs run end to end through `crate::interpreter::dispatcher::run_program`: the
//! dispatcher drives every pipeline breaker in the sink's producer chain on one thread, and the
//! sink pulls once the run has finished. Each answer is checked against the program's pull-mode
//! answer.

use indoc::indoc;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::Value;
use crate::interpreter::dispatcher::{RanPipeline, run_program, store_of};

use std::rc::Rc;

use super::loop_breaker_tests::pulled;
use super::{FanOut, FunctionGuard, TileGuard, TileProducer};
use crate::ccl::{FieldKey, TagMap};
use crate::interpreter::Predicate;

/// `source` compiled with a test sink `out`, its pipelines run through the dispatcher at morsels
/// of `rows`, then its sink pulled by the scheduler: the value `out` receives, and the pipelines.
fn dispatched(source: &str, rows: usize) -> (Value, Vec<RanPipeline>) {
    let mut ctx = GlobalContext::default();
    ctx.defer_sink_pulls();
    let sink = ctx.register_test_sink("out");
    let loaded = LoadedProgram::test(source);
    let program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
        .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
    let operators = ctx.take_operator_map();
    let stores: Vec<_> = operators
        .operators()
        .into_iter()
        .filter(|fan| fan.cached_tile().is_some())
        .collect();
    let consumers: Vec<_> = program
        .outputs
        .iter()
        .filter_map(|output| output.sink_consumer.clone())
        .collect();
    let roots: Vec<_> = consumers
        .iter()
        .map(|consumer| consumer.borrow().producer_slot().clone())
        .collect();
    let planned = run_program(&roots, &stores, ctx.scheduler(), rows);
    let beneath = pulls_beneath_breakers(&roots, &stores);
    for consumer in &consumers {
        consumer.borrow().pull_now();
    }
    let done = (0..1000).any(|_| {
        ctx.scheduler().check_for_notifications();
        program.done.try_recv().is_ok()
    });
    assert!(done, "{source}: the program completes once its sink pulls");
    assert_eq!(
        pulls_beneath_breakers(&roots, &stores),
        beneath,
        "{source}: the sink's pulls stop at the breakers, which answer from what they consumed"
    );
    let written = sink.value().expect("the sink holds a value");
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    (binding.output.clone(), planned)
}

/// The pulls of every producer beneath a pipeline breaker in the chains under `roots`, a store's
/// fan-out among `stores` counting as one: what the breakers' inputs answered.
fn pulls_beneath_breakers(
    roots: &[crate::interpreter::sinks::ProducerSlot],
    stores: &[Rc<FanOut>],
) -> u64 {
    fn walk(producer: &mut dyn TileProducer, beneath: bool, stores: &[Rc<FanOut>]) -> u64 {
        let own = if beneath { producer.base().pulls } else { 0 };
        let breaker =
            beneath || producer.as_breaking_mut().is_some() || store_of(producer, stores).is_some();
        let mut total = own;
        producer.visit_input_producers_mut(&mut |_, input| total += walk(input, breaker, stores));
        total
    }
    roots
        .iter()
        .map(|root| {
            let mut root = root.borrow_mut();
            walk(
                root.as_mut().expect("a root holds its producer").as_mut(),
                false,
                stores,
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
                breakers.iter().any(|ran| ran.name.starts_with(kind)),
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

/// A filter reads its input's memo along two paths, the values and the predicate, each through a
/// fan-out slot of its own: the aggregate's pipeline reads the memo's pipeline once.
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

/// `keys` under `tags`, innermost first.
fn under_tags(tags: &[usize], keys: Predicate) -> Predicate {
    tags.iter().fold(keys, |keys, tag| {
        Predicate::tagged(
            TagMap::from_arms(vec![(FieldKey::Index(*tag), keys)]),
            false,
        )
    })
}

/// How many guards `ran` consumed under `tags`, and how many that are every key not under them.
fn consumed_under(ran: &RanPipeline, tags: &[usize]) -> (usize, usize) {
    let rest = TileGuard::Function(FunctionGuard::Domain(
        Predicate::True.minus(&under_tags(tags, Predicate::True)),
    ));
    let mut pushed = 0;
    let mut others = 0;
    for guard in &ran.consumed {
        let TileGuard::Function(FunctionGuard::Domain(keys)) = guard else {
            panic!(
                "{} consumes guards of its input's outermost keys: {guard:?}",
                ran.name
            )
        };
        if *guard == rest {
            others += 1;
        } else {
            assert!(
                under_tags(tags, Predicate::True).subsumes(keys),
                "{} consumes a push restated under {tags:?}: {guard:?}",
                ran.name
            );
            pushed += 1;
        }
    }
    (pushed, others)
}

fn breaker<'r>(ran: &'r [RanPipeline], kind: &str) -> &'r RanPipeline {
    ran.iter()
        .find(|ran| ran.name.starts_with(kind))
        .unwrap_or_else(|| panic!("a {kind} pipeline: {ran:?}"))
}

/// A sum over a union of a comprehension and a literal: the comprehension's memo is a pipeline
/// under arm `0`, so the sum consumes the memo's morsels restated under tag `0`, and the literal
/// arm `1`, which no pipeline pushes, as one package of its own.
#[test]
fn a_sum_over_a_union_consumes_each_arm_by_tag() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << sum([x * 2 for x in xs] ++ [7, 8])
    "};
    answers_as_pull_mode_does(source, &["Memo", "Aggregate"]);
    for (rows, memo_morsels) in [(1, 3), (2, 2), (usize::MAX, 1)] {
        let (_, ran) = dispatched(source, rows);
        let consumed = consumed_under(breaker(&ran, "Aggregate"), &[0]);
        assert_eq!(consumed, (memo_morsels, 1), "at morsels of {rows}");
    }
}

/// The comprehension under the second arm: its morsels are restated under tag `1`.
#[test]
fn a_sum_over_a_union_with_the_comprehension_second() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << sum([7, 8] ++ [x * 2 for x in xs])
    "};
    answers_as_pull_mode_does(source, &["Memo", "Aggregate"]);
    let (_, ran) = dispatched(source, 1);
    assert_eq!(consumed_under(breaker(&ran, "Aggregate"), &[1]), (3, 1));
}

/// A chain of concatenations compiles to one union of three arms: the comprehension's morsels
/// are restated under tag `0`, and both literal arms are the one package of every other key.
#[test]
fn a_sum_over_a_chain_of_unions_restates_under_the_first_tag() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << sum(([x * 2 for x in xs] ++ [7]) ++ [8])
    "};
    answers_as_pull_mode_does(source, &["Memo", "Aggregate"]);
    let (_, ran) = dispatched(source, 1);
    assert_eq!(consumed_under(breaker(&ran, "Aggregate"), &[0]), (3, 1));
}

/// A union written out whole: the output's memo reads it beneath a `Unit` key, which no guard of
/// the union's keys names, so that memo reads its input whole.
#[test]
fn a_union_written_out_whole() {
    let source = indoc! {"
        out = test_sink()
        xs = [1, 2, 3]
        out << [x * 2 for x in xs] ++ [7, 8]
    "};
    answers_as_pull_mode_does(source, &["Memo"]);
    let (_, ran) = dispatched(source, 1);
    let output = ran.last().expect("the output's memo");
    assert!(
        matches!(output.consumed.as_slice(), [whole] if whole.is_universal()),
        "{output:?}"
    );
}

/// Two aggregates of one binding: their pipelines both read its memo, and the planner plans that,
/// but the output's memo reads both aggregates, so a pipeline reads two and the dispatcher refuses
/// it. Each sink's output is compiled on its own, so two sinks read no binding in common.
#[test]
#[should_panic(expected = "reads pipelines")]
fn two_aggregates_of_one_binding_are_refused_where_they_meet() {
    dispatched(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            out << sum(xs) * 10 + max(xs)
        "},
        1,
    );
}

/// A group-by's memo reads its input's memo and the `Converse` that keys the groups, which reads
/// that input's memo too: the input's memo has two readers, and the group-by's memo reads two.
#[test]
#[should_panic(expected = "reads pipelines")]
fn a_group_by_is_refused() {
    dispatched(
        indoc! {"
            out = test_sink()
            xs = [1, 2, 3, 4]
            g = groupby(xs, \\x -> x > 2)
            out << sum([sum(v) for v in g])
        "},
        1,
    );
}

/// A sum read inside another comprehension makes that comprehension's pipeline read two.
#[test]
#[should_panic(expected = "reads pipelines")]
fn a_pipeline_reading_two_pipelines_is_refused() {
    dispatched(
        indoc! {"
            out = test_sink()
            ys = [1, 2]
            n = sum(ys)
            xs = [1, 2, 3]
            out << sum([x * n for x in xs])
        "},
        1,
    );
}

#[test]
fn an_induction_loop() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total
        "},
        &["LoopBreaker", "Memo"],
    );
}

#[test]
fn a_guarded_induction_loop() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                if x > 1:
                    total += x
            out << total
        "},
        &["LoopBreaker", "Memo"],
    );
}

#[test]
fn a_transaction_store_with_a_denied_proposal() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [50, 70, 10]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            out << await_final(pool)
        "},
        &["CommitBreaker", "Memo"],
    );
}

#[test]
fn a_transaction_store_of_two_writers() {
    answers_as_pull_mode_does(
        indoc! {"
            out = test_sink()
            pool: Mut(Int, Txn) := 1000
            for r in [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]:
                with begin():
                    pool := pool - r
            for r in [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]:
                with begin():
                    pool := pool - r
            out << await_final(pool)
        "},
        &["CommitBreaker", "Memo"],
    );
}

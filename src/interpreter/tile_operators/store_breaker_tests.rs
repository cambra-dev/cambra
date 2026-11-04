//! A store compiled from a program and consumed as a pipeline breaker with no notification
//! delivered: an induction store outside its loop's scope, whose rounds are tested in
//! `crate::interpreter::dispatcher::loop_scope`, and a transaction store of two writers, each
//! writer's source an input of its own.

use std::cell::RefCell;
use std::rc::Rc;

use indoc::indoc;

use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
use crate::interpreter::{BaseType, Extent, TestDataSource};

use super::test_helpers::keys_between;
use super::*;

/// `total` summed over `[1, 2, 3]` and written to `out`: 6.
const SUM: &str = indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        total += x
    out << total
"};

/// A loop over `source1()`, a source that delivers nothing and never completes.
const OVER_A_SOURCE: &str = indoc! {"
    out = test_sink()
    total := 0
    for x in source1():
        total += x
    out << total
"};

/// A program compiled with its sinks unpulled and no notification delivered, and its one store.
struct Compiled {
    _ctx: GlobalContext,
    program: crate::ccl::context::CompiledProgram,
    store: StoreCell,
}

impl Compiled {
    fn of(source: &str) -> Self {
        Self::with(source, |_| {})
    }

    fn over_an_empty_source(source: &str) -> Self {
        Self::with(source, |ctx| {
            ctx.register_source(Rc::new(RefCell::new(TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ))));
        })
    }

    fn with(source: &str, setup: impl FnOnce(&mut GlobalContext)) -> Self {
        let mut ctx = GlobalContext::default();
        ctx.defer_sink_pulls();
        let _sink = ctx.register_test_sink("out");
        setup(&mut ctx);
        let loaded = LoadedProgram::test(source);
        let program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
            .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
        let operators = ctx.take_operator_map();
        let mut stores = operators
            .operators()
            .into_iter()
            .filter(|fan| fan.cached_tile().is_some());
        let fan = stores.next().expect("a store's fan-out is cyclic");
        assert!(stores.next().is_none(), "one store");
        let store = fan.store().expect("the program subscribed its store");
        Self {
            _ctx: ctx,
            program,
            store,
        }
    }

    /// Pull each sink once, as pull mode does: its producer reads the store through a reader
    /// slot of the store's fan-out and releases what it is done with there.
    fn pull_sinks(&self) {
        for output in &self.program.outputs {
            if let Some(consumer) = &output.sink_consumer {
                consumer.borrow().pull_now();
            }
        }
    }

    /// Call `f` with the store as a pipeline breaker.
    fn breaker<R>(&self, f: impl FnOnce(&mut dyn BreakingProducer) -> R) -> R {
        let mut store = self.store.borrow_mut();
        f(store
            .as_breaking_mut()
            .expect("a store is a pipeline breaker"))
    }

    /// Consume all of the store's input `input`.
    fn consume_whole(&self, input: usize) {
        self.breaker(|store| {
            let whole = store.input_tiling(InputId(input)).universal_guard();
            store.consume_impl(InputId(input), whole);
        });
    }

    /// The store as a consuming breaker answers it.
    fn snapshot(&self) -> Tile {
        self.breaker(|store| {
            let guard = store.tiling().universal_guard();
            store.offer_impl(guard)
        })
    }
}

/// A consuming store answers a pull from its last step and pulls its body no more.
#[test]
fn a_consuming_store_answers_from_its_snapshot() {
    let compiled = Compiled::of(SUM);
    compiled.breaker(|store| store.consume_impl(InputId::ONLY, keys_between(0, 0)));
    let body_pulls = || {
        let mut pulls = 0;
        compiled
            .store
            .borrow()
            .visit_input_producers(&mut |role, input| {
                if role == "body" {
                    pulls = input.base().pulls;
                }
            });
        pulls
    };
    let before = body_pulls();
    let snapshot = compiled.snapshot();
    let whole = compiled.store.borrow().tiling().universal_guard();
    let pulled = compiled.store.borrow_mut().get(whole);
    assert_eq!(pulled, snapshot);
    assert_eq!(body_pulls(), before);
}

/// A store that is not terminal at the run's last epoch panics, naming where it stands.
#[test]
#[should_panic(expected = "an induction store finishes the run terminal")]
fn a_store_short_of_terminal_at_the_last_epoch_panics() {
    let compiled = Compiled::of(SUM);
    compiled.breaker(|store| store.consume_impl(InputId::ONLY, keys_between(0, 0)));
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        compiled.breaker(|store| store.finish(pushes, true))
    });
}

/// A morsel whose positions have not arrived panics: no step of the store reaches them.
#[test]
#[should_panic(expected = "is consumed only for positions its input releases")]
fn a_morsel_whose_positions_have_not_arrived_panics() {
    let compiled = Compiled::over_an_empty_source(OVER_A_SOURCE);
    compiled.breaker(|store| store.consume_impl(InputId::ONLY, keys_between(0, 0)));
}

/// Two writers of one transaction store, each drawing its items from the pool: writer 0 takes 10
/// and then 20, writer 1 takes 5. Key order commits 10, 5 and 20, leaving 90, 85 and 65.
const TWO_WRITERS: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20]:
        with begin():
            pool := pool - r
    for r in [5]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"};

/// The values the transaction store's one key took, in commit order.
fn committed(store: &Tile) -> Vec<Value> {
    let Tile::Store { state, .. } = store else {
        panic!("a transaction store renders a store: {store:?}")
    };
    let Tile::Record { fields, .. } = &**state else {
        panic!("a store's state is a record of changelogs: {state:?}")
    };
    let [name] = fields.keys().collect::<Vec<_>>()[..] else {
        panic!("the store holds one key: {fields:?}")
    };
    let key = crate::interpreter::operator_conversion::store_key(
        &crate::ccl::Label::from_runtime_key(name),
    );
    store
        .store_change_positions()
        .iter()
        .map(|tick| {
            crate::interpreter::commit_operator::store_value_at(store, tick, &key)
                .expect("a commit tick holds a value")
        })
        .collect()
}

/// How many times the store's inputs, its body or writers and its seeds, have been pulled.
fn input_pulls(compiled: &Compiled) -> u64 {
    let mut pulls = 0;
    compiled
        .store
        .borrow()
        .visit_input_producers(&mut |_, input| pulls += input.base().pulls);
    pulls
}

/// A store placed in a pipeline answers a pull before its first consume with the unopened store:
/// nothing terminal, and no input pulled. Its consumes then run as they would have.
#[rstest_log::rstest]
#[case::an_induction_store(SUM)]
#[case::a_transaction_store(TWO_WRITERS)]
fn a_placed_store_pulled_before_its_first_consume_answers_nothing_final(#[case] source: &str) {
    let compiled = Compiled::of(source);
    compiled.breaker(|store| {
        store
            .entry_placement(InputId(0))
            .expect("a store's input has an entry")
            .set(Some(PipelineId(0)))
    });
    let before = input_pulls(&compiled);
    let whole = compiled.store.borrow().tiling().universal_guard();
    let pulled = compiled.store.borrow_mut().get(whole);
    assert!(!pulled.is_terminal(), "{pulled:?}");
    assert_eq!(input_pulls(&compiled), before, "the pull steps nothing");
    if source == TWO_WRITERS {
        compiled.consume_whole(0);
        compiled.consume_whole(1);
        assert_eq!(
            committed(&compiled.snapshot()),
            [90, 85, 65].map(Value::Int).to_vec()
        );
    }
}

/// A consume of one writer's source takes its proposals and commits none of them while the other
/// writer has not passed their positions, and the positions taken count as released for that
/// writer's input.
#[test]
fn a_proposal_waits_for_the_other_writer_to_pass_its_position() {
    let compiled = Compiled::of(TWO_WRITERS);
    compiled.consume_whole(0);
    assert_eq!(committed(&compiled.snapshot()), Vec::<Value>::new());
    compiled.breaker(|store| {
        let whole = store.input_tiling(InputId(0)).universal_guard();
        let released = store.input_released(InputId(0));
        assert!(
            guard_minus(&whole, &released).is_empty(),
            "the positions taken are released for writer 0's input: {released:?}"
        );
    });
}

/// Writer 1's proposal and writer 0's second were built before writer 0's first commit, so both
/// go stale. Writer 1's, the smaller key, is proposed again and commits before writer 0's second
/// does: the store commits 5 before 20.
#[test]
fn a_stale_proposal_is_proposed_again_before_a_larger_key_commits() {
    let compiled = Compiled::of(TWO_WRITERS);
    compiled.consume_whole(0);
    compiled.consume_whole(1);
    assert_eq!(
        committed(&compiled.snapshot()),
        [90, 85, 65].map(Value::Int).to_vec()
    );
}

/// The last finish of the run's last epoch, across both inputs, commits what the store still
/// holds and leaves the store terminal; the first input's last finish leaves it as it was.
#[test]
fn the_last_finish_of_the_last_input_commits_the_rest() {
    let compiled = Compiled::of(TWO_WRITERS);
    compiled.consume_whole(0);
    let dispatcher = Dispatcher::new(vec![vec![], vec![]], usize::MAX);
    // Both sources closed, so the epoch is the run's last.
    dispatcher.close(PipelineId(1));
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        compiled.breaker(|store| store.finish(pushes, true))
    });
    assert_eq!(committed(&compiled.snapshot()), Vec::<Value>::new());
    assert!(!compiled.snapshot().is_terminal());
    dispatcher.finish_by_hand(PipelineId(1), |pushes| {
        compiled.breaker(|store| store.finish(pushes, true))
    });
    let settled = compiled.snapshot();
    assert_eq!(committed(&settled), [90, 85, 65].map(Value::Int).to_vec());
    assert!(settled.is_terminal(), "{settled:?}");
}

/// Three writers of one transaction store: writer 0 takes 10, 20, 30 and 40, writer 1 takes 1, 2
/// and 3, and writer 2 takes 5 and 7.
const THREE_WRITERS: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20, 30, 40]:
        with begin():
            pool := pool - r
    for r in [1, 2, 3]:
        with begin():
            pool := pool - r
    for r in [5, 7]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"};

/// A release of the store reclaims no version a proposal the store holds read.
///
/// Writer 0's proposal at position 2 is taken at tick 3, where it reads `pool`'s change at tick
/// 3. It waits for writer 1 to pass position 2 while position 1's items commit at ticks 4 to 6.
/// Writer 0, pulled again for its item at position 3, releases its slots below tick 6, writer 1's
/// last pull at tick 4 released its own below tick 4, and the sink's `await_final` releases its
/// slot through the frontier: the fan-out's meet reaches tick 3. A reclaim through tick 3 would
/// drop the change there, since `pool` changes again at tick 4, the first tick left, and the
/// held proposal's reads would no longer be the store's at its snapshot.
#[test]
fn a_release_reclaims_no_version_a_held_proposal_read() {
    let compiled = Compiled::of(THREE_WRITERS);
    let consume = |input: usize, position: u64| {
        compiled
            .breaker(|store| store.consume_impl(InputId(input), keys_between(position, position)));
    };
    consume(0, 0);
    consume(0, 1);
    consume(1, 0);
    consume(2, 0);
    consume(0, 2);
    consume(1, 1);
    consume(2, 1);
    consume(0, 3);
    compiled.pull_sinks();
    let dispatcher = Dispatcher::new(vec![vec![]; 3], usize::MAX);
    for input in [1, 2] {
        dispatcher.close(PipelineId(input));
    }
    for input in 0..3 {
        dispatcher.finish_by_hand(PipelineId(input), |pushes| {
            compiled.breaker(|store| store.finish(pushes, true))
        });
    }
    let settled = compiled.snapshot();
    assert!(settled.is_terminal(), "{settled:?}");
    assert_eq!(committed(&settled).last(), Some(&Value::Int(-18)));
}

/// Writer 1 reads a live source that has delivered its item at position 0 and called position 1
/// complete with nothing there, so writer 1 decides nothing at 1 and has decided no item past it.
/// Its proposal stream states position 1 decided once its drive has read past it, and writer 0's
/// proposal at position 1 commits on that statement alone.
#[test]
fn a_writer_stating_a_position_read_past_lets_a_larger_key_commit() {
    let feed = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        crate::ccl::Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    let registered = feed.clone();
    let compiled = Compiled::with(
        indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20]:
            with begin():
                pool := pool - r
        for r in source1():
            with begin():
                pool := pool - r
        out << await_final(pool)
    "},
        |ctx| ctx.register_source(registered),
    );
    {
        let mut feed = feed.borrow_mut();
        feed.add_data(&[(Value::UInt(0), Value::Int(5))]);
        feed.set_yield_predicate(Predicate::at_or_below(Value::UInt(1)));
    }
    compiled.consume_whole(0);
    let source: Rc<RefCell<dyn DataSourceDomainExtentImpl>> = feed.clone();
    compiled.breaker(|store| {
        store.read_source_again(&source);
        store.consume_impl(InputId(1), keys_between(0, 1));
    });
    assert_eq!(
        committed(&compiled.snapshot()),
        [90, 85, 65].map(Value::Int).to_vec()
    );
}

/// A store of several writers is refused where a writer's source positions are not `UInt`
/// positions, since key order compares one writer's positions with another's: a concatenation's
/// positions are tagged by the side they come from.
#[test]
fn several_writers_over_positions_that_are_no_uints_are_refused() {
    let compiled = Compiled::of(indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [1, 2] ++ [3]:
            with begin():
                pool := pool - r
        for r in [5]:
            with begin():
                pool := pool - r
        out << await_final(pool)
    "});
    let refusal = compiled.breaker(|store| store.no_consuming_mode());
    assert!(
        refusal
            .as_deref()
            .is_some_and(|why| why.contains("compares its writers' source positions as `UInt`")),
        "{refusal:?}"
    );
}

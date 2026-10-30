//! A transaction store compiled from a program and stepped through its store's fan-out.

use std::cell::RefCell;
use std::rc::Rc;

use indoc::indoc;

use crate::interpreter::commit_operator::store_frontier;
use crate::interpreter::dispatcher::{
    BreakerHandle, Dispatcher, Event, PipelineId, consume, finalize, run, start,
};
use crate::interpreter::{Value, tuple_field};

use super::fanout::MemoProducer;
use super::growing::ReadsBreaker;
use super::loop_breaker_tests::{Compiled, counting, pulled, written_after};
use super::*;

/// One writer draws a pool down by every item: 100 − 10 − 20 − 30 = 40.
const COUNTER: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20, 30]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"};

/// One guarded writer whose last item is denied: 70 commits and 50 fails `30 >= 50`, so 30.
const GRANT_DENY: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [70, 50]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"};

/// [`GRANT_DENY`] with an item after the denied one: 50 commits, 70 fails `50 >= 70`, and 10
/// commits, so 40. The deny leaves the store unchanged.
const DENY_THEN_ITEM: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [50, 70, 10]:
        with begin():
            if pool >= r:
                pool := pool - r
    out << await_final(pool)
"};

/// Two writers contend for a pool too small for both draws: the first serialized commits and
/// the other denies, so 40 in either order.
const MULTI_WRITER_GRANT_DENY: &str = indoc! {"
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
"};

/// Two writers of ten draws each conflict on every commit, so a losing writer retries its item
/// at each frontier: 1000 − 20 = 980 in every serialization.
const SUSTAINED_CONTENTION: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 1000
    for r in [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]:
        with begin():
            pool := pool - r
    for r in [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"};

/// The most steps a test program takes to close its store.
const STEP_BOUND: usize = 200;

/// The guard each writer's drive has released of its source, in writer order, read through
/// `reader`, a slot of the store's fan-out.
fn sources_released(reader: &dyn TileProducer) -> Vec<TileGuard> {
    writer_sources(reader, |source| source.obsolete_guard().clone())
}

/// A reader slot of `compiled`'s store, for [`sources_released`].
fn reader_of(compiled: &mut Compiled) -> Box<dyn TileProducer> {
    let mut slot = compiled.fan.slot();
    let guard = slot.tiling().universal_guard();
    slot.subscribe(guard, Box::new(|| {}), compiled.ctx.scheduler())
}

/// Step a compiled transaction store with no notification delivered between steps until it is
/// terminal. Each step raises the store's frontier, releases more of some writer's source, or
/// closes the store, and the store then holds the value pull mode writes, which is one value
/// because every test program gives the same result in every serialization. Answers what the
/// sources had released after each step that left the frontier where it was.
fn steps_to_terminal(source: &str) -> Vec<Vec<TileGuard>> {
    let mut compiled = Compiled::of(source);
    let reader = reader_of(&mut compiled);
    let mut store = compiled.fan.cached_tile().expect("a snapshot");
    let mut released = sources_released(&*reader);
    let mut frontier_held = Vec::new();
    for _ in 0..STEP_BOUND {
        if store.is_terminal() {
            break;
        }
        let next = compiled.fan.step();
        let next_released = sources_released(&*reader);
        let rose = store_frontier(&next) > store_frontier(&store);
        let grew = next_released
            .iter()
            .zip(&released)
            .any(|(now, before)| !guard_minus(now, before).is_empty());
        assert!(
            rose || grew || next.is_terminal(),
            "{source}: a step raises the frontier, releases source positions, or closes the \
             store; it stayed at {store:?} with sources released at {released:?}"
        );
        if !rose && !next.is_terminal() {
            frontier_held.push(next_released.clone());
        }
        store = next;
        released = next_released;
    }
    assert!(
        store.is_terminal(),
        "{source}: the store closes within {STEP_BOUND} steps"
    );
    assert!(
        released.iter().all(TileGuard::is_universal),
        "{source}: a terminal store's drives have released their sources whole: {released:?}"
    );
    assert_eq!(compiled.value(), pulled(source), "{source}");
    frontier_held
}

#[test]
fn a_single_writer_steps_to_its_final_value() {
    steps_to_terminal(COUNTER);
}

#[test]
fn a_denied_last_item_steps_to_its_final_value() {
    steps_to_terminal(GRANT_DENY);
}

/// A deny leaves the store unchanged, so the step after it reaches the drive's next item only
/// because a step notifies the recurrence while the store is not terminal. The deny is the one
/// step that leaves the frontier where it was, and it releases the source through the denied
/// item, position 1, and no further.
#[test]
fn an_item_after_a_deny_steps_to_its_final_value() {
    let held = steps_to_terminal(DENY_THEN_ITEM);
    let [released] = held.as_slice() else {
        panic!("one step leaves the frontier where it was: {held:?}")
    };
    let [TileGuard::Function(FunctionGuard::Domain(released))] = released.as_slice() else {
        panic!("one writer releases a run of its source's positions: {released:?}")
    };
    assert!(
        released.contains(&Value::UInt(1)) && !released.contains(&Value::UInt(2)),
        "the deny releases the source through position 1: {released:?}"
    );
    assert_eq!(pulled(DENY_THEN_ITEM), Value::Int(40));
}

#[test]
fn contending_writers_with_a_deny_step_to_their_final_value() {
    steps_to_terminal(MULTI_WRITER_GRANT_DENY);
}

#[test]
fn sustained_contention_steps_to_its_final_value() {
    steps_to_terminal(SUSTAINED_CONTENTION);
    assert_eq!(pulled(SUSTAINED_CONTENTION), Value::Int(980));
}

/// The breaker of a compiled transaction store, as the dispatcher holds it.
fn breaker_of(compiled: &mut Compiled) -> BreakerHandle {
    Rc::new(RefCell::new(CommitBreaker::new(
        compiled.fan.clone(),
        compiled.ctx.scheduler(),
    )))
}

/// The store's pipeline, ordered, at morsels of `rows`, alone.
fn store_pipeline(rows: usize) -> Dispatcher {
    let mut dispatcher = Dispatcher::new(vec![vec![]], rows);
    dispatcher.order(PipelineId(0));
    dispatcher
}

/// A transaction store run through the dispatcher at morsels of one source position, three, and
/// one per guard ends terminal with its sources released whole and the same store at every
/// morsel size. A parent pipeline, a memo reading the store's breaker, consumes the whole store
/// its finalize pushes. The value equals the one pull mode writes, which is one value because
/// every test program gives the same result in every serialization. After the run the store's
/// own queued notification reaches a reader outside the store, and the program's sink chain,
/// pulled by a scheduler, writes that value.
fn runs_through_the_dispatcher(source: &str) {
    let expected = pulled(source);
    let mut stores = Vec::new();
    for rows in [1, 3, usize::MAX] {
        let mut compiled = Compiled::of(source);
        let mut outside_slot = compiled.fan.slot();
        let (outside, _outside) = counting(&mut outside_slot, compiled.ctx.scheduler());
        let breaker = breaker_of(&mut compiled);
        let whole = compiled.fan.tiling().universal_guard();
        let parent: BreakerHandle = Rc::new(RefCell::new(MemoProducer::over(
            Box::new(ReadsBreaker::of(&breaker)),
            compiled.fan.tiling(),
        )));
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], rows);
        dispatcher.order(PipelineId(0));
        run(&dispatcher, &[breaker.clone(), parent]);
        let parent_consumed: Vec<TileGuard> = dispatcher
            .into_events()
            .into_iter()
            .filter_map(|event| match event {
                Event::Consume {
                    pipeline: PipelineId(1),
                    guard,
                } => Some(guard),
                _ => None,
            })
            .collect();
        assert_eq!(
            parent_consumed,
            vec![whole],
            "{source} at morsels of {rows}: the parent consumes the whole store"
        );
        assert_eq!(compiled.value(), expected, "{source} at morsels of {rows}");
        let store = compiled.fan.cached_tile().expect("a snapshot");
        assert!(store.is_terminal(), "{source} at morsels of {rows}");
        assert!(
            breaker.borrow().input_released().is_universal(),
            "{source} at morsels of {rows}: the sources are released whole"
        );
        stores.push(store);

        assert_eq!(outside.get(), 0, "a run wakes no reader outside the store");
        let value = written_after(&mut compiled, source);
        assert!(outside.get() > 0, "the store's own notification reaches it");
        assert_eq!(value, expected, "{source} at morsels of {rows}");
    }
    assert!(
        stores.windows(2).all(|pair| pair[0] == pair[1]),
        "{source}: every morsel size makes the same steps, so the same store: {stores:?}"
    );
}

#[test]
fn a_single_writer_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(COUNTER);
}

#[test]
fn a_denied_last_item_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(GRANT_DENY);
}

#[test]
fn an_item_after_a_deny_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(DENY_THEN_ITEM);
}

#[test]
fn contending_writers_with_a_deny_run_through_the_dispatcher() {
    runs_through_the_dispatcher(MULTI_WRITER_GRANT_DENY);
}

#[test]
fn sustained_contention_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(SUSTAINED_CONTENTION);
}

/// Each morsel of one source position steps the store until that item is finished and no
/// later one, a deny included, and the store is terminal after the last morsel only.
#[test]
fn a_morsel_steps_the_store_to_its_last_item() {
    let mut compiled = Compiled::of(DENY_THEN_ITEM);
    let breaker = breaker_of(&mut compiled);
    let dispatcher = store_pipeline(1);
    let breakers = [breaker];
    start(&dispatcher, &breakers);
    for position in 0..3 {
        let package = dispatcher.pop().expect("a morsel per source position");
        consume(&dispatcher, &breakers, package);
        let store = compiled.fan.cached_tile().expect("a snapshot");
        let released = breakers[0].borrow().input_released();
        assert_eq!(store.is_terminal(), position == 2);
        if position == 2 {
            assert!(released.is_universal(), "{released:?}");
            continue;
        }
        let TileGuard::Function(FunctionGuard::Domain(released)) = released else {
            panic!("a source releases a run of its positions: {released:?}")
        };
        assert!(
            released.contains(&Value::UInt(position))
                && !released.contains(&Value::UInt(position + 1)),
            "the morsel at {position} finishes that item and no later one: {released:?}"
        );
    }
    assert!(dispatcher.pop().is_none());
    finalize(&dispatcher, &breakers, PipelineId(0));
}

/// A store is finalized only once it is terminal: nothing steps it after.
#[test]
#[should_panic(expected = "a transaction store finalizes after it is terminal")]
fn a_store_finalized_before_it_is_terminal_panics() {
    let mut compiled = Compiled::of(COUNTER);
    let breaker = breaker_of(&mut compiled);
    let dispatcher = Dispatcher::new(vec![vec![]], 1);
    breaker
        .borrow_mut()
        .finalize(&mut dispatcher.pushes(PipelineId(0)));
}

/// A store of several writers reads a record of their sources, which has no keys to cut, so it
/// refuses a guard that is not its whole input.
#[test]
#[should_panic(expected = "a store of 2 writers consumes its input whole")]
fn a_store_of_several_writers_refuses_part_of_its_input() {
    let mut compiled = Compiled::of(MULTI_WRITER_GRANT_DENY);
    let breaker = breaker_of(&mut compiled);
    let TileGuard::Record(mut fields) = breaker.borrow().input_tiling().universal_guard() else {
        panic!("a record of the writers' sources")
    };
    fields.insert(
        tuple_field(1),
        TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
    );
    breaker.borrow_mut().consume_impl(TileGuard::Record(fields));
}

/// A transaction store that is terminal is not stepped again.
#[test]
#[should_panic(expected = "a transaction store is not stepped once terminal")]
fn a_terminal_transaction_store_is_not_stepped() {
    let mut compiled = Compiled::of(COUNTER);
    let mut breaker = CommitBreaker::new(compiled.fan.clone(), compiled.ctx.scheduler());
    breaker.consume_impl(breaker.input_tiling().universal_guard());
    breaker.step();
}

/// A transaction store over a source that delivers nothing decides nothing once it has opened:
/// the breaker holds the morsel back, and a finalize that finds it still held back reports the
/// stall.
#[test]
#[should_panic(
    expected = "a transaction store finalizes after it is terminal: a step decides nothing"
)]
fn a_transaction_store_that_decides_nothing_is_a_stall() {
    let mut compiled = Compiled::over_an_empty_source(indoc! {"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in source1():
            with begin():
                pool := pool - r
        out << await_final(pool)
    "});
    let breaker: BreakerHandle = Rc::new(RefCell::new(CommitBreaker::new(
        compiled.fan.clone(),
        compiled.ctx.scheduler(),
    )));
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    run(&dispatcher, &[breaker]);
}

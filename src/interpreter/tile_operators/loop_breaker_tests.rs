//! An induction loop compiled from a program and stepped through its store's fan-out.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use indoc::indoc;

use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::commit_operator::store_frontier;
use crate::interpreter::dispatcher::{
    BreakerHandle, Dispatcher, PipelineId, consume, finalize, run, start,
};
use crate::interpreter::operator_conversion::OperatorMap;
use crate::interpreter::{Position, TestSink, Value};

use super::growing::ints;
use super::loop_breaker::{Reach, reach};
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

/// [`SUM`] with the write guarded by `x > 1`: 5. The guard puts `Memo`s inside the cycle,
/// between the drive and the store's body.
const GUARDED_SUM: &str = indoc! {"
    out = test_sink()
    total := 0
    for x in [1, 2, 3]:
        if x > 1:
            total += x
    out << total
"};

/// A program compiled with no notification delivered, and the cyclic fan-out of its one store.
pub(super) struct Compiled {
    pub(super) ctx: GlobalContext,
    program: CompiledProgram,
    sink: std::sync::Arc<TestSink>,
    operators: OperatorMap,
    pub(super) fan: Rc<FanOut>,
}

impl Compiled {
    pub(super) fn of(source: &str) -> Self {
        let mut ctx = GlobalContext::default();
        let sink = ctx.register_test_sink("out");
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
        Self {
            ctx,
            program,
            sink,
            operators,
            fan,
        }
    }

    /// The value the store holds for its one variable.
    pub(super) fn value(&self) -> Value {
        let state = self.operators.live_state();
        assert_eq!(state.len(), 1, "one variable: {state:?}");
        state.into_values().next().expect("one variable")
    }
}

/// The one value `out` receives when the program runs in pull mode, the scheduler delivering
/// every notification between pulls.
pub(super) fn pulled(source: &str) -> Value {
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
    written(&sink, source)
}

/// The one value `sink` received.
fn written(sink: &TestSink, source: &str) -> Value {
    let written = sink.value().expect("the sink holds a value");
    let [binding] = written.as_function().as_slice() else {
        panic!("{source} writes one value: {written:?}")
    };
    binding.output.clone()
}

/// Step a compiled loop with no notification delivered between steps: each step decides one
/// position, the last closes the store, and the store then holds what pull mode writes.
fn steps_one_position_per_step(source: &str, positions: u64) {
    let compiled = Compiled::of(source);
    for position in 0..positions {
        let tile = compiled.fan.step();
        assert_eq!(
            store_frontier(&tile),
            Some(Position::new(Value::UInt(position))),
            "{source}: step {position} decides position {position}"
        );
        assert_eq!(
            tile.is_terminal(),
            position + 1 == positions,
            "{source}: the store closes at its last position only"
        );
    }
    assert_eq!(compiled.value(), pulled(source), "{source}");
}

#[test]
fn a_flat_loop_steps_one_position_per_step() {
    steps_one_position_per_step(SUM, 3);
}

#[test]
fn a_guarded_loop_steps_one_position_per_step() {
    steps_one_position_per_step(GUARDED_SUM, 3);
}

/// How many notifications a test's consumer received.
// shared-state-ok: a test consumer counts what it is notified of and the test reads the count; no
// tile passes between operators through it.
pub(super) type Count = Rc<Cell<usize>>;

/// A subscription to `slot` that counts the notifications it receives.
pub(super) fn counting(
    slot: &mut Box<dyn TileOperator>,
    scheduler: &mut Scheduler,
) -> (Count, Box<dyn TileProducer>) {
    let count = Rc::new(Cell::new(0));
    let counted = count.clone();
    let guard = slot.tiling().universal_guard();
    let producer = slot.subscribe(
        guard,
        Box::new(move || counted.set(counted.get() + 1)),
        scheduler,
    );
    (count, producer)
}

/// A step notifies the subscribers of the store's recurrence slots and no reader outside the
/// loop, and a step once the terminal snapshot is announced notifies no one. The store's own
/// notification reaches a reader outside the loop once the scheduler delivers it.
#[test]
fn a_step_notifies_the_recurrence_and_no_reader() {
    let mut compiled = Compiled::of(GUARDED_SUM);
    let mut inside_slot = compiled.fan.recurrence_slot();
    let mut outside_slot = compiled.fan.slot();
    let (inside, _inside) = counting(&mut inside_slot, compiled.ctx.scheduler());
    let (outside, _outside) = counting(&mut outside_slot, compiled.ctx.scheduler());
    let mut last = compiled.fan.step();
    for _ in 1..3 {
        last = compiled.fan.step();
    }
    assert!(last.is_terminal());
    assert_eq!(
        outside.get(),
        0,
        "a reader outside the loop is not notified"
    );
    assert!(inside.get() > 0, "the recurrence is notified");
    compiled.ctx.scheduler().check_for_notifications();
    assert!(
        outside.get() > 0,
        "the store's own notification, delivered by the scheduler, reaches a reader outside the loop"
    );
    // The terminal snapshot is announced by the next step, and nothing after it.
    compiled.fan.step();
    let notified = inside.get();
    compiled.fan.step();
    assert_eq!(
        inside.get(),
        notified,
        "a step at an announced terminal snapshot notifies no one"
    );
}

/// A recurrence subscriber that pulls inside a step's notification would step the store a second
/// time within the step, which a debug build refuses.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "a recurrence subscriber pulls nothing inside a step's notification")]
fn a_recurrence_subscriber_pulling_inside_a_notification_is_refused() {
    let mut compiled = Compiled::of(SUM);
    let late: Rc<RefCell<Option<Box<dyn TileProducer>>>> = Rc::new(RefCell::new(None));
    let pulls = late.clone();
    let mut slot = compiled.fan.recurrence_slot();
    let guard = slot.tiling().universal_guard();
    let producer = slot.subscribe(
        guard.clone(),
        Box::new(move || {
            if let Some(producer) = pulls.borrow_mut().as_mut() {
                producer.get(guard.clone());
            }
        }),
        compiled.ctx.scheduler(),
    );
    *late.borrow_mut() = Some(producer);
    for _ in 0..3 {
        compiled.fan.step();
    }
}

/// The value the program's own sink chain writes when a scheduler pulls it after a run: its
/// `StoreFinalRead` learns of the terminal store from the store's own queued notification.
pub(super) fn written_after(compiled: &mut Compiled, source: &str) -> Value {
    let done = (0..1000).any(|_| {
        compiled.ctx.scheduler().check_for_notifications();
        compiled.program.done.try_recv().is_ok()
    });
    assert!(done, "{source}: the program completes after the run");
    written(&compiled.sink, source)
}

/// The breaker of a compiled loop, as the dispatcher holds it.
fn breaker_of(compiled: &mut Compiled) -> BreakerHandle {
    Rc::new(RefCell::new(LoopBreaker::new(
        compiled.fan.clone(),
        compiled.ctx.scheduler(),
    )))
}

/// The loop's pipeline, ordered, at morsels of `rows`.
fn loop_pipeline(rows: usize) -> Dispatcher {
    let mut dispatcher = Dispatcher::new(vec![vec![]], rows);
    dispatcher.order(PipelineId(0));
    dispatcher
}

/// A loop run through the dispatcher at morsels of one position, three, and one per guard ends
/// with the value pull mode writes and its store terminal, and its finalize pushes the whole
/// store. After the run the store's own queued notification reaches a reader outside the loop,
/// and the program's sink chain, pulled by a scheduler, writes the value pull mode writes.
fn runs_through_the_dispatcher(source: &str) {
    let expected = pulled(source);
    for rows in [1, 3, usize::MAX] {
        let mut compiled = Compiled::of(source);
        let mut outside_slot = compiled.fan.slot();
        let (outside, _outside) = counting(&mut outside_slot, compiled.ctx.scheduler());
        let breaker = breaker_of(&mut compiled);
        run(&loop_pipeline(rows), std::slice::from_ref(&breaker));
        assert_eq!(compiled.value(), expected, "{source} at morsels of {rows}");
        assert!(compiled.fan.cached_tile().is_some_and(|t| t.is_terminal()));

        let pushes_to = Dispatcher::new(vec![vec![], vec![0]], rows);
        pushes_to.finalize_by_hand(PipelineId(0), |pushes| {
            breaker.borrow_mut().finalize(pushes)
        });
        let pushed = pushes_to.pop().expect("the store's final guard").guard;
        assert_eq!(pushed, compiled.fan.tiling().universal_guard());

        assert_eq!(outside.get(), 0, "a run wakes no reader outside the loop");
        let value = written_after(&mut compiled, source);
        assert!(outside.get() > 0, "the store's own notification reaches it");
        assert_eq!(value, expected, "{source} at morsels of {rows}");
    }
}

#[test]
fn a_flat_loop_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(SUM);
}

#[test]
fn a_guarded_loop_runs_through_the_dispatcher() {
    runs_through_the_dispatcher(GUARDED_SUM);
}

/// Each morsel of one position steps the loop to that position and no further, and the store
/// is terminal at the last one only.
#[test]
fn a_morsel_steps_the_loop_to_its_highest_position() {
    let mut compiled = Compiled::of(GUARDED_SUM);
    let breaker = breaker_of(&mut compiled);
    let dispatcher = loop_pipeline(1);
    let breakers = [breaker];
    start(&dispatcher, &breakers);
    for position in 0..3 {
        let package = dispatcher.pop().expect("a morsel per position");
        consume(&dispatcher, &breakers, package);
        let store = compiled.fan.cached_tile().expect("a snapshot");
        assert_eq!(
            store_frontier(&store),
            Some(Position::new(Value::UInt(position)))
        );
        assert_eq!(store.is_terminal(), position == 2);
    }
    assert!(dispatcher.pop().is_none());
    finalize(&dispatcher, &breakers, PipelineId(0));
}

/// A loop is finalized only once its store is terminal: nothing steps it after.
#[test]
#[should_panic(expected = "a loop finalizes after its store is terminal")]
fn a_loop_finalized_before_its_store_is_terminal_panics() {
    let mut compiled = Compiled::of(SUM);
    let breaker = breaker_of(&mut compiled);
    let dispatcher = Dispatcher::new(vec![vec![]], 1);
    breaker
        .borrow_mut()
        .finalize(&mut dispatcher.pushes(PipelineId(0)));
}

/// A morsel reaches through its highest position, or through every position where its right
/// end has no bound.
#[test]
fn a_morsel_reaches_through_its_highest_position() {
    let through = |guard: TileGuard| match reach(&guard) {
        Reach::Through(at) => Some(at),
        Reach::Unbounded => None,
    };
    assert_eq!(
        through(keys_between(0, 2)),
        Some(Position::new(Value::UInt(2)))
    );
    let below = Predicate::below(Value::UInt(3));
    assert_eq!(
        through(TileGuard::Function(FunctionGuard::Domain(below))),
        Some(Position::new(Value::UInt(2)))
    );
    let above = Predicate::True.minus(&Predicate::below(Value::UInt(3)));
    assert_eq!(
        through(TileGuard::Function(FunctionGuard::Domain(above))),
        None
    );
    assert_eq!(through(ints().universal_guard()), None);
}

/// A guard that is no run of positions is refused rather than read as reaching everything.
#[test]
#[should_panic(expected = "a loop's morsel is a guard of its positions")]
fn a_guard_of_no_positions_is_refused_as_a_morsel() {
    reach(&TileGuard::Scalar(Predicate::True));
}

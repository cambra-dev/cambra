//! An induction loop compiled from a program and stepped through its store's fan-out.

use std::cell::Cell;
use std::rc::Rc;

use indoc::indoc;

use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::commit_operator::store_frontier;
use crate::interpreter::operator_conversion::OperatorMap;
use crate::interpreter::{Position, Value};

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
struct Compiled {
    ctx: GlobalContext,
    _program: CompiledProgram,
    operators: OperatorMap,
    fan: Rc<FanOut>,
}

impl Compiled {
    fn of(source: &str) -> Self {
        let mut ctx = GlobalContext::default();
        ctx.register_test_sink("out");
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
            _program: program,
            operators,
            fan,
        }
    }

    /// The value the store holds for its one variable.
    fn value(&self) -> Value {
        let state = self.operators.live_state();
        assert_eq!(state.len(), 1, "one variable: {state:?}");
        state.into_values().next().expect("one variable")
    }
}

/// The one value `out` receives when the program runs in pull mode, the scheduler delivering
/// every notification between pulls.
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
type Count = Rc<Cell<usize>>;

/// A subscription to `slot` that counts the notifications it receives.
fn counting(
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
/// loop, and a step once every snapshot is announced notifies no one. The store's own
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
        "a step that changes nothing notifies no one"
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

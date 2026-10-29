//! An induction loop compiled from a program and stepped through its store's fan-out.

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
    _ctx: GlobalContext,
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
            _ctx: ctx,
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
#[ignore = "stalls: the Memo on the drive's output answers its cache until a notification the \
            store's step queues on the scheduler is delivered"]
fn a_guarded_loop_steps_one_position_per_step() {
    steps_one_position_per_step(GUARDED_SUM, 3);
}

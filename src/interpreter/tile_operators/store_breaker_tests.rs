//! A store compiled from a program and consumed as a pipeline breaker with no notification
//! delivered: an induction store outside its loop's scope, whose rounds are tested in
//! `crate::interpreter::dispatcher::loop_scope`, and a transaction store of two writers, each
//! writer's source an input of its own.

use std::cell::RefCell;
use std::rc::Rc;

use indoc::indoc;

use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
use crate::interpreter::{BaseType, Extent, TestDataSource};

use super::test_helpers::{ConsumeInPipeline as _, keys_between};
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
    _program: CompiledProgram,
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
        store
            .borrow_mut()
            .as_breaking_mut()
            .expect("a store breaks a pipeline")
            .begin_run();
        Self {
            _ctx: ctx,
            _program: program,
            store,
        }
    }

    /// Call `f` with the store as a pipeline breaker, placed in a pipeline as a dispatched run puts
    /// it.
    fn breaker<R>(&self, f: impl FnOnce(&mut dyn BreakingProducer) -> R) -> R {
        let mut store = self.store.borrow_mut();
        let store = store
            .as_breaking_mut()
            .expect("a store is a pipeline breaker");
        f(store)
    }

    /// The breaker the store's body reads: an induction store's drive.
    fn drive(&self) -> crate::interpreter::dispatcher::BreakerHandle {
        test_helpers::drive_of(&**self.store.borrow())
    }

    /// Step an induction store to `position` as its loop's scope does: open the store with a
    /// consume at no position, consume the drive at the position, which emits it into the body
    /// once the store has decided the position before, then consume the store at it.
    fn step_to(&self, position: u64) {
        self.breaker(|store| {
            let none = store.input_tiling(InputId::ONLY).empty_guard();
            store.consume_in_pipeline(InputId::ONLY, none);
        });
        let guard = keys_between(position, position);
        self.drive()
            .borrow_mut()
            .consume_in_pipeline(InputId::ONLY, guard.clone());
        self.breaker(|store| store.consume_in_pipeline(InputId::ONLY, guard));
    }

    /// The store as a consuming breaker answers it.
    fn snapshot(&self) -> Tile {
        self.breaker(|store| {
            let guard = store.tiling().universal_guard();
            store.get(guard)
        })
    }
}

/// An induction store short of terminal holds the positions it has stepped, its decided region,
/// which grows a position a step.
#[test]
fn an_induction_store_decides_each_position_it_steps() {
    let compiled = Compiled::of(SUM);
    let decided = || compiled.breaker(|store| (store.final_guard(), store.complete()));
    compiled.step_to(0);
    let (held, after_one) = decided();
    assert_eq!(held, after_one);
    compiled.step_to(1);
    let (_, after_two) = decided();
    assert!(
        !after_one.is_empty() && guard_minus(&after_one, &after_two).is_empty(),
        "each step grows what is decided: {after_one:?}, then {after_two:?}"
    );
    assert!(
        !guard_minus(&after_two, &after_one).is_empty(),
        "the second step decides a position the first did not: {after_one:?}, then {after_two:?}"
    );
}

/// A consuming store answers a pull from its last step and pulls its body no more.
#[test]
fn a_consuming_store_answers_from_its_snapshot() {
    let compiled = Compiled::of(SUM);
    compiled.step_to(0);
    let body_pulls = || {
        let mut pulls = 0;
        compiled
            .store
            .borrow()
            .visit_input_producers(&mut |role, input| {
                if role == "body" {
                    pulls = input.base().reads.get();
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

/// A store that is not terminal at its finish panics, naming where it stands.
#[test]
#[should_panic(expected = "an induction store finishes the run terminal")]
fn a_store_short_of_terminal_at_its_finish_panics() {
    let compiled = Compiled::of(SUM);
    compiled.step_to(0);
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    dispatcher.finish_by_hand(PipelineId(0), |pushes| {
        compiled.breaker(|store| store.finish(InputId::ONLY, pushes))
    });
}

/// A morsel whose positions have not arrived steps nothing: the store steps only the positions its
/// input has decided, and the morsel stays unreleased.
#[test]
fn a_morsel_whose_positions_have_not_arrived_steps_nothing() {
    let compiled = Compiled::over_an_empty_source(OVER_A_SOURCE);
    compiled.breaker(|store| {
        store.consume_in_pipeline(InputId::ONLY, keys_between(0, 0));
        assert!(
            !guard_minus(&keys_between(0, 0), &store.input_released(InputId::ONLY)).is_empty(),
            "the morsel stays unreleased"
        );
    });
}

/// Two writers of one transaction store, each drawing its items from the pool: writer 0 takes 10
/// and then 20, writer 1 takes 5. Consuming writer 0 first commits 10 and 20 before 5.
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

/// How many times the store's inputs, its body or writers and its seeds, have been pulled.
fn input_pulls(compiled: &Compiled) -> u64 {
    let mut pulls = 0;
    compiled
        .store
        .borrow()
        .visit_input_producers(&mut |_, input| pulls += input.base().reads.get());
    pulls
}

/// A consuming store answers a pull before its first consume with the unopened store: nothing
/// terminal, and no input pulled.
#[rstest_log::rstest]
#[case::an_induction_store(SUM)]
#[case::a_transaction_store(TWO_WRITERS)]
fn a_consuming_store_pulled_before_its_first_consume_answers_nothing_final(#[case] source: &str) {
    let compiled = Compiled::of(source);
    compiled.breaker(|_| {});
    let before = input_pulls(&compiled);
    let whole = compiled.store.borrow().tiling().universal_guard();
    let pulled = compiled.store.borrow_mut().get(whole);
    assert!(!pulled.is_terminal(), "{pulled:?}");
    assert_eq!(input_pulls(&compiled), before, "the pull steps nothing");
}

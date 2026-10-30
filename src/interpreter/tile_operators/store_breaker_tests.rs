//! An induction store compiled from a program and consumed as a pipeline breaker outside its
//! loop's scope, with no notification delivered. The scope's rounds are tested in
//! `crate::interpreter::dispatcher::loop_scope`.

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
        compile_program(&mut ctx, &loaded, Box::new(|| {}))
            .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
        let operators = ctx.take_operator_map();
        let mut stores = operators
            .operators()
            .into_iter()
            .filter(|fan| fan.cached_tile().is_some());
        let fan = stores.next().expect("a store's fan-out is cyclic");
        assert!(stores.next().is_none(), "one store");
        let store = fan.store().expect("the program subscribed its store");
        Self { _ctx: ctx, store }
    }

    /// Call `f` with the store as a pipeline breaker, in consuming mode as a dispatched run puts
    /// it.
    fn breaker<R>(&self, f: impl FnOnce(&mut dyn BreakingProducer) -> R) -> R {
        let mut store = self.store.borrow_mut();
        let store = store
            .as_breaking_mut()
            .expect("an induction store is a pipeline breaker");
        store.enter_consuming_mode();
        f(store)
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

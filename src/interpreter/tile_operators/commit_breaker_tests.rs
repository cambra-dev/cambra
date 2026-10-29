//! A transaction store compiled from a program and stepped through its store's fan-out.

use indoc::indoc;

use crate::interpreter::Value;

use super::loop_breaker_tests::{Compiled, pulled};
use super::*;

/// One writer draws a pool down by every item: 100 − 10 − 20 − 30 = 40.
pub(super) const COUNTER: &str = indoc! {"
    out = test_sink()
    pool: Mut(Int, Txn) := 100
    for r in [10, 20, 30]:
        with begin():
            pool := pool - r
    out << await_final(pool)
"};

/// One guarded writer whose last item is denied: 70 commits and 50 fails `30 >= 50`, so 30.
pub(super) const GRANT_DENY: &str = indoc! {"
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
pub(super) const DENY_THEN_ITEM: &str = indoc! {"
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
pub(super) const MULTI_WRITER_GRANT_DENY: &str = indoc! {"
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
pub(super) const SUSTAINED_CONTENTION: &str = indoc! {"
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
pub(super) fn sources_released(reader: &dyn TileProducer) -> Vec<TileGuard> {
    let mut released = Vec::new();
    reader.visit_input_producers(&mut |name, store| {
        if name != "input" {
            return;
        }
        store.visit_input_producers(&mut |name, writer| {
            if name != "writer" {
                return;
            }
            writer.visit_input_producers(&mut |name, driver_slot| {
                if name != "driver" {
                    return;
                }
                driver_slot.visit_input_producers(&mut |name, driver| {
                    if name != "input" {
                        return;
                    }
                    driver.visit_input_producers(&mut |name, source| {
                        if name == "source" {
                            released.push(source.obsolete_guard().clone());
                        }
                    });
                });
            });
        });
    });
    released
}

/// A reader slot of `compiled`'s store, for [`sources_released`].
fn reader_of(compiled: &mut Compiled) -> Box<dyn TileProducer> {
    let mut slot = compiled.fan.slot();
    let guard = slot.tiling().universal_guard();
    slot.subscribe(guard, Box::new(|| {}), compiled.ctx.scheduler())
}

/// Step a compiled transaction store with no notification delivered between steps until it is
/// terminal. Each step changes the store's snapshot or releases more of some writer's source,
/// and the store then holds what pull mode writes. Answers how many steps released source
/// positions and left the snapshot unchanged.
fn steps_to_terminal(source: &str) -> usize {
    let mut compiled = Compiled::of(source);
    let reader = reader_of(&mut compiled);
    let mut store = compiled.fan.cached_tile().expect("a snapshot");
    let mut released = sources_released(&*reader);
    let mut unchanged_store = 0;
    for _ in 0..STEP_BOUND {
        if store.is_terminal() {
            break;
        }
        let next = compiled.fan.step();
        let next_released = sources_released(&*reader);
        let store_moved = next != store;
        assert!(
            store_moved || next_released != released,
            "{source}: a step changes the store or releases source positions; it stayed at \
             {store:?} with sources released at {released:?}"
        );
        if !store_moved {
            unchanged_store += 1;
        }
        store = next;
        released = next_released;
    }
    assert!(
        store.is_terminal(),
        "{source}: the store closes within {STEP_BOUND} steps"
    );
    assert_eq!(compiled.value(), pulled(source), "{source}");
    unchanged_store
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
/// because a step notifies the recurrence while the store is not terminal.
#[test]
fn an_item_after_a_deny_steps_to_its_final_value() {
    assert!(
        steps_to_terminal(DENY_THEN_ITEM) > 0,
        "the deny is a step that releases a source position and leaves the store unchanged"
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

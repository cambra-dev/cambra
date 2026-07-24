//! The CLI driver contract: a notification-gated drive loop (as in
//! `src/main.rs`) must converge a mutation-loop accumulator, whose `Recurse`
//! cycle advances one position per pull and requests its own re-pull through the
//! scheduler's deferred-wakeup queue.
//!
//! Before that mechanism existed, the first `get` returned an empty
//! (non-terminal) tile and no further notification arrived — the domain source
//! (a finite literal) had already fired — so the driver spun in
//! `while !new_data { check_for_notifications() }` forever. These tests replicate
//! the driver with **bounded** waits, so a lost-wakeup regression fails the test
//! rather than hanging it.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{
    ColumnValue, Consumer, Tile, TileGuard, Value, tile_operators::FunctionGuard,
};

/// Drive a program's `main` output exactly as `src/main.rs` does — pull only
/// after a notification, stop on a universal release — but with iteration caps
/// that convert a hang into a panic. Returns the final (terminal) tile.
fn drive_main_output(code: &str) -> Tile {
    const CAP: usize = 1000;

    let new_data = Rc::new(RefCell::new(false));
    let nd = new_data.clone();
    let consumer: Box<dyn Consumer> = Box::new(move || *nd.borrow_mut() = true);

    let mut ctx = GlobalContext::default();
    let mut compiled = match compile_program(&mut ctx, code, consumer) {
        Ok(c) => c,
        Err(e) => panic!("compile failed: {e:?}"),
    };
    let mut producer = compiled
        .main_mut()
        .and_then(|o| o.producer.take())
        .expect("program has a `main` output");
    let universal = producer.tiling().universal_guard();

    let mut pulls = 0;
    loop {
        pulls += 1;
        assert!(
            pulls < CAP,
            "driver did not converge within {CAP} pulls (hang regression)"
        );

        // Wait for data — bounded, so a never-arriving wakeup fails loudly
        // instead of spinning forever.
        let mut waited = 0;
        while !*new_data.borrow() {
            waited += 1;
            assert!(
                waited < CAP,
                "stalled waiting for a notification (lost-wakeup regression)"
            );
            ctx.scheduler().check_for_notifications();
        }
        *new_data.borrow_mut() = false;

        let tile = producer.get(universal.clone());
        let release_guard = match &tile {
            Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
            Tile::SealedFunction {
                domain_predicate, ..
            } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
            other => panic!("unexpected top-level tile shape: {other:?}"),
        };
        let done = release_guard.is_universal();
        producer.release(release_guard);
        if done {
            break tile;
        }
    }
}

/// Extract the single integer a scalar `main` output resolved to.
fn drive_scalar_int(code: &str) -> i64 {
    match drive_main_output(code) {
        Tile::Scalar(cv) => match cv.as_single() {
            Some(Value::Int(n)) => n,
            other => panic!("expected a single Int, got {other:?}"),
        },
        other => panic!("expected a scalar tile, got {other:?}"),
    }
}

/// The reported bug: a finite induction accumulator must converge through the
/// notification-gated driver. Its `Recurse` cycle self-requests re-pulls until
/// terminal; before the wakeup queue this spun forever.
#[test]
fn accumulator_converges_via_notification_gated_driver() {
    assert_eq!(
        drive_scalar_int("x := 0\nfor i in [1, 2, 3, 4, 5]:\n    x += 1\nx"),
        5
    );
}

/// A loop-carried sum (`x += i`) — the accumulator reads its own previous value,
/// so it genuinely exercises the cycle, not just a counter.
#[test]
fn loop_carried_sum_converges() {
    assert_eq!(
        drive_scalar_int("x := 0\nfor i in [1, 2, 3, 4, 5]:\n    x += i\nx"),
        15
    );
}

/// An empty iteration source: the recurrence is immediately drained (terminal on
/// the first productive pull), so the driver must return the initial value
/// without stalling.
#[test]
fn empty_loop_returns_init() {
    assert_eq!(drive_scalar_int("x := 7\nfor i in []:\n    x += 1\nx"), 7);
}

/// Control: an aggregate converges in a single pull (no cycle), so it must keep
/// working under the same driver — guards against the wakeup change perturbing
/// the ordinary one-pull path.
#[test]
fn aggregate_converges_in_one_pull() {
    assert_eq!(drive_scalar_int("sum([1, 2, 3, 4, 5])"), 15);
}

/// The integer codomain of a one-element `main` output stream (a trailing
/// standalone read-only transaction's `AsOf` reply).
fn drive_single_int(code: &str) -> i64 {
    match drive_main_output(code) {
        Tile::SealedFunction { codomain, .. } => match *codomain {
            Tile::Scalar(ColumnValue::Ints(v)) if v.len() == 1 => v[0],
            other => panic!("expected a one-element Ints stream, got {other:?}"),
        },
        other => panic!("expected a SealedFunction stream, got {other:?}"),
    }
}

/// A commit store whose writer stream **leads with a deny** must converge through
/// the notification-gated driver. A denied transaction advances the writer without
/// growing the commit frontier, so it is invisible in the store tile; the writer's
/// one-step-per-pull self-re-arm (not a reader-side drive-to-fixpoint) is what
/// keeps stepping the store past the deny. Before that re-arm, removing the drive
/// loop would strand the driver in `while !new_data` (a lost wakeup) — this test
/// turns that hang into a `drive_main_output` cap panic. The trailing `out << q`
/// is an as-of read; its value is a *member* of the as-of set (the seed `0` or a
/// committed `q`), never asserted to be a specific "final" — here the batch drains
/// so it observes a committed value, but membership is the guarantee.
#[test]
fn leading_deny_converges_no_stall() {
    // r=0 denies (guard `r != 0` false); r=1 commits q:=2; r=2 commits q:=3.
    let v = drive_single_int(
        "out = defer()\nq: Mut(Int, Txn) := 0\nfor r in [0, 1, 2]:\n    with begin():\n        if r != 0:\n            q := r + 1\nwith begin():\n    out << q\nout",
    );
    assert!(
        [0, 2, 3].contains(&v),
        "trailing as-of read {v} must be a member of the as-of set {{0, 2, 3}}"
    );
}

/// As `leading_deny_converges_no_stall`, but the deny sits in the **middle** of
/// the writer stream (`[1, 0, 2]`): r=1 commits q:=2, r=0 denies (no tick), r=2
/// commits q:=3. The store must still step past the interior deny to terminal.
#[test]
fn middle_deny_converges_no_stall() {
    let v = drive_single_int(
        "out = defer()\nq: Mut(Int, Txn) := 0\nfor r in [1, 0, 2]:\n    with begin():\n        if r != 0:\n            q := r + 1\nwith begin():\n    out << q\nout",
    );
    assert!(
        [0, 2, 3].contains(&v),
        "trailing as-of read {v} must be a member of the as-of set {{0, 2, 3}}"
    );
}

//! Finite mutation-loop programs converge under the CLI's dispatcher driver.

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{ColumnValue, Tile, Value};

fn drive_main_output(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    let mut compiled = compile_program(&mut ctx, &LoadedProgram::test(code), Box::new(|| {}))
        .expect("program compiles");
    cambra::interpreter::dispatcher::run_program(&mut compiled, 1)
        .expect("program dispatches")
        .main
        .expect("main output")
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
/// notification-gated driver. Its store/drive cycle self-requests re-pulls until
/// terminal — without the wakeup queue nothing would re-pull it, since a
/// non-terminal tile alone does not make the driver come back.
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
        Tile::DataFunction { codomain, .. } => match *codomain {
            Tile::Scalar(ColumnValue::Ints(v)) if v.len() == 1 => v[0],
            other => panic!("expected a one-element Ints stream, got {other:?}"),
        },
        other => panic!("expected a Function stream, got {other:?}"),
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
        "out: Feed(_)\nq: Mut(Int, Txn) := 0\nfor r in [0, 1, 2]:\n    with begin():\n        if r != 0:\n            q := r + 1\nwith begin():\n    out << q\nout",
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
        "out: Feed(_)\nq: Mut(Int, Txn) := 0\nfor r in [1, 0, 2]:\n    with begin():\n        if r != 0:\n            q := r + 1\nwith begin():\n    out << q\nout",
    );
    assert!(
        [0, 2, 3].contains(&v),
        "trailing as-of read {v} must be a member of the as-of set {{0, 2, 3}}"
    );
}

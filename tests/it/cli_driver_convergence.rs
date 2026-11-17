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
        drive_scalar_int(indoc::indoc! {r#"
            x := 0
            for i in [1, 2, 3, 4, 5]:
                x += 1
            x"#}),
        5
    );
}

/// A loop-carried sum (`x += i`) — the accumulator reads its own previous value,
/// so it genuinely exercises the cycle, not just a counter.
#[test]
fn loop_carried_sum_converges() {
    assert_eq!(
        drive_scalar_int(indoc::indoc! {r#"
            x := 0
            for i in [1, 2, 3, 4, 5]:
                x += i
            x"#}),
        15
    );
}

/// An empty iteration source: the recurrence is immediately drained (terminal on
/// the first productive pull), so the driver must return the initial value
/// without stalling.
#[test]
fn empty_loop_returns_init() {
    assert_eq!(
        drive_scalar_int(indoc::indoc! {r#"
        x := 7
        for i in []:
            x += 1
        x"#}),
        7
    );
}

/// Control: an aggregate converges in a single pull (no cycle), so it must keep
/// working under the same driver — guards against the wakeup change perturbing
/// the ordinary one-pull path.
#[test]
fn aggregate_converges_in_one_pull() {
    assert_eq!(drive_scalar_int("sum([1, 2, 3, 4, 5])"), 15);
}

/// The one integer a `main` output stream holds (a trailing standalone block's reply).
fn drive_single_int(code: &str) -> i64 {
    let values: Vec<i64> = match drive_main_output(code) {
        Tile::DataFunction { codomain, .. } => match *codomain {
            Tile::Scalar(ColumnValue::Ints(v)) => v,
            other => panic!("expected an Ints stream, got {other:?}"),
        },
        other => panic!("expected a Function stream, got {other:?}"),
    };
    match values.as_slice() {
        [v] => *v,
        other => panic!("expected one value across the stream, got {other:?}"),
    }
}

/// A commit store whose writer stream **leads with a deny** must converge through
/// the notification-gated driver. A denied transaction advances the writer without
/// growing the commit frontier, so it is invisible in the store tile; the writer's
/// one-step-per-pull self-re-arm (not a reader-side drive-to-fixpoint) is what
/// keeps stepping the store past the deny. Before that re-arm, removing the drive
/// loop would strand the driver in `while !new_data` (a lost wakeup) — this test
/// turns that hang into a `drive_main_output` cap panic. The trailing block is a
/// transaction unordered against the loop's, so `out << q` replies the seed `0` or a
/// committed `q`: membership is the guarantee.
#[test]
fn leading_deny_converges_no_stall() {
    // r=0 denies (guard `r != 0` false); r=1 commits q:=2; r=2 commits q:=3.
    let v = drive_single_int(indoc::indoc! {r#"
            out: Feed(_)
            q: Mut(Int, Txn) := 0
            for r in [0, 1, 2]:
                with begin():
                    if r != 0:
                        q := r + 1
            with begin():
                out << q
            out"#});
    assert!(
        [0, 2, 3].contains(&v),
        "the trailing block's read {v} must be one of {{0, 2, 3}}"
    );
}

/// As `leading_deny_converges_no_stall`, but the deny sits in the **middle** of
/// the writer stream (`[1, 0, 2]`): r=1 commits q:=2, r=0 denies, r=2
/// commits q:=3. The store must still step past the interior deny to terminal.
#[test]
fn middle_deny_converges_no_stall() {
    let v = drive_single_int(indoc::indoc! {r#"
            out: Feed(_)
            q: Mut(Int, Txn) := 0
            for r in [1, 0, 2]:
                with begin():
                    if r != 0:
                        q := r + 1
            with begin():
                out << q
            out"#});
    assert!(
        [0, 2, 3].contains(&v),
        "the trailing block's read {v} must be one of {{0, 2, 3}}"
    );
}

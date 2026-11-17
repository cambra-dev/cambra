//! Finite mutation-loop programs converge under the CLI's dispatcher driver. Each test is bounded
//! by a timeout, so a dispatcher that stalls fails the test rather than hanging the run.

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{ColumnValue, Tile, Value};
use rstest::rstest;
use std::time::Duration;

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

/// A finite induction accumulator converges: its loop runs a round per position until its store
/// is terminal.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn accumulator_converges() {
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
#[rstest]
#[timeout(Duration::from_secs(10))]
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

/// An empty iteration source: the loop runs no round, and the run answers the initial value without
/// stalling.
#[rstest]
#[timeout(Duration::from_secs(10))]
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

/// Control: an aggregate, which has no cycle, converges under the same driver.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn aggregate_converges() {
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

/// A commit store whose writer stream **leads with a deny** converges. A denied transaction
/// advances the writer without growing the commit frontier, so it is invisible in the store tile,
/// and the run must still step the store past it; a run that stalls there fails at the timeout.
/// The trailing block is a transaction unordered against the loop's, so `out << q` replies the seed
/// `0` or a committed `q`: membership is the guarantee.
#[rstest]
#[timeout(Duration::from_secs(10))]
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
#[rstest]
#[timeout(Duration::from_secs(10))]
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

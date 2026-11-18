//! The CLI driver contract: the binary's drive loop ([`LiveProgram::pull_mains`],
//! as `src/cli.rs` runs it) must converge a mutation-loop accumulator, whose
//! store/drive cycle advances one position per pull and requests its own re-pull
//! through the scheduler's deferred-wakeup queue.
//!
//! Before that mechanism existed, the first `get` returned an empty
//! (non-terminal) tile and no further notification arrived — the domain source
//! (a finite literal) had already fired — so the driver waited for a notification
//! forever. These tests run the driver for a bounded number of passes, so a
//! lost-wakeup regression fails the test rather than hanging it.

use cambra::ccl::context::GlobalContext;
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{Consumer, Tile, Value, tile_value};
use cambra::live_program::{LiveProgram, MAIN_BRANCH};

/// What driving a program's `main` output to its finish produced.
struct Driven {
    /// Every tile a pull returned, in pull order.
    tiles: Vec<Tile>,
    /// The value those tiles merge into.
    value: Value,
}

/// Drive a program's `main` output as the binary does, through
/// [`LiveProgram::pull_mains`], until it finishes. A pass pulls only an output
/// that has been notified, so a lost wakeup leaves every later pass idle; the
/// cap converts that hang into a panic.
fn drive_main_output(code: &str) -> Driven {
    const CAP: usize = 1000;

    let mut ctx = GlobalContext::default();
    let no_op = || -> Box<dyn Consumer> { Box::new(|| {}) };
    let mut live = LiveProgram::start(&mut ctx, &LoadedProgram::test(code), &no_op)
        .unwrap_or_else(|e| panic!("compile failed: {e:?}"));
    let mut merged = live
        .main_producer_mut(MAIN_BRANCH)
        .expect("the program has a `main` output")
        .tiling()
        .empty_tile();
    let mut tiles = Vec::new();
    let mut finished = false;
    for _ in 0..CAP {
        ctx.scheduler().check_for_notifications();
        live.pull_mains(|pull| {
            merged.merge(pull.tile.clone());
            tiles.push(pull.tile.clone());
            finished |= pull.finished;
        });
        if finished {
            let value = tile_value(&merged).unwrap_or_else(|e| panic!("the finished value: {e}"));
            return Driven { tiles, value };
        }
    }
    panic!(
        "the `main` output did not finish within {CAP} passes: a wakeup was lost, or the \
         driver missed that everything was released"
    );
}

/// The integer a scalar `main` output resolved to.
fn drive_scalar_int(code: &str) -> i64 {
    match drive_main_output(code).value {
        Value::Int(n) => n,
        other => panic!("expected an Int, got {other:?}"),
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

/// The one integer a `main` output stream holds (a trailing standalone block's
/// reply).
fn drive_single_int(code: &str) -> i64 {
    let Value::Function(bindings) = drive_main_output(code).value else {
        panic!("expected a stream");
    };
    match bindings.as_slice() {
        [binding] => match binding.output {
            Value::Int(n) => n,
            ref other => panic!("expected an Int, got {other:?}"),
        },
        other => panic!("expected one value in the stream, got {other:?}"),
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

/// A record whose fields finish on different pulls finishes, and its value is the
/// whole record. `b` is ready on the first pull and `a` only once the loop is
/// done, so no tile holds both: the driver released `b` before `a` arrived. Each
/// pull's own release is therefore never universal, and the driver finishes on
/// the releases accumulated over its pulls.
#[test]
fn a_record_finished_across_pulls_finishes_with_the_whole_record() {
    let driven = drive_main_output(indoc::indoc! {"
        total := 0
        for x in [1, 2]:
            total += x
        (a=total, b=1)"});
    assert!(
        driven.tiles.iter().all(|tile| !tile.is_terminal()),
        "the case under test is fields arriving on different pulls, and one tile held them \
         all: {:?}",
        driven.tiles
    );
    assert_eq!(driven.value.to_string(), "{a: 3, b: 1}");
}

/// The `cambra` binary exits once every field of a record `main` is released. It runs in a child
/// process ([`crate::it::cli`]) under a deadline, so a driver that never finishes fails the test
/// rather than hanging it.
#[test]
fn the_binary_exits_with_a_record_finished_across_pulls() {
    use std::io::Read;
    use std::process::Stdio;
    use std::sync::mpsc;
    use std::time::Duration;

    let path = std::env::temp_dir().join(format!(
        "record_finished_across_pulls_{}.cambra",
        std::process::id()
    ));
    std::fs::write(
        &path,
        indoc::indoc! {"
            total := 0
            for x in [1, 2]:
                total += x
            (a=total, b=1)
        "},
    )
    .expect("the program file is writable");
    let mut child = crate::it::cli::command()
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("the cambra binary starts");
    let mut stdout = child.stdout.take().expect("stdout is piped");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut out = String::new();
        let _ = stdout.read_to_string(&mut out);
        let _ = tx.send(out);
    });
    // Compiling takes seconds in a debug build, so the deadline is generous.
    let out = rx.recv_timeout(Duration::from_secs(120));
    if out.is_err() {
        let _ = child.kill();
    }
    let status = child.wait().expect("the child's status is readable");
    let _ = std::fs::remove_file(&path);
    let out = out.expect("the program did not exit within 120 seconds");
    assert!(status.success(), "the program exited with {status}:\n{out}");
    assert!(
        out.contains("Got value: "),
        "the program printed no value:\n{out}"
    );
}

//! The binary's dispatched run (`CAMBRA_DISPATCH`): a pure program prints what pull mode prints,
//! and a program the planner refuses says so and runs in pull mode.

use std::io::Write;
use std::process::{Command, Output, Stdio};

use indoc::indoc;

/// Run the binary on `source`, written to a file of its own, with `CAMBRA_DISPATCH` set to
/// `dispatch`.
fn run(name: &str, source: &str, dispatch: &str) -> Output {
    run_reading(name, source, dispatch, "")
}

/// [`run`] with `input` on the binary's stdin.
fn run_reading(name: &str, source: &str, dispatch: &str, input: &str) -> Output {
    let dir = std::env::temp_dir().join(format!(
        "cambra-dispatch-cli-{}-{name}-{dispatch}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("the temporary directory is writable");
    let path = dir.join(format!("{name}.cambra"));
    std::fs::write(&path, source).expect("the program file is writable");
    let mut child = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .arg(&path)
        .env("CAMBRA_DISPATCH", dispatch)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the binary runs");
    child
        .stdin
        .take()
        .expect("the binary's stdin is piped")
        .write_all(input.as_bytes())
        .expect("the binary takes its input");
    let output = child
        .wait_with_output()
        .expect("the binary runs to its end");
    std::fs::remove_dir_all(&dir).expect("the temporary directory is removable");
    assert!(
        output.status.success(),
        "{name} runs: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

/// A pure program's `main` prints the same value dispatched as in pull mode.
#[rstest::rstest]
#[case::a_scalar("a_scalar", "1 + 2\n")]
#[case::a_loop("a_loop", indoc! {"
    xs = [1, 2, 3]
    total := 0
    for x in xs:
        total += x
    total * 2
"})]
#[case::a_sum("a_sum", "sum([x * x for x in [1, 2, 3, 4]])\n")]
fn a_pure_program_prints_what_pull_mode_prints(#[case] name: &str, #[case] source: &str) {
    let pulled = run(name, source, "0");
    let dispatched = run(name, source, "1");
    assert_eq!(
        String::from_utf8_lossy(&dispatched.stdout),
        String::from_utf8_lossy(&pulled.stdout),
        "{name}: the dispatched run prints what pull mode prints"
    );
    assert!(
        !String::from_utf8_lossy(&dispatched.stderr).contains("running in pull mode"),
        "{name} runs dispatched: {}",
        String::from_utf8_lossy(&dispatched.stderr)
    );
}

/// A program the planner refuses runs in pull mode, after a note naming the refusal.
#[test]
fn a_refused_program_runs_in_pull_mode() {
    // A transaction store of two writers has no consuming mode.
    let source = indoc! {"
        pool: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                pool := pool - r
        for r in [5]:
            with begin():
                pool := pool - r
        await_final(pool)
    "};
    let pulled = run("a_refused_program", source, "0");
    let dispatched = run("a_refused_program", source, "1");
    assert_eq!(dispatched.stdout, pulled.stdout);
    let stderr = String::from_utf8_lossy(&dispatched.stderr);
    assert!(
        stderr.contains("CAMBRA_DISPATCH: ") && stderr.contains("running in pull mode"),
        "the refusal is noted: {stderr}"
    );
}

/// A program that reads stdin, which the planner refuses as a live source read by no source
/// pipeline, runs in pull mode in the context the dispatched run compiled it in: a second
/// compile would open a second stdin reader, and the first would take the input.
#[test]
fn a_refused_program_reading_stdin_takes_its_input() {
    let source = "[\"> \" + line for line in stdin()]\n";
    let input = "a\nb\nc\n";
    let pulled = run_reading("stdin_echo", source, "0", input);
    let dispatched = run_reading("stdin_echo", source, "1", input);
    let echoed = |output: &Output| {
        String::from_utf8_lossy(&output.stdout)
            .matches("\"> ")
            .count()
    };
    assert_eq!(echoed(&pulled), 3, "pull mode echoes every line");
    assert_eq!(
        echoed(&dispatched),
        3,
        "the refused program echoes every line"
    );
}

//! The binary's dispatched run (`CAMBRA_DISPATCH`): a pure program prints what pull mode prints, a
//! program over stdin prints each line's answer as the line arrives, and a program the planner
//! refuses says so and runs in pull mode.

use std::io::Write;
use std::process::{Command, Output, Stdio};

use indoc::indoc;

/// Run the binary on `source`, written to a file of its own, with `CAMBRA_DISPATCH` set to
/// `dispatch`.
fn run(name: &str, source: &str, dispatch: &str) -> Output {
    run_reading(name, source, dispatch, "")
}

/// [`run`] with `input` on the binary's stdin, read from a file.
fn run_reading(name: &str, source: &str, dispatch: &str, input: &str) -> Output {
    run_with(name, source, dispatch, None, input)
}

/// [`run_reading`] with `CAMBRA_MORSEL_ROWS` set to `rows`, where it is `Some`.
fn run_with(name: &str, source: &str, dispatch: &str, rows: Option<&str>, input: &str) -> Output {
    let dir = std::env::temp_dir().join(format!(
        "cambra-dispatch-cli-{}-{name}-{dispatch}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("the temporary directory is writable");
    let path = dir.join(format!("{name}.cambra"));
    std::fs::write(&path, source).expect("the program file is writable");
    let mut command = Command::new(env!("CARGO_BIN_EXE_cambra"));
    command.arg(&path).env("CAMBRA_DISPATCH", dispatch);
    if let Some(rows) = rows {
        command.env("CAMBRA_MORSEL_ROWS", rows);
    }
    // Stdin is a file holding the whole input, so the binary's stdin reader can read it to its
    // end, past the end of input, before the run first polls it: both modes see one delivery.
    let input_path = dir.join("input");
    std::fs::write(&input_path, input).expect("the input file is writable");
    let output = command
        .stdin(std::fs::File::open(&input_path).expect("the input file is readable"))
        .output()
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

/// A pure collection cut into several morsels prints what pull mode prints: the `main` output is
/// handed one answer per epoch, the answers of its packages merged, rather than one per package.
#[rstest::rstest]
#[case::at_morsels_of_one_row("at_one_row", "[x * 10 for x in [1, 2, 3]]\n".to_string(), Some("1"))]
#[case::over_more_than_one_morsel(
    "over_one_morsel",
    format!(
        "[x * 10 for x in [{}]]\n",
        (0..1100).map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
    ),
    None
)]
fn a_collection_in_several_morsels_prints_what_pull_mode_prints(
    #[case] name: &str,
    #[case] source: String,
    #[case] rows: Option<&str>,
) {
    let pulled = run_with(name, &source, "0", rows, "");
    let dispatched = run_with(name, &source, "1", rows, "");
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

/// A program the planner refuses runs in pull mode, after a note naming the refusal, in the
/// context the dispatched run compiled it in: the program reads stdin, and a second compile would
/// open a second stdin reader, which the first would take the input from.
#[test]
fn a_refused_program_runs_in_pull_mode() {
    // A range over stdin beside a static extent is refused: its keys pair a line's position with
    // a position of the list, which no region of one source's positions spells.
    let source = "sum([1 for line in stdin() for s in [1, 2]])\n";
    let input = "a\nb\n";
    let pulled = run_reading("a_refused_program", source, "0", input);
    let dispatched = run_reading("a_refused_program", source, "1", input);
    assert_eq!(dispatched.stdout, pulled.stdout);
    let stderr = String::from_utf8_lossy(&dispatched.stderr);
    assert!(
        stderr.contains("CAMBRA_DISPATCH: ") && stderr.contains("running in pull mode"),
        "the refusal is noted: {stderr}"
    );
}

/// A map over stdin at the `main` output prints each line's answer before the next line arrives,
/// dispatched as in pull mode: each line is written to the binary's stdin once the answer to the
/// line before it is printed.
#[rstest::rstest]
fn a_map_over_stdin_prints_each_line_as_it_arrives(#[values("0", "1")] dispatch: &str) {
    use std::io::{BufRead, BufReader};
    use std::sync::mpsc;
    use std::time::Duration;

    let source = "[\"> \" + line for line in stdin()]\n";
    let dir = std::env::temp_dir().join(format!(
        "cambra-dispatch-cli-{}-stdin-stream-{dispatch}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("the temporary directory is writable");
    let path = dir.join("stream.cambra");
    std::fs::write(&path, source).expect("the program file is writable");
    let mut child = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .arg(&path)
        .env("CAMBRA_DISPATCH", dispatch)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the binary runs");
    // The printed strings, one per line of the tiles' `Debug` rendering that holds one.
    let stdout = child.stdout.take().expect("the binary's stdout is piped");
    let (printed, strings) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines() {
            let line = line.expect("the binary prints text");
            if let Some(string) = line.trim().strip_suffix(',')
                && let Some(string) = string.strip_prefix('"')
                && let Some(string) = string.strip_suffix('"')
                && printed.send(string.to_string()).is_err()
            {
                return;
            }
        }
    });
    let mut stdin = child.stdin.take().expect("the binary's stdin is piped");
    for line in ["a", "b", "c"] {
        writeln!(stdin, "{line}").expect("the binary takes its input");
        stdin.flush().expect("the line reaches the binary");
        let answer = strings
            .recv_timeout(Duration::from_secs(20))
            .unwrap_or_else(|_| panic!("the answer to {line:?} prints within 20 s"));
        assert_eq!(
            answer,
            format!("> {line}"),
            "the answer to {line:?}, before the next line"
        );
    }
    drop(stdin);
    let output = child
        .wait_with_output()
        .expect("the binary runs to its end");
    // The reader has sent every string the binary printed once it has read stdout to its end.
    reader.join().expect("the reader reads stdout to its end");
    std::fs::remove_dir_all(&dir).expect("the temporary directory is removable");
    assert!(
        output.status.success(),
        "the binary exits once stdin closes"
    );
    assert_eq!(
        strings.try_iter().collect::<Vec<_>>(),
        Vec::<String>::new(),
        "nothing prints after the last answer"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("running in pull mode"),
        "the program runs dispatched: {stderr}"
    );
}

/// A program over stdin at the `main` output prints what pull mode prints, dispatched, the last
/// terminal answer included.
#[rstest::rstest]
#[case::a_map("stdin_map", "[\"> \" + line for line in stdin()]\n")]
#[case::a_filter("stdin_filter", "[line for line in stdin() if line != \"b\"]\n")]
#[case::a_sum("stdin_sum", "sum([1 for line in stdin()])\n")]
#[case::a_loop("stdin_loop", indoc! {"
    count := 0
    for line in stdin():
        count += 1
    count
"})]
fn a_program_over_stdin_prints_what_pull_mode_prints(#[case] name: &str, #[case] source: &str) {
    let input = "a\nb\nc\n";
    let pulled = run_reading(name, source, "0", input);
    let dispatched = run_reading(name, source, "1", input);
    assert_eq!(
        String::from_utf8_lossy(&dispatched.stdout),
        String::from_utf8_lossy(&pulled.stdout),
        "{name}: the dispatched run prints what pull mode prints"
    );
    let stderr = String::from_utf8_lossy(&dispatched.stderr);
    assert!(
        !stderr.contains("running in pull mode"),
        "{name} runs dispatched: {stderr}"
    );
}

/// An HTTP server program runs dispatched: its request sources are live sources whose
/// deliveries the run notifies the routes' pipelines of, and each request is answered while the
/// run polls.
#[test]
fn an_http_server_answers_requests_dispatched() {
    use std::io::Read;
    use std::net::TcpStream;
    use std::time::{Duration, Instant};

    let port = cambra::interpreter::http_server::reserve_test_port();
    let source = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/programs/http_greeter/program.cambra"
    ))
    .expect("the greeter is readable")
    .replace("{PORT}", &port.to_string());
    let dir = std::env::temp_dir().join(format!("cambra-dispatch-http-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("the temporary directory is writable");
    let path = dir.join("greeter.cambra");
    std::fs::write(&path, source).expect("the program file is writable");
    let mut child = Command::new(env!("CARGO_BIN_EXE_cambra"))
        .arg(&path)
        .env("CAMBRA_DISPATCH", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the binary runs");
    let deadline = Instant::now() + Duration::from_secs(20);
    let answer = loop {
        if let Ok(mut stream) = TcpStream::connect(("127.0.0.1", port)) {
            stream
                .write_all(b"GET /greet HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n")
                .expect("the request is sent");
            let mut answer = String::new();
            stream
                .read_to_string(&mut answer)
                .expect("the answer is read");
            break answer;
        }
        assert!(Instant::now() < deadline, "the server listens within 20 s");
        std::thread::sleep(Duration::from_millis(50));
    };
    child.kill().expect("the server is stopped");
    let output = child.wait_with_output().expect("the server exits");
    std::fs::remove_dir_all(&dir).expect("the temporary directory is removable");
    assert!(answer.contains("Hello, stranger!"), "the answer: {answer}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("running in pull mode"),
        "the server runs dispatched: {stderr}"
    );
}

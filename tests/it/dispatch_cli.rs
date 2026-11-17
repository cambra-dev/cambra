//! The binary's dispatched run (`CAMBRA_DISPATCH`): a pure program prints what pull mode prints,
//! and a program the planner refuses says so and runs in pull mode.

use std::io::Write;
use std::process::{Output, Stdio};

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
    let mut child = crate::it::cli::command()
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
    // A pipeline's reader that also reads a live source is refused: the sum reads the let-bound
    // list's sum, a pipeline, beside the lines of stdin.
    let source = indoc! {"
        xs = [1, 2]
        sum([x + sum(xs) for x in [1 for line in stdin()]])
    "};
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

/// A pure program that reads stdin, which the planner refuses since no push reaches the driver's
/// consumer at its `main` output, runs in pull mode in the context the dispatched run compiled it
/// in: a second compile would open a second stdin reader, and the first would take the input.
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

/// A server the test started, stopped and its program's directory removed when the guard drops,
/// so a test that fails or times out leaves no server behind.
struct Server {
    child: Option<std::process::Child>,
    dir: std::path::PathBuf,
}

impl Server {
    /// Stop the server and answer what it wrote.
    fn stop(mut self) -> Output {
        let mut child = self.child.take().expect("the server runs until stopped");
        child.kill().expect("the server is stopped");
        child.wait_with_output().expect("the server exits")
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        if let Some(child) = &mut self.child {
            let _ = child.kill();
            let _ = child.wait();
        }
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// An HTTP server program runs dispatched: its request sources are live sources whose
/// deliveries the run notifies the routes' pipelines of, and each request is answered while the
/// run polls. The connection and the answer share one 20-second bound.
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
    let server = Server {
        child: Some(
            crate::it::cli::command()
                .arg(&path)
                .env("CAMBRA_DISPATCH", "1")
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("the binary runs"),
        ),
        dir,
    };
    let deadline = Instant::now() + Duration::from_secs(20);
    let left = || {
        deadline
            .checked_duration_since(Instant::now())
            .filter(|left| !left.is_zero())
            .expect("the server answers within 20 s")
    };
    let answer = loop {
        if let Ok(mut stream) = TcpStream::connect(("127.0.0.1", port)) {
            stream
                .set_write_timeout(Some(left()))
                .expect("the write is bounded");
            stream
                .write_all(b"GET /greet HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n")
                .expect("the request is sent");
            // Each read waits at most what is left of the bound, so a server that answers a byte
            // at a time cannot hold the test past it.
            let mut answer = Vec::new();
            let mut chunk = [0; 4096];
            loop {
                stream
                    .set_read_timeout(Some(left()))
                    .expect("the read is bounded");
                match stream
                    .read(&mut chunk)
                    .expect("the server answers within 20 s")
                {
                    0 => break,
                    read => answer.extend_from_slice(&chunk[..read]),
                }
            }
            break String::from_utf8_lossy(&answer).into_owned();
        }
        left();
        std::thread::sleep(Duration::from_millis(50));
    };
    let output = server.stop();
    assert!(answer.contains("Hello, stranger!"), "the answer: {answer}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("running in pull mode"),
        "the server runs dispatched: {stderr}"
    );
}

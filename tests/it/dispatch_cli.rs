//! CLI output, incremental stdin delivery, and HTTP execution through the dispatcher.

use indoc::indoc;
use std::io::Write;
use std::process::{Output, Stdio};

fn run_with(name: &str, source: &str, rows: Option<&str>, input: &str) -> Output {
    let dir =
        std::env::temp_dir().join(format!("cambra-dispatch-cli-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch directory");
    let path = dir.join("program.cambra");
    std::fs::write(&path, source).expect("program");
    let input_path = dir.join("input");
    std::fs::write(&input_path, input).expect("input");
    let mut command = crate::it::cli::command();
    command.arg(&path);
    if let Some(rows) = rows {
        command.env("CAMBRA_MORSEL_ROWS", rows);
    }
    let output = command
        .stdin(std::fs::File::open(input_path).expect("input file"))
        .output()
        .expect("run binary");
    std::fs::remove_dir_all(dir).expect("remove scratch directory");
    assert!(
        output.status.success(),
        "{name}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

/// Integer value columns, excluding UInt domain keys, across printed output tiles.
fn printed_ints(output: &Output) -> Vec<i64> {
    let flat: String = String::from_utf8_lossy(&output.stdout)
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    flat.match_indices("Ints([")
        .filter(|(at, _)| *at == 0 || flat.as_bytes()[at - 1] != b'U')
        .flat_map(|(at, _)| {
            flat[at + 6..]
                .split(']')
                .next()
                .unwrap()
                .split(',')
                .filter(|v| !v.is_empty())
                .map(|v| v.parse::<i64>().expect("integer value"))
                .collect::<Vec<_>>()
        })
        .collect()
}
fn printed_strings(output: &Output) -> Vec<String> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            line.trim()
                .strip_prefix('"')?
                .strip_suffix("\",")
                .map(str::to_owned)
        })
        .collect()
}

#[rstest::rstest]
#[case::scalar("scalar", "1 + 2", 3)]
#[case::loop_sum("loop", indoc! {"
    total := 0
    for x in [1, 2, 3]:
        total += x
    total * 2
"}, 12)]
#[case::sum("sum", "sum([x * x for x in [1, 2, 3, 4]])", 30)]
fn a_pure_program_prints_its_value(
    #[case] name: &str,
    #[case] source: &str,
    #[case] expected: i64,
) {
    assert_eq!(printed_ints(&run_with(name, source, None, "")), [expected]);
}

#[rstest::rstest]
#[case::small("small", vec![1, 2, 3], Some("1"))]
#[case::large("large", (0..1100).collect(), None)]
fn morsels_preserve_every_output_value(
    #[case] name: &str,
    #[case] input: Vec<i64>,
    #[case] rows: Option<&str>,
) {
    let source = format!(
        "[x * 10 for x in [{}]]",
        input
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    );
    assert_eq!(
        printed_ints(&run_with(name, &source, rows, "")),
        input.iter().map(|x| x * 10).collect::<Vec<_>>()
    );
}

#[test]
fn a_live_product_runs_dispatched() {
    assert_eq!(
        printed_ints(&run_with(
            "live-product",
            "sum([1 for line in stdin() for s in [1, 2]])",
            None,
            "a\nb\n"
        )),
        [4]
    );
}

#[rstest::rstest]
#[case::map("stdin_map", "[\"> \" + line for line in stdin()]", &[], &["> a", "> b", "> c"])]
#[case::filter("stdin_filter", "sum([1 for line in stdin() if line != \"b\"])", &[2], &[])]
#[case::sum("stdin_sum", "sum([1 for line in stdin()])", &[3], &[])]
#[case::loop_count("stdin_loop", indoc! {"
    count := 0
    for line in stdin():
        count += 1
    count
"}, &[3], &[])]
fn stdin_programs_print_expected_values(
    #[case] name: &str,
    #[case] source: &str,
    #[case] ints: &[i64],
    #[case] strings: &[&str],
) {
    let output = run_with(name, source, None, "a\nb\nc\n");
    assert_eq!(printed_ints(&output), ints);
    assert_eq!(printed_strings(&output), strings);
}

/// A map over stdin at the `main` output prints each line's answer before the next line arrives,
/// each line is written to the binary's stdin once the answer to the
/// line before it is printed.
#[rstest::rstest]
fn a_map_over_stdin_prints_each_line_as_it_arrives() {
    use std::io::{BufRead, BufReader};
    use std::sync::mpsc;
    use std::time::Duration;

    let source = "[\"> \" + line for line in stdin()]\n";
    let dir = std::env::temp_dir().join(format!(
        "cambra-dispatch-cli-{}-stdin-stream",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("the temporary directory is writable");
    let path = dir.join("stream.cambra");
    std::fs::write(&path, source).expect("the program file is writable");
    let mut child = crate::it::cli::command()
        .arg(&path)
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
    let mut child = crate::it::cli::command()
        .arg(&path)
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
    child.wait_with_output().expect("the server exits");
    std::fs::remove_dir_all(&dir).expect("the temporary directory is removable");
    assert!(answer.contains("Hello, stranger!"), "the answer: {answer}");
}

//! The inspector under `--control`: the payload it serves follows `main`'s
//! version, per `src/inspector_model/design.md`, "A reload of main is followed".

use std::collections::HashSet;
use std::io::Write;
use std::net::TcpStream;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::Value;
use tungstenite::{Message, WebSocket};

use super::harness::{RunningProgram, launch_under_control_with};
use super::serving::{http_get, raw_http, raw_http_response, reserve_test_port};

/// The served `/api/snapshot`, parsed.
fn snapshot(port: u16) -> Value {
    serde_json::from_str(&http_get(port, "/api/snapshot")).expect("the snapshot is JSON")
}

fn version(snapshot: &Value) -> u64 {
    snapshot["meta"]["version"]
        .as_u64()
        .expect("meta.version is a number")
}

/// Every node id of the operator pane.
fn operator_ids(snapshot: &Value) -> HashSet<u64> {
    let pane = snapshot["panes"]
        .as_array()
        .expect("panes")
        .iter()
        .find(|pane| pane["kind"] == "operators")
        .expect("an operator pane");
    pane["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .map(|node| node["nodeId"].as_u64().expect("nodeId"))
        .collect()
}

/// Send `body` to `path` on the control port, and answer the reply's body.
fn control(port: u16, path: &str, body: &str) -> String {
    raw_http(
        port,
        &format!(
            "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Length: {}\r\n\
             Connection: close\r\n\r\n{body}",
            body.len()
        ),
    )
}

/// The served snapshot, once the driver has followed every control request
/// answered before this call.
///
/// The driver answers one control request per pass and runs `follow` right
/// after it (`poll_control`, `src/main.rs`), so the reply to a further request
/// arrives on a later pass, after that `follow`. `/branches` only reads.
fn settled_snapshot(inspect: u16, control_port: u16) -> Value {
    control(control_port, "/branches", "");
    snapshot(inspect)
}

/// Wait until the inspector on `port` accepts a connection.
fn await_inspector(port: u16) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while TcpStream::connect(("127.0.0.1", port)).is_err() {
        assert!(Instant::now() < deadline, "the inspector never opened");
        thread::sleep(Duration::from_millis(50));
    }
}

/// A client of the inspector's `/api/live` socket.
fn connect_live(port: u16) -> WebSocket<TcpStream> {
    let stream = TcpStream::connect(("127.0.0.1", port)).expect("connecting");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .expect("a read timeout");
    let (socket, _) =
        tungstenite::client::client(format!("ws://127.0.0.1:{port}/api/live"), stream)
            .expect("the handshake completes");
    socket
}

/// The version the next probe frame on `socket` carries, failing the test if
/// none arrives before `deadline`.
///
/// The server pings an idle socket, so a read can keep returning before any
/// frame does; the deadline is checked on every message.
fn next_frame_version(socket: &mut WebSocket<TcpStream>, deadline: Instant) -> u64 {
    loop {
        assert!(Instant::now() < deadline, "no probe frame arrived in time");
        match socket.read().expect("reading a frame") {
            Message::Text(text) => {
                let frame: Value = serde_json::from_str(&text).expect("a frame is JSON");
                return frame["version"]
                    .as_u64()
                    .expect("a frame carries a version");
            }
            Message::Ping(_) | Message::Pong(_) => continue,
            other => panic!("expected a text frame, got {other:?}"),
        }
    }
}

/// Read probe frames on `socket` until one carries version 2, failing the test
/// if an earlier one carries any version but 1, or if none arrives before
/// `deadline`.
///
/// Frames of version 1 can precede it: one published before the reload is
/// still in flight when the reload is answered.
fn await_reloaded_frame(socket: &mut WebSocket<TcpStream>, deadline: Instant) {
    loop {
        let version = next_frame_version(socket, deadline);
        if version == 2 {
            return;
        }
        assert_eq!(version, 1, "a frame names a version `main` has run");
    }
}

/// A reload of `main` replaces the served payload with the new version's, and
/// creating another branch does not.
#[test]
fn the_served_payload_follows_a_reload_of_main_and_no_other_branch() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);

    let first = snapshot(inspect);
    assert_eq!(version(&first), 1, "a run starts at `main`'s first version");

    let created = control(
        launched.control,
        "/branch/b",
        "[\"B\" + line for line in stdin()]\n",
    );
    assert!(created.starts_with("created `b@1`"), "{created}");
    let after_branch = settled_snapshot(inspect, launched.control);
    assert_eq!(
        version(&after_branch),
        1,
        "another branch leaves the payload alone"
    );
    assert_eq!(operator_ids(&after_branch), operator_ids(&first));

    let reloaded = control(
        launched.control,
        "/reload",
        "[\"C\" + line for line in stdin()]\n",
    );
    assert!(reloaded.starts_with("reloaded"), "{reloaded}");
    let second = settled_snapshot(inspect, launched.control);
    assert_eq!(
        version(&second),
        2,
        "the reload moved the payload to version 2"
    );
    assert!(
        !operator_ids(&second).is_subset(&operator_ids(&first)),
        "the reload rebuilt an operator, so the new payload names an id the first did not",
    );
}

/// After a reload of `main`, probe frames carry the new version, and
/// `/api/snapshot` already serves that version when the first such frame
/// arrives (`src/inspector_model/design.md`, "A reload of main is followed").
#[test]
fn probe_frames_follow_a_reload_of_main_after_the_payload_does() {
    let inspect = reserve_test_port();
    let mut launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);
    let mut socket = connect_live(inspect);
    let mut input = launched.input.take().expect("piped stdin");

    writeln!(input, "x").expect("feeding stdin");
    let deadline = Instant::now() + Duration::from_secs(10);
    assert_eq!(
        next_frame_version(&mut socket, deadline),
        1,
        "a run's frames start at `main`'s first version"
    );

    let reloaded = control(
        launched.control,
        "/reload",
        "[\"C\" + line for line in stdin()]\n",
    );
    assert!(reloaded.starts_with("reloaded"), "{reloaded}");
    writeln!(input, "y").expect("feeding stdin");

    await_reloaded_frame(&mut socket, Instant::now() + Duration::from_secs(10));
    assert_eq!(
        version(&snapshot(inspect)),
        2,
        "a frame named version 2 before `/api/snapshot` served it"
    );
}

/// A reload of `main` publishes a frame of the new version even when no flow
/// follows it: until one does, the newest frame names the old version's source
/// anchors, and a client connecting is handed it. The new version holds no
/// constant, so with nothing on `stdin` none of its operators takes a reading
/// that carries rows.
///
/// The first version can publish a frame of its own before the reload. Each
/// constant's first reading carries its row, and the driver takes it with
/// probing on when the client connects before the driver's first pass.
#[test]
fn a_reload_of_main_publishes_a_frame_before_any_input() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);
    let mut socket = connect_live(inspect);

    let reloaded = control(launched.control, "/reload", "[line for line in stdin()]\n");
    assert!(reloaded.starts_with("reloaded"), "{reloaded}");

    await_reloaded_frame(&mut socket, Instant::now() + Duration::from_secs(10));
    assert_eq!(version(&snapshot(inspect)), 2);
}

/// The inspector's `POST /api/reload` with `source` as the version, sent the way
/// the page sends it: JSON, from the page's own origin. Answers the status and
/// the parsed body.
fn post_reload(port: u16, source: &str) -> (u16, Value) {
    let body = serde_json::json!({ "source": source }).to_string();
    let response = raw_http_response(
        port,
        &format!(
            "POST /api/reload HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\n\
             Origin: http://127.0.0.1:{port}\r\nContent-Type: application/json\r\n\
             Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        ),
    );
    let (head, body) = response.split_once("\r\n\r\n").expect("a response");
    let status = head
        .split_whitespace()
        .nth(1)
        .and_then(|code| code.parse().ok())
        .expect("a status line");
    (
        status,
        serde_json::from_str(body).expect("the reply is JSON"),
    )
}

/// A version posted to the inspector replaces `main`, and the served payload
/// follows it as it follows a reload from the control port.
#[test]
fn the_inspector_reloads_main_with_a_posted_version() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);

    let capabilities: Value =
        serde_json::from_str(&http_get(inspect, "/api/capabilities")).expect("JSON");
    assert_eq!(
        capabilities["reload"], true,
        "a run with a control port reloads"
    );

    let edited = "[\"C\" + line for line in stdin()]\n";
    let (status, reply) = post_reload(inspect, edited);
    assert_eq!(status, 200, "{reply}");
    let (kept, bound) = (reply["kept"].as_u64(), reply["bound"].as_u64());
    assert!(
        kept.zip(bound).is_some_and(|(kept, bound)| kept <= bound),
        "an accepted reload carries its tally: {reply}"
    );

    let after = settled_snapshot(inspect, launched.control);
    assert_eq!(version(&after), 2, "the posted version is `main`'s second");
    assert_eq!(after["source"]["text"], edited);
}

/// A posted version that does not compile is refused with diagnostics whose
/// spans point into the posted text, and `main` keeps running the version it
/// had.
#[test]
fn a_posted_version_that_does_not_compile_is_refused_with_its_spans() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);

    let broken = "[\"A\" + nowhere for line in stdin()]\n";
    let (status, reply) = post_reload(inspect, broken);
    assert_eq!(status, 400, "{reply}");
    let diagnostics = reply["diagnostics"].as_array().expect("diagnostics");
    let span = diagnostics
        .iter()
        .find_map(|d| d["span"].as_object())
        .unwrap_or_else(|| panic!("a diagnostic with a span: {reply}"));
    let (start, end) = (
        span["start"].as_u64().unwrap() as usize,
        span["end"].as_u64().unwrap() as usize,
    );
    assert_eq!(&broken[start..end], "nowhere", "{reply}");

    let after = settled_snapshot(inspect, launched.control);
    assert_eq!(version(&after), 1, "a refused version installs nothing");
}

/// Without a control port the inspector takes no reload, and says so before the
/// page offers one.
#[test]
fn an_inspector_without_a_control_port_takes_no_reload() {
    use std::process::{Command, Stdio};

    let inspect = reserve_test_port();
    let dir = std::env::temp_dir().join(format!("cambra-inspect-{inspect}"));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("prog.cambra");
    std::fs::write(&file, "[\"A\" + line for line in stdin()]\n").expect("write the program");
    let _program = RunningProgram {
        child: Command::new(env!("CARGO_BIN_EXE_cambra"))
            .arg(format!("--inspect={inspect}"))
            .arg(&file)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn cambra"),
        dir,
    };
    await_inspector(inspect);

    let capabilities: Value =
        serde_json::from_str(&http_get(inspect, "/api/capabilities")).expect("JSON");
    assert_eq!(capabilities["reload"], false);
    let (status, reply) = post_reload(inspect, "[\"B\" + line for line in stdin()]\n");
    assert_eq!(status, 404, "{reply}");
}

/// A page on another origin cannot reload the program, whatever it sends.
#[test]
fn a_reload_from_another_origin_is_refused() {
    let inspect = reserve_test_port();
    let launched = launch_under_control_with(
        "[\"A\" + line for line in stdin()]\n",
        &[format!("--inspect={inspect}")],
    );
    await_inspector(inspect);

    let body = serde_json::json!({ "source": "[\"X\" + line for line in stdin()]\n" }).to_string();
    let response = raw_http_response(
        inspect,
        &format!(
            "POST /api/reload HTTP/1.1\r\nHost: 127.0.0.1:{inspect}\r\n\
             Origin: http://example.com\r\nContent-Type: application/json\r\n\
             Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        ),
    );
    assert!(response.starts_with("HTTP/1.1 403"), "{response}");
    assert_eq!(version(&settled_snapshot(inspect, launched.control)), 1);
}

/// A finished program takes no reload: the driver loop has ended, and the
/// inspector goes on serving with nothing behind the control port.
#[test]
fn a_finished_program_takes_no_reload() {
    use std::process::{Command, Stdio};

    let inspect = reserve_test_port();
    let control = reserve_test_port();
    let dir = std::env::temp_dir().join(format!("cambra-finished-{inspect}"));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("prog.cambra");
    std::fs::write(&file, "[x + 1 for x in [1, 2, 3]]\n").expect("write the program");
    let mut program = RunningProgram {
        child: Command::new(env!("CARGO_BIN_EXE_cambra"))
            .arg(format!("--inspect={inspect}"))
            .arg(format!("--control={control}"))
            .arg(&file)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn cambra"),
        dir,
    };
    await_inspector(inspect);
    // The program prints its value and finishes; the binary then parks. The
    // reader thread keeps the pipe open, so the rest of the print does not fail.
    let (tx, rx) = std::sync::mpsc::channel();
    let out = program.child.stdout.take().expect("piped stdout");
    thread::spawn(move || {
        use std::io::BufRead;
        for line in std::io::BufReader::new(out).lines().map_while(Result::ok) {
            let _ = tx.send(line);
        }
    });
    let first = rx
        .recv_timeout(Duration::from_secs(30))
        .expect("the program prints its value");
    assert!(first.starts_with("Got value"), "{first}");

    let deadline = Instant::now() + Duration::from_secs(10);
    let (status, reply) = loop {
        let (status, reply) = post_reload(inspect, "[x + 2 for x in [1, 2, 3]]\n");
        if status != 200 || Instant::now() > deadline {
            break (status, reply);
        }
        thread::sleep(Duration::from_millis(50));
    };
    assert_eq!(status, 409, "{reply}");
    assert!(
        reply["message"]
            .as_str()
            .is_some_and(|m| m.contains("finished")),
        "{reply}"
    );
}

/// Under `--inspect=0 --control=0` the OS picks both ports, and each banner
/// names the port it picked, so a reader of stderr can reach both servers.
#[test]
fn port_zero_prints_the_port_the_os_picked() {
    use std::io::{BufRead, BufReader};
    use std::process::{Command, Stdio};
    use std::sync::mpsc;

    let dir = std::env::temp_dir().join(format!("cambra-port-zero-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let source = dir.join("v1.cambra");
    std::fs::write(&source, "[line for line in stdin()]\n").expect("write v1");
    let mut program = RunningProgram {
        child: Command::new(env!("CARGO_BIN_EXE_cambra"))
            .args(["--inspect=0", "--control=0"])
            .arg(&source)
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn cambra"),
        dir,
    };
    let err = program.child.stderr.take().expect("piped stderr");
    let (lines, banners) = mpsc::channel();
    thread::spawn(move || {
        for line in BufReader::new(err).lines().map_while(Result::ok) {
            let _ = lines.send(line);
        }
    });

    // The port in a banner's `http://localhost:PORT`.
    let port_after = |banner: &str, prefix: &str| -> Option<u16> {
        let rest = banner.strip_prefix(prefix)?;
        let (_, url) = rest.split_once("http://localhost:")?;
        url.split(|c: char| !c.is_ascii_digit())
            .next()?
            .parse()
            .ok()
    };
    let (mut inspect, mut control_port) = (None, None);
    let deadline = Instant::now() + Duration::from_secs(10);
    while inspect.is_none() || control_port.is_none() {
        let left = deadline.saturating_duration_since(Instant::now());
        let banner = banners
            .recv_timeout(left)
            .expect("both servers announce themselves on stderr");
        inspect = inspect.or_else(|| port_after(&banner, "cambra: inspecting "));
        control_port = control_port.or_else(|| port_after(&banner, "cambra: control port at "));
    }
    let (inspect, control_port) = (inspect.unwrap(), control_port.unwrap());
    assert_ne!(inspect, 0, "the inspector's banner names the bound port");
    assert_ne!(
        control_port, 0,
        "the control port's banner names the bound port"
    );

    assert_eq!(version(&snapshot(inspect)), 1);
    let branches = control(control_port, "/branches", "");
    assert!(branches.contains("main"), "{branches}");
}

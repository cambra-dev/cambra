//! End-to-end tests for the HTTP server source/sink (`http_serve`).
//!
//! These tests compile a CHL program that uses `http_serve`, drive the Cambra
//! scheduler on the main thread, and send real HTTP requests from a background
//! thread, verifying that the computed responses are delivered back to the
//! caller.

use std::{
    io::{Read, Write},
    net::{TcpListener, TcpStream},
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::{
        context::{GlobalContext, compile_program},
        lower::{LoweringContext, LoweringError, lower_stmts},
    },
    interpreter::Consumer,
};
use rstest_log::rstest;
use rustpython_parser::{ast as pyast, parser};
use test_log::test;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Allocate a free TCP port by briefly binding to port 0 and reading the
/// OS-assigned address.
fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port()
}

/// Send a raw HTTP/1.1 POST to `127.0.0.1:port` at `path` with the given
/// `body`.  Returns the HTTP response body string.
///
/// Uses a plain `TcpStream` so no HTTP-client crate is needed as a
/// dev-dependency.
fn http_post(port: u16, path: &str, body: &str) -> String {
    let request = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: 127.0.0.1:{port}\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len()
    );
    let mut stream =
        TcpStream::connect(format!("127.0.0.1:{port}")).expect("failed to connect to test server");
    stream
        .write_all(request.as_bytes())
        .expect("failed to write HTTP request");
    stream.flush().unwrap();

    let mut raw = String::new();
    stream
        .read_to_string(&mut raw)
        .expect("failed to read HTTP response");

    // The response body follows the first blank line.
    raw.split_once("\r\n\r\n")
        .map(|(_, b)| b.to_string())
        .unwrap_or_default()
}

fn http_get(port: u16, path: &str) -> String {
    let request = format!(
        "GET {path} HTTP/1.1\r\n\
         Host: 127.0.0.1:{port}\r\n\
         Connection: close\r\n\
         \r\n"
    );
    let mut stream =
        TcpStream::connect(format!("127.0.0.1:{port}")).expect("failed to connect to test server");
    stream
        .write_all(request.as_bytes())
        .expect("failed to write HTTP request");
    stream.flush().unwrap();

    let mut raw = String::new();
    stream
        .read_to_string(&mut raw)
        .expect("failed to read HTTP response");

    raw.split_once("\r\n\r\n")
        .map(|(_, b)| b.to_string())
        .unwrap_or_default()
}

/// Drive the Cambra scheduler on the current thread until `rx` delivers a
/// value or `timeout` elapses.
///
/// HTTP response dispatch is handled automatically by [`SinkConsumer`] when
/// the scheduler notifies it; this function only needs to keep the scheduler
/// ticking.
fn drive_until<T>(ctx: &mut GlobalContext, rx: &mpsc::Receiver<T>, timeout: Duration) -> T {
    let deadline = Instant::now() + timeout;
    loop {
        ctx.scheduler().check_for_notifications();

        if let Ok(value) = rx.try_recv() {
            return value;
        }

        assert!(
            Instant::now() < deadline,
            "timed out after {timeout:?} waiting for HTTP response"
        );
        thread::sleep(Duration::from_millis(10));
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// A CHL program echoes each POST body back with a "Received: " prefix.
#[rstest]
fn test_http_serve_echo() {
    let port = free_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << \"Received: \" + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    // Give tiny_http a moment to bind the port before the client connects.
    thread::sleep(Duration::from_millis(50));

    // Send one POST request from a background thread and collect the response.
    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_post(port, "/echo", "hello");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));

    assert_eq!(response, "Received: hello");
}

#[rstest]
fn test_http_serve_const() {
    let port = free_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"GET\", \"/static\")\n\
         for req in requests:\n\
         \tresponses << \"Hello, world!\"\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    // Give tiny_http a moment to bind the port before the client connects.
    thread::sleep(Duration::from_millis(50));

    // Send one GET request from a background thread and collect the response.
    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_get(port, "/static");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));

    assert_eq!(response, "Hello, world!");
}

/// Sending two sequential requests processes them independently, each getting
/// its own prefixed response.
#[rstest]
fn test_http_serve_two_sequential_requests() {
    let port = free_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << \"OK: \" + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    thread::sleep(Duration::from_millis(50));

    // Send two requests sequentially; each blocks until the server responds.
    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let r1 = http_post(port, "/echo", "first");
        let r2 = http_post(port, "/echo", "second");
        tx.send(vec![r1, r2]).unwrap();
    });

    let responses = drive_until(&mut ctx, &rx, Duration::from_secs(5));

    assert_eq!(responses, vec!["OK: first", "OK: second"]);
}

/// Two independent endpoints on the same port both handle their requests correctly.
///
/// The background thread sends requests sequentially — GET to the first endpoint,
/// then POST to the second — and collects both response bodies.  Both handlers
/// must fire and produce the expected responses.
#[rstest]
fn test_http_serve_two_paths() {
    let port1 = free_port();
    let code = format!(
        "reqs1, resps1 = http_serve(\"{port1}\", \"GET\", \"/greet\")\n\
         for req in reqs1:\n\
         \tresps1 << \"hello\"\n\
        reqs2, resps2 = http_serve(\"{port1}\", \"POST\", \"/echo\")\n\
         for req in reqs2:\n\
         \tresps2 << \"echo: \" + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    thread::sleep(Duration::from_millis(50));

    // Send requests sequentially: each http_post/http_get blocks until the
    // server responds, so the second request is only sent after the first
    // endpoint has been processed.
    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let r1 = http_get(port1, "/greet");
        let r2 = http_post(port1, "/echo", "world");
        tx.send(vec![r1, r2]).unwrap();
    });

    let responses = drive_until(&mut ctx, &rx, Duration::from_secs(5));

    assert_eq!(responses, vec!["hello", "echo: world"]);
}

/// Two endpoints that share an outer `let` binding both compile and serve
/// requests correctly.  Verifies that the shared upstream binding is in scope
/// inside both for-loop bodies after the trailing-Record lowering.
#[rstest]
fn test_http_serve_two_paths_shared_outer_let() {
    let port = free_port();
    let code = format!(
        "prefix = \"greeting: \"\n\
         reqs1, resps1 = http_serve(\"{port}\", \"POST\", \"/a\")\n\
         reqs2, resps2 = http_serve(\"{port}\", \"POST\", \"/b\")\n\
         for req in reqs1:\n\
         \tresps1 << prefix + \"alice\"\n\
         for req in reqs2:\n\
         \tresps2 << prefix + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    thread::sleep(Duration::from_millis(50));

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let r1 = http_post(port, "/a", "ignored");
        let r2 = http_post(port, "/b", "bob");
        tx.send(vec![r1, r2]).unwrap();
    });

    let responses = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(responses, vec!["greeting: alice", "greeting: bob"]);
}

/// A program where the request handler uses an outer `let` binding compiles
/// and handles requests correctly.  This is a regression test for issue A:
/// chained outer lets must remain visible to the for-loop body.
#[rstest]
fn test_http_serve_echo_with_outer_let() {
    let port = free_port();
    let code = format!(
        "prefix = \"Echo: \"\n\
         requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << prefix + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    thread::sleep(Duration::from_millis(50));

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_post(port, "/echo", "world");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(response, "Echo: world");
}

/// `http_serve` inside an if/else branch is rejected at lowering time.
#[test]
fn test_http_serve_in_if_branch_is_error() {
    let port = free_port();
    let code = format!(
        "if True:\n\
         \trequests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         \tfor req in requests:\n\
         \t\tresponses << req\n"
    );
    let mut ctx = LoweringContext::default();
    let parsed = parser::parse(&code, parser::Mode::Module, "<test>").unwrap();
    let stmts = match parsed {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("unexpected: {other:?}"),
    };
    let result = lower_stmts(&stmts, &mut ctx);
    assert!(
        matches!(result, Err(LoweringError::Unsupported(_))),
        "expected Unsupported error, got: {result:?}"
    );
}

/// `http_serve` inside a function body is rejected at lowering time.
#[test]
fn test_http_serve_in_function_body_is_error() {
    let port = free_port();
    let code = format!(
        "def handler():\n\
         \trequests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         \tfor req in requests:\n\
         \t\tresponses << req\n\
         handler()\n"
    );
    let mut ctx = LoweringContext::default();
    let parsed = parser::parse(&code, parser::Mode::Module, "<test>").unwrap();
    let stmts = match parsed {
        pyast::Mod::Module { body, .. } => body,
        other => panic!("unexpected: {other:?}"),
    };
    let result = lower_stmts(&stmts, &mut ctx);
    assert!(
        matches!(result, Err(LoweringError::Unsupported(_))),
        "expected Unsupported error, got: {result:?}"
    );
}

/// Non-matching paths receive a 404 and do not produce a domain element.
#[rstest]
fn test_http_serve_wrong_path_gets_404() {
    let port = free_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &code, consumer);

    thread::sleep(Duration::from_millis(50));

    // Send to a path that doesn't match — expect a 404 status line.
    let request = format!(
        "POST /wrong HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
    );
    let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).unwrap();
    stream.write_all(request.as_bytes()).unwrap();
    stream.flush().unwrap();
    let mut raw = String::new();
    stream.read_to_string(&mut raw).unwrap();

    assert!(
        raw.starts_with("HTTP/1.1 404"),
        "expected 404 status, got: {raw:?}"
    );
}

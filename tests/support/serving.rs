//! Running a program a test talks to, and talking to it.
//!
//! Compiled into every test binary that drives a program rather than evaluating
//! one: the gallery (`tests/programs/main.rs`) and the hot-reload suite
//! (`tests/hot_reload.rs`). It holds what both need — a compiled sink program, a
//! scheduler pump, and an HTTP client built on `TcpStream` so no client crate
//! becomes a dev dependency. The gallery's own expectation helpers
//! (`expect_scalar` and its siblings) stay in `tests/programs/common/mod.rs`,
//! which nothing else wants.

use std::{
    io::{Read, Write},
    net::TcpStream,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::context::{CompileResultExt, GlobalContext, compile_program},
    interpreter::Consumer,
    live_program::LiveProgram,
};

// ---------------------------------------------------------------------------
// Sink programs (HTTP, etc.)
// ---------------------------------------------------------------------------

/// Compile `source` for a sink program and return the surrounding
/// [`GlobalContext`].  Sink programs (e.g. `http_serve`) have no `main`
/// output; their sinks bind their resources during `compile_program` and
/// then await scheduler ticks to dispatch values.
///
/// The caller must keep the returned context alive (and drive its scheduler
/// via [`drive_until`]) for the duration of the test — sinks are only
/// serviced while the scheduler is running.
// The gallery binary's: a suite that replaces a version wants `start_sink`.
#[allow(dead_code)]
pub fn compile_sink(source: &str) -> GlobalContext {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let _ = compile_program(&mut ctx, source, consumer).unwrap_or_render("<test>", source);
    ctx
}

/// Start `source` as a [`LiveProgram`], for a test that replaces it with
/// another version.
///
/// [`compile_sink`] is the right helper when a test only runs one version. This
/// one hands back the program, which [`LiveProgram::reload`] needs and which the
/// caller must keep alive alongside the context.
pub fn start_sink(source: &str) -> (GlobalContext, LiveProgram) {
    let mut ctx = GlobalContext::default();
    let program = LiveProgram::start(&mut ctx, source, &|| Box::new(|| {}))
        .unwrap_or_render("<test>", source);
    (ctx, program)
}

/// Port allocation for the `{PORT}` placeholder in sink programs.  Lives in the
/// library, behind `test-helpers`, so this crate and `tests/http_server.rs`
/// share one implementation — see [`reserve_test_port`] for why the naive
/// "bind `:0` and close" allocator is not safe here.
pub use cambra::interpreter::http_server::reserve_test_port;

/// Send a raw HTTP/1.1 GET request and return the response body.  Uses a
/// plain `TcpStream` so we don't need an HTTP-client crate as a dev
/// dependency.
pub fn http_get(port: u16, path: &str) -> String {
    let request =
        format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n");
    raw_http(port, &request)
}

/// Send a raw HTTP/1.1 POST with `body` and return the response body.
pub fn http_post(port: u16, path: &str, body: &str) -> String {
    let request = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: 127.0.0.1:{port}\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len(),
    );
    raw_http(port, &request)
}

pub fn raw_http(port: u16, request: &str) -> String {
    raw_http_response(port, request)
        .split_once("\r\n\r\n")
        .map(|(_, body)| body.to_string())
        .unwrap_or_default()
}

/// Send `request` and return the whole response, status line and headers
/// included.
///
/// [`raw_http`] answers with the body, which is what a test about a program's
/// output wants. Use this one where the status code is the contract — the control
/// port distinguishes an accepted request from a rejected one by status, and a
/// body-only reading cannot tell them apart.
pub fn raw_http_response(port: u16, request: &str) -> String {
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
    raw
}

/// Drive `ctx`'s scheduler on the current thread until `rx` delivers a
/// value or `timeout` elapses.
///
/// HTTP sink dispatch is handled automatically by `SinkConsumer` when the
/// scheduler notifies it; this function only needs to keep the scheduler
/// ticking while the request-sending thread runs.
///
/// `check_for_notifications` has no blocking form, so the scheduler has to be
/// pumped on a timer; `recv_timeout` supplies that cadence while still returning
/// the instant the response lands, rather than up to a tick later.
pub fn drive_until<T>(ctx: &mut GlobalContext, rx: &mpsc::Receiver<T>, timeout: Duration) -> T {
    const PUMP_INTERVAL: Duration = Duration::from_millis(10);

    let deadline = Instant::now() + timeout;
    loop {
        ctx.scheduler().check_for_notifications();
        match rx.recv_timeout(PUMP_INTERVAL) {
            Ok(value) => return value,
            Err(mpsc::RecvTimeoutError::Timeout) => assert!(
                Instant::now() < deadline,
                "timed out after {timeout:?} waiting for sink response",
            ),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                panic!("request thread dropped the channel without sending a response")
            }
        }
    }
}

/// Run `requests` on a client thread and pump the scheduler until they finish.
///
/// [`drive_until`] with the channel and the thread it always comes with: a
/// request blocks on a response the scheduler has not computed yet, so the
/// requests have to run somewhere other than the thread doing the driving.
pub fn exchange<T, F>(ctx: &mut GlobalContext, requests: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<T>();
    thread::spawn(move || tx.send(requests()).unwrap());
    drive_until(ctx, &rx, Duration::from_secs(5))
}

/// The main-output consumer a sink-only program never uses.
pub fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

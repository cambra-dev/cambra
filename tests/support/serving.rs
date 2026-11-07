//! Running a program a test talks to, and talking to it.
//!
//! Shared by the suites that drive a program rather than evaluating one: the
//! gallery (`tests/programs/mod.rs`) and the hot-reload suite
//! (`tests/it/hot_reload.rs`). It holds what both need — a compiled sink program, a
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

use cambra::ccl::load::LoadedProgram;
use cambra::{
    ccl::context::{CompileResultExt, GlobalContext, compile_program},
    interpreter::Consumer,
    live_program::LiveProgram,
};

// ---------------------------------------------------------------------------
// Sink programs (HTTP, etc.)
// ---------------------------------------------------------------------------

/// Compile a sink program and retain its resource context for dispatched execution.
pub fn compile_sink(source: &str) -> SinkProgram {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let loaded = LoadedProgram::test(source);
    let program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);
    SinkProgram {
        _context: ctx,
        program,
    }
}

/// Start `source` as a [`LiveProgram`], for a test that replaces it with
/// another version.
///
/// [`compile_sink`] is the right helper when a test only runs one version. This
/// one hands back the program, which [`LiveProgram::reload`] needs and which the
/// caller must keep alive alongside the context.
pub fn start_sink(source: &str) -> (GlobalContext, LiveProgram) {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(source);
    let program =
        LiveProgram::start(&mut ctx, &loaded, &|| Box::new(|| {})).unwrap_or_render(&loaded);
    (ctx, program)
}

/// Port allocation for the `{PORT}` placeholder in sink programs.  Lives in the
/// library, behind `test-helpers`, so this crate and `tests/it/http_server.rs`
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

/// Run `program` until `rx` delivers a value or `timeout` elapses.
/// The observer checks the response channel at drained dispatcher boundaries.
pub fn drive_until<T>(
    program: &mut impl DispatchProgram,
    rx: &mpsc::Receiver<T>,
    timeout: Duration,
) -> T {
    drive_until_named(program, rx, timeout, "sink response")
}

pub fn drive_until_named<T>(
    program: &mut impl DispatchProgram,
    rx: &mpsc::Receiver<T>,
    timeout: Duration,
    what: &'static str,
) -> T {
    let mut response = Response {
        rx,
        deadline: Instant::now() + timeout,
        timeout,
        what,
        value: None,
    };
    program.dispatch(&mut response);
    response
        .value
        .expect("the program stays live until its response")
}

/// Run available work and pause at the first drained boundary.
pub fn dispatch_until_idle(program: &mut impl DispatchProgram) {
    struct Pause;
    impl cambra::interpreter::dispatcher::RunObserver for Pause {
        fn drained(&mut self, _: bool) -> std::ops::ControlFlow<()> {
            std::ops::ControlFlow::Break(())
        }
    }
    program.dispatch(&mut Pause);
}

pub struct SinkProgram {
    _context: GlobalContext,
    program: cambra::ccl::context::CompiledProgram,
}

pub trait DispatchProgram {
    fn dispatch(&mut self, observer: &mut dyn cambra::interpreter::dispatcher::RunObserver);
}

impl DispatchProgram for SinkProgram {
    fn dispatch(&mut self, observer: &mut dyn cambra::interpreter::dispatcher::RunObserver) {
        self.program.dispatch(observer);
    }
}

impl DispatchProgram for cambra::ccl::context::CompiledProgram {
    fn dispatch(&mut self, observer: &mut dyn cambra::interpreter::dispatcher::RunObserver) {
        let mut targets = cambra::interpreter::dispatcher::Targets::default();
        targets.add_sinks(self);
        targets
            .run(1, observer)
            .unwrap_or_else(|why| panic!("sink program dispatches: {why}"));
    }
}

struct IgnoreMain;
impl cambra::interpreter::DataSink for IgnoreMain {
    fn process(&self, _: &cambra::interpreter::Tile) {}
}

impl DispatchProgram for LiveProgram {
    fn dispatch(&mut self, observer: &mut dyn cambra::interpreter::dispatcher::RunObserver) {
        self.run(1, &|_| std::sync::Arc::new(IgnoreMain), observer)
            .unwrap_or_else(|why| panic!("live program dispatches: {why}"));
    }
}

struct Response<'a, T> {
    rx: &'a mpsc::Receiver<T>,
    deadline: Instant,
    timeout: Duration,
    what: &'static str,
    value: Option<T>,
}

impl<T> cambra::interpreter::dispatcher::RunObserver for Response<'_, T> {
    fn drained(&mut self, _: bool) -> std::ops::ControlFlow<()> {
        match self.rx.recv_timeout(Duration::from_millis(10)) {
            Ok(value) => {
                self.value = Some(value);
                std::ops::ControlFlow::Break(())
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                assert!(
                    Instant::now() < self.deadline,
                    "timed out after {:?} waiting for {}",
                    self.timeout,
                    self.what
                );
                std::ops::ControlFlow::Continue(())
            }
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
pub fn exchange<T, F>(program: &mut impl DispatchProgram, requests: F) -> T
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<T>();
    thread::spawn(move || tx.send(requests()).unwrap());
    drive_until(program, &rx, Duration::from_secs(5))
}

/// The main-output consumer a sink-only program never uses.
pub fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

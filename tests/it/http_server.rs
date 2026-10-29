//! End-to-end tests for the HTTP server source/sink (`http_serve`).
//!
//! These tests compile a CHL program that uses `http_serve`, drive the Cambra
//! scheduler on the main thread, and send real HTTP requests from a background
//! thread, verifying that the computed responses are delivered back to the
//! caller.

use cambra::ccl::load::LoadedProgram;
use cambra::chl_parser::FileId;
use std::{
    io::{Read, Write},
    net::TcpStream,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

use cambra::{
    ccl::{
        context::{CompileResultExt, GlobalContext, compile_program},
        lower::{LoweringContext, LoweringError, lower_stmts},
    },
    chl_parser,
    interpreter::{
        Consumer, DataSourceDomainExtentImpl, HttpServerDataSource,
        http_server::{SharedHttpServer, reserve_test_port},
    },
};
use indoc::formatdoc;
use indoc::indoc;
use rstest_log::rstest;
use test_log::test;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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
///
/// `check_for_notifications` has no blocking form, so the scheduler has to be
/// pumped on a timer; `recv_timeout` supplies that cadence while still returning
/// the instant the response lands, rather than up to a tick later.
fn drive_until<T>(ctx: &mut GlobalContext, rx: &mpsc::Receiver<T>, timeout: Duration) -> T {
    const PUMP_INTERVAL: Duration = Duration::from_millis(10);

    let deadline = Instant::now() + timeout;
    loop {
        ctx.scheduler().check_for_notifications();

        match rx.recv_timeout(PUMP_INTERVAL) {
            Ok(value) => return value,
            Err(mpsc::RecvTimeoutError::Timeout) => assert!(
                Instant::now() < deadline,
                "timed out after {timeout:?} waiting for HTTP response"
            ),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                panic!("request thread dropped the channel without sending a response")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// A CHL program echoes each POST body back with a "Received: " prefix.
#[rstest]
fn test_http_serve_echo() {
    let port = reserve_test_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << \"Received: \" + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port = reserve_test_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"GET\", \"/static\")\n\
         for req in requests:\n\
         \tresponses << \"Hello, world!\"\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port = reserve_test_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << \"OK: \" + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port1 = reserve_test_port();
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
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port = reserve_test_port();
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
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port = reserve_test_port();
    let code = format!(
        "prefix = \"Echo: \"\n\
         requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << prefix + req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let port = reserve_test_port();
    let code = format!(
        "if True:\n\
         \trequests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         \tfor req in requests:\n\
         \t\tresponses << req\n"
    );
    let mut ctx = LoweringContext::default();
    let module = chl_parser::parse_module(FileId::ROOT, &code)
        .into_result()
        .expect("parse failed");
    let result = lower_stmts(&module, &mut ctx);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, LoweringError::Unsupported { .. })),
        "expected Unsupported error, got: {:?}",
        result.errors,
    );
}

/// `http_serve` inside a function body is rejected at lowering time.
#[test]
fn test_http_serve_in_function_body_is_error() {
    let port = reserve_test_port();
    let code = format!(
        "def handler():\n\
         \trequests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         \tfor req in requests:\n\
         \t\tresponses << req\n\
         handler()\n"
    );
    let mut ctx = LoweringContext::default();
    let module = chl_parser::parse_module(FileId::ROOT, &code)
        .into_result()
        .expect("parse failed");
    let result = lower_stmts(&module, &mut ctx);
    assert!(
        result
            .errors
            .iter()
            .any(|e| matches!(e, LoweringError::Unsupported { .. })),
        "expected Unsupported error, got: {:?}",
        result.errors,
    );
}

/// Lower `template` with a free port in place of `PORT`, and assert that `http_serve` is refused
/// as not top level.
fn assert_http_serve_refused_as_nested(template: &str) {
    let code = template.replace("PORT", &reserve_test_port().to_string());
    let mut ctx = LoweringContext::default();
    let module = chl_parser::parse_module(FileId::ROOT, &code)
        .into_result()
        .expect("parse failed");
    let result = lower_stmts(&module, &mut ctx);
    assert!(
        result
            .errors
            .iter()
            .any(|e| format!("{e:?}").contains("http_serve is only supported at the top level")),
        "expected a top-level restriction, got: {:?}",
        result.errors,
    );
}

/// A loop body lowers its statements apart from the top level, and refuses `http_serve` the
/// same as any other nested block.
#[test]
fn test_http_serve_in_loop_body_is_error() {
    assert_http_serve_refused_as_nested(indoc! {r#"
        for x in [1, 2]:
            requests, responses = http_serve("PORT", "POST", "/echo")
        0
    "#});
}

/// A `with` block lowers its statements apart from the top level, and refuses `http_serve`
/// the same as any other nested block.
#[test]
fn test_http_serve_in_with_block_is_error() {
    assert_http_serve_refused_as_nested(indoc! {r#"
        pool: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                requests, responses = http_serve("PORT", "POST", "/echo")
                pool := x
        0
    "#});
}

/// Non-matching paths receive a 404 and do not produce a domain element.
#[rstest]
fn test_http_serve_wrong_path_gets_404() {
    let port = reserve_test_port();
    let code = format!(
        "requests, responses = http_serve(\"{port}\", \"POST\", \"/echo\")\n\
         for req in requests:\n\
         \tresponses << req\n"
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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

/// A conditionally fed output answers the requests its guard admits, and only those.
///
/// Feeding under a guard restricts the channel's domain, so the output's type is
/// `{source(…) | __elem ▷ …} ⤇ String`, a refined collection that planning marks as an
/// iteration site like any other (`Type::is_collection`). A rejected request gets no
/// response, so it goes first on its own connection, left open, and the admitted request
/// after it must still be answered with its own body.
#[rstest]
fn a_conditionally_fed_output_answers_the_requests_its_guard_admits() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        reqs, resps = http_serve("{port}", "POST", "/g")
        for req in reqs:
            if req != "skip":
                resps << req
    "#};
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<(String, TcpStream)>();
    thread::spawn(move || {
        let mut rejected = TcpStream::connect(format!("127.0.0.1:{port}")).unwrap();
        rejected
            .write_all(
                format!(
                    "POST /g HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Length: 4\r\n\
                     Connection: close\r\n\r\nskip"
                )
                .as_bytes(),
            )
            .unwrap();
        rejected.flush().unwrap();
        tx.send((http_post(port, "/g", "go"), rejected)).unwrap();
    });
    let (admitted, mut rejected) = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(admitted, "go");

    ctx.scheduler().check_for_notifications();
    rejected.set_nonblocking(true).unwrap();
    let mut buf = [0u8; 64];
    assert!(
        matches!(rejected.read(&mut buf), Err(e) if e.kind() == std::io::ErrorKind::WouldBlock),
        "the request the guard rejects is not answered",
    );
}

/// A retired route answers a request it had already accepted.
///
/// `answer_in_flight` is what retirement calls, and this is the stage a request
/// reaches once the source has taken it off the dispatcher's channel: the reply
/// is written from the shared pending map, and only the sink writes one. With no
/// sink here nothing ever will, which is the position a client is in when the
/// version that would have replied has been retired.
///
/// Driven at the source rather than through a program because the accepted-but
/// -unanswered state is reachable deterministically here: `check_for_new_data`
/// accepts without replying, where pumping a compiled program's scheduler
/// answers a one-step route outright.
/// `a_request_that_arrived_before_its_route_was_retired_is_answered` covers the
/// other stage, a request still in the channel, through a real reload.
#[test]
fn a_retired_route_answers_a_request_it_had_accepted() {
    let port = reserve_test_port();
    let server = SharedHttpServer::new(port).expect("the reserved port binds");
    let mut source = HttpServerDataSource::new(
        &server,
        "GET".to_string(),
        "/x".to_string(),
        "s".to_string(),
    );

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || tx.send(http_get(port, "/x")).unwrap());

    // Accept it. Polled rather than slept on, so the precondition holds however
    // long the dispatcher takes.
    let deadline = Instant::now() + Duration::from_secs(5);
    while !source.check_for_new_data() {
        assert!(
            Instant::now() < deadline,
            "the request never reached the source",
        );
        thread::sleep(Duration::from_millis(5));
    }
    assert!(
        rx.try_recv().is_err(),
        "the request is accepted and unanswered: no sink exists to reply",
    );

    source.answer_in_flight();
    assert_eq!(
        rx.recv_timeout(Duration::from_secs(5))
            .expect("retirement answers the request"),
        "Not Found",
        "the same answer the address gives once the route is gone",
    );
}

/// Compile `code`, send one request with `request`, and return the reply body, failing after five
/// seconds without one.
fn reply_to(code: &str, request: impl FnOnce() -> String + Send + 'static) -> String {
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(code);
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let _ = tx.send(request());
    });
    drive_until(&mut ctx, &rx, Duration::from_secs(5))
}

/// A reply fed in the loop body, after a block that writes a mutable variable, answers each
/// request.
#[test]
fn a_reply_after_a_writing_block_answers_the_request() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        reqs, resps = http_serve("{port}", "POST", "/hit")
        hits: Mut(Int, Txn) := 0
        for req in reqs:
            with begin():
                hits := hits + 1
            resps << "ok\n"
    "#};
    assert_eq!(
        reply_to(&code, move || http_post(port, "/hit", "x")),
        "ok\n"
    );
}

/// A reply fed inside the block that writes a mutable variable never answers the request.
///
/// `docs/chl-spec.md`, "8.4 Feeds are the second form of mutability" admits a reply inside a
/// block, sequenced after the commit and indexed by commit tick. The same in-block feed over a
/// `stdin()` loop into a `defer()` replies (`progress_feed_inside_tx` in
/// `tests/it/compilation_pipeline/transactions.rs` covers the literal-list loop), and the reply
/// moved after the block answers (the sibling above).
// Pinned on the failure rather than deferred: an `#[ignore]` reports the same green whether the
// gap closed, regressed, or went away, and nothing runs ignored tests here. The hang is pinned on
// `drive_until`'s timeout, which returns control to the test, where rstest's `#[timeout]` would
// leave the driving thread running.
#[test]
#[should_panic(expected = "timed out after 5s waiting for HTTP response")]
fn a_reply_inside_a_writing_block_answers_the_request() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        reqs, resps = http_serve("{port}", "POST", "/hit")
        hits: Mut(Int, Txn) := 0
        for req in reqs:
            with begin():
                hits := hits + 1
                resps << "ok\n"
    "#};
    assert_eq!(
        reply_to(&code, move || http_post(port, "/hit", "x")),
        "ok\n"
    );
}

/// A module whose route takes its address from `const` parameters serves, in each run, the
/// address that run gives it (`docs/chl-spec.md`, "9.19 Constants").
#[rstest]
fn two_runs_serve_the_routes_their_arguments_give() {
    let port = reserve_test_port();
    let service = indoc! {r#"
        const param port: String
        const param path: String
        param reply: String
        requests, responses = http_serve(port, "GET", path)
        for req in requests:
            responses << reply
    "#};
    let root = formatdoc! {r#"
        run service(port="{port}", path="/eu", reply="hello from eu") as eu
        run service(port="{port}", path="/us", reply="hello from us") as us
    "#};
    let loaded = LoadedProgram::load(
        cambra::ccl::load::RootFile {
            path: "main.cambra".to_owned(),
            module: None,
            text: root,
        },
        &mut cambra::ccl::load::InMemory::default().with("service", service),
    );
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut ctx = GlobalContext::default();
    let _ = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let eu = http_get(port, "/eu");
        let us = http_get(port, "/us");
        tx.send(vec![eu, us]).unwrap();
    });
    let responses = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(responses, vec!["hello from eu", "hello from us"]);
}

// ---------------------------------------------------------------------------
// The inline dispatcher
// ---------------------------------------------------------------------------

/// How a scenario drives the program: the serial scheduler loop, or the inline dispatcher.
#[derive(Clone, Copy, Debug)]
enum Mode {
    Serial,
    Inline,
}

/// A program compiled for `mode`: the context, the program, and the inline run when there is one.
struct Served {
    ctx: GlobalContext,
    _program: cambra::ccl::context::CompiledProgram,
    run: Option<cambra::interpreter::parallel::PooledRun>,
}

impl Served {
    /// Compile `code`, and start the inline dispatcher over it for [`Mode::Inline`], which
    /// refuses a program the plan does not admit.
    fn start(mode: Mode, code: &str) -> Self {
        let mut ctx = GlobalContext::default();
        let loaded = LoadedProgram::test(code);
        let mut program =
            compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
        let run = match mode {
            Mode::Serial => None,
            Mode::Inline => Some(
                cambra::interpreter::parallel::PooledRun::start(
                    &mut ctx,
                    &mut program,
                    &mut None,
                    &cambra::interpreter::parallel::Config { morsel_rows: 3 },
                    Box::new(|| {}),
                )
                .unwrap_or_else(|why| panic!("the inline dispatcher refuses the program: {why}")),
            ),
        };
        Self {
            ctx,
            _program: program,
            run,
        }
    }

    /// One pass of the loop the binary runs: deliver, serve the pool, pull the sinks. Says whether
    /// a lap ran a morsel.
    fn pump(&mut self) -> bool {
        self.ctx.scheduler().check_for_notifications();
        let Some(run) = self.run.as_mut() else {
            return false;
        };
        let ran = run.lap() == cambra::interpreter::parallel::Lap::Ran;
        self.ctx.scheduler().pull_sinks();
        ran
    }
}

/// What one request of a scenario sends and whether the program answers it.
struct Sent {
    path: &'static str,
    body: &'static str,
    answered: bool,
}

fn sent(path: &'static str, body: &'static str) -> Sent {
    Sent {
        path,
        body,
        answered: true,
    }
}

fn unanswered(path: &'static str, body: &'static str) -> Sent {
    Sent {
        path,
        body,
        answered: false,
    }
}

/// What a scenario observed: the reply to each request, and how many laps ran a morsel.
struct Observed {
    replies: Vec<Option<String>>,
    laps_that_ran: usize,
}

/// Send `requests` from threads of their own, one wave at a time: the requests of a wave are sent
/// at once, and the next wave once every answered request of the waves before has its reply.
/// Pump the program in `mode` throughout. A request that is not answered stays `None` and is
/// checked to be left open after further passes; every reply is checked to have been written
/// once, and an inline run to hold no row afterwards.
fn serve_requests(mode: Mode, code: impl Fn(u16) -> String, waves: &[&[Sent]]) -> Observed {
    let port = reserve_test_port();
    let mut served = Served::start(mode, &code(port));
    let (tx, rx) = mpsc::channel::<(usize, String)>();
    let (open_tx, open_rx) = mpsc::channel::<(usize, TcpStream)>();
    let mut replies: Vec<Option<String>> = Vec::new();
    let mut laps_that_ran = 0;
    let mut expected = 0;
    let mut got = 0;
    for wave in waves {
        for request in *wave {
            let index = replies.len();
            replies.push(None);
            expected += usize::from(request.answered);
            let (path, body, answered) = (request.path, request.body, request.answered);
            let (tx, open_tx) = (tx.clone(), open_tx.clone());
            thread::spawn(move || {
                if answered {
                    let _ = tx.send((index, http_post(port, path, body)));
                } else {
                    let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).unwrap();
                    let head = format!(
                        "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\n\
                         Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                        body.len()
                    );
                    stream.write_all(head.as_bytes()).unwrap();
                    stream.flush().unwrap();
                    let _ = open_tx.send((index, stream));
                }
            });
        }
        let deadline = Instant::now() + Duration::from_secs(10);
        while got < expected {
            laps_that_ran += usize::from(served.pump());
            match rx.recv_timeout(Duration::from_millis(5)) {
                Ok((index, reply)) => {
                    assert!(replies[index].replace(reply).is_none(), "one reply each");
                    got += 1;
                }
                Err(_) => assert!(
                    Instant::now() < deadline,
                    "{mode:?}: {got} of {expected} replies after 10 s"
                ),
            }
        }
    }
    drop((tx, open_tx));
    // Further passes: a reply written twice, or to a request the program does not answer, would
    // show on the sockets by now.
    for _ in 0..50 {
        served.pump();
        thread::sleep(Duration::from_millis(1));
    }
    assert!(
        rx.try_recv().is_err(),
        "{mode:?}: a request was answered twice"
    );
    for (index, stream) in open_rx.try_iter() {
        stream.set_nonblocking(true).unwrap();
        let mut buf = [0u8; 64];
        assert!(
            matches!((&stream).read(&mut buf), Err(e) if e.kind() == std::io::ErrorKind::WouldBlock),
            "{mode:?}: request {index} is not answered by the program"
        );
    }
    assert_eq!(
        cambra::interpreter::http_server::unmatched_replies_on_this_thread(),
        0,
        "{mode:?}: the reply sink was handed an index no request waits on"
    );
    if let Some(run) = &served.run {
        assert_eq!(
            run.held_keys(),
            0,
            "{mode:?}: every row was read and released"
        );
    }
    Observed {
        replies,
        laps_that_ran,
    }
}

/// The replies of `requests` to `code` are the same through the serial loop and the inline
/// dispatcher, and are `expected`. The inline run takes the requests in the waves given.
fn replies_agree(
    code: impl Fn(u16) -> String + Copy,
    waves: &[&[Sent]],
    expected: &[Option<&str>],
) -> Observed {
    let serial = serve_requests(Mode::Serial, code, waves);
    let inline = serve_requests(Mode::Inline, code, waves);
    let expected: Vec<Option<String>> = expected.iter().map(|r| r.map(str::to_string)).collect();
    assert_eq!(serial.replies, expected, "the serial loop");
    assert_eq!(
        inline.replies, serial.replies,
        "the inline dispatcher answers as the serial loop does"
    );
    inline
}

fn echo_program(port: u16) -> String {
    formatdoc! {r#"
        requests, responses = http_serve("{port}", "POST", "/echo")
        for req in requests:
            responses << "Received: " + req
    "#}
}

/// Source, map, sink: one request, and eight in two waves, each answered once with its own body.
/// The second wave arrives after the first was answered, so the dispatcher runs more than one lap
/// and more than one morsel of three rows.
#[test]
fn source_map_sink_replies_to_each_request_once() {
    replies_agree(
        echo_program,
        &[&[sent("/echo", "hello")]],
        &[Some("Received: hello")],
    );
    let first = [
        sent("/echo", "a"),
        sent("/echo", "b"),
        sent("/echo", "c"),
        sent("/echo", "d"),
    ];
    let second = [
        sent("/echo", "e"),
        sent("/echo", "f"),
        sent("/echo", "g"),
        sent("/echo", "h"),
    ];
    let expected: Vec<Option<&str>> = [
        "Received: a",
        "Received: b",
        "Received: c",
        "Received: d",
        "Received: e",
        "Received: f",
        "Received: g",
        "Received: h",
    ]
    .into_iter()
    .map(Some)
    .collect();
    let observed = replies_agree(echo_program, &[&first, &second], &expected);
    assert!(
        observed.laps_that_ran >= 2,
        "the waves ran in {} laps",
        observed.laps_that_ran
    );
}

/// A map with a filter reads each request twice, in the predicate and in the value: the compiled
/// program reads the request memo at each key of the iterated source, a keyed read. The inline
/// dispatcher admits it, and answers as the serial loop does: the admitted requests, and the
/// others left open.
#[test]
fn a_filtered_map_replies_to_the_admitted_requests_only() {
    let code = |port: u16| {
        formatdoc! {r#"
            reqs, resps = http_serve("{port}", "POST", "/g")
            kept = [r + "!" for r in reqs if r != "skip"]
            for k in kept:
                resps << k
        "#}
    };
    let first = [
        sent("/g", "one"),
        unanswered("/g", "skip"),
        sent("/g", "two"),
        sent("/g", "three"),
    ];
    let second = [
        sent("/g", "four"),
        sent("/g", "five"),
        unanswered("/g", "skip"),
    ];
    replies_agree(
        code,
        &[&first, &second],
        &[
            Some("one!"),
            None,
            Some("two!"),
            Some("three!"),
            Some("four!"),
            Some("five!"),
            None,
        ],
    );
}

/// A reply fed under an `if` reads the request at the loop's own key too, and is answered the same
/// way through both loops.
#[test]
fn a_reply_fed_under_an_if_replies_to_the_admitted_requests_only() {
    let code = |port: u16| {
        formatdoc! {r#"
            reqs, resps = http_serve("{port}", "POST", "/g")
            for req in reqs:
                if req != "skip":
                    resps << req
        "#}
    };
    let requests = [
        sent("/g", "one"),
        unanswered("/g", "skip"),
        sent("/g", "two"),
        sent("/g", "three"),
    ];
    replies_agree(
        code,
        &[&requests],
        &[Some("one"), None, Some("two"), Some("three")],
    );
}

/// A comprehension read by a loop is a `Memo` between two maps.
#[test]
fn a_memo_between_two_maps_replies_to_each_request_once() {
    let code = |port: u16| {
        formatdoc! {r#"
            reqs, resps = http_serve("{port}", "POST", "/m")
            shouted = [r + "!" for r in reqs]
            for s in shouted:
                resps << s + "?"
        "#}
    };
    let requests = [
        sent("/m", "a"),
        sent("/m", "b"),
        sent("/m", "c"),
        sent("/m", "d"),
        sent("/m", "e"),
    ];
    replies_agree(
        code,
        &[&requests],
        &[
            Some("a!?"),
            Some("b!?"),
            Some("c!?"),
            Some("d!?"),
            Some("e!?"),
        ],
    );
}

/// A request that arrives after laps that found nothing to run is answered by a later lap, and a
/// request after that is answered too.
#[test]
fn a_request_that_arrives_after_idle_laps_is_replied_in_a_later_lap() {
    use cambra::interpreter::parallel::Lap;

    let port = reserve_test_port();
    let mut served = Served::start(Mode::Inline, &echo_program(port));
    for _ in 0..3 {
        served.ctx.scheduler().check_for_notifications();
        let run = served.run.as_mut().expect("an inline run");
        assert_eq!(run.lap(), Lap::Idle, "no request has arrived");
        served.ctx.scheduler().pull_sinks();
    }
    for body in ["late", "later"] {
        let (tx, rx) = mpsc::channel::<String>();
        thread::spawn(move || {
            tx.send(http_post(port, "/echo", body)).unwrap();
        });
        let mut ran = 0;
        let deadline = Instant::now() + Duration::from_secs(5);
        let reply = loop {
            ran += usize::from(served.pump());
            match rx.recv_timeout(Duration::from_millis(5)) {
                Ok(reply) => break reply,
                Err(_) => assert!(Instant::now() < deadline, "no reply to {body}"),
            }
        };
        assert_eq!(reply, format!("Received: {body}"));
        assert_eq!(ran, 1, "the request is one morsel of one lap");
    }
}

/// `payload` written to the echo program's port as bytes, and what comes back before the
/// connection closes, with the program pumped in `mode`.
fn exchange_raw(mode: Mode, payload: &'static str) -> String {
    let port = reserve_test_port();
    let mut served = Served::start(mode, &echo_program(port));
    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let mut stream = TcpStream::connect(format!("127.0.0.1:{port}")).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(2)))
            .unwrap();
        stream.write_all(payload.as_bytes()).unwrap();
        let mut raw = String::new();
        let _ = stream.read_to_string(&mut raw);
        tx.send(raw).unwrap();
    });
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        served.pump();
        match rx.recv_timeout(Duration::from_millis(5)) {
            // The `Date` header is the second the server wrote it in.
            Ok(raw) => {
                return raw
                    .lines()
                    .filter(|line| !line.starts_with("Date:"))
                    .collect::<Vec<_>>()
                    .join("\n");
            }
            Err(_) => assert!(Instant::now() < deadline, "{mode:?}: no answer"),
        }
    }
}

/// A request for another path and a malformed one are answered as they are in the serial loop:
/// the route table and the HTTP parser answer them, and the program is not asked.
#[test]
fn an_unmatched_or_malformed_request_is_handled_as_in_the_serial_loop() {
    let unmatched =
        "POST /wrong HTTP/1.1\r\nHost: x\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";
    for payload in [unmatched, "NOT HTTP AT ALL\r\n\r\n"] {
        let serial = exchange_raw(Mode::Serial, payload);
        let inline = exchange_raw(Mode::Inline, payload);
        assert_eq!(inline, serial, "{payload:?}");
    }
    assert!(
        exchange_raw(Mode::Inline, unmatched).starts_with("HTTP/1.1 404"),
        "an unmatched path is a 404"
    );
}

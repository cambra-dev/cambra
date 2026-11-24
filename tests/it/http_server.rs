//! End-to-end tests for the HTTP server source/sink (`std::http::serve`).
//!
//! These tests compile a CHL program that runs `std::http::serve`, drive the Cambra
//! scheduler on the main thread, and send real HTTP requests from a background
//! thread, verifying that the computed responses are delivered back to the
//! caller.

use cambra::ccl::load::LoadedProgram;
use cambra::chl_parser::FileId;
use cambra::interpreter::Value;
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
        lower::LoweringContext,
    },
    interpreter::{
        Consumer, DataSourceDomainExtentImpl, HttpServerDataSource,
        http_server::{SharedHttpServer, reserve_test_port},
    },
};
use indoc::formatdoc;
use indoc::indoc;
use rstest_log::rstest;

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
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            run std::http::serve(port="{port}", method="POST", path="/echo") as server
            server_replies: Feed(http_api::Response)
            for req in [request.body() for request in server::requests]:
                server_replies << http_api::ok_text("Received: " + req)
            server::respond(server_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    // Send one POST request from a background thread and collect the response.
    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_post(port, "/echo", "hello");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));

    assert_eq!(response, "Received: hello");
}

/// A request reaches the route whose path its target spells equivalently: percent-encodings of
/// unreserved characters, hex case and dot segments do not change the path (RFC 3986,
/// "6.2.2. Syntax-Based Normalization").
#[rstest]
#[case::the_declared_spelling("/a%62/c%2f")]
#[case::decoded("/ab/c%2F")]
#[case::dot_segments("/x/../ab/./c%2F")]
#[case::absolute_form("http://localhost/ab/c%2F?q=1")]
fn a_request_reaches_the_route_its_path_spells_equivalently(#[case] target: &str) {
    let port = reserve_test_port();
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            run std::http::serve(port="{port}", method="POST", path="/a%62/c%2f") as server
            server::respond([http_api::ok_text("at " + r.target()) for r in server::requests])
            "#
    );
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel::<String>();
    let sent = target.to_string();
    thread::spawn(move || {
        tx.send(http_post(port, &sent, "")).unwrap();
    });
    let expected = format!("at {target}");
    assert_eq!(drive_until(&mut ctx, &rx, Duration::from_secs(5)), expected);
}

#[rstest]
fn test_http_serve_const() {
    let port = reserve_test_port();
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            run std::http::serve(port="{port}", method="GET", path="/static") as http_responses
            http_responses_replies: Feed(http_api::Response)
            requests = [request.body() for request in http_responses::requests]
            for req in requests:
                http_responses_replies << http_api::ok_text("Hello, world!")
            http_responses::respond(http_responses_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            run std::http::serve(port="{port}", method="POST", path="/echo") as http_responses
            http_responses_replies: Feed(http_api::Response)
            requests = [request.body() for request in http_responses::requests]
            for req in requests:
                http_responses_replies << http_api::ok_text("OK: " + req)
            http_responses::respond(http_responses_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            def handle(req: http_api::Request, prefix: String) => http_api::Response:
                http_api::ok_text(prefix + req.body())
            run std::http::serve(port="{port1}", method="GET", path="/greet") as greet
            run std::http::serve(port="{port1}", method="POST", path="/echo") as echo
            greet::respond([handle(req, "hello") for req in greet::requests])
            echo::respond([handle(req, "echo: ") for req in echo::requests])
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            prefix = "greeting: "
            run std::http::serve(port="{port}", method="POST", path="/a") as http_resps1
            http_resps1_replies: Feed(http_api::Response)
            reqs1 = [request.body() for request in http_resps1::requests]
            run std::http::serve(port="{port}", method="POST", path="/b") as http_resps2
            http_resps2_replies: Feed(http_api::Response)
            reqs2 = [request.body() for request in http_resps2::requests]
            for req in reqs1:
                http_resps1_replies << http_api::ok_text(prefix + "alice")
            for req in reqs2:
                http_resps2_replies << http_api::ok_text(prefix + req)
            http_resps1::respond(http_resps1_replies)
            http_resps2::respond(http_resps2_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            prefix = "Echo: "
            run std::http::serve(port="{port}", method="POST", path="/echo") as http_responses
            http_responses_replies: Feed(http_api::Response)
            requests = [request.body() for request in http_responses::requests]
            for req in requests:
                http_responses_replies << http_api::ok_text(prefix + req)
            http_responses::respond(http_responses_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_post(port, "/echo", "world");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(response, "Echo: world");
}

/// A route exposes ordinary request values through its module.
#[rstest]
fn test_http_serve_module_request_values() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http as http_api
        run std::http::serve(port="{port}", method="POST", path="/echo") as http_responses
        http_responses_replies: Feed(http_api::Response)
        requests = [request.body() for request in http_responses::requests]
        for req in requests:
            http_responses_replies << http_api::ok_text("Echo: " + req)
        http_responses::respond(http_responses_replies)
    "#};

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let resp = http_post(port, "/echo", "world");
        tx.send(resp).unwrap();
    });

    let response = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(response, "Echo: world");
}

/// Lower `template` with a free port in place of `PORT`, and answer the lowering errors'
/// debug renderings.
fn http_serve_lowering_errors(template: &str) -> Vec<String> {
    let code = template.replace("PORT", &reserve_test_port().to_string());
    let mut ctx = LoweringContext::default();
    let loaded = LoadedProgram::test(&code);
    let result = cambra::ccl::lower::modules::lower_program(&loaded, &mut ctx);
    result.errors.iter().map(|e| format!("{e:?}")).collect()
}

/// `http_serve` is no builtin, so a module may bind the name.
#[test_log::test]
fn a_module_may_bind_the_name_http_serve() {
    let errors = http_serve_lowering_errors(indoc! {r#"
        def http_serve(port: String, method: String, path: String) => String:
            method + " " + path + " on " + port
        http_serve("PORT", "POST", "/echo")
    "#});
    assert!(errors.is_empty(), "{errors:?}");
}

/// A route whose responses the program never feeds is refused, and the error names the call
/// rather than the name its response channel is bound under.
#[test_log::test]
fn a_route_whose_responses_are_never_fed_names_the_call() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http as http_api
        run std::http::serve(port="{port}", method="POST", path="/e") as http_responses
        requests = [request.body() for request in http_responses::requests]
        1
    "#};
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let Err(errors) = compile_program(&mut ctx, &loaded, consumer) else {
        panic!("a route whose responses are never fed compiled");
    };
    let rendered = cambra::ccl::context::render_errors(&errors, loaded.sources());
    assert!(rendered.contains("has no feed or define"), "{rendered}");
    let error = errors
        .iter()
        .find(|error| error.message().contains("has no feed or define"))
        .expect("an unfilled response collection is reported");
    let span = error.span().expect("the error names the run statement");
    assert_eq!(span.file, FileId::ROOT);
    assert!(code[span.start..span.end].starts_with("run std::http"));
    assert!(error.message().contains("call `respond`"), "{rendered}");
}

/// Two routes whose paths differ only in a character no identifier holds are two routes.
#[test_log::test]
fn paths_differing_only_in_punctuation_are_two_routes() {
    let errors = http_serve_lowering_errors(indoc! {r#"
        import std::http as http_api
        run std::http::serve(port="PORT", method="GET", path="/a-b") as http_resps1
        http_resps1_replies: Feed(http_api::Response)
        reqs1 = [request.body() for request in http_resps1::requests]
        for req in reqs1:
            http_resps1_replies << http_api::ok_text("dash")
        run std::http::serve(port="PORT", method="GET", path="/a_b") as http_resps2
        http_resps2_replies: Feed(http_api::Response)
        reqs2 = [request.body() for request in http_resps2::requests]
        for req in reqs2:
            http_resps2_replies << http_api::ok_text("underscore")
        http_resps1::respond(http_resps1_replies)
        http_resps2::respond(http_resps2_replies)
    "#});
    assert!(
        errors.is_empty(),
        "expected no lowering errors, got: {errors:?}"
    );
}

/// Two spellings of one port are one route, so serving it under both is refused.
#[test_log::test]
fn spellings_of_one_port_are_one_route() {
    for spelled in ["0PORT", "+PORT"] {
        let errors = http_serve_lowering_errors(&formatdoc! {r#"
            import std::http as http_api
            run std::http::serve(port="PORT", method="GET", path="/x") as http_resps1
            http_resps1_replies: Feed(http_api::Response)
            reqs1 = [request.body() for request in http_resps1::requests]
            for req in reqs1:
                http_resps1_replies << http_api::ok_text("one")
            run std::http::serve(port="{spelled}", method="GET", path="/x") as http_resps2
            http_resps2_replies: Feed(http_api::Response)
            reqs2 = [request.body() for request in http_resps2::requests]
            for req in reqs2:
                http_resps2_replies << http_api::ok_text("two")
            http_resps1::respond(http_resps1_replies)
            http_resps2::respond(http_resps2_replies)
        "#});
        assert!(
            errors
                .iter()
                .any(|e| e.contains("a route is unique across all runs")),
            "expected `{spelled}` to be refused as a duplicate route, got: {errors:?}"
        );
    }
}

/// Non-matching paths receive a 404 and do not produce a domain element.
#[rstest]
fn test_http_serve_wrong_path_gets_404() {
    let port = reserve_test_port();
    let code = indoc::formatdoc!(
        r#"
            import std::http as http_api
            run std::http::serve(port="{port}", method="POST", path="/echo") as http_responses
            http_responses_replies: Feed(http_api::Response)
            requests = [request.body() for request in http_responses::requests]
            for req in requests:
                http_responses_replies << http_api::ok_text(req)
            http_responses::respond(http_responses_replies)
            "#
    );

    let consumer: Box<dyn Consumer> = Box::new(|| {});

    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

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

/// A response definition cannot omit requests selected out by a guard.
#[test_log::test]
fn a_conditionally_fed_output_is_rejected_as_incomplete() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/g") as server
        replies: Feed(http::Response)
        for req in server::requests:
            if req.body() != "skip":
                replies << http::ok_text(req.body())
        server::respond(replies)
    "#};
    let loaded = LoadedProgram::test(&code);
    let result = compile_program(&mut GlobalContext::default(), &loaded, Box::new(|| {}));
    let errors = match result {
        Ok(_) => panic!("an incomplete response definition compiled"),
        Err(e) => e,
    };
    let text = cambra::ccl::context::render_errors(&errors, loaded.sources());
    assert!(
        text.contains("do not answer exactly its requests"),
        "{text}"
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
#[test_log::test]
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
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let _ = tx.send(request());
    });
    drive_until(&mut ctx, &rx, Duration::from_secs(5))
}

/// A reply fed in the loop body, after a block that writes a mutable variable, answers each
/// request.
#[test_log::test]
fn a_reply_after_a_writing_block_answers_the_request() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http as http_api
        run std::http::serve(port="{port}", method="POST", path="/hit") as http_resps
        http_resps_replies: Feed(http_api::Response)
        reqs = [request.body() for request in http_resps::requests]
        hits: Mut(Int, Txn) := 0
        for req in reqs:
            with begin():
                hits := hits + 1
            http_resps_replies << http_api::ok_text("ok\n")
        http_resps::respond(http_resps_replies)
    "#};
    assert_eq!(
        reply_to(&code, move || http_post(port, "/hit", "x")),
        "ok\n"
    );
}

/// A reply fed inside the block that writes a mutable variable answers the request: it rides
/// the transaction's commit and is keyed by the request it answers (`docs/chl-spec.md`, "8.4
/// Deferred collections").
#[test_log::test]
fn a_reply_inside_a_writing_block_answers_the_request() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http as http_api
        run std::http::serve(port="{port}", method="POST", path="/hit") as http_resps
        http_resps_replies: Feed(http_api::Response)
        reqs = [request.body() for request in http_resps::requests]
        hits: Mut(Int, Txn) := 0
        for req in reqs:
            with begin():
                hits := hits + 1
                http_resps_replies << http_api::ok_text("ok\n")
        http_resps::respond(http_resps_replies)
    "#};
    assert_eq!(
        reply_to(&code, move || http_post(port, "/hit", "x")),
        "ok\n"
    );
}

/// Each request is answered with the reply its own transaction fed: the reply is keyed by the
/// request, and the commit order (here the arrival order) decides what each transaction read.
#[test_log::test]
fn a_reply_inside_a_writing_block_answers_each_request_with_its_own_value() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http as http_api
        run std::http::serve(port="{port}", method="POST", path="/hit") as server
        reqs = [request.body() for request in server::requests]
        resps: Feed(http_api::Response)
        seen: Mut(String, Txn) := ""
        for req in reqs:
            with begin():
                seen := seen + req
                resps << http_api::ok_text(seen)
        server::respond(resps)
    "#};
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let a = http_post(port, "/hit", "a");
        let b = http_post(port, "/hit", "b");
        tx.send(vec![a, b]).unwrap();
    });
    assert_eq!(
        drive_until(&mut ctx, &rx, Duration::from_secs(5)),
        vec!["a", "ab"]
    );
}

/// A module whose route takes its address from `const` parameters serves, in each run, the
/// address that run gives it (`docs/chl-spec.md`, "9.19 Constants").
#[rstest]
fn two_runs_serve_the_routes_their_arguments_give() {
    let port = reserve_test_port();
    let service = indoc! {r#"
        import std::http as http_api
        const param port: String
        const param path: String
        param reply: String
        run std::http::serve(port=port, method="GET", path=path) as http_responses
        http_responses_replies: Feed(http_api::Response)
        requests = [request.body() for request in http_responses::requests]
        for req in requests:
            http_responses_replies << http_api::ok_text(reply)
        http_responses::respond(http_responses_replies)
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
    let _program = compile_program(&mut ctx, &loaded, consumer).unwrap_or_render(&loaded);

    let (tx, rx) = mpsc::channel::<Vec<String>>();
    thread::spawn(move || {
        let eu = http_get(port, "/eu");
        let us = http_get(port, "/us");
        tx.send(vec![eu, us]).unwrap();
    });
    let responses = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(responses, vec!["hello from eu", "hello from us"]);
}

struct HttpReply {
    status: u16,
    headers: Vec<(String, String)>,
    body: String,
}

fn exchange(port: u16, path: &str, body: &[u8], headers: &[(&str, &str)]) -> HttpReply {
    exchange_method(port, "POST", path, body, headers)
}

fn exchange_method(
    port: u16,
    method: &str,
    path: &str,
    body: &[u8],
    headers: &[(&str, &str)],
) -> HttpReply {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    write!(
        stream,
        "{method} {path} HTTP/1.1\r\nHost: localhost\r\nContent-Length: {}\r\nConnection: close\r\n",
        body.len()
    )
    .unwrap();
    for (name, value) in headers {
        write!(stream, "{name}: {value}\r\n").unwrap();
    }
    stream.write_all(b"\r\n").unwrap();
    stream.write_all(body).unwrap();
    let mut response = String::new();
    stream.read_to_string(&mut response).unwrap();
    let (head, body) = response.split_once("\r\n\r\n").expect("an HTTP response");
    let mut lines = head.lines();
    let status = lines
        .next()
        .unwrap()
        .split_whitespace()
        .nth(1)
        .unwrap()
        .parse()
        .unwrap();
    let headers = lines
        .map(|l| {
            let (name, value) = l.split_once(':').unwrap();
            (name.to_string(), value.trim().to_string())
        })
        .collect();
    HttpReply {
        status,
        headers,
        body: body.to_string(),
    }
}

#[test_log::test]
fn typed_http_preserves_metadata_status_and_repeated_headers() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/typed") as server
        def handle(req: http::Request) => http::Response:
            repeated := ""
            for h in req.headers():
                if h.name() == "X-Input":
                    repeated += h.value() + ";"
            http::Response::new(201, box([
                http::Header::new("X-Output", "one"),
                http::Header::new("X-Output", "two"),
            ]), req.method() + " " + req.target() + " " + req.body() + " " + repeated)
        server::respond([handle(req) for req in server::requests])
    "#};
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        tx.send(exchange(
            port,
            "/typed?query=yes",
            "héllo".as_bytes(),
            &[("X-Input", "a"), ("X-Input", "b")],
        ))
        .unwrap();
    });
    let reply = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(reply.status, 201);
    assert_eq!(reply.body, "POST /typed?query=yes héllo a;b;");
    let repeated: Vec<_> = reply
        .headers
        .iter()
        .filter(|(n, _)| n.eq_ignore_ascii_case("X-Output"))
        .map(|(_, v)| v.as_str())
        .collect();
    assert_eq!(repeated, ["one", "two"]);
}

#[test_log::test]
fn typed_http_rejects_non_utf8_without_poisoning_the_route() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/text") as server
        server::respond([http::ok_text(req.body()) for req in server::requests])
    "#};
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let bad = exchange(port, "/text", &[0xff], &[]);
        let good = exchange(port, "/text", "λ".as_bytes(), &[]);
        tx.send((bad, good)).unwrap();
    });
    let (bad, good) = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(bad.status, 400);
    assert_eq!(good.status, 200);
    assert_eq!(good.body, "λ");
    let source = ctx
        .conversion_ctx()
        .get_source(&cambra::ccl::lower::http_requests_source_name(
            port, "POST", "/text",
        ))
        .unwrap();
    let admitted = source.borrow().get_yield_predicate();
    assert!(admitted.contains_path(&[Value::UInt(0)]));
    assert!(
        !admitted.contains_path(&[Value::UInt(1)]),
        "only the valid request gets a key"
    );
}

#[rstest]
#[case::wrong_route(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/left") as left
    run std::http::serve(port="{PORT}", method="POST", path="/right") as right
    left::respond([http::ok_text(r.body()) for r in right::requests])
    right::respond([http::ok_text(r.body()) for r in left::requests])
"#}, "Conflicting Types: left::Reqs | right::Reqs")]
#[case::missing_keys(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/typed") as server
    server::respond([http::ok_text(r.body()) for r in server::requests if r.body() == "only"])
"#}, "domain")]
#[case::nominal_response(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/typed") as server
    server::respond([r.body() for r in server::requests])
"#}, "Response")]
#[case::missing_connection(indoc! {r#"
    run std::http::serve(port="{PORT}", method="POST", path="/typed") as server
"#}, "no feed or define")]
#[case::conditional_connection(indoc! {r#"
    import std::http
    enabled = sum([1 for line in stdin()]) > 0
    run std::http::serve(port="{PORT}", method="POST", path="/typed") as server
    if enabled:
        server::respond([http::ok_text(r.body()) for r in server::requests])
    else:
        ()
    0
"#}, "<<= must occur as a top-level statement")]
#[case::repeated_connection(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/typed") as server
    server::respond([http::ok_text(r.body()) for r in server::requests])
    server::respond([http::ok_text(r.body()) for r in server::requests])
"#}, "multiple definitions")]
#[case::two_write_sites(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/twice") as server
    replies: Feed(http::Response)
    for req in server::requests:
        replies << http::ok_text(req.body())
    for req in server::requests:
        replies << http::ok_text(req.body())
    server::respond(replies)
"#}, "do not answer exactly its requests")]
#[case::match_filtered_feed(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/match") as server
    replies: Feed(http::Response)
    discarded: Feed(Int)
    for req in server::requests:
        selected = `yes(req) if req.body() == "only" else `no
        match selected:
            case `yes(value):
                replies << http::ok_text(value.body())
            case `no:
                discarded << 0
    server::respond(replies)
"#}, "do not answer exactly its requests")]
#[case::connection_in_a_loop(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/loop") as server
    for unused in [0]:
        server::respond([http::ok_text(req.body()) for req in server::requests])
    0
"#}, "<<= must occur as a top-level statement")]
#[case::connection_in_a_transaction(indoc! {r#"
    import std::http
    run std::http::serve(port="{PORT}", method="POST", path="/transaction") as server
    with begin():
        server::respond([http::ok_text(req.body()) for req in server::requests])
    0
"#}, "<<= must occur as a top-level statement")]
fn typed_http_rejects_invalid_response_contracts(#[case] template: &str, #[case] needle: &str) {
    let code = template.replace("{PORT}", &reserve_test_port().to_string());
    let loaded = LoadedProgram::test(&code);
    let result = compile_program(&mut GlobalContext::default(), &loaded, Box::new(|| {}));
    let errors = match result {
        Ok(_) => panic!("invalid response contract compiled"),
        Err(e) => e,
    };
    let text = cambra::ccl::context::render_errors(&errors, loaded.sources());
    assert!(text.contains(needle), "expected {needle:?}: {text}");
}

#[test_log::test]
fn a_response_waits_for_its_complete_header_list() {
    use cambra::{
        ccl::Type,
        interpreter::{BaseType, Extent, Predicate, TestDataSource, Value},
    };
    use std::{cell::RefCell, rc::Rc};
    let control = Rc::new(RefCell::new(TestDataSource::new(
        "control",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/later") as server
        later = "seven" if sum(control()) == 7 else "other"
        server::respond([
            http::Response::new(202, box([
                http::Header::new("X-Later", later) for unused in [0]
            ]), req.body())
            for req in server::requests
        ])
    "#};
    let mut ctx = GlobalContext::default();
    ctx.register_source(control.clone());
    let loaded = LoadedProgram::test(&code);
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        tx.send(exchange(port, "/later", b"ready body", &[]))
            .unwrap();
    });
    let source = ctx
        .conversion_ctx()
        .get_source(&cambra::ccl::lower::http_requests_source_name(
            port, "POST", "/later",
        ))
        .unwrap();
    let admission_deadline = Instant::now() + Duration::from_secs(5);
    while !source
        .borrow()
        .get_yield_predicate()
        .contains_path(&[Value::UInt(0)])
    {
        ctx.scheduler().check_for_notifications();
        assert!(
            Instant::now() < admission_deadline,
            "the request was not admitted"
        );
        thread::sleep(Duration::from_millis(2));
    }
    let deadline = Instant::now() + Duration::from_millis(150);
    while Instant::now() < deadline {
        ctx.scheduler().check_for_notifications();
        assert!(
            rx.try_recv().is_err(),
            "response sent before its headers completed"
        );
        thread::sleep(Duration::from_millis(5));
    }
    control
        .borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(7))]);
    control.borrow_mut().set_yield_predicate(Predicate::True);
    let reply = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(reply.status, 202);
    assert_eq!(reply.body, "ready body");
    assert!(
        reply
            .headers
            .iter()
            .any(|(n, v)| n.eq_ignore_ascii_case("X-Later") && v == "seven")
    );
}

#[test_log::test]
fn invalid_response_headers_fail_one_request_and_leave_the_route_usable() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/headers") as server
        server::respond([
            http::Response::new(200, box([
                http::Header::new("X-Echo", req.body()) for unused in [0]
            ]), "body")
            for req in server::requests
        ])
    "#};
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(&code);
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let bad = exchange(port, "/headers", b"unsafe\r\nX-Injected: yes", &[]);
        let good = exchange(port, "/headers", b"valid", &[]);
        tx.send((bad, good)).unwrap();
    });
    let (bad, good) = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(bad.status, 500);
    assert!(
        !bad.headers
            .iter()
            .any(|(n, _)| n.eq_ignore_ascii_case("X-Injected"))
    );
    assert_eq!(good.status, 200);
    assert_eq!(good.body, "body");
    assert!(
        good.headers
            .iter()
            .any(|(n, v)| n.eq_ignore_ascii_case("X-Echo") && v == "valid")
    );
}

#[rstest]
#[case::no_content(204, "", 204)]
#[case::not_modified(304, "", 304)]
#[case::no_content_with_body(204, "body", 500)]
#[case::not_modified_with_body(304, "body", 500)]
fn status_and_body_are_validated_on_the_wire(
    #[case] status: i64,
    #[case] body: &str,
    #[case] expected: u16,
) {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/status") as server
        server::respond([http::Response::new({status}, box([]), "{body}") for req in server::requests])
    "#};
    let loaded = LoadedProgram::test(&code);
    let mut ctx = GlobalContext::default();
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || tx.send(exchange(port, "/status", b"", &[])).unwrap());
    let reply = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(reply.status, expected);
    if matches!(expected, 204 | 304) {
        assert!(reply.body.is_empty());
        assert!(
            !reply
                .headers
                .iter()
                .any(|(name, _)| name.eq_ignore_ascii_case("Content-Length")
                    || name.eq_ignore_ascii_case("Transfer-Encoding"))
        );
    }
}

#[rstest]
#[case("Content-Length")]
#[case("Transfer-Encoding")]
#[case("Connection")]
#[case("Keep-Alive")]
#[case("TE")]
#[case("Proxy-Connection")]
fn framing_headers_fail_one_request_and_leave_the_route_usable(#[case] forbidden: &'static str) {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/headers") as server
        server::respond([http::Response::new(200, box([
            http::Header::new(req.body(), "managed") for unused in [0]
        ]), "ok") for req in server::requests])
    "#};
    let loaded = LoadedProgram::test(&code);
    let mut ctx = GlobalContext::default();
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let invalid = exchange(port, "/headers", forbidden.as_bytes(), &[]);
        let valid = exchange(port, "/headers", b"X-Safe", &[]);
        tx.send((invalid, valid)).unwrap();
    });
    let (invalid, valid) = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(invalid.status, 500);
    assert_eq!(valid.status, 200);
    assert_eq!(valid.body, "ok");
}

#[test]
fn methods_are_case_sensitive_and_trailing_slashes_distinguish_routes() {
    let port = reserve_test_port();
    let code = formatdoc! {r#"
        import std::http
        run std::http::serve(port="{port}", method="POST", path="/ping") as plain
        run std::http::serve(port="{port}", method="POST", path="/ping/") as slash
        plain::respond([http::ok_text("plain") for req in plain::requests])
        slash::respond([http::ok_text("slash") for req in slash::requests])
    "#};
    let loaded = LoadedProgram::test(&code);
    let mut ctx = GlobalContext::default();
    let _compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_render(&loaded);
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let wrong = exchange_method(port, "post", "/ping", b"", &[]);
        let plain = exchange(port, "/ping", b"", &[]);
        let slash = exchange(port, "/ping/", b"", &[]);
        tx.send((wrong, plain, slash)).unwrap();
    });
    let (wrong, plain, slash) = drive_until(&mut ctx, &rx, Duration::from_secs(5));
    assert_eq!(wrong.status, 404);
    assert_eq!(plain.body, "plain");
    assert_eq!(slash.body, "slash");
}

#[rstest]
#[case(199)]
#[case(600)]
#[case(-1)]
fn response_status_literals_must_be_final_statuses(#[case] status: i64) {
    let code = formatdoc! {r#"
        import std::http
        http::Response::new({status}, box([]), "")
    "#};
    let loaded = LoadedProgram::test(&code);
    let Err(errors) = cambra::ccl::context::compile_to(&loaded, cambra::ccl::context::Phase::Infer)
    else {
        panic!("invalid status compiled");
    };
    let text = cambra::ccl::context::render_errors(&errors, loaded.sources());
    assert!(
        text.contains("expected {Int where _ >= 200 and _ <= 599}"),
        "{text}"
    );
}

#[test]
fn a_top_level_helper_can_connect_a_route() {
    let loaded = LoadedProgram::test(indoc! {r#"
        import std::http
        run std::http::serve(port="0", method="POST", path="/function") as server
        def connect():
            server::respond([http::ok_text(req.body()) for req in server::requests])
        connect()
    "#});
    cambra::ccl::context::compile_to(&loaded, cambra::ccl::context::Phase::Channelize)
        .unwrap_or_render(&loaded);
}

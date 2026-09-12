//! `wasm_serve`: an address a program serves through its embedding host.
//!
//! The construct is `http_serve`'s shape minus the port — the page is the
//! listener, so there is nothing to bind — and the tests below are the four
//! claims that makes: a route is a request/response pair of host channels
//! declared under one name, `wasm_serve` binds that pair by destructuring a
//! 2-tuple, its arguments are compile-time constants, and rows cross as the
//! record types the declarations give them rather than as bodies anything
//! parses. Design: `src/interpreter/design-host-channels.md`, "Routes".
//!
//! The fifth claim — that all of this exists on a target with no sockets — is
//! the reason the construct is not `http_serve` with a default port, and no test
//! here can make it: a `wasm32` test would have to run on a target the suite
//! does not build. `./ci.sh wasm` type-checks the library for that target
//! instead, and what it gates is that nothing on this path reaches for a socket
//! or a thread.
//!
//! Driven through [`Host`] rather than by pulling producers, because a route is
//! a host-facing construct and `Host::request` is the call a page makes.

use cambra::ccl::channels::{ChannelDecl, ChannelError};
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::embed::Host;
use cambra::interpreter::{Consumer, Value};
use indoc::indoc;

/// Both halves of one route, as a host declares them.
fn route(method: &str, path: &str, request: &str, response: &str) -> Vec<ChannelDecl> {
    vec![
        ChannelDecl::request(method, path, request),
        ChannelDecl::response(method, path, response),
    ]
}

/// The route `POST /echo` carries `{n: Int}` in and `{n: Int, doubled: Int}` out.
fn echo_route() -> Vec<ChannelDecl> {
    route("POST", "/echo", "{n: Int}", "{n: Int, doubled: Int}")
}

fn int_row(fields: &[(&str, i64)]) -> Value {
    Value::Record(
        fields
            .iter()
            .map(|(name, value)| ((*name).to_string(), Value::Int(*value)))
            .collect(),
    )
}

/// Tick until a sink answers, and return what every sink produced.
///
/// A reader fires a tick or more after the write it reads, so a host that ticks
/// once per call and looks immediately sees nothing. Eight is the bound
/// `tests/embed.rs` drives the same shape with.
fn settle(host: &mut Host) -> Vec<(String, Vec<Value>)> {
    for _ in 0..8 {
        let outputs = host.tick().outputs;
        if !outputs.is_empty() {
            return outputs;
        }
    }
    Vec::new()
}

/// Compile `code` against `decls` and render the rejection.
///
/// The declarations are expected to be well formed: a test that means to reject
/// a declaration asserts on [`GlobalContext::register_channels`] directly, so a
/// rejection reaching here is the program's.
fn rejection(code: &str, decls: &[ChannelDecl]) -> String {
    let mut ctx = GlobalContext::default();
    ctx.register_channels(decls)
        .expect("the declarations are well formed");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errors = compile_program(&mut ctx, code, consumer)
        .err()
        .expect("the program is rejected");
    format!("{errors:?}")
}

/// A call goes in as a record and its reply comes out as a record.
///
/// Nothing in the program parses a body or renders one: `r.n` is a field of the
/// declared request type, and the reply is the record the feed writes. That is
/// the difference from `http_serve`, whose replies are strings by construction.
#[test]
fn a_route_carries_a_call_in_and_its_reply_out() {
    let code = indoc! {r#"
        echo_reqs, echo_replies = wasm_serve("POST", "/echo")

        for r in echo_reqs:
            echo_replies << (n=r.n, doubled=r.n * 2)
    "#};
    let mut host = Host::compile("echo.cambra", code, &echo_route()).expect("the program embeds");

    host.request("POST", "/echo", [int_row(&[("n", 21)])])
        .expect("a declared route");
    let outputs = settle(&mut host);

    assert_eq!(
        outputs,
        vec![(
            "POST /echo".to_string(),
            vec![int_row(&[("n", 21), ("doubled", 42)])]
        )],
        "the reply leaves under the route's own name, as the record the feed wrote"
    );
}

/// Two routes over one transactional store: the address is the unit, not the
/// program.
///
/// The cross-route read is what a pair of endpoints is for — `POST /set` commits
/// and `GET /latest` reads what committed — and it is the shape
/// `tests/programs/http_counter` demonstrates over sockets.
#[test]
fn two_routes_share_one_transactional_store() {
    let code = indoc! {r#"
        set_reqs, set_acks = wasm_serve("POST", "/set")
        get_reqs, get_replies = wasm_serve("GET", "/latest")

        latest: Mut(Int, Txn) := 0

        for s in set_reqs:
            with begin():
                latest := s.n
            set_acks << (ok=True, n=s.n)

        for g in get_reqs:
            with begin():
                get_replies << (n=latest, doubled=latest * 2)
    "#};
    let decls: Vec<ChannelDecl> = route("POST", "/set", "{n: Int}", "{ok: Bool, n: Int}")
        .into_iter()
        .chain(route(
            "GET",
            "/latest",
            "{ask: Bool}",
            "{n: Int, doubled: Int}",
        ))
        .collect();
    let mut host = Host::compile("counter.cambra", code, &decls).expect("the program embeds");

    host.request("POST", "/set", [int_row(&[("n", 7)])])
        .expect("a declared route");
    settle(&mut host);

    host.request(
        "GET",
        "/latest",
        [Value::Record(
            [("ask".to_string(), Value::Bool(true))]
                .into_iter()
                .collect(),
        )],
    )
    .expect("a declared route");
    let outputs = settle(&mut host);

    assert_eq!(
        outputs
            .iter()
            .find(|(name, _)| name == "GET /latest")
            .map(|(_, rows)| rows.clone()),
        Some(vec![int_row(&[("n", 7), ("doubled", 14)])]),
        "the read endpoint serves what the write endpoint committed"
    );
}

/// A route is two declarations under one name, and both halves are registered.
///
/// The name is the route spelled as a request line, so the declaration reads as
/// the address it serves and a host needs no second table to pair the halves.
#[test]
fn a_route_registers_both_halves_under_the_address() {
    let mut ctx = GlobalContext::default();
    let channels = ctx
        .register_channels(&echo_route())
        .expect("a request and a response under one name are a route");

    assert!(
        channels.route("POST", "/echo").is_some(),
        "the pair is reachable by method and path"
    );
    assert!(
        channels.source("POST /echo").is_some() && channels.sink("POST /echo").is_some(),
        "both halves are ordinary channels, so a host drives them by name too"
    );
}

/// A half-declared route is rejected where it is declared.
///
/// A request with no response is an address whose callers never hear back, and a
/// response with no request is a reply channel nothing can trigger. Both are the
/// host's mistake, so neither waits for a `wasm_serve` to name the route.
#[test]
fn a_route_missing_a_half_is_rejected() {
    let missing = |decls: &[ChannelDecl]| {
        GlobalContext::default()
            .register_channels(decls)
            .err()
            .expect("a half-declared route is rejected")
    };

    assert_eq!(
        missing(&[ChannelDecl::request("POST", "/echo", "{n: Int}")]),
        ChannelError::HalfRoute {
            route: "POST /echo".to_string(),
            missing: "response",
        }
    );
    assert_eq!(
        missing(&[ChannelDecl::response("POST", "/echo", "{n: Int}")]),
        ChannelError::HalfRoute {
            route: "POST /echo".to_string(),
            missing: "request",
        }
    );
}

/// A route is the only reason two declarations share a name.
///
/// The relaxation is not "names may repeat": a `source` and a `sink` spelled the
/// same are still two channels a host believes are one, and two requests under
/// one name are two readers of one address with nothing deciding which reply
/// answers a call.
#[test]
fn only_a_route_may_declare_one_name_twice() {
    let duplicate = |decls: &[ChannelDecl]| {
        GlobalContext::default()
            .register_channels(decls)
            .err()
            .expect("a repeated name is rejected")
    };

    assert_eq!(
        duplicate(&[
            ChannelDecl::source("prices", "Int"),
            ChannelDecl::sink("prices", "Int"),
        ]),
        ChannelError::DuplicateName("prices".to_string())
    );
    assert_eq!(
        duplicate(&[
            ChannelDecl::request("POST", "/echo", "{n: Int}"),
            ChannelDecl::request("POST", "/echo", "{n: Int}"),
            ChannelDecl::response("POST", "/echo", "{n: Int}"),
        ]),
        ChannelError::DuplicateName("POST /echo".to_string())
    );
    assert_eq!(
        duplicate(&[
            ChannelDecl::request("POST", "/echo", "{n: Int}"),
            ChannelDecl::sink("POST /echo", "Int"),
        ]),
        ChannelError::DuplicateName("POST /echo".to_string())
    );
}

/// The arguments are compile-time constants, as `http_serve`'s are.
///
/// An address is the identity of a route: lowering binds one while the program
/// is still a tree, before there is a value to compute an address from. A
/// program computing one is refused by name rather than falling through to
/// "`wasm_serve` is unbound", which would describe the recognizer instead of the
/// program.
#[test]
fn a_route_address_is_a_compile_time_constant() {
    let code = indoc! {r#"
        path = "/echo"
        echo_reqs, echo_replies = wasm_serve("POST", path)

        for r in echo_reqs:
            echo_replies << (n=r.n, doubled=r.n * 2)
    "#};
    let rendered = rejection(code, &echo_route());
    assert!(
        rendered.contains("compile-time constants"),
        "the rejection names the rule; got: {rendered}"
    );
}

/// A route the host never declared is an address nothing can reach.
///
/// Refused at the statement that names the address, which is where a host can
/// act on it, rather than at a bind that would fail once the page has already
/// loaded the module.
#[test]
fn serving_an_undeclared_route_is_rejected() {
    let code = indoc! {r#"
        reqs, replies = wasm_serve("POST", "/nope")

        for r in reqs:
            replies << (n=r.n, doubled=r.n * 2)
    "#};
    let rendered = rejection(code, &echo_route());
    assert!(
        rendered.contains("POST /nope"),
        "the rejection names the address; got: {rendered}"
    );
}

/// One address is served once.
///
/// Two `wasm_serve` calls on one route would give it two request readers and two
/// reply writers, with nothing deciding which reply answers a call.
#[test]
fn a_route_may_be_served_only_once() {
    let code = indoc! {r#"
        first_reqs, first_replies = wasm_serve("POST", "/echo")
        second_reqs, second_replies = wasm_serve("POST", "/echo")

        for r in first_reqs:
            first_replies << (n=r.n, doubled=r.n * 2)

        for r in second_reqs:
            second_replies << (n=r.n, doubled=r.n * 2)
    "#};
    let rendered = rejection(code, &echo_route());
    assert!(
        rendered.contains("duplicate wasm_serve registration"),
        "the rejection names the repeat; got: {rendered}"
    );
}

/// A `wasm_serve` is a top-level statement.
///
/// The same rule `http_serve` has, for the same reason: the statement binds a
/// route for the whole program, and a route bound on one arm of a conditional
/// would be an address whose existence depends on a value.
#[test]
fn a_route_is_bound_at_the_top_level() {
    let code = indoc! {r#"
        flag = True
        if flag:
            echo_reqs, echo_replies = wasm_serve("POST", "/echo")
            1
        else:
            2
    "#};
    let rendered = rejection(code, &echo_route());
    assert!(
        rendered.contains("wasm_serve is only supported at the top level"),
        "the rejection names the rule; got: {rendered}"
    );
}

/// A declared route the program does not serve leaves nothing behind.
///
/// A route's reply sink is bound by the `wasm_serve` that names it, not by a
/// `Defer` wrapped around the program, so an address this version stopped
/// serving is not an unfed sink. A host-declared `sink` the program never feeds
/// still is.
#[test]
fn a_declared_route_the_program_ignores_is_not_an_unfed_sink() {
    let code = indoc! {r#"
        echo_reqs, echo_replies = wasm_serve("POST", "/echo")

        for r in echo_reqs:
            echo_replies << (n=r.n, doubled=r.n * 2)
    "#};
    let decls: Vec<ChannelDecl> = echo_route()
        .into_iter()
        .chain(route("GET", "/unused", "{ask: Bool}", "{n: Int}"))
        .collect();

    Host::compile("echo.cambra", code, &decls)
        .expect("an address this version does not serve is not an error");
}

//! `wasm_socket_subscribe`: a source an embedding host fills from a socket.
//!
//! The construct is the source half of what `wasm_serve` binds: a feed has
//! nothing to reply to, so it is a plain `=` over a single name rather than a
//! tuple destructure. The tests below are the four claims that makes. A
//! subscription binds a source the host declared, rows pushed into it arrive as
//! the record type its declaration gives them, the arguments are compile-time
//! constants — the products being a list of them — and the host reads the
//! subscription back, which is what the arguments are for. Design:
//! `src/interpreter/design-host-channels.md`, "Sockets".
//!
//! The claim no test here can make is the one the construct exists for: that
//! all of this compiles on a target with no sockets. A `wasm32` test would have
//! to run on a target the suite does not build, so `./ci.sh wasm` type-checks
//! the library for it instead, and what it gates is that nothing on this path
//! reaches for `tungstenite` or a thread.
//!
//! Driven through [`Host`] rather than by pulling producers, because the host
//! owns the socket: `Host::socket_subscriptions` is what it connects from, and
//! `Host::push` is what it does with what comes back.

use cambra::ccl::channels::ChannelDecl;
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::embed::Host;
use cambra::interpreter::{Consumer, Value};
use indoc::indoc;

/// The feed `v1.cambra` reads, and the sink a test watches it through.
///
/// The row type is the demo's: a bare ticker and a price scaled by 10⁸. The
/// host decodes a quote into that shape before pushing it, which is the reason
/// nothing in any program below parses JSON or splits a string.
fn feed_channels() -> Vec<ChannelDecl> {
    vec![
        ChannelDecl::source("ticker_updates", "{ticker: String, price: Int}"),
        ChannelDecl::sink("quotes", "{ticker: String, price: Int}"),
    ]
}

/// The subscription every program below writes, as source text.
const SUBSCRIBE: &str = indoc! {r#"
    ticker_updates = wasm_socket_subscribe(
        "wss://ws-feed.exchange.coinbase.com",
        "ticker_batch",
        ["BTC-USD", "ETH-USD", "SOL-USD"],
    )
"#};

fn quote(ticker: &str, price: i64) -> Value {
    Value::Record(
        [
            ("ticker".to_string(), Value::String(ticker.into())),
            ("price".to_string(), Value::Int(price)),
        ]
        .into_iter()
        .collect(),
    )
}

/// Tick until a sink answers, and return what every sink produced.
///
/// A reader fires a tick or more after the write it reads, so a host that ticks
/// once per push and looks immediately sees nothing. Eight is the bound
/// `tests/wasm_serve.rs` drives the same shape with.
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

/// The rows the host pushes arrive on the name the subscription binds.
///
/// The statement binds the declared source, so `for u in ticker_updates:` reads
/// the feed the host is filling, and `u.price` is a field of the declared row
/// rather than something the program parsed out of a message.
#[test]
fn a_subscribed_source_carries_the_hosts_rows_into_the_program() {
    let code = format!(
        "{SUBSCRIBE}\n{}",
        indoc! {r#"
            for u in ticker_updates:
                quotes << (ticker=u.ticker, price=u.price)
        "#}
    );
    let mut host =
        Host::compile("feed.cambra", &code, &feed_channels()).expect("the program embeds");

    host.push("ticker_updates", [quote("BTC", 8_169_291_000_000)])
        .expect("a declared source");
    let outputs = settle(&mut host);

    assert_eq!(
        outputs,
        vec![("quotes".to_string(), vec![quote("BTC", 8_169_291_000_000)])],
        "the row the host decoded off the socket reaches the program as a row"
    );
}

/// The host reads back what to connect to.
///
/// The source is found by the name the statement binds, so unlike a route's
/// method and path the arguments are not a lookup key. Carrying them puts the
/// endpoint in the program instead of in a page that has to be kept in step
/// with it, and the host reads them before the first tick, which is why they
/// cannot be computed.
#[test]
fn the_host_reads_back_the_subscription_it_must_make() {
    let code = format!(
        "{SUBSCRIBE}\n{}",
        indoc! {r#"
            for u in ticker_updates:
                quotes << (ticker=u.ticker, price=u.price)
        "#}
    );
    let host = Host::compile("feed.cambra", &code, &feed_channels()).expect("the program embeds");

    let subscriptions = host.socket_subscriptions();
    assert_eq!(subscriptions.len(), 1, "one feed, one subscription");
    let subscription = &subscriptions[0];
    assert_eq!(
        (
            subscription.source.as_str(),
            subscription.endpoint.as_str(),
            subscription.feed.as_str()
        ),
        (
            "ticker_updates",
            "wss://ws-feed.exchange.coinbase.com",
            "ticker_batch"
        )
    );
    assert_eq!(
        subscription.products,
        ["BTC-USD", "ETH-USD", "SOL-USD"],
        "the products the host names in the subscription it sends, in the \
         endpoint's own spelling"
    );
}

/// A subscribed source is an ordinary host source, and the host drives it as
/// one.
///
/// Nothing about the declaration says "socket": the host declares a `source`,
/// the program says what fills it, and the rows arrive through the same buffer
/// a pushed source uses. That is what lets a recorded slice replay into the
/// feed offline with no second path through the program.
#[test]
fn a_subscribed_source_is_an_ordinary_declared_source() {
    let mut ctx = GlobalContext::default();
    let channels = ctx
        .register_channels(&feed_channels())
        .expect("the declarations are well formed");

    assert!(
        channels.source("ticker_updates").is_some(),
        "the feed is reachable by name, as any source is"
    );
}

/// The feed's rows commit into a transactional store, which is what a price
/// feed is for.
///
/// `v1.cambra`'s shape: the socket's rows are the only writer of `prices`, and
/// a reader reads what committed. The subscription changes nothing about that —
/// a write inside `with begin():` is a write inside `with begin():` whether the
/// row arrived from a socket, a terminal or a replayed slice.
#[test]
fn a_subscribed_feed_writes_a_transactional_store() {
    let code = format!(
        "{SUBSCRIBE}\n{}",
        indoc! {r#"
            prices: Mut(Map(String, Int), Txn) := empty_map()

            for u in ticker_updates:
                with begin():
                    prices[u.ticker] := u.price

            quote_reqs, quote_replies = wasm_serve("GET", "/price")

            for q in quote_reqs:
                with begin():
                    quote_replies << (ticker=q.ticker, price=prices[q.ticker])
        "#}
    );
    let decls = [
        ChannelDecl::source("ticker_updates", "{ticker: String, price: Int}"),
        // Not `feed_channels()`: this program answers through the route rather
        // than the `quotes` sink, and a declared sink the program never feeds is
        // rejected at lowering, as any unfed sink is.
        ChannelDecl::request("GET", "/price", "{ticker: String}"),
        ChannelDecl::response("GET", "/price", "{ticker: String, price: Int}"),
    ];
    let mut host = Host::compile("feed.cambra", &code, &decls).expect("the program embeds");

    host.push("ticker_updates", [quote("BTC", 8_169_291_000_000)])
        .expect("a declared source");
    settle(&mut host);

    host.request(
        "GET",
        "/price",
        [Value::Record(
            [("ticker".to_string(), Value::String("BTC".into()))]
                .into_iter()
                .collect(),
        )],
    )
    .expect("a declared route");
    let outputs = settle(&mut host);

    assert_eq!(
        outputs
            .iter()
            .find(|(name, _)| name == "GET /price")
            .map(|(_, rows)| rows.clone()),
        Some(vec![quote("BTC", 8_169_291_000_000)]),
        "the route serves the quote the feed committed"
    );
}

/// The arguments are compile-time constants, as `wasm_serve`'s are.
///
/// A host reads the subscription off the compiled program before it has ticked
/// it once, so there is no value in the program to have computed one from. A
/// program computing an endpoint is refused by name rather than falling through
/// to "`wasm_socket_subscribe` is unbound", which would describe the recogniser
/// instead of the program.
#[test]
fn a_subscription_is_a_compile_time_constant() {
    let code = indoc! {r#"
        endpoint = "wss://ws-feed.exchange.coinbase.com"
        ticker_updates = wasm_socket_subscribe(endpoint, "ticker_batch", ["BTC-USD"])

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("compile-time constants") && rendered.contains("the endpoint"),
        "the rejection names the rule and which argument broke it; got: {rendered}"
    );
}

/// The products are a list of constants, and both halves of that are checked.
///
/// The list itself is a literal — a comprehension over one would be a computed
/// subscription, and reading it would mean running it during lowering — and so
/// is every product in it.
#[test]
fn the_products_are_a_list_of_constants() {
    let computed_item = indoc! {r#"
        sol = "SOL-USD"
        ticker_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", ["BTC-USD", sol]
        )

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(computed_item, &feed_channels());
    assert!(
        rendered.contains("compile-time constants") && rendered.contains("each product"),
        "the rejection names the rule; got: {rendered}"
    );

    let not_a_list = indoc! {r#"
        ticker_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", "BTC-USD"
        )

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(not_a_list, &feed_channels());
    assert!(
        rendered.contains("list literal"),
        "the rejection says what the third argument is; got: {rendered}"
    );
}

/// A subscription with no products asks for nothing.
///
/// The source it binds would be one the host can never fill, and every read of
/// it would wait forever on a feed behaving exactly as written — so it is
/// refused where the empty list is, rather than diagnosed later as a quiet
/// program.
#[test]
fn a_subscription_names_at_least_one_product() {
    let code = indoc! {r#"
        ticker_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", []
        )

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("subscribes to nothing"),
        "the rejection says what an empty subscription is; got: {rendered}"
    );
}

/// A source the host never declared is a feed nothing can fill.
///
/// The rows come from the host, so the name has to be one the host knows: it
/// declares the source and the row type, and the program says what fills it.
/// Refused at the statement that names it, which is where a host can act on it.
#[test]
fn subscribing_an_undeclared_source_is_rejected() {
    let code = indoc! {r#"
        book_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "level2", ["BTC-USD"]
        )

        for u in book_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("book_updates"),
        "the rejection names the source; got: {rendered}"
    );
}

/// One source is filled by one subscription.
///
/// Two of them on one name would be two sockets pushing into one buffer with
/// nothing saying which rows the program is reading — and, since the statement
/// binds the source, the second would shadow the first while its socket stayed
/// connected.
#[test]
fn a_source_is_subscribed_once() {
    let code = indoc! {r#"
        ticker_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", ["BTC-USD"]
        )
        ticker_updates = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", ["ETH-USD"]
        )

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("duplicate wasm_socket_subscribe registration"),
        "the rejection names the repeat; got: {rendered}"
    );
}

/// A subscription binds one name, not a pair.
///
/// This is where it parts company with `wasm_serve`, which binds the calls and
/// the channel their replies leave by. A feed has nothing to reply to, so a
/// tuple target has no reading — and saying that beats "the name is unbound",
/// which would describe the recogniser.
#[test]
fn a_subscription_binds_one_name() {
    let code = indoc! {r#"
        ticker_updates, acks = wasm_socket_subscribe(
            "wss://ws-feed.exchange.coinbase.com", "ticker_batch", ["BTC-USD"]
        )

        for u in ticker_updates:
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("binds one source"),
        "the rejection names the rule; got: {rendered}"
    );
}

/// A subscription is a top-level statement.
///
/// The same rule `wasm_serve` has, for the same reason: the statement says
/// where a source's rows come from for the whole program, and one made on a
/// branch would be a socket whose existence depends on a value.
#[test]
fn a_subscription_is_bound_at_the_top_level() {
    let code = indoc! {r#"
        flag = True
        if flag:
            ticker_updates = wasm_socket_subscribe(
                "wss://ws-feed.exchange.coinbase.com", "ticker_batch", ["BTC-USD"]
            )
            1
        else:
            2
    "#};
    let rendered = rejection(code, &feed_channels());
    assert!(
        rendered.contains("wasm_socket_subscribe is only supported at the top level"),
        "the rejection names the rule; got: {rendered}"
    );
}

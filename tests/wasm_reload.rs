//! `Program.reload`: swapping a running program's source from the page that
//! embeds it.
//!
//! The page has no control port — `tiny_http` does not exist on `wasm32` — so
//! the reload the binary answers over `/reload` reaches a browser tab through
//! [`Host::reload`], which `src/wasm_api.rs` renders as one JSON string. The
//! tests below are the four claims that binding makes. An accepted version keeps
//! the state the running one holds and reports how much of its graph it kept, a
//! rejected one leaves the program serving, the generation counts the accepted
//! ones so a reader can tell which version a frame describes, and the
//! subscriptions are the running version's rather than the first version's.
//!
//! The claim no test here can make is the JSON: a `wasm32` test would have to
//! run on a target the suite does not build, so `scripts/wasm-contract.mjs`
//! makes it against the built module under `./ci.sh wasm` — the field names, the
//! throw, and that the page's own state survives an edit.
//!
//! What a reload may change and what it carries is `tests/hot_reload.rs`, over
//! the whole guard table. These are about what an embedding host reads back from
//! one.

use cambra::ccl::channels::ChannelDecl;
use cambra::embed::Host;
use cambra::interpreter::Value;
use indoc::indoc;

/// A cart whose quantity accumulates, read through a route.
///
/// The smallest program that can tell a carried value from a recomputed one:
/// `qty` is the only state, the source is the only thing that writes it, and the
/// route reads it without adding any of its own.
const CART: &str = indoc! {r#"
    qty: Mut(Int, Txn) := 0

    for c in cart_changes():
        with begin():
            qty := qty + c.qty

    view_reqs, view_replies = wasm_serve("GET", "/cart")

    for req in view_reqs:
        with begin():
            view_replies << (qty=qty)
"#};

/// [`CART`] with the accumulating loop edited, which is the edit a reload
/// carries a value across: the store is rebuilt and `qty` resumes from what the
/// replaced version left it holding, so the new rule governs from the swap
/// onwards without discarding what came before.
const CART_DOUBLING: &str = indoc! {r#"
    qty: Mut(Int, Txn) := 0

    for c in cart_changes():
        with begin():
            qty := qty + c.qty * 2

    view_reqs, view_replies = wasm_serve("GET", "/cart")

    for req in view_reqs:
        with begin():
            view_replies << (qty=qty)
"#};

/// A program reading a feed the page fills, with the products left to
/// [`feed`] to substitute — the one thing a version of it varies by.
const FEED: &str = indoc! {r#"
    ticker_updates = wasm_socket_subscribe(
        "wss://ws-feed.exchange.coinbase.com",
        "ticker_batch",
        {PRODUCTS},
    )

    for u in ticker_updates:
        quotes << (ticker=u.ticker, price=u.price)
"#};

/// [`FEED`] subscribed to `products`, written as the list literal a
/// subscription takes.
fn feed(products: &str) -> String {
    FEED.replace("{PRODUCTS}", products)
}

/// The channels [`CART`] is compiled against.
fn cart_channels() -> Vec<ChannelDecl> {
    vec![
        ChannelDecl::source("cart_changes", "{qty: Int}"),
        ChannelDecl::request("GET", "/cart", "{ack: Bool}"),
        ChannelDecl::response("GET", "/cart", "{qty: Int}"),
    ]
}

fn int_row(field: &str, value: i64) -> Value {
    Value::Record(
        [(field.to_string(), Value::Int(value))]
            .into_iter()
            .collect(),
    )
}

/// The one-field record a call against `GET /cart` carries.
fn ack() -> Value {
    Value::Record(
        [("ack".to_string(), Value::Bool(true))]
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

/// Add `qty` to the cart.
fn change(host: &mut Host, qty: i64) {
    host.push("cart_changes", [int_row("qty", qty)])
        .expect("a declared source");
    settle(host);
}

/// What the route answers the cart is now.
fn view(host: &mut Host) -> i64 {
    host.request("GET", "/cart", [ack()])
        .expect("a declared route");
    let outputs = settle(host);
    let (_, rows) = outputs
        .iter()
        .find(|(name, _)| name == "GET /cart")
        .expect("the route answers");
    match &rows[0] {
        Value::Record(fields) => match fields.get("qty") {
            Some(Value::Int(qty)) => *qty,
            other => panic!("the reply carries an Int quantity, got {other:?}"),
        },
        other => panic!("the reply is a record, got {other:?}"),
    }
}

/// A reload carries the value the running version holds, and says how much of
/// its graph it kept.
///
/// Four numbers the cart could read, and one of them is a carried value. `8` is
/// the store resuming at the `2` it held and folding the new row under the
/// edited rule. `6` would be a version that started from its init, `5` the rule
/// before the edit, and `10` a second program fed both rows again — which is
/// what swapping versions by replaying a journal of pushed rows produces.
/// `kept` counts the operators behind the `8`: the ones taken from the replaced
/// version rather than built.
#[test]
fn a_reload_carries_the_value_the_running_version_holds() {
    let mut host =
        Host::compile("cart.cambra", CART, &cart_channels()).expect("the program embeds");

    change(&mut host, 2);
    assert_eq!(view(&mut host), 2, "the cart holds what was added");

    let report = host.reload(CART_DOUBLING).expect("an edit to a loop body");
    assert!(
        report.reuse.kept > 0 && report.reuse.kept < report.reuse.bound,
        "the version keeps what it can and rebuilds the loop that changed, got {}/{}",
        report.reuse.kept,
        report.reuse.bound,
    );

    change(&mut host, 3);
    assert_eq!(
        view(&mut host),
        8,
        "the store resumes at the value it held and the new rule governs from here",
    );
}

/// A version identical to the running one keeps every operator.
///
/// The tally's upper end, and what makes the number readable: `kept` short of
/// `bound` is the graph the edit reached, so a reload that edits nothing has to
/// reach nothing.
#[test]
fn a_version_that_changes_nothing_keeps_every_operator() {
    let mut host =
        Host::compile("cart.cambra", CART, &cart_channels()).expect("the program embeds");
    change(&mut host, 2);

    let report = host.reload(CART).expect("the same source reloads");

    assert!(report.reuse.bound > 0, "the program binds operators");
    assert_eq!(
        report.reuse.kept, report.reuse.bound,
        "an unedited version rebuilds nothing",
    );
}

/// A version that does not compile leaves the running one serving, and the
/// diagnostics say what was wrong with it.
///
/// The behaviour a live edit depends on: the page reloads what is in its editor,
/// so a half-typed version is an ordinary event rather than an exceptional one.
/// The guard compiles the version and checks it against the state this one holds
/// before anything is torn down, so a refusal costs the program nothing.
#[test]
fn a_version_that_does_not_compile_leaves_the_program_serving() {
    let mut host =
        Host::compile("cart.cambra", CART, &cart_channels()).expect("the program embeds");
    change(&mut host, 2);

    let broken = CART.replace("qty + c.qty", "qty + c.nonesuch");
    let rejection = host
        .reload(&broken)
        .err()
        .expect("no row of the declared type has that field")
        .to_string();
    assert!(
        rejection.contains("nonesuch"),
        "the rejection names what it could not compile; got: {rejection}"
    );

    change(&mut host, 3);
    assert_eq!(
        view(&mut host),
        5,
        "the running version is still accumulating under its own rule",
    );
}

/// A version that cannot take over the state is refused the same way.
///
/// The second rejection a page meets, and the one an editor produces by
/// deleting a line: a version that stops declaring `qty` would leave the value
/// the running program has accumulated with nowhere to go. Reported rather than
/// performed, so the cart is still there to be read.
#[test]
fn a_version_that_drops_the_state_leaves_the_program_serving() {
    let mut host =
        Host::compile("cart.cambra", CART, &cart_channels()).expect("the program embeds");
    change(&mut host, 2);

    let stateless = indoc! {r#"
        view_reqs, view_replies = wasm_serve("GET", "/cart")

        for req in view_reqs:
            view_replies << (qty=0)
    "#};
    let rejection = host
        .reload(stateless)
        .err()
        .expect("the running program holds a value this version cannot seat")
        .to_string();
    assert!(
        rejection.contains("cannot take over state") && rejection.contains("`qty`"),
        "the rejection names the rule and the variable; got: {rejection}"
    );

    assert_eq!(view(&mut host), 2, "the cart the running version holds");
}

/// The generation counts accepted reloads, and a rejected one does not count.
///
/// What a reader holding a payload and a stream of frames compares. A reload
/// rebuilds the operators it could not keep and a rebuilt operator is minted a
/// fresh `NodeId`, so a frame from a later generation names nodes the payload
/// does not have — the number is how a page knows to re-read the payload rather
/// than draw them against panes describing another version.
#[test]
fn an_accepted_reload_advances_the_generation() {
    let mut host =
        Host::compile("cart.cambra", CART, &cart_channels()).expect("the program embeds");
    assert_eq!(host.generation(), 0, "the first version is generation 0");

    host.reload(CART_DOUBLING).expect("an edit to a loop body");
    assert_eq!(host.generation(), 1);

    host.reload(&CART.replace("qty + c.qty", "qty + c.nonesuch"))
        .err()
        .expect("a version that does not compile");
    assert_eq!(
        host.generation(),
        1,
        "a refused version is not a version anything is holding",
    );

    host.reload(CART).expect("a revert is a version too");
    assert_eq!(host.generation(), 2);

    let payload: serde_json::Value =
        serde_json::from_str(host.snapshot()).expect("the payload is valid JSON");
    assert_eq!(
        payload["meta"]["generation"], 2,
        "the payload describes the version now running",
    );
    change(&mut host, 1);
    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    assert_eq!(
        frame["generation"], 2,
        "a frame says which version produced it",
    );
}

/// The subscriptions are the running version's, so a reload replaces them.
///
/// The page owns the socket, and what it should be connected to is a claim the
/// running version makes. A version that asks for another product is a socket
/// the page resubscribes, and a version that stops reading the feed is one it
/// closes — which it can only do by reading the list back after the swap.
#[test]
fn a_reload_replaces_what_the_page_subscribes_to() {
    let channels = [
        ChannelDecl::source("ticker_updates", "{ticker: String, price: Int}"),
        ChannelDecl::source("manual_quotes", "{ticker: String, price: Int}"),
        ChannelDecl::sink("quotes", "{ticker: String, price: Int}"),
    ];
    let mut host = Host::compile("feed.cambra", &feed(r#"["BTC-USD"]"#), &channels)
        .expect("the program embeds");
    assert_eq!(
        host.socket_subscriptions()[0].products,
        ["BTC-USD"],
        "the first version's products"
    );

    host.reload(&feed(r#"["BTC-USD", "ETH-USD"]"#))
        .expect("a version may ask for another product");
    assert_eq!(
        host.socket_subscriptions()[0].products,
        ["BTC-USD", "ETH-USD"],
        "the running version's products, not the first version's",
    );

    // The same sink, filled from a source the page pushes by hand: a declared
    // sink no version feeds is refused at lowering, so dropping the feed means
    // moving what fills it rather than deleting the loop.
    let unsubscribed = indoc! {r#"
        for u in manual_quotes():
            quotes << (ticker=u.ticker, price=u.price)
    "#};
    host.reload(unsubscribed)
        .expect("a version may stop reading a feed");
    assert!(
        host.socket_subscriptions().is_empty(),
        "a feed that leaves the list is a socket the page closes",
    );
}

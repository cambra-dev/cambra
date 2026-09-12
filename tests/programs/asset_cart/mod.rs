//! A live asset cart over host channels: a filtered price stream, a quantity
//! per ticker, and a priced line per ticker — the demo program, at the rung
//! today's compiler runs.
//!
//! The program reads three host sources and feeds one host sink per ticker, all
//! declared in `channels.json` beside it. It is the gallery's first program
//! whose meaning depends on something the file does not contain, which is what
//! a component is: `price_updates` is a name the host binds, the way `stdin` is
//! a name the runtime binds.
//!
//! Driven the way a host drives — push, let the scheduler settle, drain — so
//! the assertions are over what the host would render.
//!
//! The subtotal is summed here rather than in the program, and the reader is
//! split one-per-ticker, for the reason `v0.cambra`'s TODO records: a block
//! reading all six slots costs about two seconds per price row. [`subtotal`] is
//! what the demo host does instead.
//!
//! # Why the program is shaped the way it is
//!
//! Three rules, each of which breaks it if violated. A write goes inside `with
//! begin():`, and a reply from a loop that also writes never fires — so the
//! writer loops carry no feed. The reader's reads go inside its own block: a
//! transactional variable read outside one is rejected, and the read is live
//! rather than terminal because the block does not write. The filter key is a
//! literal, because a key taken from another stream is not a shape the planner
//! accepts.
//!
//! One ticker is one filter, one slot, one loop and one reader, three times
//! over. Naming the tickers once as data needs a join against a static list;
//! holding prices and quantities in one collection needs `Mut(Map(String, Int),
//! Txn)` and `for t -> q in cart`. Both are language work and neither changes
//! what the program means.
//!
//! Three readers over one source cannot feed one sink — their branches fail to
//! unify at post-channelize — which is why there is a sink per ticker rather
//! than three readers sharing `cart_view`.
//!
//! The program text stays short because the inspector renders it on a slide,
//! and a reader arriving at it should meet the program rather than a preamble —
//! which is why the rules above live here and not in a comment block above the
//! first line of the program.
//!
//! # The ladder above this rung
//!
//! `v1.cambra` is that ladder written down. `Mut(Map({AccountId, Ticker}, Int),
//! Txn)` replaces the six slots with three keyed collections, `for (a, t) -> q
//! in cart` collapses the three readers into one that serves the whole cart
//! (subtotal included), and three `wasm_serve` routes replace the three sources
//! and the sink per ticker — so the page calls `PATCH /cart`, `PUT /checkout`
//! and `GET /cart` instead of pushing rows at named channels. It does not
//! compile; [`asset_cart_v1_currently_blocked_on_entry_iteration`] is what it
//! waits on, and the file is here so the shape is reviewable while those
//! constructs are built.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::channels::{ChannelFile, ChannelKind};
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{Consumer, HostSink, HostSource, Value};

use super::common::expect_compile_error;

/// Dollars × 10⁸ — the scale every price crosses a channel in.
const SCALE: i64 = 100_000_000;

fn price(dollars: i64) -> i64 {
    dollars * SCALE
}

fn ticker_row(field: &str, ticker: &str, value: i64) -> Value {
    Value::Record(
        [
            ("ticker".to_string(), Value::String(ticker.into())),
            (field.to_string(), Value::Int(value)),
        ]
        .into_iter()
        .collect(),
    )
}

/// One ticker's line, as the host reads it off that ticker's sink.
#[derive(Debug, PartialEq, Eq)]
struct Line {
    qty: i64,
    price: i64,
    total: i64,
}

fn expect(qty: i64, price_paid: i64, total: i64) -> Line {
    Line {
        qty,
        price: price_paid,
        total,
    }
}

/// The cart, wired to the channels its own `channels.json` declares.
struct Cart {
    ctx: GlobalContext,
    price_updates: Rc<RefCell<HostSource>>,
    cart_changes: Rc<RefCell<HostSource>>,
    view_requests: Rc<RefCell<HostSource>>,
    lines: Vec<(&'static str, Rc<HostSink>)>,
}

impl Cart {
    fn compile() -> Self {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
        let program = std::path::Path::new(dir).join("v0.cambra");
        let source = std::fs::read_to_string(&program).expect("the program is readable");
        let declared = ChannelFile::beside(&program)
            .expect("the channel file parses")
            .expect("the program has a channel file");

        let mut ctx = GlobalContext::default();
        let channels = ctx
            .register_channels(&declared.channels)
            .expect("the declarations are well formed");
        let source_handle = |name: &str| {
            channels
                .source(name)
                .unwrap_or_else(|| panic!("'{name}' is a declared source"))
                .clone()
        };
        let sink_handle = |name: &str| {
            channels
                .sink(name)
                .unwrap_or_else(|| panic!("'{name}' is a declared sink"))
                .clone()
        };
        let cart = Self {
            price_updates: source_handle("price_updates"),
            cart_changes: source_handle("cart_changes"),
            view_requests: source_handle("view_requests"),
            lines: vec![
                ("BTC-USD", sink_handle("btc_line")),
                ("ETH-USD", sink_handle("eth_line")),
                ("SOL-USD", sink_handle("sol_line")),
            ],
            ctx,
        };

        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let mut ctx = cart.ctx;
        let _compiled =
            compile_program(&mut ctx, &source, consumer).unwrap_or_render("v0.cambra", &source);
        Self { ctx, ..cart }
    }

    fn quote(&mut self, ticker: &str, dollars: i64) {
        self.price_updates
            .borrow_mut()
            .push([ticker_row("price", ticker, price(dollars))]);
        self.ctx.scheduler().check_for_notifications();
    }

    fn set_quantity(&mut self, ticker: &str, qty: i64) {
        self.cart_changes
            .borrow_mut()
            .push([ticker_row("qty", ticker, qty)]);
        self.ctx.scheduler().check_for_notifications();
    }

    /// Ask for a view and collect the line each ticker served.
    fn view(&mut self) -> Vec<(&'static str, Line)> {
        self.view_requests.borrow_mut().push([Value::Bool(true)]);
        self.ctx.scheduler().check_for_notifications();
        self.lines
            .iter()
            .map(|(ticker, sink)| {
                let mut rows = sink.drain();
                assert_eq!(rows.len(), 1, "{ticker}: one view request serves one line");
                let Value::Record(fields) = rows.remove(0) else {
                    panic!("{ticker}: a line is a record");
                };
                let int = |name: &str| match fields.get(name) {
                    Some(Value::Int(v)) => *v,
                    other => panic!("{ticker}: '{name}' is an Int, got {other:?}"),
                };
                (
                    *ticker,
                    Line {
                        qty: int("qty"),
                        price: int("price"),
                        total: int("total"),
                    },
                )
            })
            .collect()
    }
}

/// The cart's subtotal, summed over the lines the program served.
///
/// The host's job rather than the program's, for the reason `v0.cambra`
/// records: a block reading every slot at once is what costs, and a subtotal is
/// exactly that read.
fn subtotal(view: &[(&str, Line)]) -> i64 {
    view.iter().map(|(_, line)| line.total).sum()
}

/// The line `ticker` served.
fn line<'a>(view: &'a [(&str, Line)], ticker: &str) -> &'a Line {
    view.iter()
        .find(|(t, _)| *t == ticker)
        .map(|(_, l)| l)
        .unwrap_or_else(|| panic!("the view carries a '{ticker}' line"))
}

/// The cart prices what the host pushed: quantity times the latest price, per
/// ticker.
#[test]
fn asset_cart_serves_the_cart_it_was_told_about() {
    let mut cart = Cart::compile();

    cart.quote("BTC-USD", 81_692);
    cart.quote("ETH-USD", 4_413);
    cart.quote("SOL-USD", 197);
    cart.set_quantity("BTC-USD", 2);
    cart.set_quantity("ETH-USD", 3);

    let view = cart.view();
    assert_eq!(
        line(&view, "BTC-USD"),
        &expect(2, price(81_692), price(163_384))
    );
    assert_eq!(
        line(&view, "ETH-USD"),
        &expect(3, price(4_413), price(13_239))
    );
    assert_eq!(
        line(&view, "SOL-USD"),
        &expect(0, price(197), 0),
        "a ticker with no quantity is priced and contributes nothing"
    );
    assert_eq!(subtotal(&view), price(163_384 + 13_239));
}

/// A price the program does not track moves nothing, which is what the ingest
/// filter is for: the host's feed carries more tickers than the program keeps.
#[test]
fn asset_cart_ignores_a_ticker_it_does_not_track() {
    let mut cart = Cart::compile();

    cart.quote("BTC-USD", 81_692);
    cart.set_quantity("BTC-USD", 1);
    let before = cart.view();

    cart.quote("DOGE-USD", 1);
    cart.quote("XRP-USD", 3);
    let after = cart.view();

    assert_eq!(line(&before, "BTC-USD"), line(&after, "BTC-USD"));
    assert_eq!(subtotal(&before), subtotal(&after));
}

/// Each view is served against the prices that preceded it, so a cart held
/// still revalues as the feed moves.
#[test]
fn asset_cart_revalues_a_held_position_as_the_price_moves() {
    let mut cart = Cart::compile();

    cart.set_quantity("BTC-USD", 2);
    cart.quote("BTC-USD", 81_692);
    let first = cart.view();

    cart.quote("BTC-USD", 90_000);
    let second = cart.view();

    assert_eq!(
        line(&first, "BTC-USD"),
        &expect(2, price(81_692), price(163_384))
    );
    assert_eq!(
        line(&second, "BTC-USD"),
        &expect(2, price(90_000), price(180_000))
    );
    assert_eq!(subtotal(&second), price(180_000));
}

/// A quantity change is the new quantity, not a delta.
#[test]
fn asset_cart_takes_a_quantity_change_as_the_new_quantity() {
    let mut cart = Cart::compile();

    cart.quote("SOL-USD", 200);
    cart.set_quantity("SOL-USD", 5);
    assert_eq!(
        line(&cart.view(), "SOL-USD"),
        &expect(5, price(200), price(1_000))
    );

    cart.set_quantity("SOL-USD", 2);
    assert_eq!(
        line(&cart.view(), "SOL-USD"),
        &expect(2, price(200), price(400))
    );

    cart.set_quantity("SOL-USD", 0);
    let emptied = cart.view();
    assert_eq!(line(&emptied, "SOL-USD"), &expect(0, price(200), 0));
    assert_eq!(subtotal(&emptied), 0);
}

/// The program keeps up with the feed it was designed for.
///
/// The recorded Coinbase slice runs at 2.33 rows/s across 20 products, so a row
/// has ~430 ms of budget and the wasm host will want most of that back.
///
/// One second per row is the bound because it has to separate the two shapes in
/// either build. This program measures ~170 ms per row in debug and ~22 ms in
/// release; the single six-slot reader it replaced measured ~10 s and ~2 s. The
/// bound sits about six times above the first and ten below the second, so it
/// fails on a return to that shape and on nothing else. `v0.cambra` records why
/// the reader is split, and
/// `transactions.rs`, "as_of_read_cost_grows_in_the_number_of_stores_one_block_reads"
/// measures the underlying cost.
///
/// A regression here is the demo failing on stage, so it is a bound rather than
/// a measurement.
#[test]
fn asset_cart_keeps_up_with_the_feed() {
    const ROWS: usize = 40;
    let feed = ["BTC-USD", "ETH-USD", "SOL-USD", "DOGE-USD", "XRP-USD"];
    let mut cart = Cart::compile();
    cart.set_quantity("BTC-USD", 2);

    let start = std::time::Instant::now();
    for i in 0..ROWS {
        cart.quote(feed[i % feed.len()], 100 + i as i64);
    }
    let per_row = start.elapsed() / ROWS as u32;

    assert!(
        per_row < std::time::Duration::from_secs(1),
        "{per_row:?} per price row against a 2.33 rows/s feed; the cart cannot keep up"
    );
}

/// The declaration file is what makes the program compilable from a path.
///
/// Without it the program is not wrong, it is unbound: `price_updates` names
/// nothing. This is what `cambra <path>` reads, and what the golden sweep reads
/// when it dumps every gallery program.
#[test]
fn asset_cart_needs_the_channels_declared_beside_it() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = std::path::Path::new(dir).join("v0.cambra");
    let source = std::fs::read_to_string(&program).expect("the program is readable");

    let declared = ChannelFile::beside(&program)
        .expect("the channel file parses")
        .expect("the program has a channel file");
    assert_eq!(
        declared.channels.len(),
        6,
        "three sources and one sink per ticker"
    );

    let mut bare = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errors = compile_program(&mut bare, &source, consumer)
        .err()
        .expect("with no channels registered, the source names are unbound");
    let rendered = format!("{errors:?}");
    assert!(
        rendered.contains("price_updates"),
        "the rejection names the unbound source; got: {rendered}"
    );
}

/// The binary is a host: JSON rows in, JSON rows out.
///
/// The in-process tests above push rows straight into the sources, which skips
/// everything between a program on a path and a running one — the declaration
/// file, the row codec and the drive loop. This drives the real binary the way
/// `streaming_echo` drives real stdin.
///
/// One line is one host event, so the view request lands after the price it
/// should see rather than committing alongside it.
#[test]
fn asset_cart_runs_as_a_subprocess_driven_by_json_lines() {
    let input = concat!(
        r#"{"source":"cart_changes","rows":[{"ticker":"BTC-USD","qty":2}]}"#,
        "\n",
        r#"{"source":"price_updates","rows":[{"ticker":"BTC-USD","price":8169291000000}]}"#,
        "\n",
        r#"{"source":"price_updates","rows":[{"ticker":"DOGE-USD","price":100}]}"#,
        "\n",
        r#"{"source":"view_requests","rows":[true]}"#,
        "\n",
    );
    super::common::expect_channel_program(
        "asset_cart",
        "v0.cambra",
        input,
        &[
            r#"{"sink":"btc_line","rows":[{"price":8169291000000,"qty":2,"total":16338582000000}]}"#,
            r#"{"sink":"eth_line","rows":[{"price":0,"qty":0,"total":0}]}"#,
        ],
    );
}

// ---------------------------------------------------------------------------
// v1 — the map-based cart
// ---------------------------------------------------------------------------

/// `v1.cambra` is blocked in the front end, on a **filter in a statement `for`
/// header**.
///
/// `for (a, t) -> q in cart if a == r.account:` — the checkout's
/// credit-and-drain — is what the expression grammar ends at the `:`, reporting
/// a binary operator expected. A comprehension takes `if`; a loop header does
/// not, and the drain is written as one.
///
/// Behind that sits one wall, not the three the entry-iteration work measured.
/// A compound key `(a, t)` is taken apart now, by the binder or by the program's
/// own `k.0`
/// ([`crate::compilation_pipeline`]'s `an_entry_binder_takes_a_compound_key_apart`),
/// and a transactional collection is read as a collection by its **values**,
/// materialized per commit and opened into a collection per transaction. What
/// remains is sweeping one by its **entries**: `lambda_elim` curries the
/// comprehension's body over the transaction's reads, and the curried type does
/// not carry the Σ binder its domain names — which op-conversion meets as a
/// `curry` it cannot compile.
///
/// The same run reports the three routes as undeclared, because
/// [`expect_compile_error`] compiles against a bare context with no host
/// channels registered. That is what every program with host channels looks
/// like there, and [`asset_cart_needs_the_channels_declared_beside_it`] pins the
/// same fact for `v0.cambra`; [`asset_cart_v1_declares_the_routes_it_serves`] is
/// the test that reads v1's own declarations.
///
/// Two further blockers sit behind these, unreachable until the front end
/// clears and so pinned by no needle here. A `Mut(Map(K, V), Txn)` seeded from
/// `map([…])` is rejected by inference, which meets a compute function and a
/// data collection at the initializer's position with no ordering between the
/// two kinds; and `box(map([]))` — what the cart and the prices are seeded with
/// — panics in post-letrec with unresolved inference variables. Neither is
/// about the program's shape: both are the seed of a keyed transactional store,
/// which no gallery program has needed before.
#[test]
fn asset_cart_v1_currently_blocked_on_entry_iteration() {
    // The needle is the parse of the checkout's drain header. It is deliberately
    // the *first* thing v1 meets rather than the deepest: a pin on a later wall
    // would go green the moment an earlier one moved, and this test's whole job
    // is to fail loudly when the blocker changes — which is how it caught that
    // entry iteration, `for`-in-a-block and the compound key had landed.
    expect_compile_error(
        include_str!("v1.cambra"),
        "found ':', expected binary operator",
    );
}

/// v1's wiring, beside it: three routes and the price feed.
///
/// `v1.channels.json` rather than `channels.json`, because v0 holds that name
/// and the two versions are wired differently — v1 replaces three sources and
/// three per-ticker sinks with three request/response pairs. One file carrying
/// the union would give each version sinks it never feeds, which lowering
/// rejects, so `ChannelFile::beside` reads a program-qualified file first.
///
/// The view reply is what this asserts registers. It is a record carrying two
/// lists, and a list's extent names a length that is data — so it is declarable
/// exactly because an egress row type needs no extent
/// (`src/interpreter/design-host-channels.md`, "Row types"). The program cannot
/// yet *produce* that row, but the declaration and the JSON codec beneath it are
/// no longer what stands in the way.
#[test]
fn asset_cart_v1_declares_the_routes_it_serves() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = std::path::Path::new(dir).join("v1.cambra");
    let declared = ChannelFile::beside(&program)
        .expect("the channel file parses")
        .expect("the program has a channel file");

    let declares = |name: &str, kind: ChannelKind| {
        declared
            .channels
            .iter()
            .any(|d| d.name == name && d.kind == kind)
    };
    let routes = ["PATCH /cart", "PUT /checkout", "GET /cart"];
    for route in routes {
        assert!(
            declares(route, ChannelKind::Request) && declares(route, ChannelKind::Response),
            "'{route}' is declared as a request/response pair"
        );
    }
    assert_eq!(
        declared.channels.len(),
        7,
        "two halves per route, plus the price feed"
    );

    let mut ctx = GlobalContext::default();
    let channels = ctx
        .register_channels(&declared.channels)
        .expect("v1's declarations are well formed");
    for route in routes {
        let (method, path) = route.split_once(' ').expect("a route is a request line");
        assert!(
            channels.route(method, path).is_some(),
            "'{route}' resolves to both of its halves"
        );
    }
}

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
//! split one-per-ticker, for the reason `v0.cambra` records: a block reading all
//! six slots costs about two seconds per price row. [`subtotal`] is what the
//! demo host does instead.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::channels::ChannelFile;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{Consumer, HostSink, HostSource, Value};

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

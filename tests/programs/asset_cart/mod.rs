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
//! and `GET /cart` instead of pushing rows at named channels. The one source
//! that survives is the price feed, which `wasm_socket_subscribe` binds and
//! names the subscription behind (`tests/wasm_socket_subscribe.rs`). It does not
//! compile, and two tests report why:
//! [`asset_cart_v1_currently_blocked_on_entry_iteration`] takes the whole program
//! and meets the checkout's drain, while
//! [`asset_cart_v1_read_sites_are_blocked_on_a_filtered_entry_comprehension`]
//! takes `v1_read_sites.cambra` and meets what the three sites reading the cart
//! report once nothing stops lowering before them. The file is here so the shape
//! is reviewable while those constructs are built.
//!
//! `v1_single_line.cambra` is that ladder with one cart line per account, which
//! replaces every entry iteration with a keyed lookup — and it runs, routes and
//! all ([`asset_cart_single_line_serves_its_routes`]). It carries v1's refined
//! `Balance`, which the checkout's guard discharges
//! ([`asset_cart_single_line_rejects_a_weakened_checkout_guard`]).
//!
//! `v2_single_line.cambra` is its reload target, unwinding the fixed-scale
//! assumption into a divisor per asset. The two share a wiring, and swapping one
//! for the other over a running cart is the demo's reload
//! ([`asset_cart_single_line_reloads_to_per_asset_scales`]).

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::channels::{ChannelFile, ChannelKind};
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::embed::Host;
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

/// `v1.cambra` is blocked in lowering, on an **entry binder in a statement `for`
/// inside a transaction**.
///
/// `for (a, t) -> q in cart if a == r.account:` — the checkout's
/// credit-and-drain — parses now: a loop header takes an `if`, which folds into
/// the body it guards (`docs/chl-spec.md`, "4.6 `for` — iteration"). What it
/// meets is the target: the transaction path reads a loop's binder by name where
/// the induction path classifies it, so a two-tuple binder is refused there and
/// nowhere else.
///
/// Two things sit behind that, and they are independent. A compound key `(a, t)`
/// is taken apart now, by the binder or by the program's own `k.0`
/// ([`crate::compilation_pipeline`]'s `an_entry_binder_takes_a_compound_key_apart`),
/// and a transactional collection is read as a collection by its **values**,
/// materialized per commit and opened into a collection per transaction.
///
/// What remains first is the key leaving the binder that scopes it.
/// `lambda_elim` curries the comprehension body over the transaction's reads and
/// pairs the key beside the sum that binds it rather than under it, so the
/// witness is free where the body uses it: a key compared against `r.account`
/// reports as a join of `Int` and a witness during inference, and one merely
/// bound reports as a free witness reference on `curry` after `lambda_elim`. One
/// escape, two phases.
///
/// Second, and reachable with no transaction and no correlation, the filter on
/// the key refines the key domain and that refinement arrives at op-conversion
/// as a `collection_contains` term needing an input. Binding
/// `c = map([(1, 10), (2, 20)])` and summing `[q for a -> q in c if a == 1]`
/// produces it.
///
/// The same run reports the three routes and the price feed as undeclared,
/// because [`expect_compile_error`] compiles against a bare context with no host
/// channels registered — the feed among them since `wasm_socket_subscribe` binds
/// a source the host declared rather than opening one, so with nothing declared
/// there is nothing for it to bind. That is what every program with host channels looks
/// like there, and [`asset_cart_needs_the_channels_declared_beside_it`] pins the
/// same fact for `v0.cambra`; [`asset_cart_v1_declares_the_routes_it_serves`] is
/// the test that reads v1's own declarations.
///
/// The seeds no longer block. A `Mut(Map(K, V), Txn)` initializer takes
/// `box(map([…]))` for a seeded store and `empty_map()` for an empty one, which
/// is what v1 writes; a bare `map([…])` there still meets a compute function and
/// a data collection with no ordering between the two kinds, and `map([])` is
/// rejected by the language (`docs/chl-spec.md`, "3.11 List, tuple, record
/// literals").
#[test]
fn asset_cart_v1_currently_blocked_on_entry_iteration() {
    // The needle is the parse of the checkout's drain header. It is deliberately
    // the *first* thing v1 meets rather than the deepest: a pin on a later wall
    // would go green the moment an earlier one moved, and this test's whole job
    // is to fail loudly when the blocker changes — which is how it caught that
    // entry iteration, `for`-in-a-block, the compound key and the header's `if`
    // had landed.
    expect_compile_error(
        include_str!("v1.cambra"),
        "for-loop target: only simple name targets are supported",
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

/// What the sites that read the cart report, which `v1.cambra` itself cannot show.
///
/// Three separate things are reported ahead of `due`, `lines` and `positions`, so the read
/// half of v1 is unobserved in the program of record. `v1_read_sites.cambra` elides all
/// three — the drain, `Balance`'s refinement, and the unbuilt price feed, each for a reason
/// its own header gives — and those sites then report on their own.
///
/// **A filter that names the request row is no longer what stops them.** All three read
/// `… if a == v.account`, and the contribution a `<<` makes abstracts over the channel's
/// position, so `v` resolves there to the request at that position rather than escaping to
/// the top-level feed that holds the reply (`feed_contribution` in
/// `src/ccl/infer/emit.rs`).
///
/// What they meet instead is the **compound key**, which needs no reply and no correlation
/// to fail: `cart` and `holdings` are keyed by `{AccountId, Ticker}`, and a filtered entry
/// comprehension over one collides on its upper bounds — the key tuple arrives beside the
/// witness domain the map's keys are. A scalar key does not collide, so this is about the
/// key rather than the filter or the transaction.
/// `a_filtered_entry_comprehension_over_a_compound_key_is_not_reachable`
/// (`tests/compilation_pipeline/comprehensions.rs`) pins it in five lines.
///
/// The needle is that collision rather than a later one, on the same rule as
/// [`asset_cart_v1_currently_blocked_on_entry_iteration`]: it is the *first* thing these
/// sites meet, so the test goes red when the obstruction changes rather than staying green
/// over a different one.
#[test]
fn asset_cart_v1_read_sites_are_blocked_on_a_filtered_entry_comprehension() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    // The wiring is v1's and the elisions are inside the program, so this reads v1's
    // channel file. A duplicate would be a second thing to keep in step for no gain.
    let declared = ChannelFile::beside(&std::path::Path::new(dir).join("v1.cambra"))
        .expect("the channel file parses")
        .expect("the program has a channel file");
    let mut ctx = GlobalContext::default();
    ctx.register_channels(&declared.channels)
        .expect("v1's declarations are well formed");

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let source = include_str!("v1_read_sites.cambra");
    // `unwrap_or_render` so a returned diagnostic and an internal panic arrive the same
    // way: the obstruction has been both as it moved, and a test that reads only one of
    // them goes green when it changes species. `CompiledProgram` is not `Debug`, so the
    // success arm is discarded rather than reported.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compile_program(&mut ctx, source, consumer)
            .map(|_| ())
            .unwrap_or_render("v1_read_sites.cambra", source)
    }));
    let payload = match outcome {
        Ok(()) => panic!("the read sites do not compile yet"),
        Err(payload) => payload,
    };

    let message = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| {
            payload
                .downcast_ref::<&'static str>()
                .map(|s| s.to_string())
        })
        .unwrap_or_else(|| "<non-string panic payload>".to_string());
    let needle = "Conflicting Types: σ | (Int, String)";
    assert!(
        message.contains(needle),
        "expected the read sites to report {needle:?}; got: {message}"
    );
}

// ---------------------------------------------------------------------------
// v1_single_line — the map-based cart with one line per account
// ---------------------------------------------------------------------------

/// `v1_single_line.cambra` runs, which `v1.cambra` does not compile.
///
/// One line per account turns every read of the cart from an iteration over one account's
/// entries into a keyed lookup, and that is the whole difference: the four obstructions
/// v1's header lists are all obstructions to the iteration. What remains here is the same
/// app — keyed collections, three routes, a live feed, and the atomicity claim.
///
/// Driven the way a host drives, one route at a time: a quote, then `PATCH /cart`,
/// `GET /cart` and `PUT /checkout`. Each reply arrives in the tick after the call, and the
/// checkout's three writes — the debit, the credit and the clear — land together.
///
/// The quantities are small next to the cart's 10⁸ scale because `qty * price` is an `Int`
/// product: one whole BTC at a five-figure price overflows `i64` before the `// one_btc`
/// divides it back down.
#[test]
fn asset_cart_single_line_serves_its_routes() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = std::path::Path::new(dir).join("v1_single_line.cambra");
    let declared = ChannelFile::beside(&program)
        .expect("the channel file parses")
        .expect("the program has a channel file");
    let source = include_str!("v1_single_line.cambra");
    let mut host = Host::compile("v1_single_line.cambra", source, &declared.channels)
        .expect("the program embeds");

    // Settle the price feed first, so the reads below have a quote to price against.
    host.push(
        "price_updates",
        [record(&[
            ("ticker", Value::String("BTC".into())),
            ("price", Value::Int(1_000 * SCALE)),
        ])],
    )
    .expect("`price_updates` is a declared source");
    tick_until_quiet(&mut host);

    // 0.001 BTC into account 1's cart.
    let qty = SCALE / 1_000;
    assert_eq!(
        call(
            &mut host,
            "PATCH",
            "/cart",
            &[
                ("account", Value::Int(1)),
                ("ticker", Value::String("BTC".into())),
                ("qty", Value::Int(qty)),
            ],
        ),
        vec![record(&[
            ("ok", Value::Bool(true)),
            ("ticker", Value::String("BTC".into())),
            ("qty", Value::Int(qty)),
        ])],
    );

    // The view prices that line against the quote the feed delivered.
    let due = qty * 1_000 * SCALE / SCALE;
    assert_eq!(
        call(&mut host, "GET", "/cart", &[("account", Value::Int(1))]),
        vec![record(&[
            ("cash", Value::Int(500 * SCALE)),
            ("ticker", Value::String("BTC".into())),
            ("qty", Value::Int(qty)),
            ("price", Value::Int(1_000 * SCALE)),
            ("total", Value::Int(due)),
            ("held", Value::Int(2 * SCALE)),
        ])],
    );

    // Checkout debits the cash the line is worth, and says what is left.
    assert_eq!(
        call(&mut host, "PUT", "/checkout", &[("account", Value::Int(1))]),
        vec![record(&[
            ("ok", Value::Bool(true)),
            ("due", Value::Int(due)),
            ("cash", Value::Int(500 * SCALE - due)),
        ])],
    );

    // The credit and the clear committed with that debit: the holding grew by the
    // line's quantity and the cart is back to zero.
    assert_eq!(
        call(&mut host, "GET", "/cart", &[("account", Value::Int(1))]),
        vec![record(&[
            ("cash", Value::Int(500 * SCALE - due)),
            ("ticker", Value::String("BTC".into())),
            ("qty", Value::Int(0)),
            ("price", Value::Int(1_000 * SCALE)),
            ("total", Value::Int(0)),
            ("held", Value::Int(2 * SCALE + qty)),
        ])],
    );
}

/// A record value from `(field, value)` pairs.
fn record(fields: &[(&str, Value)]) -> Value {
    Value::Record(
        fields
            .iter()
            .map(|(name, value)| ((*name).to_string(), value.clone()))
            .collect(),
    )
}

/// Tick until a tick produces nothing — the host's "let it settle" step.
fn tick_until_quiet(host: &mut Host) -> Vec<Value> {
    let mut rows = Vec::new();
    for _ in 0..TICKS_TO_SETTLE {
        let result = host.tick();
        rows.extend(result.outputs.into_iter().flat_map(|(_, rows)| rows));
    }
    rows
}

/// Call `method path` with one row and return what the route replied.
fn call(host: &mut Host, method: &str, path: &str, fields: &[(&str, Value)]) -> Vec<Value> {
    host.request(method, path, [record(fields)])
        .unwrap_or_else(|e| panic!("{method} {path} is a declared route: {e:?}"));
    tick_until_quiet(host)
}

/// Ticks allowed for one call to settle. A transaction commits over a few delivery
/// rounds, and this is far above what any route here takes, so exceeding it would be a
/// stall rather than a slow answer.
const TICKS_TO_SETTLE: usize = 32;

/// Weakening the checkout's guard makes the debit ill-typed — the claim the refined
/// `Balance` exists to make.
///
/// `^-` types the debit `{Microcents | __elem == cash ^- due}`, and `Balance` demands
/// `__elem >= 0`; the `cash >= due` guard is what closes the gap, assumable inside its own
/// arm. A guard that does not imply it leaves the write unproved. Without this, a program
/// that kept the declaration and lost the check would still pass every other test here.
#[test]
fn asset_cart_single_line_rejects_a_weakened_checkout_guard() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = std::path::Path::new(dir).join("v1_single_line.cambra");
    let declared = ChannelFile::beside(&program)
        .expect("the channel file parses")
        .expect("the program has a channel file");
    let source = include_str!("v1_single_line.cambra");
    let weakened = source.replace("if cash >= due:", "if cash >= 0:");
    assert_ne!(
        weakened, source,
        "the guard this weakens is spelled `if cash >= due:`"
    );
    match Host::compile("v1_single_line.cambra", &weakened, &declared.channels) {
        Ok(_) => panic!("a weakened guard leaves the debit unproved, so it must not compile"),
        Err(e) => {
            let msg = e.to_string();
            assert!(
                msg.contains("expected {Int | __elem >= 0}"),
                "the rejection names the balance's invariant; got: {msg}"
            );
        }
    }
}

/// The demo's reload: `v1_single_line.cambra` running, `v2_single_line.cambra` swapped in
/// over it, and the cart it had built still there.
///
/// v1 divides every line by `one_btc`; v2 reads a divisor per asset out of `scales`. The
/// swap is visible on ETH, whose scale is gwei rather than satoshis, and invisible on BTC,
/// whose is unchanged — so the run separates "the new code took effect" from "the old state
/// survived" instead of conflating them.
#[test]
fn asset_cart_single_line_reloads_to_per_asset_scales() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let v1 = std::path::Path::new(dir).join("v1_single_line.cambra");
    let declared = ChannelFile::beside(&v1)
        .expect("the channel file parses")
        .expect("the program has a channel file");
    // A reload changes the program and not the channels, so the two versions' wirings are
    // one wiring. They are separate files because either program can be booted alone.
    assert_eq!(
        std::fs::read_to_string(std::path::Path::new(dir).join("v1_single_line.channels.json"))
            .expect("v1's wiring is readable"),
        std::fs::read_to_string(std::path::Path::new(dir).join("v2_single_line.channels.json"))
            .expect("v2's wiring is readable"),
        "the versions a reload swaps between share one wiring",
    );

    let mut host = Host::compile(
        "v1_single_line.cambra",
        include_str!("v1_single_line.cambra"),
        &declared.channels,
    )
    .expect("v1 embeds");

    // A quote for each asset, then a line in each account's cart.
    for (ticker, dollars) in [("BTC", 1_000), ("ETH", 2_000)] {
        host.push(
            "price_updates",
            [record(&[
                ("ticker", Value::String(ticker.into())),
                ("price", Value::Int(dollars * SCALE)),
            ])],
        )
        .expect("`price_updates` is a declared source");
        tick_until_quiet(&mut host);
    }
    let qty = SCALE / 1_000;
    for (account, ticker) in [(1i64, "BTC"), (2, "ETH")] {
        call(
            &mut host,
            "PATCH",
            "/cart",
            &[
                ("account", Value::Int(account)),
                ("ticker", Value::String(ticker.into())),
                ("qty", Value::Int(qty)),
            ],
        );
    }

    let view = |host: &mut Host, account: i64| -> Value {
        let mut rows = call(host, "GET", "/cart", &[("account", Value::Int(account))]);
        assert_eq!(rows.len(), 1, "one request serves one line");
        rows.remove(0)
    };
    let (btc_before, eth_before) = (view(&mut host, 1), view(&mut host, 2));

    host.reload(include_str!("v2_single_line.cambra"))
        .expect("v2 declares the same state v1 holds, so the swap is accepted");

    let (btc_after, eth_after) = (view(&mut host, 1), view(&mut host, 2));

    // BTC's scale is satoshis in both versions, so its line is untouched — every field of
    // it, which is the state that had to survive the swap.
    assert_eq!(btc_after, btc_before, "BTC's line is unchanged by the swap");

    // ETH's divisor becomes gwei, so its total falls by the ratio of the two scales and
    // nothing else about it moves.
    let field = |row: &Value, name: &str| match row {
        Value::Record(fields) => fields.get(name).cloned().expect("the field is present"),
        other => panic!("a line is a record, got {other:?}"),
    };
    for name in ["cash", "ticker", "qty", "price", "held"] {
        assert_eq!(
            field(&eth_after, name),
            field(&eth_before, name),
            "the swap keeps ETH's {name}",
        );
    }
    let Value::Int(before) = field(&eth_before, "total") else {
        panic!("a total is an Int");
    };
    assert_eq!(
        field(&eth_after, "total"),
        Value::Int(before / 10),
        "ETH prices at gwei after the swap, a tenth of what satoshis gave",
    );
}

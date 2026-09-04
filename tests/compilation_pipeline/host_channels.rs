//! Host channels: a program reading rows the host pushed, and feeding rows the
//! host reads back.
//!
//! These drive a program the way an embedding host does — push, let the
//! scheduler settle, pull, release — rather than presenting all the data at
//! once, because the shapes the demo program depends on are properties of a
//! live stream and not of a finite collection.

use std::cell::RefCell;
use std::rc::Rc;

use cambra::ccl::Type;
use cambra::ccl::channels::ChannelDecl;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program};
use cambra::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, FunctionGuard, HostSink, HostSource, Tile, TileGuard,
    Value, tile_operators::TileProducer,
};
use indoc::indoc;

/// `{ticker: String, price: Int}` as a type and the matching extent.
fn price_row_type() -> (Type, Extent) {
    (
        Type::Record(
            [
                ("ticker".to_string(), Type::Base(BaseType::String)),
                ("price".to_string(), Type::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        ),
        Extent::record(
            [
                ("ticker".to_string(), Extent::Base(BaseType::String)),
                ("price".to_string(), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        ),
    )
}

fn price_row(ticker: &str, price: i64) -> Value {
    Value::Record(
        [
            ("ticker".to_string(), Value::String(ticker.into())),
            ("price".to_string(), Value::Int(price)),
        ]
        .into_iter()
        .collect(),
    )
}

/// Pull the program's output and release what it delivered, which is one turn
/// of the host's drive loop.
///
/// The release is what advances the sources' windows and the reading loop's
/// latch. A driver that only pulls reads a stream that never moves.
fn pull_and_release(producer: &mut Box<dyn TileProducer>) -> Tile {
    let tile = producer.get(producer.tiling().universal_guard());
    let guard = match &tile {
        Tile::Scalar(cv) => TileGuard::Scalar(!cv.is_empty()),
        Tile::SealedFunction {
            domain_predicate, ..
        } => TileGuard::Function(FunctionGuard::Domain(domain_predicate.clone())),
        other => panic!("unexpected top-level tile shape: {other:?}"),
    };
    producer.release(guard);
    tile
}

/// The `Int` codomain of a sealed function tile, in domain order.
fn ints_in_domain_order(tile: &Tile) -> Vec<i64> {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        panic!("expected a SealedFunction, got {tile:?}");
    };
    let ColumnValue::UInts(keys) = domain else {
        panic!("expected UInt keys, got {domain:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(values)) = codomain.as_ref() else {
        panic!("expected an Int codomain, got {codomain:?}");
    };
    let mut rows: Vec<(usize, i64)> = keys.iter().copied().zip(values.iter().copied()).collect();
    rows.sort();
    rows.into_iter().map(|(_, v)| v).collect()
}

/// The demo program's spine at one ticker: the host pushes price rows and view
/// requests, the program filters the stream by ticker into a transactional
/// slot, and a reading loop feeds the slot's current value out per request.
///
/// Each read must see the price that preceded it. This is the property a served
/// cart view rests on, and the one a source with unordered keys and no release
/// does not have.
#[test]
fn a_read_per_request_sees_the_price_that_preceded_it() {
    let code = indoc! {r#"
        btc_updates = [u for u in price_updates() if u.ticker == "BTC-USD"]
        btc_px: Mut(Int, Txn) := 0
        for u in btc_updates:
            with begin():
                btc_px := u.price
        view = defer()
        for req in view_requests():
            with begin():
                view << btc_px
        view
    "#};

    let (row_type, row_extent) = price_row_type();
    let updates = Rc::new(RefCell::new(HostSource::new(
        "price_updates",
        row_type,
        row_extent,
    )));
    let requests = Rc::new(RefCell::new(HostSource::new(
        "view_requests",
        Type::Base(BaseType::Bool),
        Extent::Base(BaseType::Bool),
    )));

    let mut ctx = GlobalContext::default();
    ctx.register_source(updates.clone());
    ctx.register_source(requests.clone());

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled
        .main_mut()
        .expect("the program has a main output")
        .producer
        .take()
        .expect("the main output has a producer");

    // Three rounds, each a price for the tracked ticker, a price for one the
    // program ignores, and a view request — the cadence the host drives.
    for (price, other) in [(100i64, 5i64), (300, 6), (700, 7)] {
        updates
            .borrow_mut()
            .push([price_row("BTC-USD", price), price_row("ETH-USD", other)]);
        ctx.scheduler().check_for_notifications();
        pull_and_release(&mut producer);

        requests.borrow_mut().push([Value::Bool(true)]);
        ctx.scheduler().check_for_notifications();
        pull_and_release(&mut producer);
    }

    // The reading loop's feed accumulates one row per request, so the final
    // pull carries every view the run served.
    updates.borrow_mut().close();
    requests.borrow_mut().close();
    ctx.scheduler().check_for_notifications();
    let tile = pull_and_release(&mut producer);
    assert_eq!(ints_in_domain_order(&tile), vec![100, 300, 700]);
}

/// The source's window is the rows it still holds, which is what the inspector
/// renders as the stream's live tail.
///
/// A window is sampled before the pull and drains on the release, which is why
/// the driver samples between the two (`src/main.rs`, the `sample_sources`
/// closure). Both halves are asserted here: a row that has arrived is in the
/// window, and a row every producer has released is not.
#[test]
fn a_host_source_window_holds_what_has_not_been_released() {
    let code = "[u.price for u in price_updates()]";
    let (row_type, row_extent) = price_row_type();
    let updates = Rc::new(RefCell::new(HostSource::new(
        "price_updates",
        row_type,
        row_extent,
    )));

    let mut ctx = GlobalContext::default();
    ctx.register_source(updates.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled
        .main_mut()
        .expect("the program has a main output")
        .producer
        .take()
        .expect("the main output has a producer");

    updates
        .borrow_mut()
        .push([price_row("BTC-USD", 100), price_row("ETH-USD", 20)]);
    ctx.scheduler().check_for_notifications();

    let window = |ctx: &mut GlobalContext| -> ColumnValue {
        ctx.scheduler()
            .sources()
            .find(|(name, _)| *name == "price_updates")
            .map(|(_, handle)| handle)
            .expect("the program subscribes the source it reads")
            .borrow()
            .retained_keys()
            .expect("a host source has a window")
    };

    assert_eq!(
        window(&mut ctx),
        ColumnValue::from_uints(vec![0, 1]),
        "rows that have arrived and not been consumed are the live tail"
    );

    pull_and_release(&mut producer);
    assert!(
        window(&mut ctx).is_empty(),
        "a row every producer has released leaves the window"
    );
}

/// A program feeding a host sink, driven the way a host drives it: push rows,
/// let the scheduler settle, drain what arrived.
///
/// The sink carries the value the program computed, as a value. Nothing is
/// rendered to a string on the way out, which is what separates a host channel
/// from an HTTP response — and why the demo program needs no `str` builtin.
#[test]
fn a_host_sink_carries_the_rows_the_program_fed_it() {
    let code = indoc! {r#"
        btc_updates = [u for u in price_updates() if u.ticker == "BTC-USD"]
        btc_px: Mut(Int, Txn) := 0
        for u in btc_updates:
            with begin():
                btc_px := u.price
        for req in view_requests():
            with begin():
                cart_view << btc_px * 2
    "#};

    let (row_type, row_extent) = price_row_type();
    let updates = Rc::new(RefCell::new(HostSource::new(
        "price_updates",
        row_type,
        row_extent,
    )));
    let requests = Rc::new(RefCell::new(HostSource::new(
        "view_requests",
        Type::Base(BaseType::Bool),
        Extent::Base(BaseType::Bool),
    )));
    let view = Rc::new(HostSink::new("cart_view"));

    let mut ctx = GlobalContext::default();
    ctx.register_source(updates.clone());
    ctx.register_source(requests.clone());
    ctx.declare_host_sink(view.clone());

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let _compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);

    let mut served = Vec::new();
    for price in [100i64, 300, 700] {
        updates.borrow_mut().push([price_row("BTC-USD", price)]);
        ctx.scheduler().check_for_notifications();
        requests.borrow_mut().push([Value::Bool(true)]);
        ctx.scheduler().check_for_notifications();
        served.extend(view.drain());
    }

    assert_eq!(
        served,
        vec![Value::Int(200), Value::Int(600), Value::Int(1400)]
    );
}

/// A sink the host declares and the program never feeds is rejected, as any
/// unfed sink is.
#[test]
fn a_declared_sink_the_program_never_feeds_is_rejected() {
    let code = "[u.price for u in price_updates()]";
    let (row_type, row_extent) = price_row_type();
    let updates = Rc::new(RefCell::new(HostSource::new(
        "price_updates",
        row_type,
        row_extent,
    )));

    let mut ctx = GlobalContext::default();
    ctx.register_source(updates);
    ctx.declare_host_sink(Rc::new(HostSink::new("cart_view")));

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compile_program(&mut ctx, code, consumer).map(|_| ())
    }));
    let message = match outcome {
        Err(payload) => payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
            .unwrap_or_default(),
        Ok(Ok(())) => panic!("a declared sink with no feed compiled"),
        Ok(Err(errors)) => format!("{errors:?}"),
    };
    assert!(
        message.contains("cart_view"),
        "the rejection names the unfed sink; got: {message}"
    );
}

/// The whole wiring from declarations: four channels named and typed in CHL,
/// registered in one call, and a program that reads three and feeds the fourth.
///
/// This is the shape a host uses. Nothing here builds a `Type` or an `Extent`
/// by hand — the row types are the text a program would write in an annotation.
#[test]
fn a_program_wires_to_channels_the_host_declared() {
    let code = indoc! {r#"
        btc_updates = [u for u in price_updates() if u.ticker == "BTC-USD"]
        btc_changes = [c for c in cart_changes() if c.ticker == "BTC-USD"]

        btc_px: Mut(Int, Txn) := 0
        btc_qty: Mut(Int, Txn) := 0

        for u in btc_updates:
            with begin():
                btc_px := u.price
        for c in btc_changes:
            with begin():
                btc_qty := c.qty

        for req in view_requests():
            with begin():
                cart_view << (qty=btc_qty, price=btc_px, total=btc_qty * btc_px)
    "#};

    let decls = [
        ChannelDecl::source("price_updates", "{ticker: String, price: Int}"),
        ChannelDecl::source("cart_changes", "{ticker: String, qty: Int}"),
        ChannelDecl::source("view_requests", "Bool"),
        ChannelDecl::sink("cart_view", "{qty: Int, price: Int, total: Int}"),
    ];

    let mut ctx = GlobalContext::default();
    let channels = ctx
        .register_channels(&decls)
        .expect("the declarations are well formed");
    let prices = channels
        .source("price_updates")
        .expect("a declared source has a handle")
        .clone();
    let changes = channels
        .source("cart_changes")
        .expect("a declared source has a handle")
        .clone();
    let requests = channels
        .source("view_requests")
        .expect("a declared source has a handle")
        .clone();
    let view = channels
        .sink("cart_view")
        .expect("a declared sink has a handle")
        .clone();

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let _compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);

    let cart_row = |ticker: &str, qty: i64| {
        Value::Record(
            [
                ("ticker".to_string(), Value::String(ticker.into())),
                ("qty".to_string(), Value::Int(qty)),
            ]
            .into_iter()
            .collect(),
        )
    };

    prices.borrow_mut().push([price_row("BTC-USD", 81_692)]);
    changes.borrow_mut().push([cart_row("BTC-USD", 2)]);
    ctx.scheduler().check_for_notifications();
    requests.borrow_mut().push([Value::Bool(true)]);
    ctx.scheduler().check_for_notifications();

    let rows = view.drain();
    assert_eq!(rows.len(), 1, "one view request serves one row");
    let Value::Record(row) = &rows[0] else {
        panic!("the sink carries a record row, got {:?}", rows[0]);
    };
    assert_eq!(row["qty"], Value::Int(2));
    assert_eq!(row["price"], Value::Int(81_692));
    assert_eq!(row["total"], Value::Int(163_384));
}

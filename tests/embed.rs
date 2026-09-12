//! The embedding contract: compile, push, tick, read.
//!
//! These are the calls a host makes, in the order it makes them, against the
//! demo program. They are the same scenario the WebAssembly wrapper has to
//! satisfy, so a failure here is a failure of the embedding surface rather than
//! of a particular host.

use std::path::Path;

use cambra::ccl::channels::{ChannelFile, row_to_json};
use cambra::embed::Host;
use cambra::interpreter::Value;

/// Dollars × 10⁸ — the scale a price crosses a channel in.
const SCALE: i64 = 100_000_000;

fn asset_cart() -> Host {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = Path::new(dir).join("v0.cambra");
    let code = std::fs::read_to_string(&program).expect("the program is readable");
    let declared = ChannelFile::beside(&program)
        .expect("the channel file parses")
        .expect("the program has a channel file");
    Host::compile("v0.cambra", &code, &declared.channels).expect("the demo program embeds")
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

/// One channel's recorded tail, by the name it was registered under.
fn channel_tail<'a>(frame: &'a serde_json::Value, name: &str) -> Option<&'a serde_json::Value> {
    frame["nodes"]
        .as_array()?
        .iter()
        .flat_map(|node| node["producers"].as_array().into_iter().flatten())
        .find(|producer| producer["producer"] == name)
}

/// The rendered values of a recorded producer's rows.
fn row_values(producer: &serde_json::Value) -> Vec<String> {
    producer["rows"]
        .as_array()
        .expect("a producer carries rows")
        .iter()
        .map(|row| row["value"].as_str().unwrap_or_default().to_string())
        .collect()
}

/// Push a row and tick until the sinks answer, returning what they produced.
///
/// A reader fires a tick or more after the write it reads, so a host that ticks
/// once per push and looks immediately sees nothing. This is what the real drive
/// loops do on their own clocks.
fn push_and_settle(host: &mut Host, source: &str, row: Value) -> Vec<(String, Vec<Value>)> {
    host.push(source, [row]).expect("a declared source");
    for _ in 0..8 {
        let result = host.tick();
        if !result.outputs.is_empty() {
            return result.outputs;
        }
    }
    Vec::new()
}

/// The whole contract in the order a host uses it.
#[test]
fn a_host_compiles_pushes_ticks_and_reads() {
    let mut host = asset_cart();

    assert!(
        host.snapshot().contains("\"payloadKind\":\"program\""),
        "a compiled program's snapshot is the program payload"
    );

    assert!(
        push_and_settle(&mut host, "cart_changes", ticker_row("qty", "BTC-USD", 2)).is_empty(),
        "a cart change alone produces no view"
    );
    push_and_settle(
        &mut host,
        "price_updates",
        ticker_row("price", "BTC-USD", 81_692 * SCALE),
    );

    let outputs = push_and_settle(&mut host, "view_requests", Value::Bool(true));
    let names: Vec<&str> = outputs.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(
        names,
        vec!["btc_line", "eth_line", "sol_line"],
        "a view request serves every line, in a stable order"
    );

    let (_, btc) = outputs.first().expect("a btc line");
    let json = row_to_json(&btc[0]).expect("a line encodes as JSON");
    assert_eq!(json["qty"], 2);
    assert_eq!(json["price"], 81_692 * SCALE);
    assert_eq!(json["total"], 2 * 81_692 * SCALE);
}

/// A frame carries the operators that produced and the sources' live windows.
///
/// The values pane is built from this, so a frame with no `sources` is a pane
/// that cannot show the stream moving.
#[test]
fn a_frame_carries_the_nodes_and_the_source_windows() {
    let mut host = asset_cart();
    push_and_settle(
        &mut host,
        "price_updates",
        ticker_row("price", "BTC-USD", 81_692 * SCALE),
    );
    push_and_settle(&mut host, "view_requests", Value::Bool(true));

    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    assert_eq!(frame["final"], false);
    assert!(
        frame["nodes"].as_array().is_some_and(|n| !n.is_empty()),
        "a producing run records operators"
    );

    let sources = frame["sources"]
        .as_array()
        .expect("a frame carries a sources array");
    let named: Vec<&str> = sources.iter().filter_map(|s| s["name"].as_str()).collect();
    assert!(
        named.contains(&"price_updates"),
        "the stream the program reads reports its window; got {named:?}"
    );
    assert!(
        !named.contains(&"stdin"),
        "a source the program never reads is not part of the program; got {named:?}"
    );
}

/// Inspecting a source shows the feed, including the rows the program filters
/// out.
///
/// The retained window cannot answer this: a consumer releases a row from inside
/// the pull that reads it, so by the time any frame renders, the buffer holds
/// nothing. What crossed the channel is recorded as it crosses.
#[test]
fn a_source_tail_carries_the_whole_feed_after_its_rows_are_released() {
    let mut host = asset_cart();
    for (i, ticker) in ["BTC-USD", "DOGE-USD", "ETH-USD"].iter().enumerate() {
        push_and_settle(
            &mut host,
            "price_updates",
            ticker_row("price", ticker, (80_000 + i as i64) * SCALE),
        );
    }
    push_and_settle(&mut host, "view_requests", Value::Bool(true));

    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    let feed = channel_tail(&frame, "price_updates").expect("the source records what crosses it");
    assert_eq!(feed["total"], 3, "every pushed row crossed the channel");
    let rows = row_values(feed);
    assert_eq!(rows.len(), 3);
    assert!(
        rows.iter().any(|row| row.contains("DOGE-USD")),
        "a ticker the program filters out still crossed the source; got {rows:?}"
    );
    assert!(
        frame["sources"]
            .as_array()
            .expect("a frame carries a sources array")
            .iter()
            .any(|s| s["name"] == "price_updates"),
        "the retained window still ships beside the tail"
    );
}

/// Inspecting a sink shows the rows the program served, which a drain would
/// otherwise have taken before any frame rendered.
#[test]
fn a_sink_tail_carries_the_line_the_program_served() {
    let mut host = asset_cart();
    push_and_settle(&mut host, "cart_changes", ticker_row("qty", "BTC-USD", 2));
    push_and_settle(
        &mut host,
        "price_updates",
        ticker_row("price", "BTC-USD", 81_692 * SCALE),
    );
    let outputs = push_and_settle(&mut host, "view_requests", Value::Bool(true));
    assert!(!outputs.is_empty(), "the drain took the rows");

    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    let line = channel_tail(&frame, "btc_line").expect("the sink records what it served");
    let rows = row_values(line);
    assert_eq!(rows.len(), 1, "one view request serves one line");
    assert!(
        rows[0].contains(&format!("{}", 2 * 81_692 * SCALE)),
        "the served line carries the priced total; got {rows:?}"
    );
}

/// An operator that answered with rows once and empty ever since still reports
/// the rows.
///
/// A filter over a host source is pulled hundreds of times per row by a settling
/// scheduler, so the ring of recent calls has evicted the row-carrying answer
/// long before a frame renders. Without the preserved tail every operator in the
/// program reads as though it had never been pulled.
#[test]
fn an_operator_reports_rows_the_call_ring_has_evicted() {
    let mut host = asset_cart();
    push_and_settle(
        &mut host,
        "price_updates",
        ticker_row("price", "BTC-USD", 81_692 * SCALE),
    );
    push_and_settle(&mut host, "view_requests", Value::Bool(true));

    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    let filtering: Vec<&serde_json::Value> = frame["nodes"]
        .as_array()
        .expect("a frame carries nodes")
        .iter()
        .flat_map(|n| n["producers"].as_array().expect("producers").iter())
        .filter(|p| {
            p["shape"] == "SealedFunction"
                && p["producer"]
                    .as_str()
                    .is_some_and(|n| n.starts_with("Restrict"))
        })
        .collect();
    assert!(
        !filtering.is_empty(),
        "the three ingest filters lower to Restrict operators"
    );
    assert!(
        filtering.iter().all(|p| p["total"].as_u64() == Some(1)),
        "each filter saw the pushed row"
    );
    assert!(
        filtering.iter().all(|p| p["stale"] == true),
        "newer calls carried nothing, so the rows report as stale"
    );
}

/// Inspecting a transactional slot shows what was written to it and when.
///
/// A store is a changelog, and reading it *at a tick* means folding every
/// earlier change — which is why it once rendered as a count with no rows. What
/// a reader asks of a slot is the changes themselves.
#[test]
fn a_store_carries_the_writes_that_landed_on_it() {
    let mut host = asset_cart();
    push_and_settle(&mut host, "cart_changes", ticker_row("qty", "BTC-USD", 2));
    for i in 0..3 {
        push_and_settle(
            &mut host,
            "price_updates",
            ticker_row("price", "BTC-USD", (80_000 + i) * SCALE),
        );
    }

    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(false)).expect("a frame is valid JSON");
    let store = frame["nodes"]
        .as_array()
        .expect("a frame carries nodes")
        .iter()
        .flat_map(|n| n["producers"].as_array().into_iter().flatten())
        // Found by what it carries rather than by its producer name: a name's
        // ordinal counts every producer of that kind built in the process, so it
        // names a different store depending on what else has compiled.
        .find(|p| p["shape"] == "Store" && row_values(p).iter().any(|row| row.contains("btc_px")))
        .expect("the btc slots commit through a store");

    let rows = row_values(store);
    assert!(
        rows.iter()
            .any(|row| row.contains("btc_qty") && row.contains("2")),
        "the quantity write landed; got {rows:?}"
    );
    assert!(
        rows.iter()
            .any(|row| row.contains("btc_px") && row.contains(&format!("{}", 80_002 * SCALE))),
        "the latest price write landed; got {rows:?}"
    );
    assert_eq!(
        store["dropped"], 0,
        "five writes sit well inside the row cap, so none are dropped"
    );
}

/// A final frame says the run is over, so a reader can tell a converged program
/// from an idle one.
#[test]
fn a_final_frame_says_the_run_is_over() {
    let host = asset_cart();
    let frame: serde_json::Value =
        serde_json::from_str(&host.frame(true)).expect("a frame is valid JSON");
    assert_eq!(frame["final"], true);
}

/// Pushing to a name no source has is an error rather than a silent no-op.
#[test]
fn pushing_to_an_unknown_source_is_an_error() {
    let mut host = asset_cart();
    let err = host
        .push("nowhere", [Value::Bool(true)])
        .expect_err("no source is named 'nowhere'");
    assert!(
        err.to_string().contains("nowhere"),
        "the rejection names the source: {err}"
    );
}

/// Two hosts fed the same rows in the same order produce the same outputs.
///
/// A reload keeps what the running version was holding.
///
/// The counterpart of replaying: the host pushes rows, swaps in a new version of
/// the source, and the cart it had accumulated is still there — nothing is
/// pushed a second time. This is what `LiveProgram::reload` carries and what a
/// replay-based swap could not.
#[test]
fn a_reload_keeps_what_the_running_version_was_holding() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs/asset_cart");
    let program = std::path::Path::new(dir).join("v0.cambra");
    let code = std::fs::read_to_string(&program).expect("the program is readable");

    let mut host = asset_cart();
    push_and_settle(&mut host, "cart_changes", ticker_row("qty", "BTC-USD", 2));
    let before = push_and_settle(&mut host, "view_requests", Value::Bool(true));
    assert!(!before.is_empty(), "the view serves before the reload");

    // The same source: a reload that changes nothing still rebuilds nothing it
    // can keep, so what survives is what the runtime carried rather than what
    // the program recomputed.
    host.reload("v0.cambra", &code)
        .expect("the same source reloads");

    let after = push_and_settle(&mut host, "view_requests", Value::Bool(true));
    assert_eq!(
        after, before,
        "the cart the running version held survives the swap",
    );
}

/// This is what lets a host rebuild a program's state in a new process by
/// replaying what it pushed. Carrying state across a *new version of the
/// source* is [`Host::reload`] instead, which keeps the operators it can and
/// resumes each mutable variable in place.
#[test]
fn the_same_rows_in_the_same_order_produce_the_same_outputs() {
    let journal = [
        ("cart_changes", ticker_row("qty", "BTC-USD", 2)),
        ("cart_changes", ticker_row("qty", "ETH-USD", 5)),
        (
            "price_updates",
            ticker_row("price", "BTC-USD", 81_692 * SCALE),
        ),
        ("price_updates", ticker_row("price", "DOGE-USD", 100)),
        (
            "price_updates",
            ticker_row("price", "ETH-USD", 4_413 * SCALE),
        ),
        ("view_requests", Value::Bool(true)),
    ];

    let replay = |host: &mut Host| {
        let mut served = Vec::new();
        for (source, row) in &journal {
            served.extend(push_and_settle(host, source, row.clone()));
        }
        served
    };

    let original = replay(&mut asset_cart());
    let replayed = replay(&mut asset_cart());

    assert!(!original.is_empty(), "the journal serves at least one view");
    assert_eq!(
        original, replayed,
        "a fresh program fed the same rows reaches the same state"
    );
}

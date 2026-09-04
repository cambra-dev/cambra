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
/// This is what lets a host rebuild a running program's state in a fresh
/// instance by replaying what it pushed — the only mechanism there is for
/// carrying state across a recompile, since nothing in the runtime serializes a
/// `Mut` cell.
#[test]
fn replaying_the_same_rows_reproduces_the_same_outputs() {
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

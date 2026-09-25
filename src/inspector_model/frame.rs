//! Rendering a probe frame: the JSON probe publishing sends.
//!
//! A pure function of the probe table and the sources' windows, so it is wire
//! and only its delivery is transport. Leaving it behind the websocket route would
//! have put a socket between a host with no sockets and the bytes it needs.

use std::collections::HashMap;

use crate::ccl::provenance::NodeId;
use crate::interpreter::value_probe::{Reading, ReadingRow, SharedProbeTable, SourceWindow};

/// The JSON probe publishing sends: one entry per node, holding each of its
/// probes' last row-carrying reading.
///
/// Collapsed here rather than when a reading is taken. A producer pulled twice
/// in one tick answers the second call empty, and another answers with the
/// same tile twice, so the newest reading is the wrong one to send and merging
/// the two double-counts. See
/// [`ProbeTable::last_flow`](crate::interpreter::value_probe::ProbeTable::last_flow)..
pub fn render_probe_frame(
    probes: &SharedProbeTable,
    sources: &[SourceWindow],
    tick: u64,
    published: u64,
    final_frame: bool,
) -> String {
    let probes = probes.borrow();
    let mut by_node: HashMap<u64, Vec<serde_json::Value>> = HashMap::new();
    for (node_id, producer_id) in probes.probe_keys() {
        let Some(node) = node_id else { continue };
        let Some((reading, stale)) = probes.last_flow(node_id, producer_id) else {
            continue;
        };
        by_node
            .entry(node_key(node))
            .or_default()
            .push(probe_json(reading, stale));
    }
    let mut by_node: Vec<(u64, Vec<serde_json::Value>)> = by_node.into_iter().collect();
    // Ascending `NodeId`, which is both stable and meaningful: an operator's id
    // is minted when it is constructed, and construction is bottom-up, so a
    // smaller id sits further upstream. A `HashMap` iteration is neither —
    // unsorted, this array arrived in a different order on every run.
    by_node.sort_by_key(|(node, _)| *node);
    let nodes: Vec<serde_json::Value> = by_node
        .into_iter()
        .map(|(node, mut node_probes)| {
            // A node's probes are keyed by the producer's allocation counter, so
            // ordering by it is stable across ticks; a `HashMap` iteration is not.
            node_probes.sort_by_key(|p| p["producerId"].as_u64().unwrap_or(0));
            serde_json::json!({ "nodeId": node, "probes": node_probes })
        })
        .collect();
    // `published` counts frames rather than ticks, so a client that reconnects
    // or misses a wake can tell it is behind. A producer's own `seq` is the
    // finer signal, for a gap within one probe's readings.
    // `final` says the run is over and this frame is the last. A reader that
    // never sees one and then loses the socket has been disconnected; a reader
    // holding one knows the quiet is the end rather than a pause.
    // A source ships beside the operators rather than among them: it has no
    // producer and takes no `get`, so it carries a window rather than a
    // probe reading. A source is not a graph node, so the window names the
    // `IterateExtent`s over its domain, which is where a click resolves.
    let sources: Vec<serde_json::Value> = sources
        .iter()
        .map(|window| {
            serde_json::json!({
                "nodeIds": window.node_ids.iter().map(|id| node_key(*id)).collect::<Vec<_>>(),
                "name": window.name,
                "total": window.total,
                "dropped": window.dropped(),
                "rows": window.rows.iter().map(row_json).collect::<Vec<_>>(),
            })
        })
        .collect();
    serde_json::json!({
        "tick": tick,
        "published": published,
        "final": final_frame,
        "nodes": nodes,
        "sources": sources,
    })
    .to_string()
}

/// A `NodeId` as the number it ships as on the static wire.
fn node_key(node: NodeId) -> u64 {
    serde_json::to_value(node)
        .ok()
        .and_then(|value| value.as_u64())
        .unwrap_or_default()
}

/// One rendered row.
fn row_json(row: &ReadingRow) -> serde_json::Value {
    serde_json::json!({
        "key": row.key,
        "value": row.value,
        "deleted": row.deleted,
    })
}

/// One probe's last row-carrying reading.
fn probe_json(reading: &Reading, stale: bool) -> serde_json::Value {
    let rows: Vec<serde_json::Value> = reading.rows.iter().map(row_json).collect();
    serde_json::json!({
        "producerId": reading.producer_id,
        "producer": reading.producer,
        "shape": reading.shape,
        "watermark": reading.watermark,
        "note": reading.note,
        "tick": reading.tick,
        "seq": reading.seq,
        "stale": stale,
        "total": reading.total,
        "dropped": reading.dropped(),
        "rows": rows,
    })
}

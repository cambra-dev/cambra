//! Rendering one live frame: what a run has produced, as of a tick.
//!
//! A frame is the values half of the inspector's wire, where
//! [`wire`](super::wire) is the program half. It is a pure function of the
//! recorder and the sources' windows, with no transport in it, so a host that
//! has no socket — a WebAssembly one — renders the same bytes the websocket
//! route sends.
//!
//! The shape is pinned by the frontend's own validator (`web/src/liveValidate.ts`).

use std::collections::HashMap;

use crate::ccl::provenance::NodeId;
use crate::interpreter::value_recorder::{RecordedRow, Recording, SharedRecorder, SourceWindow};

/// The JSON a publish sends: one entry per producer that produced this tick.
///
/// Collapsed here rather than at recording time. A producer pulled twice in one
/// tick answers the second call empty, and another answers with the same tile
/// twice, so the newest recording is the wrong one to send and merging the two
/// double-counts — see
/// [`ValueRecorder::latest_non_empty`](crate::interpreter::value_recorder::ValueRecorder::latest_non_empty).
pub fn render_frame(
    recorder: &SharedRecorder,
    sources: &[SourceWindow],
    tick: u64,
    generation: u64,
    published: u64,
    final_frame: bool,
) -> String {
    let recorder = recorder.borrow();
    let mut by_node: HashMap<u64, Vec<serde_json::Value>> = HashMap::new();
    for (node_id, producer_id) in recorder.producers() {
        let Some(node) = node_id else { continue };
        let Some((recording, stale)) = recorder.latest_non_empty(node_id, producer_id) else {
            continue;
        };
        by_node
            .entry(node_key(node))
            .or_default()
            .push(producer_json(recording, stale));
    }
    let mut by_node: Vec<(u64, Vec<serde_json::Value>)> = by_node.into_iter().collect();
    // Ascending `NodeId`, which is both stable and meaningful: an operator's id
    // is minted when it is constructed, and construction is bottom-up, so a
    // smaller id sits further upstream. A `HashMap` iteration is neither —
    // unsorted, this array arrived in a different order on every run.
    by_node.sort_by_key(|(node, _)| *node);
    let nodes: Vec<serde_json::Value> = by_node
        .into_iter()
        .map(|(node, mut producers)| {
            // A node's producers are keyed by an allocation counter, so ordering
            // by it is stable across ticks; a `HashMap` iteration is not.
            producers.sort_by_key(|p| p["producerId"].as_u64().unwrap_or(0));
            serde_json::json!({ "nodeId": node, "producers": producers })
        })
        .collect();
    // `published` counts frames rather than ticks, so a client that reconnects
    // or misses a wake can tell it is behind. A producer's own `seq` is the
    // finer signal, for a gap within one node's recordings.
    // `final` says the run is over and this frame is the last. A reader that
    // never sees one and then loses the socket has been disconnected; a reader
    // holding one knows the quiet is the end rather than a pause.
    // A source ships beside the operators rather than among them: it has no
    // producer and takes no `get`, so it carries a window rather than a
    // recording, and a click on a source resolves to its own graph node.
    let sources: Vec<serde_json::Value> = sources
        .iter()
        .map(|window| {
            serde_json::json!({
                "nodeId": window.node_id.map(node_key),
                "name": window.name,
                "total": window.total,
                "dropped": window.dropped(),
                "abandoned": window.abandoned,
                "rows": window.rows.iter().map(row_json).collect::<Vec<_>>(),
            })
        })
        .collect();
    serde_json::json!({
        "tick": tick,
        // Which version produced this. A client holding an older payload reads
        // node ids that a rebuilt operator no longer answers to, so it refetches
        // rather than drawing them against the wrong pane.
        "generation": generation,
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
fn row_json(row: &RecordedRow) -> serde_json::Value {
    serde_json::json!({
        "key": row.key,
        "value": row.value,
        "deleted": row.deleted,
    })
}

/// One producer's rows.
fn producer_json(recording: &Recording, stale: bool) -> serde_json::Value {
    let rows: Vec<serde_json::Value> = recording.rows.iter().map(row_json).collect();
    serde_json::json!({
        "producerId": recording.producer_id,
        "producer": recording.producer,
        "shape": recording.shape,
        "watermark": recording.watermark,
        "note": recording.note,
        "tick": recording.tick,
        "seq": recording.seq,
        "stale": stale,
        "total": recording.total,
        "dropped": recording.dropped(),
        "rows": rows,
    })
}

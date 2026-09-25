//! Rendering a probe frame: the JSON probe publishing sends.
//!
//! A pure function of the probe table and the sources' windows, so it is wire
//! and only its delivery is transport. Leaving it behind the websocket route would
//! have put a socket between a host with no sockets and the bytes it needs.
//!
//! The shape is declared once, as the `Serialize` types below.
//! `wire_check::assert_probe_frame_shape` pins it from outside: its key lists
//! are written out rather than derived from these types, so a field renamed
//! here fails there.

use std::collections::BTreeMap;

use crate::ccl::provenance::NodeId;
use crate::interpreter::value_probe::{Reading, ReadingRow, SharedProbeTable, SourceWindow};

/// What `/api/live` sends: the whole probe state, published after a pull that
/// carried rows.
#[derive(Clone, Debug, serde::Serialize)]
pub struct ProbeFrame {
    /// The driver tick the frame was published on.
    pub tick: u64,
    /// Frames published before and including this one, so a client that
    /// reconnects or misses a wake can tell it is behind. A reading's own `seq`
    /// is the finer signal, for a gap within one probe's readings.
    pub published: u64,
    /// Whether the run is over and this frame is the last. A reader that never
    /// sees one and then loses the socket has been disconnected; a reader
    /// holding one knows the quiet is the end rather than a pause.
    #[serde(rename = "final")]
    pub final_frame: bool,
    /// Every node with a probe that has carried rows, in ascending `NodeId`.
    pub nodes: Vec<ProbedNode>,
    /// Every source with a window. A source ships beside the operators rather
    /// than among them: it has no producer and takes no `get`.
    pub sources: Vec<SourceWindowWire>,
}

/// One operator's probes.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProbedNode {
    pub node_id: NodeId,
    /// In ascending `producer_id`.
    pub probes: Vec<ProbeWire>,
}

/// One probe's last row-carrying reading.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProbeWire {
    pub producer_id: usize,
    pub producer: String,
    pub shape: &'static str,
    pub watermark: Option<String>,
    pub note: Option<&'static str>,
    pub tick: u64,
    pub seq: u64,
    /// Whether newer readings of this probe carried nothing.
    ///
    /// A producer under a settling scheduler answers empty many times per row,
    /// so most probes are stale in most frames. How recent the rows are is this
    /// probe's `tick` against the frame's.
    pub stale: bool,
    pub total: usize,
    /// `total - rows.len()`.
    pub dropped: usize,
    pub rows: Vec<RowWire>,
}

/// One rendered row.
#[derive(Clone, Debug, serde::Serialize)]
pub struct RowWire {
    pub key: Option<String>,
    pub value: String,
    pub deleted: bool,
}

/// A source's retained window.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SourceWindowWire {
    /// The `IterateExtent`s over the source's domain. A source is not a graph
    /// node, so these are where a click on its window resolves.
    pub node_ids: Vec<NodeId>,
    pub name: String,
    pub total: usize,
    /// `total - rows.len()`.
    pub dropped: usize,
    pub rows: Vec<RowWire>,
}

/// Build the probe frame for the probe table's current state.
///
/// Each probe contributes its last flow rather than its newest reading. A
/// producer pulled twice in one tick answers the second call empty, and
/// another answers with the same tile twice, so the newest reading is the
/// wrong one to send and merging the two double-counts. See
/// [`ProbeTable::last_flow`](crate::interpreter::value_probe::ProbeTable::last_flow).
pub fn probe_frame(
    probes: &SharedProbeTable,
    sources: &[SourceWindow],
    tick: u64,
    published: u64,
    final_frame: bool,
) -> ProbeFrame {
    let probes = probes.borrow();
    // Ordered by `NodeId`, which is both stable and meaningful: an operator's id
    // is minted when it is constructed, and construction is bottom-up, so a
    // smaller id sits further upstream.
    let mut by_node: BTreeMap<NodeId, Vec<ProbeWire>> = BTreeMap::new();
    for (node_id, producer_id) in probes.probe_keys() {
        let Some(node) = node_id else { continue };
        let Some((reading, stale)) = probes.last_flow(node_id, producer_id) else {
            continue;
        };
        by_node
            .entry(node)
            .or_default()
            .push(probe_wire(reading, stale));
    }
    let nodes = by_node
        .into_iter()
        .map(|(node_id, mut node_probes)| {
            // A node's probes are keyed by the producer's allocation counter, so
            // ordering by it is stable across ticks; a `HashMap` iteration is not.
            node_probes.sort_by_key(|probe| probe.producer_id);
            ProbedNode {
                node_id,
                probes: node_probes,
            }
        })
        .collect();
    let sources = sources
        .iter()
        .map(|window| SourceWindowWire {
            node_ids: window.node_ids.clone(),
            name: window.name.clone(),
            total: window.total,
            dropped: window.dropped(),
            rows: window.rows.iter().map(row_wire).collect(),
        })
        .collect();
    ProbeFrame {
        tick,
        published,
        final_frame,
        nodes,
        sources,
    }
}

/// [`probe_frame`], serialized: the text a publish sends.
pub fn render_probe_frame(
    probes: &SharedProbeTable,
    sources: &[SourceWindow],
    tick: u64,
    published: u64,
    final_frame: bool,
) -> String {
    serde_json::to_string(&probe_frame(probes, sources, tick, published, final_frame))
        .expect("a probe frame holds only strings, numbers and booleans")
}

fn row_wire(row: &ReadingRow) -> RowWire {
    RowWire {
        key: row.key.clone(),
        value: row.value.clone(),
        deleted: row.deleted,
    }
}

fn probe_wire(reading: &Reading, stale: bool) -> ProbeWire {
    ProbeWire {
        producer_id: reading.producer_id,
        producer: reading.producer.to_string(),
        shape: reading.shape,
        watermark: reading.watermark.clone(),
        note: reading.note,
        tick: reading.tick,
        seq: reading.seq,
        stale,
        total: reading.total,
        dropped: reading.dropped(),
        rows: reading.rows.iter().map(row_wire).collect(),
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, collections::HashMap, rc::Rc};

    use bit_set::BitSet;
    use serde_json::Value;

    use super::*;
    use crate::inspector_server::wire_check::assert_probe_frame_shape;
    use crate::interpreter::{
        ColumnValue, Value as CellValue,
        tiling::{Predicate, Tile},
        value_probe::{ProbeTable, ROWS_PER_READING, render_source_window},
    };

    /// The committed frame, shared with the frontend's tests once a reader of
    /// `/api/live` exists there.
    const GOLDEN: &str = "web/src/__fixtures__/probe_frame.json";

    fn strings(values: &[&str]) -> ColumnValue {
        ColumnValue::Strings(values.iter().map(|s| (*s).into()).collect())
    }

    fn collection(values: &[&str], deleted: &[usize]) -> Tile {
        Tile::data_function(
            ColumnValue::UInts((0..values.len()).collect()),
            Box::new(Tile::Scalar(strings(values))),
            Predicate::True,
            deleted.iter().copied().collect::<BitSet>(),
        )
    }

    /// Replace each id `minted` holds with its position in `minted`, counting
    /// from 1, so the frame is the same bytes in every process. An id `minted`
    /// does not hold fails: the frame named a node the test never built.
    fn renumber(v: &mut Value, minted: &HashMap<u64, u64>) {
        let renumbered = |id: &Value| {
            let raw = id.as_u64().expect("an id is a number");
            let ordinal = minted.get(&raw).unwrap_or_else(|| {
                panic!("the frame names node {raw}, which the test never minted")
            });
            Value::from(*ordinal)
        };
        for node in v["nodes"].as_array_mut().expect("nodes") {
            node["nodeId"] = renumbered(&node["nodeId"]);
        }
        for source in v["sources"].as_array_mut().expect("sources") {
            for id in source["nodeIds"].as_array_mut().expect("nodeIds") {
                *id = renumbered(id);
            }
        }
    }

    /// One frame covering every row shape the pane renders: a stale probe, a
    /// deleted row, a record codomain, a store's changelog, a reading truncated
    /// past the row cap, two probes on one node, and a source window.
    #[test]
    fn a_probe_frame_matches_its_golden() {
        let ids: Vec<NodeId> = (0..4).map(|_| NodeId::fresh()).collect();
        let probes = Rc::new(RefCell::new(ProbeTable::with_defaults()));
        {
            let mut table = probes.borrow_mut();
            table.set_tick(3);
            table.observe(
                Some(ids[0]),
                1,
                "IterateExtent#1",
                &collection(&["a", "b"], &[]),
            );
            table.observe(Some(ids[0]), 1, "IterateExtent#1", &collection(&[], &[]));
            table.observe(
                Some(ids[1]),
                1,
                "Restrict#1",
                &collection(&["a", "skip"], &[1]),
            );
            table.observe(Some(ids[1]), 2, "Restrict#2", &collection(&["b"], &[]));
            let mut fields = HashMap::new();
            fields.insert("text".to_string(), Tile::Scalar(strings(&["a"])));
            fields.insert("tagged".to_string(), Tile::Scalar(strings(&["> a"])));
            table.observe(
                Some(ids[2]),
                1,
                "FanIn#1",
                &Tile::data_function(
                    ColumnValue::UInts(vec![0]),
                    Box::new(Tile::Record(fields)),
                    Predicate::True,
                    BitSet::new(),
                ),
            );
            table.set_tick(4);
            table.observe(
                Some(ids[3]),
                1,
                "Commit#1",
                &Tile::Store {
                    changes: ColumnValue::UInts(vec![0, 1]),
                    deltas: ColumnValue::Variants(vec![CellValue::Unit, CellValue::Unit]),
                    frontier: Predicate::True,
                    terminal: true,
                    closed_keys: Vec::new(),
                },
            );
            let long: Vec<String> = (0..ROWS_PER_READING + 2).map(|i| format!("v{i}")).collect();
            let long: Vec<&str> = long.iter().map(String::as_str).collect();
            table.observe(Some(ids[3]), 2, "MapResult#1", &collection(&long, &[]));
        }
        let window = render_source_window(
            vec![ids[0]],
            "stdin",
            &ColumnValue::UInts(vec![1]),
            &strings(&["b"]),
            ROWS_PER_READING,
        );

        let mut frame = serde_json::to_value(probe_frame(&probes, &[window], 4, 2, false))
            .expect("a probe frame serializes");
        assert_probe_frame_shape(&frame);
        let minted: HashMap<u64, u64> = ids
            .iter()
            .zip(1..)
            .map(|(id, ordinal)| (id.as_u64(), ordinal))
            .collect();
        renumber(&mut frame, &minted);
        let rendered = serde_json::to_string_pretty(&frame).expect("pretty") + "\n";

        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(GOLDEN);
        if std::env::var_os("CAMBRA_BLESS").is_some() {
            std::fs::write(&path, &rendered).expect("writing the golden frame");
        }
        let golden = std::fs::read_to_string(&path).unwrap_or_default();
        assert_eq!(
            rendered, golden,
            "the probe frame differs from {GOLDEN}; if the change is intended, re-run \
             with CAMBRA_BLESS=1 and review the fixture's diff"
        );
    }
}

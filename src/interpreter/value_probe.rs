//! Probes: what each producer returned, rendered and bounded, for the live
//! value pane.
//!
//! A probe is attached to every producer built while a [`ProbeSession`] is
//! live, and takes a [`Reading`] of each result
//! [`TileProducer::get`](crate::interpreter::tile_operators::TileProducer::get)
//! returns. Every operator-to-operator handoff passes through `get`, so a probe
//! observes a call the program already makes. Calling `get` from an observer is
//! not an alternative: it takes `&mut self`, and `MemoProducer::get_impl`
//! releases its input on what it just took, so the observer would discard the
//! data it was reading.
//!
//! "Probe" here is an observation point on an operator's output. It is unrelated
//! to the probe side of a hash join (`JoinPlan::Hash`).
//!
//! A reading is rendered and truncated when it is taken. The count of readings
//! per probe does not bound their size, since one `DataFunction` off a join
//! carries as many rows as the join produced. The row cap is what bounds the
//! footprint to `probes × (readings + 1) × rows`. Rendering happens on the
//! driver thread, and no tile is cloned.
//!
//! A pane asks what flowed through a node, which a ring of recent readings
//! cannot answer: empty readings outnumber row-carrying ones by orders of
//! magnitude. Each probe therefore holds its last row-carrying reading outside
//! the ring.

use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::{
    ccl::provenance::NodeId,
    interpreter::{tiling::Tile, types::ColumnValue},
};

/// Rows kept per reading.
pub const ROWS_PER_READING: usize = 32;

/// Readings kept in each probe's ring.
pub const READINGS_PER_PROBE: usize = 16;

/// A shared handle to the probe table, held by every producer built while a
/// [`ProbeSession`] is live.
// shared-state-ok: the observation boundary. A producer writes what it has
// already returned to its consumer, rendered; nothing reads it back into the
// graph, and no operator reaches another operator's rows. Shared because the
// driver reads one table and every producer writes it, and the producer graph
// has no `&self` traversal that would let the driver collect per-producer
// buffers instead.
pub type SharedProbeTable = Rc<RefCell<ProbeTable>>;

/// One row of a probed tile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadingRow {
    /// The domain key this row sits at, or `None` for a shape whose positions
    /// are implicit.
    pub key: Option<String>,
    /// The value at that position, rendered.
    pub value: String,
    /// Whether the tile marks this position deleted.
    ///
    /// Rendered rather than omitted: a `DataFunction` carries `deleted`
    /// alongside a column that still holds the value, and a `Restrict` and the
    /// `Memo` below it disagree on that representation for the same rows.
    /// Hiding it makes two producers look alike where they differ.
    pub deleted: bool,
}

/// What one `get` returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reading {
    /// The driver tick the call happened in.
    pub tick: u64,
    /// Position in the probe table's total order, so a consumer can tell
    /// "nothing arrived" from "readings were evicted".
    pub seq: u64,
    /// The operator that built the producer, or `None` for a producer built
    /// outside any subscribe.
    pub node_id: Option<NodeId>,
    /// The producer instance, since one operator can build several.
    pub producer_id: usize,
    /// The producer's display name, e.g. `"MapResultWithSource#1"`.
    pub producer: String,
    /// The tile's variant name.
    pub shape: &'static str,
    /// The tile's `domain_predicate` in its `Debug` form, which is the progress
    /// signal: `False`, then `LessThanEq(uN)`, then `True`. `None` for a shape
    /// carrying no such region.
    pub watermark: Option<String>,
    /// Why this reading carries no rows, when the shape is one that is not
    /// rendered.
    pub note: Option<&'static str>,
    /// The rows kept, oldest first.
    pub rows: Vec<ReadingRow>,
    /// Rows the tile held, of which `rows` is the last `rows.len()`.
    pub total: usize,
}

impl Reading {
    /// Rows the tile held that this reading does not carry.
    pub fn dropped(&self) -> usize {
        self.total.saturating_sub(self.rows.len())
    }

    /// Whether the call returned nothing. A producer pulled twice in one tick
    /// answers the second call empty.
    pub fn is_empty(&self) -> bool {
        self.total == 0
    }
}

/// Every attached probe, keyed by `(operator, producer instance)`.
///
/// Keyed by instance as well as operator because one operator can build
/// several producers. Which of them a reader is shown is a rendering choice,
/// and keeping both keys leaves it open.
pub struct ProbeTable {
    tick: u64,
    next_seq: u64,
    next_flow: u64,
    rows_per_reading: usize,
    readings_per_probe: usize,
    probes: HashMap<(Option<NodeId>, usize), Probe>,
}

/// One producer's probe: its recent readings, and the last reading that
/// carried rows.
///
/// The two answer different questions. `recent` answers what the producer has
/// been doing, empty readings included, and is where a watermark's progress is
/// read. `last_flow` answers what flowed through it. It sits outside the ring
/// because an operator under a settling scheduler answers empty hundreds of
/// times per row, so a ring deep enough to hold the row would have to be deeper
/// than the busiest pass.
///
/// `last_flow` is one reading under the same row cap as any other, so the
/// footprint stays `probes × (readings + 1) × rows`.
#[derive(Default)]
struct Probe {
    /// Recent readings, empty or not, oldest first.
    recent: VecDeque<Reading>,
    /// The newest reading that carried rows, which `recent` may have evicted.
    last_flow: Option<Reading>,
}

impl ProbeTable {
    /// A probe table with the given caps.
    pub fn new(rows_per_reading: usize, readings_per_probe: usize) -> Self {
        Self {
            tick: 0,
            next_seq: 0,
            next_flow: 0,
            rows_per_reading,
            readings_per_probe,
            probes: HashMap::new(),
        }
    }

    /// A probe table with [`ROWS_PER_READING`] and [`READINGS_PER_PROBE`].
    pub fn with_defaults() -> Self {
        Self::new(ROWS_PER_READING, READINGS_PER_PROBE)
    }

    /// Name the tick that subsequent readings belong to.
    ///
    /// The driver advances this once per pull, so every reading taken during
    /// one `get` of the root producer carries the same tick, including the
    /// several a shared subtree produces when it is pulled once per consumer.
    pub fn set_tick(&mut self, tick: u64) {
        self.tick = tick;
    }

    /// The tick readings are currently attributed to.
    pub fn tick(&self) -> u64 {
        self.tick
    }

    /// Readings that carried rows, since this table was built. Monotone.
    ///
    /// Probe publishing compares this against the count it last published at.
    /// A count of all readings would advance on every poll of the driver's
    /// sink loop, since a poll that delivers nothing still takes an empty
    /// reading from every producer it pulls.
    pub fn flows(&self) -> u64 {
        self.next_flow
    }

    /// Render `tile` as a reading of this producer's probe, evicting the
    /// probe's oldest reading once the ring is full.
    pub fn observe(
        &mut self,
        node_id: Option<NodeId>,
        producer_id: usize,
        producer: &str,
        tile: &Tile,
    ) {
        let rendered = render(tile, self.rows_per_reading);
        let reading = Reading {
            tick: self.tick,
            seq: self.next_seq,
            node_id,
            producer_id,
            producer: producer.to_string(),
            shape: rendered.shape,
            watermark: rendered.watermark,
            note: rendered.note,
            rows: rendered.rows,
            total: rendered.total,
        };
        self.next_seq += 1;
        let carried_rows = !reading.is_empty();
        if carried_rows {
            self.next_flow += 1;
        }

        let cap = self.readings_per_probe;
        let probe = self.probes.entry((node_id, producer_id)).or_default();
        if carried_rows {
            probe.last_flow = Some(reading.clone());
        }
        if probe.recent.len() == cap {
            probe.recent.pop_front();
        }
        probe.recent.push_back(reading);
    }

    /// Detach a producer's probe, dropping its readings.
    ///
    /// Called from [`ProducerBase`](crate::interpreter::tile_operators::ProducerBase)'s
    /// `Drop`, so a replaced version's probes go at the moment its producers
    /// do. `LiveProgram::reload` tears down exactly the producers it could not
    /// keep, so a kept operator's producer is never dropped and its readings
    /// continue across the swap.
    ///
    /// Nothing else detaches a probe. A running producer whose probe was
    /// detached would read on the wire as a node that has produced nothing,
    /// which is what an idle node looks like.
    pub fn detach(&mut self, node_id: Option<NodeId>, producer_id: usize) {
        self.probes.remove(&(node_id, producer_id));
    }

    /// Every reading in one probe's ring, oldest first.
    ///
    /// An iterator rather than a slice: the backing `VecDeque` wraps once it has
    /// evicted, so its readings are not contiguous.
    pub fn readings(
        &self,
        node_id: Option<NodeId>,
        producer_id: usize,
    ) -> impl Iterator<Item = &Reading> + '_ {
        self.probes
            .get(&(node_id, producer_id))
            .into_iter()
            .flat_map(|probe| probe.recent.iter())
    }

    /// The key of every attached probe.
    pub fn probe_keys(&self) -> impl Iterator<Item = (Option<NodeId>, usize)> + '_ {
        self.probes.keys().copied()
    }

    /// One probe's newest reading that carried rows, and whether newer readings
    /// exist that carried nothing.
    ///
    /// Read from [`Probe::last_flow`], which the ring cannot evict, so a
    /// producer that answered with rows once and empty a thousand times since
    /// still reports the rows.
    ///
    /// The winning reading is chosen, not merged: a producer pulled twice in
    /// one tick answers the second call empty, and another answers with the
    /// same tile twice, so neither last-write-wins nor `Tile::merge` is
    /// correct. Two consumers pulling with different projection guards could
    /// return disjoint partial answers, which this drops; the ring shows that
    /// case if it occurs.
    pub fn last_flow(
        &self,
        node_id: Option<NodeId>,
        producer_id: usize,
    ) -> Option<(&Reading, bool)> {
        let probe = self.probes.get(&(node_id, producer_id))?;
        let found = probe.last_flow.as_ref()?;
        let stale = probe
            .recent
            .back()
            .is_some_and(|newest| found.seq != newest.seq);
        Some((found, stale))
    }

    /// Readings kept in every probe's ring, in total.
    pub fn len(&self) -> usize {
        self.probes.values().map(|probe| probe.recent.len()).sum()
    }

    /// Whether no probe holds a reading.
    pub fn is_empty(&self) -> bool {
        self.probes.values().all(|probe| probe.recent.is_empty())
    }
}

/// A source's retained window, rendered.
///
/// Not a probe reading: a source has no producer and takes no `get`. Its window is
/// what has arrived and not yet been released, read through `&self`, so
/// sampling it moves nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceWindow {
    /// The `IterateExtent`s over the source's domain, which is what a click on
    /// the window resolves to: a source is not a node of the operator graph.
    pub node_ids: Vec<NodeId>,
    /// The source's registered name, e.g. `"stdin"`.
    pub name: String,
    /// The retained keys and their values, truncated to the last `limit`.
    pub rows: Vec<ReadingRow>,
    /// Keys the window held, of which `rows` is the last `rows.len()`.
    pub total: usize,
}

impl SourceWindow {
    /// Keys the window held that this does not carry.
    pub fn dropped(&self) -> usize {
        self.total.saturating_sub(self.rows.len())
    }
}

/// Render the last `limit` of a source's retained window.
///
/// `keys` and `values` come from the source's own `retained_keys` and `get`,
/// both `&self`. Truncation follows the same rule a reading uses: a source
/// domain is index-ordered, so the last keys are the most recent arrivals.
pub fn render_source_window(
    node_ids: Vec<NodeId>,
    name: &str,
    keys: &ColumnValue,
    values: &ColumnValue,
    limit: usize,
) -> SourceWindow {
    let total = keys.len();
    SourceWindow {
        node_ids,
        name: name.to_string(),
        rows: tail(total, limit)
            .map(|i| ReadingRow {
                key: Some(cell(keys, i)),
                value: cell(values, i),
                deleted: false,
            })
            .collect(),
        total,
    }
}

/// A rendered tile, before it is stamped with tick and sequence.
struct Rendered {
    shape: &'static str,
    watermark: Option<String>,
    note: Option<&'static str>,
    rows: Vec<ReadingRow>,
    total: usize,
}

/// The last `limit` rows of `tile`, rendered.
fn render(tile: &Tile, limit: usize) -> Rendered {
    match tile {
        Tile::Scalar(column) => {
            let total = column.len();
            Rendered {
                shape: "Scalar",
                watermark: None,
                note: None,
                rows: tail(total, limit)
                    .map(|i| ReadingRow {
                        key: None,
                        value: cell(column, i),
                        deleted: false,
                    })
                    .collect(),
                total,
            }
        }
        Tile::Record(fields) => {
            let mut names: Vec<&String> = fields.keys().collect();
            // `Tile::Record` is a `HashMap`, whose iteration order varies
            // between runs of one program. Sorting is what makes a rendering
            // reproducible.
            names.sort();
            let total = names.len();
            Rendered {
                shape: "Record",
                watermark: None,
                note: None,
                rows: names
                    .into_iter()
                    .skip(total.saturating_sub(limit))
                    .map(|name| ReadingRow {
                        key: Some(name.clone()),
                        value: one_level(&fields[name], 0),
                        deleted: false,
                    })
                    .collect(),
                total,
            }
        }
        Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
            ..
        } => {
            let total = domain.len();
            Rendered {
                shape: "DataFunction",
                watermark: Some(format!("{domain_predicate:?}")),
                note: None,
                rows: tail(total, limit)
                    .map(|i| ReadingRow {
                        key: Some(cell(domain, i)),
                        value: one_level(codomain, i),
                        deleted: deleted.contains(i),
                    })
                    .collect(),
                total,
            }
        }
        Tile::Aggregation {
            kind,
            accumulator,
            terminal,
        } => Rendered {
            shape: "Aggregation",
            watermark: Some(format!("terminal: {}", cell(terminal, 0))),
            note: None,
            rows: vec![ReadingRow {
                key: Some(format!("{kind:?}")),
                value: one_level(accumulator, 0),
                deleted: false,
            }],
            total: 1,
        },
        Tile::Store {
            changes,
            deltas,
            frontier,
            ..
        } => {
            // The change events themselves, rather than the step function they
            // decide. A store is right-continuous over its whole decided prefix,
            // so reading it *at a tick* means folding every earlier change; but
            // what a reader asks of a slot is what was written to it and when,
            // and that is the changelog unfolded.
            let total = changes.len();
            Rendered {
                shape: "Store",
                watermark: Some(format!("{frontier:?}")),
                note: None,
                rows: tail(total, limit)
                    .map(|i| ReadingRow {
                        key: Some(cell(changes, i)),
                        value: cell(deltas, i),
                        deleted: false,
                    })
                    .collect(),
                total,
            }
        }
    }
}

/// The last `limit` of `total` positions, oldest first.
///
/// A source-derived domain is index-ordered, so its last positions are its most
/// recent rows.
fn tail(total: usize, limit: usize) -> std::ops::Range<usize> {
    total.saturating_sub(limit)..total
}

/// One position of a column, or a marker when the column is shorter than the
/// domain beside it.
fn cell(column: &ColumnValue, i: usize) -> String {
    if i < column.len() {
        column.index_at(i).to_string()
    } else {
        "<absent>".to_string()
    }
}

/// A codomain position, one level deep.
///
/// A nested collection renders as its row's key count rather than recursing: a
/// summary that walks a whole subtree is not bounded by the row cap.
fn one_level(tile: &Tile, i: usize) -> String {
    match tile {
        Tile::Scalar(column) => cell(column, i),
        Tile::Record(fields) => {
            let mut names: Vec<&String> = fields.keys().collect();
            names.sort();
            let rendered: Vec<String> = names
                .into_iter()
                .map(|name| format!("{name}: {}", one_level(&fields[name], i)))
                .collect();
            format!("({})", rendered.join(", "))
        }
        Tile::DataFunction { .. } if i < tile.rows() => {
            let (start, end) = tile.row_run(i);
            format!("<{} entries>", end - start)
        }
        Tile::DataFunction { .. } => "<absent>".to_string(),
        Tile::Aggregation { accumulator, .. } => one_level(accumulator, i),
        Tile::Store { .. } => "<Store>".to_string(),
    }
}

// The probe table every producer built during a session attaches its probe to.
//
// `ProducerBase::new` is called from inside producer constructors, which take no
// context parameter. The same argument `OperatorBase::new` makes for
// `ACTIVE_GRAPH`, and the session is live only while the graph is being
// subscribed: at runtime each producer uses the handle it was built with.
// shared-state-ok: a probe table attached for the duration of a subscribe. What
// crosses it is a handle, never a value passed between operators.
thread_local! {
    // shared-state-ok: the session's handle itself, for the reason on the macro
    // above. The declaration matches the checker's ambient-state shape twice —
    // once at the macro, once at the `static` — and its upward scan stops at
    // `thread_local! {`, which is neither a comment nor an attribute, so the
    // note above does not reach this line.
    static SESSION: RefCell<Option<SharedProbeTable>> = const { RefCell::new(None) };
}

/// Attach a probe writing to `probes` to every producer built until the
/// returned session drops.
///
/// Held across `LiveProgram::start` and `LiveProgram::reload`, which is where
/// subscribing happens.
pub fn attach_probes(probes: SharedProbeTable) -> ProbeSession {
    SESSION.with(|slot| {
        let previous = slot.borrow_mut().replace(probes);
        debug_assert!(
            previous.is_none(),
            "a probe session is already live; sessions are per-compile and do not nest",
        );
        ProbeSession
    })
}

/// The probe table a producer built now attaches to, if a session is live.
pub(crate) fn session_probes() -> Option<SharedProbeTable> {
    SESSION.with(|slot| slot.borrow().clone())
}

/// Ends probe attachment on drop.
pub struct ProbeSession;

impl Drop for ProbeSession {
    fn drop(&mut self) {
        SESSION.with(|slot| *slot.borrow_mut() = None);
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;

    use super::*;
    use crate::interpreter::{tiling::Predicate, types::Value};

    fn strings(values: &[&str]) -> ColumnValue {
        ColumnValue::Strings(values.iter().map(|s| (*s).into()).collect())
    }

    fn uints(values: &[usize]) -> ColumnValue {
        ColumnValue::UInts(values.to_vec())
    }

    fn collection(domain: &[usize], values: &[&str], deleted: &[usize]) -> Tile {
        Tile::data_function(
            uints(domain),
            Box::new(Tile::Scalar(strings(values))),
            Predicate::True,
            deleted.iter().copied().collect::<BitSet>(),
        )
    }

    fn values(reading: &Reading) -> Vec<String> {
        reading.rows.iter().map(|r| r.value.clone()).collect()
    }

    #[test]
    fn a_reading_of_a_collection_keeps_its_keys_values_and_watermark() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "MapResultWithSource#1",
            &collection(&[0, 1], &["a", "b"], &[]),
        );

        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "DataFunction");
        assert_eq!(reading.watermark.as_deref(), Some("True"));
        assert_eq!(
            reading.rows,
            vec![
                ReadingRow {
                    key: Some("u0".into()),
                    value: "\"a\"".into(),
                    deleted: false
                },
                ReadingRow {
                    key: Some("u1".into()),
                    value: "\"b\"".into(),
                    deleted: false
                },
            ]
        );
        assert_eq!(reading.total, 2);
        assert_eq!(reading.dropped(), 0);
    }

    /// A `Restrict` marks a filtered row deleted while its column still holds
    /// the value, and the `Memo` below it has compacted the same rows away.
    /// Rendering the mark is what keeps the two distinguishable.
    #[test]
    fn a_deleted_position_is_rendered_and_marked() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "Restrict#1",
            &collection(&[0, 1, 2], &["a", "skip", "c"], &[1]),
        );

        let reading = probes.readings(None, 1).next().expect("observed");
        let marked: Vec<bool> = reading.rows.iter().map(|r| r.deleted).collect();
        assert_eq!(marked, vec![false, true, false]);
        assert_eq!(values(reading), vec!["\"a\"", "\"skip\"", "\"c\""]);
    }

    /// A producer answers empty far more often than it answers with rows — an
    /// operator under a settling scheduler does so hundreds of times per row —
    /// so a probe's ring of recent readings cannot be what the pane reads.
    /// Without a slot the ring cannot evict, every such operator reports as
    /// though it had never been pulled.
    #[test]
    fn rows_survive_more_empty_readings_than_the_probe_ring_can_hold() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "Restrict#1", &collection(&[0], &["a"], &[]));
        for _ in 0..READINGS_PER_PROBE * 4 {
            probes.observe(None, 1, "Restrict#1", &collection(&[], &[], &[]));
        }

        let (reading, stale) = probes.last_flow(None, 1).expect("the rows are kept");
        assert_eq!(values(reading), vec!["\"a\""]);
        assert!(stale, "newer calls carried nothing, so the rows are stale");
        assert!(
            probes.readings(None, 1).all(Reading::is_empty),
            "the ring itself has evicted the row-carrying call",
        );
    }

    /// Probe publishing gates on readings that carried rows: a driver polling on
    /// a timer takes an empty reading per poll, and a frame published on one of
    /// those re-samples every source window after the pull that drained it.
    #[test]
    fn only_a_reading_carrying_rows_counts_as_a_flow() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "Restrict#1", &collection(&[], &[], &[]));
        assert_eq!(probes.flows(), 0);

        probes.observe(None, 1, "Restrict#1", &collection(&[0], &["a"], &[]));
        assert_eq!(probes.flows(), 1);
    }

    #[test]
    fn a_reading_keeps_the_last_rows_and_counts_the_rest() {
        let mut probes = ProbeTable::new(2, 4);
        probes.observe(
            None,
            1,
            "P#1",
            &collection(&[0, 1, 2, 3], &["a", "b", "c", "d"], &[]),
        );

        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(
            values(reading),
            vec!["\"c\"", "\"d\""],
            "the most recent rows"
        );
        assert_eq!(reading.total, 4);
        assert_eq!(reading.dropped(), 2);
    }

    #[test]
    fn a_probe_keeps_only_its_last_readings() {
        let mut probes = ProbeTable::new(8, 2);
        for i in 0..5 {
            probes.set_tick(i);
            probes.observe(None, 1, "P#1", &Tile::Scalar(strings(&["v"])));
        }

        let ticks: Vec<u64> = probes.readings(None, 1).map(|r| r.tick).collect();
        assert_eq!(ticks, vec![3, 4], "the cap evicts from the front");
        assert_eq!(probes.len(), 2);
    }

    /// The shape the trace shows: a shared subtree is pulled once per consumer,
    /// and `IterateExtent` answers the second call empty. Rendering the newest
    /// reading would show nothing.
    #[test]
    fn a_producer_answering_empty_on_a_second_pull_still_reads_as_its_data() {
        let mut probes = ProbeTable::with_defaults();
        probes.set_tick(7);
        probes.observe(None, 1, "IterateExtent#1", &collection(&[0], &["a"], &[]));
        probes.observe(None, 1, "IterateExtent#1", &collection(&[], &[], &[]));

        let (reading, stale) = probes.last_flow(None, 1).expect("observed");
        assert_eq!(values(reading), vec!["\"a\""]);
        assert!(stale, "a newer reading carried nothing");
    }

    /// The other shape in the same trace: a `Memo` replays its cache, so the
    /// two calls carry the same tile. Merging them would render `["a", "a"]`.
    #[test]
    fn a_producer_answering_twice_alike_is_not_doubled() {
        let mut probes = ProbeTable::with_defaults();
        probes.set_tick(7);
        probes.observe(None, 1, "Memo#2", &collection(&[0], &["a"], &[]));
        probes.observe(None, 1, "Memo#2", &collection(&[0], &["a"], &[]));

        let (reading, stale) = probes.last_flow(None, 1).expect("observed");
        assert_eq!(values(reading), vec!["\"a\""]);
        assert!(!stale, "the newest reading carried the data");
    }

    #[test]
    fn one_operator_with_two_producers_keeps_them_apart() {
        let node = Some(NodeId::fresh());
        let mut probes = ProbeTable::with_defaults();
        probes.observe(node, 1, "FanOut#1", &Tile::Scalar(strings(&["left"])));
        probes.observe(node, 2, "FanOut#1", &Tile::Scalar(strings(&["right"])));

        assert_eq!(probes.probe_keys().count(), 2);
        assert_eq!(
            values(probes.readings(node, 1).next().unwrap()),
            vec!["\"left\""]
        );
        assert_eq!(
            values(probes.readings(node, 2).next().unwrap()),
            vec!["\"right\""]
        );
    }

    /// `Tile::Record` is a `HashMap`, whose iteration order varies between runs
    /// of one program, so an unsorted rendering is not reproducible.
    #[test]
    fn a_record_codomain_renders_its_fields_in_sorted_order() {
        let mut fields = HashMap::new();
        fields.insert("text".to_string(), Tile::Scalar(strings(&["a"])));
        fields.insert("tagged".to_string(), Tile::Scalar(strings(&["> a"])));
        let tile = Tile::data_function(
            uints(&[0]),
            Box::new(Tile::Record(fields)),
            Predicate::True,
            BitSet::new(),
        );

        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "FanIn#1", &tile);
        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(values(reading), vec!["(tagged: \"> a\", text: \"a\")"]);
    }

    /// A nested collection renders as the size of the row's group, which bounds
    /// the cost of a cell by the row cap however deep the value is.
    #[test]
    fn a_nested_collection_renders_its_group_size() {
        let inner = Tile::grouped(
            uints(&[0, 2]),
            uints(&[0, 1, 0]),
            Box::new(Tile::Scalar(strings(&["a", "b", "c"]))),
            Predicate::True,
            BitSet::new(),
        );
        let tile = Tile::data_function(
            uints(&[0, 1]),
            Box::new(inner),
            Predicate::True,
            BitSet::new(),
        );

        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "GroupBy#1", &tile);
        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "DataFunction");
        assert_eq!(values(reading), vec!["<2 entries>", "<1 entries>"]);
    }

    #[test]
    fn a_reading_of_a_store_keeps_its_changes_and_the_frontier_it_decided() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "Commit#1",
            &Tile::Store {
                changes: uints(&[0, 1]),
                deltas: ColumnValue::Variants(vec![Value::Unit, Value::Unit]),
                frontier: Predicate::True,
                terminal: true,
                closed_keys: Vec::new(),
            },
        );

        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "Store");
        assert_eq!(reading.total, 2);
        assert_eq!(
            reading
                .rows
                .iter()
                .map(|r| r.key.clone())
                .collect::<Vec<_>>(),
            vec![Some("u0".into()), Some("u1".into())],
            "a store's rows are its change ticks",
        );
        assert_eq!(reading.watermark.as_deref(), Some("True"));
    }

    /// A source window renders keys against values and truncates to the tail,
    /// the same rule a reading uses: a source domain is index-ordered, so the
    /// last keys are the most recent arrivals.
    #[test]
    fn a_source_window_renders_the_last_keys_and_counts_the_rest() {
        let keys = uints(&[2, 3, 4]);
        let values = strings(&["c", "d", "e"]);
        let window = render_source_window(Vec::new(), "stdin", &keys, &values, 2);

        assert_eq!(window.name, "stdin");
        assert_eq!(window.total, 3);
        assert_eq!(window.dropped(), 1);
        assert_eq!(
            window.rows,
            vec![
                ReadingRow {
                    key: Some("u3".into()),
                    value: "\"d\"".into(),
                    deleted: false
                },
                ReadingRow {
                    key: Some("u4".into()),
                    value: "\"e\"".into(),
                    deleted: false
                },
            ]
        );
    }

    /// A converged source holds nothing: a universal release closes the buffer.
    #[test]
    fn an_empty_source_window_carries_no_rows() {
        let window = render_source_window(
            Vec::new(),
            "stdin",
            &ColumnValue::from_uints(Vec::new()),
            &strings(&[]),
            8,
        );
        assert_eq!(window.total, 0);
        assert_eq!(window.dropped(), 0);
        assert!(window.rows.is_empty());
    }

    #[test]
    fn a_sequence_number_orders_every_reading() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "A#1", &Tile::Scalar(strings(&["x"])));
        probes.observe(None, 2, "B#1", &Tile::Scalar(strings(&["y"])));
        probes.observe(None, 1, "A#1", &Tile::Scalar(strings(&["z"])));

        let seqs: Vec<u64> = probes.readings(None, 1).map(|r| r.seq).collect();
        assert_eq!(seqs, vec![0, 2], "the gap is B's reading");
    }
}

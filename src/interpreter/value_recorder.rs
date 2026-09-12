//! What each producer returned, rendered and bounded, for the live value pane.
//!
//! Every operator-to-operator handoff passes through
//! [`TileProducer::get`](crate::interpreter::tile_operators::TileProducer::get),
//! so recording its result there observes a call the program already makes.
//! Calling `get` from an observer is not an alternative: it takes `&mut self`,
//! and `MemoProducer::get_impl` releases its input on what it just took, so a
//! read would discard the data it was reading.
//!
//! A recording is rendered and truncated when it is taken. A count of
//! recordings bounds how many there are and not how large they are — one
//! `SealedFunction` off a join carries as many rows as the join produced — so
//! the row cap is what makes the footprint `producers × recordings × rows`.
//! Rendering on the driver thread is the cost of that bound, and it is also why
//! no tile is cloned.
//!
//! What a pane asks of a node is what flowed through it, which a ring of recent
//! calls cannot answer on its own: empties outnumber row-carrying answers by
//! orders of magnitude, so each producer holds its last row-carrying recording
//! outside the ring.

use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    rc::Rc,
};

use crate::{
    ccl::provenance::NodeId,
    interpreter::{
        tiling::Tile,
        types::{ColumnValue, Value},
    },
};

/// Rows kept per recording.
pub const DEFAULT_ROWS_PER_RECORDING: usize = 32;

/// Recordings kept per producer.
pub const DEFAULT_RECORDINGS_PER_PRODUCER: usize = 16;

/// A shared handle to the recorder, held by every producer built while a
/// [`RecorderSession`] is installed.
// shared-state-ok: the observation boundary. A producer writes what it has
// already returned to its consumer, rendered; nothing reads it back into the
// graph, and no operator reaches another operator's rows. Shared because the
// driver reads one store and every producer writes it, and the producer graph
// has no `&self` traversal that would let the driver collect per-producer
// buffers instead.
pub type SharedRecorder = Rc<RefCell<ValueRecorder>>;

/// One row of a recorded tile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordedRow {
    /// The domain key this row sits at, or `None` for a shape whose positions
    /// are implicit.
    pub key: Option<String>,
    /// The value at that position, rendered.
    pub value: String,
    /// Whether the tile marks this position deleted.
    ///
    /// Rendered rather than omitted: a `SealedFunction` carries `deleted`
    /// alongside a column that still holds the value, and a `Restrict` and the
    /// `Memo` below it disagree on that representation for the same rows.
    /// Hiding it makes two producers look alike where they differ.
    pub deleted: bool,
}

/// What one `get` returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Recording {
    /// The driver tick the call happened in.
    pub tick: u64,
    /// Position in the recorder's total order, so a consumer can tell "nothing
    /// arrived" from "recordings were dropped".
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
    /// Why this recording carries no rows, when the shape is one that is not
    /// rendered.
    pub note: Option<&'static str>,
    /// The rows kept, oldest first.
    pub rows: Vec<RecordedRow>,
    /// Rows the tile held, of which `rows` is the last `rows.len()`.
    pub total: usize,
}

impl Recording {
    /// Rows the tile held that this recording does not carry.
    pub fn dropped(&self) -> usize {
        self.total.saturating_sub(self.rows.len())
    }

    /// Whether the call returned nothing. The collapse policy skips these: a
    /// producer pulled twice in one tick answers the second call empty.
    pub fn is_empty(&self) -> bool {
        self.total == 0
    }
}

/// A bounded record of what every producer returned.
///
/// Keyed by `(operator, producer instance)` rather than by operator alone,
/// because a `FanOut` branch is subscribed once per branch and each subscribe
/// builds a producer. Which of them a reader is shown is a rendering choice,
/// and keeping both keys leaves it open.
pub struct ValueRecorder {
    tick: u64,
    next_seq: u64,
    next_flow: u64,
    rows_per_recording: usize,
    recordings_per_producer: usize,
    by_producer: HashMap<(Option<NodeId>, usize), ProducerLog>,
}

/// What one producer has returned: its recent calls, and the last call that
/// carried rows.
///
/// Two questions rather than one. `recent` answers what the producer has been
/// doing, empties included, which is where a watermark's progress is read. `tail`
/// answers what flowed through it, and sits outside the ring because the two
/// counts are orders of magnitude apart: an operator under a settling scheduler
/// answers empty hundreds of times per row, so a ring deep enough to hold the
/// row would have to be deeper than the busiest pass.
///
/// One recording, under the same row cap as any other, so the footprint stays
/// `producers × (recordings + 1) × rows`.
#[derive(Default)]
struct ProducerLog {
    /// Recent calls, empty or not, oldest first.
    recent: VecDeque<Recording>,
    /// The newest call that carried rows, which `recent` may have evicted.
    tail: Option<Recording>,
}

impl ValueRecorder {
    /// A recorder with the given caps.
    pub fn new(rows_per_recording: usize, recordings_per_producer: usize) -> Self {
        Self {
            tick: 0,
            next_seq: 0,
            next_flow: 0,
            rows_per_recording,
            recordings_per_producer,
            by_producer: HashMap::new(),
        }
    }

    /// A recorder with [`DEFAULT_ROWS_PER_RECORDING`] and
    /// [`DEFAULT_RECORDINGS_PER_PRODUCER`].
    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_ROWS_PER_RECORDING, DEFAULT_RECORDINGS_PER_PRODUCER)
    }

    /// Name the tick that subsequent recordings belong to.
    ///
    /// The driver advances this once per pull, so every recording taken during
    /// one `get` of the root producer carries the same tick — including the
    /// several a shared subtree produces when it is pulled once per consumer.
    pub fn set_tick(&mut self, tick: u64) {
        self.tick = tick;
    }

    /// The tick recordings are currently attributed to.
    pub fn tick(&self) -> u64 {
        self.tick
    }

    /// Recordings taken since this recorder was built, including evicted ones.
    ///
    /// Monotone, so a publisher compares it against its own last value to tell
    /// whether anything was produced. The driver's sink loop polls on a timer
    /// and most polls record nothing.
    pub fn recorded(&self) -> u64 {
        self.next_seq
    }

    /// Recordings that carried rows, since this recorder was built.
    ///
    /// Monotone like [`recorded`](Self::recorded), and what a publisher compares
    /// against: a producer answers empty far more often than it answers with
    /// data, so a tick counted by `recorded` counts the driver's timer rather
    /// than the program's progress — and a frame published on one of those
    /// re-samples every source window after the pull that drained it.
    pub fn produced(&self) -> u64 {
        self.next_flow
    }

    /// Render `tile` and keep it, evicting this producer's oldest recording
    /// once the cap is reached.
    pub fn record(
        &mut self,
        node_id: Option<NodeId>,
        producer_id: usize,
        producer: &str,
        tile: &Tile,
    ) {
        let rendered = render(tile, self.rows_per_recording);
        let recording = Recording {
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
        let carried_rows = !recording.is_empty();
        if carried_rows {
            self.next_flow += 1;
        }

        let cap = self.recordings_per_producer;
        let log = self.by_producer.entry((node_id, producer_id)).or_default();
        if carried_rows {
            log.tail = Some(recording.clone());
        }
        if log.recent.len() == cap {
            log.recent.pop_front();
        }
        log.recent.push_back(recording);
    }

    /// Extend one channel's tail with the rows that just crossed it.
    ///
    /// A channel's tail is the last [`rows_per_recording`](Self::new) rows to
    /// cross it, accumulated; an operator's is its newest row-carrying answer.
    /// The difference is in the thing being recorded rather than in the policy:
    /// one `get` delivers a whole tile, so the tile is the unit, while rows cross
    /// a channel a batch at a time and a host that pushes one row per tick would
    /// otherwise leave a one-row tail no matter how long the feed ran.
    ///
    /// `first_key` is the arrival index of `rows[0]`, so the keys a reader sees
    /// are the ones the source minted rather than a position within the tail.
    /// `None` counts from what this channel has already carried, which is what a
    /// sink has: its rows are numbered by arrival and nothing else mints a key.
    ///
    /// A channel builds no producer and takes no `get`, so it occupies producer
    /// slot 0 under its own graph node, which no producer shares, and its ring
    /// of recent calls stays empty.
    pub fn record_channel(
        &mut self,
        node_id: Option<NodeId>,
        name: &str,
        shape: &'static str,
        first_key: Option<usize>,
        rows: &[Value],
    ) {
        if rows.is_empty() {
            return;
        }
        self.next_seq += 1;
        self.next_flow += 1;

        let cap = self.rows_per_recording;
        let log = self.by_producer.entry((node_id, 0)).or_default();
        let tail = log.tail.get_or_insert_with(|| Recording {
            tick: self.tick,
            seq: 0,
            node_id,
            producer_id: 0,
            producer: name.to_string(),
            shape,
            watermark: None,
            note: None,
            rows: Vec::new(),
            total: 0,
        });
        let first_key = first_key.unwrap_or(tail.total);
        tail.tick = self.tick;
        tail.seq = self.next_seq - 1;
        tail.total += rows.len();
        tail.rows
            .extend(rows.iter().enumerate().map(|(i, row)| RecordedRow {
                key: Some(format!("u{}", first_key + i)),
                value: row.to_string(),
                deleted: false,
            }));
        if tail.rows.len() > cap {
            tail.rows.drain(..tail.rows.len() - cap);
        }
    }

    /// Forget everything one producer recorded.
    ///
    /// Called by [`ProducerBase`](crate::interpreter::tile_operators::ProducerBase)'s
    /// `Drop`, which is what makes a replaced version's recordings go at the
    /// moment its producers do. `LiveProgram::reload` tears down exactly the
    /// producers it could not keep, so a kept operator's producer is never
    /// dropped and its series stays continuous across the swap.
    ///
    /// Nothing else may retire an entry: a producer that is still running and
    /// whose recordings were dropped would read on the wire as a node that has
    /// produced nothing, which is what an idle node looks like.
    pub fn retire(&mut self, node_id: Option<NodeId>, producer_id: usize) {
        self.by_producer.remove(&(node_id, producer_id));
    }

    /// Every recording for one producer, oldest first.
    ///
    /// An iterator rather than a slice: the backing `VecDeque` wraps once it has
    /// evicted, so its rows are not contiguous.
    pub fn recordings(
        &self,
        node_id: Option<NodeId>,
        producer_id: usize,
    ) -> impl Iterator<Item = &Recording> + '_ {
        self.by_producer
            .get(&(node_id, producer_id))
            .into_iter()
            .flat_map(|log| log.recent.iter())
    }

    /// The producers recorded so far.
    pub fn producers(&self) -> impl Iterator<Item = (Option<NodeId>, usize)> + '_ {
        self.by_producer.keys().copied()
    }

    /// The newest recording for one producer that carried rows, and whether
    /// newer recordings exist that carried nothing.
    ///
    /// Read from [`ProducerLog`]'s preserved slot, which the call ring cannot
    /// evict, so a producer that answered with rows once and empty a thousand
    /// times since still reports the rows. Scanning the ring instead loses them:
    /// the ring is sized for a progress signal, not for how long a row survives
    /// a settling pass.
    ///
    /// Which recording wins is a choice rather than a merge: a producer pulled
    /// twice in one tick answers the second call empty, and another answers with
    /// the same tile twice, so neither last-write-wins nor `Tile::merge` is
    /// correct. Two consumers pulling with different projection guards could
    /// return disjoint partial answers, which this drops; the ring shows that
    /// case if it occurs.
    pub fn latest_non_empty(
        &self,
        node_id: Option<NodeId>,
        producer_id: usize,
    ) -> Option<(&Recording, bool)> {
        let log = self.by_producer.get(&(node_id, producer_id))?;
        let found = log.tail.as_ref()?;
        // A channel records no calls, so there is nothing newer for its rows to
        // be stale against: what crossed it is what it last carried.
        let stale = log
            .recent
            .back()
            .is_some_and(|newest| found.seq != newest.seq);
        Some((found, stale))
    }

    /// Total recordings kept, across every producer.
    pub fn len(&self) -> usize {
        self.by_producer.values().map(|log| log.recent.len()).sum()
    }

    /// Whether nothing has been recorded.
    pub fn is_empty(&self) -> bool {
        self.by_producer.values().all(|log| log.recent.is_empty())
    }
}

/// A source's retained window, rendered.
///
/// Not a recording: a source has no producer and takes no `get`. Its window is
/// what has arrived and not yet been released, read through `&self`, so
/// sampling it moves nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceWindow {
    /// The source's node in the operator graph, which is what a click resolves
    /// to.
    pub node_id: Option<NodeId>,
    /// The source's registered name, e.g. `"stdin"`.
    pub name: String,
    /// The retained keys and their values, truncated to the last `limit`.
    pub rows: Vec<RecordedRow>,
    /// Keys the window held, of which `rows` is the last `rows.len()`.
    pub total: usize,
    /// Retained keys below the first position a new producer would be offered.
    ///
    /// Zero for a source nothing has abandoned. After a reload it is the leading
    /// run the retired version's producers left behind: still in the buffer,
    /// and offered to nobody. Shipped beside `total` rather than trimmed out of
    /// it, because both are true and they answer different questions — what the
    /// source is holding, and what the running program will still be given.
    pub abandoned: usize,
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
/// both `&self`. Truncation follows the same rule a recording uses: a source
/// domain is index-ordered, so the last keys are the most recent arrivals.
pub fn render_source_window(
    node_id: Option<NodeId>,
    name: &str,
    keys: &ColumnValue,
    values: &ColumnValue,
    offerable_from: usize,
    limit: usize,
) -> SourceWindow {
    let total = keys.len();
    // The keys of a source tiled by arrival order *are* its positions, so the
    // abandoned prefix is those below the first one still on offer.
    let abandoned = match keys {
        ColumnValue::UInts(ks) => ks.iter().filter(|k| **k < offerable_from).count(),
        _ => 0,
    };
    SourceWindow {
        node_id,
        name: name.to_string(),
        abandoned,
        rows: tail(total, limit)
            .map(|i| RecordedRow {
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
    rows: Vec<RecordedRow>,
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
                    .map(|i| RecordedRow {
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
                    .map(|name| RecordedRow {
                        key: Some(name.clone()),
                        value: one_level(&fields[name], 0),
                        deleted: false,
                    })
                    .collect(),
                total,
            }
        }
        Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => {
            let total = domain.len();
            Rendered {
                shape: "SealedFunction",
                watermark: Some(format!("{domain_predicate:?}")),
                note: None,
                rows: tail(total, limit)
                    .map(|i| RecordedRow {
                        key: Some(cell(domain, i)),
                        value: one_level(codomain, i),
                        deleted: deleted.contains(i),
                    })
                    .collect(),
                total,
            }
        }
        Tile::CurriedFunction {
            domain1,
            offsets,
            codomain,
            domain_predicate,
            ..
        } => {
            let total = domain1.len();
            Rendered {
                shape: "CurriedFunction",
                watermark: Some(format!("{domain_predicate:?}")),
                note: None,
                rows: tail(total, limit)
                    .map(|i| RecordedRow {
                        key: Some(cell(domain1, i)),
                        value: format!("<{} entries>", group_len(offsets, codomain.len(), i)),
                        deleted: false,
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
            rows: vec![RecordedRow {
                key: Some(format!("{kind:?}")),
                value: cell(accumulator, 0),
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
                    .map(|i| RecordedRow {
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
/// A nested function renders as its shape rather than recursing: a summary that
/// walks a whole subtree is not bounded by the row cap.
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
        Tile::SealedFunction { .. } => "<SealedFunction>".to_string(),
        Tile::CurriedFunction { .. } => "<CurriedFunction>".to_string(),
        Tile::Aggregation { accumulator, .. } => cell(accumulator, i),
        Tile::Store { .. } => "<Store>".to_string(),
    }
}

/// How many flat rows `domain1[i]`'s group spans in a curried tile.
fn group_len(offsets: &ColumnValue, flat_len: usize, i: usize) -> usize {
    let at = |j: usize| -> usize {
        match offsets.index_at(j) {
            Value::UInt(u) => u,
            other => panic!("a curried tile's offsets are UInts, found {other:?}"),
        }
    };
    let start = at(i);
    let end = if i + 1 < offsets.len() {
        at(i + 1)
    } else {
        flat_len
    };
    end.saturating_sub(start)
}

// The recorder handed to every producer built while it is installed.
//
// `ProducerBase::new` is called from inside producer constructors, which take no
// context parameter. The same argument `OperatorBase::new` makes for
// `ACTIVE_GRAPH`, and the session is live only while the graph is being
// subscribed — at runtime each producer uses the handle it was built with.
// shared-state-ok: a recorder installed for the duration of a subscribe. What
// crosses it is a handle, never a value passed between operators.
thread_local! {
    // shared-state-ok: the installed handle itself, for the reason on the macro
    // above. The declaration matches the checker's ambient-state shape twice —
    // once at the macro, once at the `static` — and its upward scan stops at
    // `thread_local! {`, which is neither a comment nor an attribute, so the
    // note above does not reach this line.
    static INSTALLED: RefCell<Option<SharedRecorder>> = const { RefCell::new(None) };
}

/// Installs `recorder` for every producer built until the returned guard drops.
///
/// Held across `compile_program`, which is where subscribing happens.
pub fn install(recorder: SharedRecorder) -> RecorderSession {
    INSTALLED.with(|slot| {
        let previous = slot.borrow_mut().replace(recorder);
        debug_assert!(
            previous.is_none(),
            "a recorder session is already installed; sessions are per-compile and do not nest",
        );
        RecorderSession
    })
}

/// The handle to build a producer with, if a session is installed.
pub(crate) fn installed() -> Option<SharedRecorder> {
    INSTALLED.with(|slot| slot.borrow().clone())
}

/// Uninstalls the recorder on drop.
pub struct RecorderSession;

impl Drop for RecorderSession {
    fn drop(&mut self) {
        INSTALLED.with(|slot| *slot.borrow_mut() = None);
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

    fn sealed(domain: &[usize], values: &[&str], deleted: &[usize]) -> Tile {
        Tile::SealedFunction {
            domain: uints(domain),
            codomain: Box::new(Tile::Scalar(strings(values))),
            domain_predicate: Predicate::True,
            deleted: deleted.iter().copied().collect::<BitSet>(),
        }
    }

    fn values(recording: &Recording) -> Vec<String> {
        recording.rows.iter().map(|r| r.value.clone()).collect()
    }

    #[test]
    fn a_sealed_function_records_its_keys_values_and_watermark() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(
            None,
            1,
            "MapResultWithSource#1",
            &sealed(&[0, 1], &["a", "b"], &[]),
        );

        let recording = recorder.recordings(None, 1).next().expect("recorded");
        assert_eq!(recording.shape, "SealedFunction");
        assert_eq!(recording.watermark.as_deref(), Some("True"));
        assert_eq!(
            recording.rows,
            vec![
                RecordedRow {
                    key: Some("u0".into()),
                    value: "\"a\"".into(),
                    deleted: false
                },
                RecordedRow {
                    key: Some("u1".into()),
                    value: "\"b\"".into(),
                    deleted: false
                },
            ]
        );
        assert_eq!(recording.total, 2);
        assert_eq!(recording.dropped(), 0);
    }

    /// A `Restrict` marks a filtered row deleted while its column still holds
    /// the value, and the `Memo` below it has compacted the same rows away.
    /// Rendering the mark is what keeps the two distinguishable.
    #[test]
    fn a_deleted_position_is_rendered_and_marked() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(
            None,
            1,
            "Restrict#1",
            &sealed(&[0, 1, 2], &["a", "skip", "c"], &[1]),
        );

        let recording = recorder.recordings(None, 1).next().expect("recorded");
        let marked: Vec<bool> = recording.rows.iter().map(|r| r.deleted).collect();
        assert_eq!(marked, vec![false, true, false]);
        assert_eq!(values(recording), vec!["\"a\"", "\"skip\"", "\"c\""]);
    }

    /// A producer answers empty far more often than it answers with rows — an
    /// operator under a settling scheduler does so hundreds of times per row —
    /// so the ring of recent calls cannot be what the pane reads. Without a slot
    /// the ring cannot evict, every such operator reports as though it had never
    /// been pulled.
    #[test]
    fn rows_survive_more_empty_calls_than_the_ring_can_hold() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(None, 1, "Restrict#1", &sealed(&[0], &["a"], &[]));
        for _ in 0..DEFAULT_RECORDINGS_PER_PRODUCER * 4 {
            recorder.record(None, 1, "Restrict#1", &sealed(&[], &[], &[]));
        }

        let (recording, stale) = recorder
            .latest_non_empty(None, 1)
            .expect("the rows are kept");
        assert_eq!(values(recording), vec!["\"a\""]);
        assert!(stale, "newer calls carried nothing, so the rows are stale");
        assert!(
            recorder.recordings(None, 1).all(Recording::is_empty),
            "the ring itself has evicted the row-carrying call",
        );
    }

    /// The publish gate counts production rather than calls: a driver polling on
    /// a timer records an empty answer per poll, and a frame published on one of
    /// those re-samples every source window after the pull that drained it.
    #[test]
    fn only_a_call_carrying_rows_counts_as_production() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(None, 1, "Restrict#1", &sealed(&[], &[], &[]));
        assert_eq!(recorder.produced(), 0);
        assert_eq!(recorder.recorded(), 1);

        recorder.record(None, 1, "Restrict#1", &sealed(&[0], &["a"], &[]));
        assert_eq!(recorder.produced(), 1);
        assert_eq!(recorder.recorded(), 2);
    }

    #[test]
    fn a_recording_keeps_the_last_rows_and_counts_the_rest() {
        let mut recorder = ValueRecorder::new(2, 4);
        recorder.record(
            None,
            1,
            "P#1",
            &sealed(&[0, 1, 2, 3], &["a", "b", "c", "d"], &[]),
        );

        let recording = recorder.recordings(None, 1).next().expect("recorded");
        assert_eq!(
            values(recording),
            vec!["\"c\"", "\"d\""],
            "the most recent rows"
        );
        assert_eq!(recording.total, 4);
        assert_eq!(recording.dropped(), 2);
    }

    #[test]
    fn a_producer_keeps_only_its_last_recordings() {
        let mut recorder = ValueRecorder::new(8, 2);
        for i in 0..5 {
            recorder.set_tick(i);
            recorder.record(None, 1, "P#1", &Tile::Scalar(strings(&["v"])));
        }

        let ticks: Vec<u64> = recorder.recordings(None, 1).map(|r| r.tick).collect();
        assert_eq!(ticks, vec![3, 4], "the cap evicts from the front");
        assert_eq!(recorder.len(), 2);
    }

    /// The shape the trace shows: a shared subtree is pulled once per consumer,
    /// and `IterateExtent` answers the second call empty. Rendering the newest
    /// recording would show nothing.
    #[test]
    fn a_producer_answering_empty_on_a_second_pull_still_reads_as_its_data() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.set_tick(7);
        recorder.record(None, 1, "IterateExtent#1", &sealed(&[0], &["a"], &[]));
        recorder.record(None, 1, "IterateExtent#1", &sealed(&[], &[], &[]));

        let (recording, stale) = recorder.latest_non_empty(None, 1).expect("recorded");
        assert_eq!(values(recording), vec!["\"a\""]);
        assert!(stale, "a newer recording carried nothing");
    }

    /// The other shape in the same trace: a `Memo` replays its cache, so the
    /// two calls carry the same tile. Merging them would render `["a", "a"]`.
    #[test]
    fn a_producer_answering_twice_alike_is_not_doubled() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.set_tick(7);
        recorder.record(None, 1, "Memo#2", &sealed(&[0], &["a"], &[]));
        recorder.record(None, 1, "Memo#2", &sealed(&[0], &["a"], &[]));

        let (recording, stale) = recorder.latest_non_empty(None, 1).expect("recorded");
        assert_eq!(values(recording), vec!["\"a\""]);
        assert!(!stale, "the newest recording carried the data");
    }

    #[test]
    fn one_operator_with_two_producers_keeps_them_apart() {
        let node = Some(NodeId::fresh());
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(node, 1, "FanOut#1", &Tile::Scalar(strings(&["left"])));
        recorder.record(node, 2, "FanOut#1", &Tile::Scalar(strings(&["right"])));

        assert_eq!(recorder.producers().count(), 2);
        assert_eq!(
            values(recorder.recordings(node, 1).next().unwrap()),
            vec!["\"left\""]
        );
        assert_eq!(
            values(recorder.recordings(node, 2).next().unwrap()),
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
        let tile = Tile::SealedFunction {
            domain: uints(&[0]),
            codomain: Box::new(Tile::Record(fields)),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(None, 1, "FanIn#1", &tile);
        let recording = recorder.recordings(None, 1).next().expect("recorded");
        assert_eq!(values(recording), vec!["(tagged: \"> a\", text: \"a\")"]);
    }

    #[test]
    fn a_store_records_its_size_and_says_why_it_has_no_rows() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(
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

        let recording = recorder.recordings(None, 1).next().expect("recorded");
        assert_eq!(recording.shape, "Store");
        assert_eq!(recording.total, 2);
        assert_eq!(
            recording
                .rows
                .iter()
                .map(|r| r.key.clone())
                .collect::<Vec<_>>(),
            vec![Some("u0".into()), Some("u1".into())],
            "a store's rows are its change ticks",
        );
        assert_eq!(recording.watermark.as_deref(), Some("True"));
    }

    /// The count a publisher compares against to skip an unchanged frame. The
    /// driver's sink loop polls on a timer and most polls record nothing.
    #[test]
    fn the_recorded_count_advances_only_when_something_is_recorded() {
        let mut recorder = ValueRecorder::with_defaults();
        assert_eq!(recorder.recorded(), 0);
        recorder.record(None, 1, "P#1", &Tile::Scalar(strings(&["x"])));
        assert_eq!(recorder.recorded(), 1);
        recorder.set_tick(9);
        assert_eq!(recorder.recorded(), 1, "advancing the tick records nothing");
        recorder.record(None, 1, "P#1", &sealed(&[], &[], &[]));
        assert_eq!(recorder.recorded(), 2, "an empty tile is still a recording");
    }

    /// A source window renders keys against values and truncates to the tail,
    /// the same rule a recording uses: a source domain is index-ordered, so the
    /// last keys are the most recent arrivals.
    #[test]
    fn a_source_window_renders_the_last_keys_and_counts_the_rest() {
        let keys = uints(&[2, 3, 4]);
        let values = strings(&["c", "d", "e"]);
        let window = render_source_window(None, "stdin", &keys, &values, 0, 2);

        assert_eq!(window.name, "stdin");
        assert_eq!(window.total, 3);
        assert_eq!(window.dropped(), 1);
        assert_eq!(
            window.rows,
            vec![
                RecordedRow {
                    key: Some("u3".into()),
                    value: "\"d\"".into(),
                    deleted: false
                },
                RecordedRow {
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
            None,
            "stdin",
            &ColumnValue::from_uints(Vec::new()),
            &strings(&[]),
            0,
            8,
        );
        assert_eq!(window.total, 0);
        assert_eq!(window.dropped(), 0);
        assert!(window.rows.is_empty());
    }

    #[test]
    fn a_sequence_number_orders_every_recording() {
        let mut recorder = ValueRecorder::with_defaults();
        recorder.record(None, 1, "A#1", &Tile::Scalar(strings(&["x"])));
        recorder.record(None, 2, "B#1", &Tile::Scalar(strings(&["y"])));
        recorder.record(None, 1, "A#1", &Tile::Scalar(strings(&["z"])));

        let seqs: Vec<u64> = recorder.recordings(None, 1).map(|r| r.seq).collect();
        assert_eq!(seqs, vec![0, 2], "the gap is B's recording");
    }
}

//! Probes: what each producer returned, rendered and bounded, for the live
//! value pane.
//!
//! Every producer holds the [`ProbeSlot`] of the scheduler it was built under.
//! While the slot holds a table, each producer's probe takes a [`Reading`] of
//! each result
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
//! carries as many rows as the join produced. The row cap bounds the rows held to
//! `probes × (readings + 1) × rows`, and [`CHARS_PER_CELL`] bounds each rendered
//! key, value, completeness and obsolete guard, however deeply the value nests.
//! Rendering stops at the budget, so its cost is bounded by it too rather than
//! by the value's length. Rendering happens on the driver thread, and no tile
//! is cloned.
//!
//! A pane asks what flowed through a node, which a ring of recent readings
//! cannot answer: empty readings outnumber row-carrying ones by orders of
//! magnitude. Each probe therefore holds its last row-carrying reading outside
//! the ring.

use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque, hash_map::Entry},
    fmt::{self, Write as _},
    rc::Rc,
};

use crate::{
    ccl::provenance::NodeId,
    interpreter::{
        tiling::{Tile, TileGuard, running_frontier},
        types::ColumnValue,
    },
};

/// Rows kept per reading.
pub const ROWS_PER_READING: usize = 32;

/// Characters kept per rendered key or value, however deeply the value nests.
pub const CHARS_PER_CELL: usize = 256;

/// Readings kept in each probe's ring.
pub const READINGS_PER_PROBE: usize = 16;

/// The probe table of one program's producers, or nothing while no one is
/// watching.
///
/// Every producer holds a clone, taken from its [`Scheduler`] when it is built,
/// so one [`enable`](Self::enable) or [`disable`](Self::disable) switches
/// probing for all of them at once. While the slot is empty a
/// `TileProducer::get` costs one `None` check.
///
/// [`Scheduler`]: crate::interpreter::Scheduler
#[derive(Clone, Default)]
pub struct ProbeSlot(
    // shared-state-ok: the observation boundary. A producer writes what it has
    // already returned to its consumer, rendered; nothing reads it back into
    // the graph, and no operator reaches another operator's rows. Shared
    // because the driver reads one table and every producer writes it, and the
    // producer graph has no `&self` traversal that would let the driver collect
    // per-producer buffers instead.
    Rc<RefCell<Option<ProbeTable>>>,
);

impl ProbeSlot {
    /// Start probing with an empty [`ProbeTable`], if not already probing.
    pub fn enable(&self) {
        self.0
            .borrow_mut()
            .get_or_insert_with(ProbeTable::with_defaults);
    }

    /// Stop probing and drop every reading taken so far.
    pub fn disable(&self) {
        *self.0.borrow_mut() = None;
    }

    /// Whether producers are taking readings.
    pub fn is_enabled(&self) -> bool {
        self.0.borrow().is_some()
    }

    /// Read the table, or `None` while probing is off.
    pub fn with_table<R>(&self, read: impl FnOnce(&ProbeTable) -> R) -> Option<R> {
        self.0.borrow().as_ref().map(read)
    }

    /// Take a reading of `tile` for one producer. A no-op while probing is off.
    pub(crate) fn observe_named(
        &self,
        node_id: Option<NodeId>,
        producer_id: usize,
        name: impl FnOnce() -> String,
        tile: &Tile,
        obsolete: &TileGuard,
    ) {
        if let Some(table) = self.0.borrow_mut().as_mut() {
            table.observe_named(node_id, producer_id, name, tile, obsolete);
        }
    }

    /// Detach one producer's probe, when that producer is dropped.
    ///
    /// Nothing drops a producer while the table is borrowed: `observe_named`
    /// holds a mutable borrow only for the call, and a frame render holds a
    /// shared one while it iterates, building no producers and dropping none. A
    /// failed borrow is that invariant breaking. It panics in debug builds only,
    /// since this runs in `Drop` and a panic there during an unwind aborts.
    pub(crate) fn detach(&self, node_id: Option<NodeId>, producer_id: usize) {
        match self.0.try_borrow_mut() {
            Ok(mut slot) => {
                if let Some(table) = slot.as_mut() {
                    table.detach(node_id, producer_id);
                }
            }
            Err(_) => debug_assert!(
                false,
                "a producer was dropped while the probe table was borrowed, so its \
                 probe outlives it",
            ),
        }
    }
}

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
    /// Position in the probe table's total order, so a consumer can tell
    /// "nothing arrived" from "readings were evicted".
    pub seq: u64,
    /// The operator that built the producer, or `None` for a producer built
    /// outside any subscribe.
    pub node_id: Option<NodeId>,
    /// The producer instance, since one operator can build several.
    pub producer_id: usize,
    /// The producer's display name, e.g. `"MapResultWithSource#1"`, shared by
    /// every reading of one probe.
    pub producer: Rc<str>,
    /// The tile's variant name.
    pub shape: &'static str,
    /// The region of the domain the output is complete for: a collection's
    /// `domain_predicate` or a store's `frontier`, in its `Debug` form, which
    /// advances `False`, then `LessThanEq(uN)`, then `True`. An aggregation
    /// reports whether it is terminal. `None` for a shape carrying no such
    /// region.
    pub completeness: Option<String>,
    /// The producer's obsolete guard when the call returned, in its `Debug`
    /// form: the region its consumer has released, which the producer never
    /// returns again. `completeness` says how much of the output is final; this
    /// says how much of it the consumer is done with.
    ///
    /// `None` when the guard is empty: the consumer has released nothing, which
    /// is the common case and not worth a rendering.
    pub obsolete: Option<String>,
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

    /// Whether the call returned nothing. A producer pulled twice in one pass
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
/// been doing, empty readings included, and is where progress toward completeness is
/// read. `last_flow` answers what flowed through it. It sits outside the ring
/// because an operator under a settling scheduler answers empty hundreds of
/// times per row, so a ring deep enough to hold the row would have to be deeper
/// than the busiest pass.
///
/// `last_flow` is one reading under the same caps as any other, so the rows
/// held stay `probes × (readings + 1) × rows`.
///
/// A reading is held behind an `Rc`, so `last_flow` and the ring share one
/// allocation rather than each holding a copy.
struct Probe {
    /// The producer's display name, computed once when the probe is attached.
    name: Rc<str>,
    /// Recent readings, empty or not, oldest first.
    recent: VecDeque<Rc<Reading>>,
    /// The newest reading that carried rows, which `recent` may have evicted.
    last_flow: Option<Rc<Reading>>,
}

impl ProbeTable {
    /// A probe table with the given caps.
    pub fn new(rows_per_reading: usize, readings_per_probe: usize) -> Self {
        Self {
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

    /// Readings that carried rows, since this table was built. Monotone.
    ///
    /// Probe publishing compares this against the count it last published at.
    /// A count of all readings would advance on every poll of the driver's
    /// sink loop, since a poll that delivers nothing still takes an empty
    /// reading from every producer it pulls.
    pub fn flows(&self) -> u64 {
        self.next_flow
    }

    /// Render `tile`, and the `obsolete` guard the producer held when it
    /// returned it, as a reading of this producer's probe, evicting the probe's
    /// oldest reading once the ring is full.
    pub fn observe(
        &mut self,
        node_id: Option<NodeId>,
        producer_id: usize,
        producer: &str,
        tile: &Tile,
        obsolete: &TileGuard,
    ) {
        self.observe_named(
            node_id,
            producer_id,
            || producer.to_string(),
            tile,
            obsolete,
        );
    }

    /// [`observe`](Self::observe), computing the producer's display name only
    /// when its probe is first attached. `TileProducer::get` calls this on every
    /// pull, and a name is a fresh `String` each time it is asked for.
    pub(crate) fn observe_named(
        &mut self,
        node_id: Option<NodeId>,
        producer_id: usize,
        name: impl FnOnce() -> String,
        tile: &Tile,
        obsolete: &TileGuard,
    ) {
        let rendered = render(tile, self.rows_per_reading);
        let probe = match self.probes.entry((node_id, producer_id)) {
            Entry::Occupied(entry) => {
                // `alloc_id` counts per producer type, so two types built for
                // one operator could share this key and interleave readings.
                // An operator builds one producer per subscribe; a second name
                // under one key is that rule breaking.
                debug_assert_eq!(
                    &*entry.get().name,
                    name(),
                    "two producers share the probe key ({node_id:?}, {producer_id})",
                );
                entry.into_mut()
            }
            Entry::Vacant(entry) => entry.insert(Probe {
                name: name().into(),
                recent: VecDeque::new(),
                last_flow: None,
            }),
        };
        let reading = Rc::new(Reading {
            seq: self.next_seq,
            node_id,
            producer_id,
            producer: Rc::clone(&probe.name),
            shape: rendered.shape,
            completeness: rendered.completeness,
            obsolete: (!obsolete.is_empty()).then(|| bounded(|out| write!(out, "{obsolete:?}"))),
            note: rendered.note,
            rows: rendered.rows,
            total: rendered.total,
        });
        self.next_seq += 1;
        let carried_rows = !reading.is_empty();
        if carried_rows {
            self.next_flow += 1;
            probe.last_flow = Some(Rc::clone(&reading));
        }
        if probe.recent.len() == self.readings_per_probe {
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
            .flat_map(|probe| probe.recent.iter().map(|reading| &**reading))
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
    /// one pass answers the second call empty, and another answers with the
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
        let found: &Reading = probe.last_flow.as_ref()?;
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

/// The last `limit` indices of a source's retained `window`: the keys a
/// sample fetches, so its cost is bounded by `limit` rather than by how much
/// the source retains.
pub fn window_tail(window: std::ops::Range<usize>, limit: usize) -> std::ops::Range<usize> {
    window.end.saturating_sub(limit).max(window.start)..window.end
}

/// Render the tail of a source's retained window.
///
/// `keys` and `values` are the part of the window the caller fetched, through
/// the source's own `retained_window` and `get`, both `&self`. The caller
/// fetches the window's last keys, following the rule a reading uses: a source
/// domain is index-ordered, so the last keys are the most recent arrivals.
/// `total` is the whole window's length, of which `keys` is the end.
pub fn render_source_window(
    node_ids: Vec<NodeId>,
    name: &str,
    total: usize,
    keys: &ColumnValue,
    values: &ColumnValue,
) -> SourceWindow {
    debug_assert!(
        keys.len() <= total,
        "a window's fetched tail is longer than the window: {} of {total}",
        keys.len(),
    );
    SourceWindow {
        node_ids,
        name: name.to_string(),
        rows: (0..keys.len())
            .map(|i| ReadingRow {
                key: Some(cell(keys, i)),
                value: cell(values, i),
                deleted: false,
            })
            .collect(),
        total,
    }
}

/// A rendered tile, before it is stamped with its sequence number.
struct Rendered {
    shape: &'static str,
    completeness: Option<String>,
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
                completeness: None,
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
        Tile::Record { fields, .. } => {
            let mut names: Vec<&String> = fields.keys().collect();
            // `Tile::Record` is a `HashMap`, whose iteration order varies
            // between runs of one program. Sorting is what makes a rendering
            // reproducible.
            names.sort();
            let total = names.len();
            Rendered {
                shape: "Record",
                completeness: None,
                note: None,
                rows: names
                    .into_iter()
                    .skip(total.saturating_sub(limit))
                    .map(|name| ReadingRow {
                        key: Some(name.clone()),
                        value: bounded(|out| write_field(tile, name, 0, out)),
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
                completeness: Some(bounded(|out| write!(out, "{domain_predicate:?}"))),
                note: None,
                rows: tail(total, limit)
                    .map(|i| ReadingRow {
                        key: Some(cell(domain, i)),
                        value: position(codomain, i),
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
            completeness: Some(format!("terminal: {}", cell(terminal, 0))),
            note: None,
            rows: vec![ReadingRow {
                key: Some(format!("{kind:?}")),
                value: position(accumulator, 0),
                deleted: false,
            }],
            total: 1,
        },
        Tile::Store {
            frontier, terminal, ..
        } => {
            // One row per key, holding the change events themselves rather than
            // the step function they decide: what a reader asks of a slot is what
            // was written to it and when, and that is the changelog unfolded.
            let names = sorted_store_keys(tile);
            let total = names.len();
            // A terminal store is decided everywhere; a live one through its
            // running row's watermark.
            let completeness = if *terminal {
                "True".to_string()
            } else {
                bounded(|out| write!(out, "{:?}", running_frontier(frontier)))
            };
            Rendered {
                shape: "Store",
                completeness: Some(completeness),
                note: None,
                rows: names
                    .into_iter()
                    .skip(total.saturating_sub(limit))
                    .map(|name| ReadingRow {
                        key: Some(name.clone()),
                        value: bounded(|out| write_changelog(tile, name, out)),
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

/// One position of a column, rendered within [`CHARS_PER_CELL`].
fn cell(column: &ColumnValue, i: usize) -> String {
    bounded(|out| write_cell(column, i, out))
}

/// One codomain position, rendered within [`CHARS_PER_CELL`] however deep it
/// nests.
fn position(tile: &Tile, i: usize) -> String {
    bounded(|out| write_position(tile, i, out))
}

/// What `write` renders, cut at [`CHARS_PER_CELL`] characters.
///
/// A cut ends in `…`, followed by how many entries it passed over in the
/// outermost collection that has any left.
fn bounded(write: impl FnOnce(&mut Bounded) -> fmt::Result) -> String {
    let mut out = Bounded {
        text: String::new(),
        remaining: CHARS_PER_CELL,
        passed_over: None,
    };
    if write(&mut out).is_err() {
        out.text.push('…');
        if let Some(entries) = out.passed_over {
            out.text.push_str(&format!("<+{entries} entries>"));
        }
    }
    out.text
}

/// A `fmt::Write` sink that stops at a character budget.
///
/// It fails the write that crosses the budget, which aborts the formatting
/// that called it. A value is therefore rendered in time proportional to the
/// budget rather than to its length: `Value`'s `Display` writes a string's
/// content in one `write_str`, of which this copies a prefix.
struct Bounded {
    text: String,
    remaining: usize,
    /// Entries left unrendered in the outermost collection a cut fell inside.
    passed_over: Option<usize>,
}

impl fmt::Write for Bounded {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // `nth` stops at the budget, so a long `s` is not scanned to its end.
        match s.char_indices().nth(self.remaining) {
            None => {
                self.text.push_str(s);
                // At most `remaining` characters, or `nth` would have found one.
                self.remaining -= s.chars().count();
                Ok(())
            }
            Some((cut, _)) => {
                self.text.push_str(&s[..cut]);
                self.remaining = 0;
                Err(fmt::Error)
            }
        }
    }
}

fn write_cell(column: &ColumnValue, i: usize, out: &mut Bounded) -> fmt::Result {
    if i < column.len() {
        write!(out, "{}", column.index_at(i))
    } else {
        // The column is shorter than the domain beside it.
        out.write_str("<absent>")
    }
}

/// A codomain position, descending into every level it holds.
///
/// A nested collection renders its entries as `[key ↦ value, …]`, and a nested
/// store its changelog the same way, drawing on the one budget the enclosing
/// cell was given. The budget is what bounds the rendering, not the depth.
fn write_position(tile: &Tile, i: usize, out: &mut Bounded) -> fmt::Result {
    match tile {
        Tile::Scalar(column) => write_cell(column, i, out),
        Tile::Record { fields, .. } => {
            let mut names: Vec<&String> = fields.keys().collect();
            names.sort();
            write_fields(names, out, |name, out| write_field(tile, name, i, out))
        }
        Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } if i < tile.rows() => {
            let (start, end) = tile.row_run(i);
            write_entries(start..end, out, |j, out| {
                write_cell(domain, j, out)?;
                out.write_str(" ↦ ")?;
                write_position(codomain, j, out)?;
                if deleted.contains(j) {
                    out.write_str(" (deleted)")?;
                }
                Ok(())
            })
        }
        Tile::DataFunction { .. } => out.write_str("<absent>"),
        Tile::Aggregation { accumulator, .. } => write_position(accumulator, i, out),
        // A store is a whole value, so it stands at one row.
        Tile::Store { .. } if i < tile.rows() => {
            write_fields(sorted_store_keys(tile), out, |name, out| {
                write_changelog(tile, name, out)
            })
        }
        Tile::Store { .. } => out.write_str("<absent>"),
    }
}

/// `(name: …, …)` over `names`, each value written by `write_value`.
fn write_fields(
    names: Vec<&String>,
    out: &mut Bounded,
    mut write_value: impl FnMut(&str, &mut Bounded) -> fmt::Result,
) -> fmt::Result {
    out.write_str("(")?;
    for (n, name) in names.into_iter().enumerate() {
        if n > 0 {
            out.write_str(", ")?;
        }
        write!(out, "{name}: ")?;
        write_value(name, out)?;
    }
    out.write_str(")")
}

/// Field `name` of `record` at row `i`. A field absent at some rows holds the
/// other rows' cells in order, so row `i` sits at `i` less the absent rows
/// below it.
fn write_field(record: &Tile, name: &str, i: usize, out: &mut Bounded) -> fmt::Result {
    let Tile::Record { fields, absent } = record else {
        unreachable!("a field is read off a record, got {record:?}")
    };
    let absent = absent.get(name);
    if absent.is_some_and(|rows| rows.contains(i)) {
        return out.write_str("<absent>");
    }
    let below = absent.map_or(0, |rows| rows.iter().take_while(|&row| row < i).count());
    write_position(&fields[name], i - below, out)
}

/// A store's keys, sorted: its state is a `HashMap`, whose iteration order
/// varies between runs.
fn sorted_store_keys(store: &Tile) -> Vec<&String> {
    let mut names: Vec<&String> = store.store_keys().collect();
    names.sort();
    names
}

/// Store key `name`'s changelog as `[position ↦ value, …]`.
fn write_changelog(store: &Tile, name: &str, out: &mut Bounded) -> fmt::Result {
    let (positions, values) = store
        .store_changelog(name)
        .unwrap_or_else(|| unreachable!("{name} is one of the store's own keys"));
    write_entries(0..positions.len(), out, |j, out| {
        write_cell(positions, j, out)?;
        out.write_str(" ↦ ")?;
        write_position(values, j, out)
    })
}

/// `[e₀, e₁, …]` over `entries`, recording how many a cut passes over.
///
/// Each enclosing collection with entries left overwrites the count as the cut
/// unwinds through it, so the count left is the outermost nonzero one.
fn write_entries(
    entries: std::ops::Range<usize>,
    out: &mut Bounded,
    mut write_entry: impl FnMut(usize, &mut Bounded) -> fmt::Result,
) -> fmt::Result {
    let end = entries.end;
    out.write_str("[")?;
    for (n, j) in entries.enumerate() {
        let written =
            if n > 0 { out.write_str(", ") } else { Ok(()) }.and_then(|()| write_entry(j, out));
        if written.is_err() {
            let passed_over = end - j - 1;
            if passed_over > 0 {
                out.passed_over = Some(passed_over);
            }
            return written;
        }
    }
    out.write_str("]")
}

/// A one-row store holding one key, `key`, written `values` at `positions` and
/// decided through `watermark`, for fixtures that render one.
#[cfg(test)]
pub(crate) fn one_key_store(
    key: &str,
    positions: Vec<usize>,
    values: ColumnValue,
    watermark: Option<usize>,
    terminal: bool,
) -> Tile {
    use std::collections::HashMap;

    use bit_set::BitSet;

    use crate::interpreter::tiling::{Predicate, one_row_decided};

    let decided = positions.clone();
    Tile::Store {
        state: Box::new(Tile::record(HashMap::from([(
            key.to_string(),
            Tile::data_function(
                ColumnValue::UInts(positions),
                Box::new(Tile::Scalar(values)),
                Predicate::False,
                BitSet::new(),
            ),
        )]))),
        seed: Box::new(Tile::record(HashMap::from([(
            key.to_string(),
            Tile::Scalar(ColumnValue::Units(0)),
        )]))),
        decided: Box::new(one_row_decided(ColumnValue::UInts(decided))),
        frontier: Box::new(one_row_decided(ColumnValue::UInts(
            watermark.into_iter().collect(),
        ))),
        terminal,
        closed_keys: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use bit_set::BitSet;

    use super::*;
    use crate::interpreter::{
        tiling::{FunctionGuard, Predicate},
        types::Value,
    };

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

    /// The obsolete guard of a producer whose consumer has released nothing.
    fn unreleased() -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::False))
    }

    #[test]
    fn a_reading_of_a_collection_keeps_its_keys_values_and_completeness() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "MapResultWithSource#1",
            &collection(&[0, 1], &["a", "b"], &[]),
            &unreleased(),
        );

        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "DataFunction");
        assert_eq!(reading.completeness.as_deref(), Some("True"));
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
            &unreleased(),
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
        probes.observe(
            None,
            1,
            "Restrict#1",
            &collection(&[0], &["a"], &[]),
            &unreleased(),
        );
        for _ in 0..READINGS_PER_PROBE * 4 {
            probes.observe(
                None,
                1,
                "Restrict#1",
                &collection(&[], &[], &[]),
                &unreleased(),
            );
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
        probes.observe(
            None,
            1,
            "Restrict#1",
            &collection(&[], &[], &[]),
            &unreleased(),
        );
        assert_eq!(probes.flows(), 0);

        probes.observe(
            None,
            1,
            "Restrict#1",
            &collection(&[0], &["a"], &[]),
            &unreleased(),
        );
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
            &unreleased(),
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
        for _ in 0..5 {
            probes.observe(
                None,
                1,
                "P#1",
                &Tile::Scalar(strings(&["v"])),
                &unreleased(),
            );
        }

        let seqs: Vec<u64> = probes.readings(None, 1).map(|r| r.seq).collect();
        assert_eq!(seqs, vec![3, 4], "the cap evicts from the front");
        assert_eq!(probes.len(), 2);
    }

    /// The shape the trace shows: a shared subtree is pulled once per consumer,
    /// and `IterateExtent` answers the second call empty. Rendering the newest
    /// reading would show nothing.
    #[test]
    fn a_producer_answering_empty_on_a_second_pull_still_reads_as_its_data() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "IterateExtent#1",
            &collection(&[0], &["a"], &[]),
            &unreleased(),
        );
        probes.observe(
            None,
            1,
            "IterateExtent#1",
            &collection(&[], &[], &[]),
            &unreleased(),
        );

        let (reading, stale) = probes.last_flow(None, 1).expect("observed");
        assert_eq!(values(reading), vec!["\"a\""]);
        assert!(stale, "a newer reading carried nothing");
    }

    /// The other shape in the same trace: a `Memo` replays its cache, so the
    /// two calls carry the same tile. Merging them would render `["a", "a"]`.
    #[test]
    fn a_producer_answering_twice_alike_is_not_doubled() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "Memo#2",
            &collection(&[0], &["a"], &[]),
            &unreleased(),
        );
        probes.observe(
            None,
            1,
            "Memo#2",
            &collection(&[0], &["a"], &[]),
            &unreleased(),
        );

        let (reading, stale) = probes.last_flow(None, 1).expect("observed");
        assert_eq!(values(reading), vec!["\"a\""]);
        assert!(!stale, "the newest reading carried the data");
    }

    #[test]
    fn one_operator_with_two_producers_keeps_them_apart() {
        let node = Some(NodeId::fresh());
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            node,
            1,
            "FanOut#1",
            &Tile::Scalar(strings(&["left"])),
            &unreleased(),
        );
        probes.observe(
            node,
            2,
            "FanOut#1",
            &Tile::Scalar(strings(&["right"])),
            &unreleased(),
        );

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
            Box::new(Tile::record(fields)),
            Predicate::True,
            BitSet::new(),
        );

        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "FanIn#1", &tile, &unreleased());
        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(values(reading), vec!["(tagged: \"> a\", text: \"a\")"]);
    }

    /// A nested collection renders its entries, so a reading below the top
    /// level shows the values and not only how many there are.
    #[test]
    fn a_nested_collection_renders_its_entries() {
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
        probes.observe(None, 1, "GroupBy#1", &tile, &unreleased());
        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "DataFunction");
        assert_eq!(
            values(reading),
            vec!["[u0 ↦ \"a\", u1 ↦ \"b\"]", "[u0 ↦ \"c\"]"]
        );
    }

    /// One long string is cut at the budget rather than held at full size in
    /// every reading that carries it.
    #[test]
    fn a_long_value_is_cut_at_the_cell_budget() {
        let long = "x".repeat(CHARS_PER_CELL * 4);
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "Memo#1",
            &collection(&[0], &[&long], &[]),
            &unreleased(),
        );
        let reading = probes.readings(None, 1).next().expect("observed");
        let value = &reading.rows[0].value;
        assert_eq!(value.chars().count(), CHARS_PER_CELL + 1, "{value}");
        assert!(value.starts_with("\"xxx"));
        assert!(value.ends_with('…'));
    }

    /// Nesting spends one budget, and a cut inside a collection says how many
    /// of its entries it passed over.
    #[test]
    fn a_cut_inside_a_nested_collection_counts_what_it_passed_over() {
        let entries = CHARS_PER_CELL;
        let inner = Tile::grouped(
            uints(&[0]),
            uints(&(0..entries).collect::<Vec<_>>()),
            Box::new(Tile::Scalar(strings(&vec!["v"; entries]))),
            Predicate::True,
            BitSet::new(),
        );
        let tile =
            Tile::data_function(uints(&[0]), Box::new(inner), Predicate::True, BitSet::new());

        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "GroupBy#1", &tile, &unreleased());
        let reading = probes.readings(None, 1).next().expect("observed");
        let value = &reading.rows[0].value;
        let (shown, marker) = value.split_once('…').expect("the value was cut");
        assert_eq!(shown.chars().count(), CHARS_PER_CELL);
        // The cut falls inside the entry after the last whole one, so that
        // entry is started and not counted as passed over.
        let whole_entries = shown.matches('↦').count();
        assert_eq!(
            marker,
            format!("<+{} entries>", entries - whole_entries - 1),
            "{value}",
        );
    }

    /// A store nested in a codomain renders its changelog as entries, the way a
    /// nested collection does.
    #[test]
    fn a_nested_store_renders_its_changelog() {
        let store = one_key_store("acc", vec![0, 2], strings(&["a", "b"]), Some(2), false);
        let tile =
            Tile::data_function(uints(&[0]), Box::new(store), Predicate::True, BitSet::new());

        let mut probes = ProbeTable::with_defaults();
        probes.observe(None, 1, "AsOf#1", &tile, &unreleased());
        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(values(reading), vec!["(acc: [u0 ↦ \"a\", u2 ↦ \"b\"])"]);
    }

    #[test]
    fn a_reading_of_a_store_keeps_each_keys_changelog_and_the_frontier_it_decided() {
        let mut probes = ProbeTable::with_defaults();
        let live = one_key_store("acc", vec![0, 1], strings(&["a", "b"]), Some(1), false);
        probes.observe(None, 1, "Commit#1", &live, &unreleased());

        let reading = probes.readings(None, 1).next().expect("observed");
        assert_eq!(reading.shape, "Store");
        assert_eq!(reading.total, 1, "a store's rows are its keys");
        assert_eq!(reading.rows[0].key.as_deref(), Some("acc"));
        assert_eq!(reading.rows[0].value, "[u0 ↦ \"a\", u1 ↦ \"b\"]");
        assert_eq!(
            reading.completeness,
            Some(format!("{:?}", Predicate::at_or_below(Value::UInt(1)))),
            "a live store is decided through its watermark",
        );

        let done = one_key_store("acc", vec![0, 1], strings(&["a", "b"]), Some(1), true);
        probes.observe(None, 1, "Commit#1", &done, &unreleased());
        let reading = probes.readings(None, 1).last().expect("observed");
        assert_eq!(reading.completeness.as_deref(), Some("True"));
    }

    /// A sample fetches the window's last keys, the same rule a reading uses:
    /// a source domain is index-ordered, so the last keys are the most recent
    /// arrivals.
    #[test]
    fn a_window_tail_is_the_last_keys_and_never_reaches_before_the_window() {
        assert_eq!(window_tail(2..5, 2), 3..5);
        assert_eq!(
            window_tail(2..5, 8),
            2..5,
            "a short window is fetched whole"
        );
        assert_eq!(window_tail(0..0, 8), 0..0);
        assert_eq!(window_tail(10_000..1_000_000, 32), 999_968..1_000_000);
    }

    /// A source window renders the tail it was handed against the whole
    /// window's length.
    #[test]
    fn a_source_window_renders_its_tail_and_counts_the_rest() {
        let keys = uints(&[3, 4]);
        let values = strings(&["d", "e"]);
        let window = render_source_window(Vec::new(), "stdin", 3, &keys, &values);

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
            0,
            &ColumnValue::from_uints(Vec::new()),
            &strings(&[]),
        );
        assert_eq!(window.total, 0);
        assert_eq!(window.dropped(), 0);
        assert!(window.rows.is_empty());
    }

    #[test]
    fn a_sequence_number_orders_every_reading() {
        let mut probes = ProbeTable::with_defaults();
        probes.observe(
            None,
            1,
            "A#1",
            &Tile::Scalar(strings(&["x"])),
            &unreleased(),
        );
        probes.observe(
            None,
            2,
            "B#1",
            &Tile::Scalar(strings(&["y"])),
            &unreleased(),
        );
        probes.observe(
            None,
            1,
            "A#1",
            &Tile::Scalar(strings(&["z"])),
            &unreleased(),
        );

        let seqs: Vec<u64> = probes.readings(None, 1).map(|r| r.seq).collect();
        assert_eq!(seqs, vec![0, 2], "the gap is B's reading");
    }

    /// The guard ships only once the consumer has released something, so a
    /// reader is not shown an empty region on every probe.
    #[test]
    fn an_obsolete_guard_is_reported_only_once_something_is_released() {
        let mut probes = ProbeTable::with_defaults();
        let tile = collection(&[0], &["a"], &[]);
        probes.observe(None, 1, "Memo#1", &tile, &unreleased());
        let released = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            Value::UInt(0),
        )));
        probes.observe(None, 1, "Memo#1", &tile, &released);

        let obsolete: Vec<Option<String>> = probes
            .readings(None, 1)
            .map(|reading| reading.obsolete.clone())
            .collect();
        assert_eq!(obsolete, vec![None, Some(format!("{released:?}"))]);
    }

    #[test]
    fn a_slot_takes_readings_only_while_enabled() {
        let slot = ProbeSlot::default();
        let tile = collection(&[0], &["a"], &[]);
        slot.observe_named(None, 1, || "P#1".into(), &tile, &unreleased());
        assert!(slot.with_table(ProbeTable::len).is_none(), "off: no table");

        slot.enable();
        slot.observe_named(None, 1, || "P#1".into(), &tile, &unreleased());
        assert_eq!(slot.with_table(ProbeTable::len), Some(1));

        slot.disable();
        slot.enable();
        assert_eq!(
            slot.with_table(ProbeTable::len),
            Some(0),
            "switching off drops the readings, and switching on starts empty",
        );
    }

    /// Every producer holds a clone of one slot, so one switch reaches all.
    #[test]
    fn enabling_one_clone_enables_every_clone() {
        let slot = ProbeSlot::default();
        let held_by_a_producer = slot.clone();
        slot.enable();
        assert!(held_by_a_producer.is_enabled());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "two producers share the probe key")]
    fn two_names_under_one_probe_key_are_refused() {
        let mut probes = ProbeTable::with_defaults();
        let tile = collection(&[0], &["a"], &[]);
        probes.observe(None, 1, "Memo#1", &tile, &unreleased());
        probes.observe(None, 1, "Restrict#1", &tile, &unreleased());
    }
}

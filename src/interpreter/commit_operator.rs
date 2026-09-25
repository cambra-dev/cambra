//! The commit operator: a transaction engine as a tile operator.
//!
//! Implements the transactional time-domain machinery from
//! `src/ccl/design/mutability.md` ("The runtime engines"): concurrent
//! writers propose transactions against a shared variable, and this operator
//! serializes them onto a single `CommitTimestamp` clock, validating read sets
//! and emitting the store with a watermark.
//!
//! # Structure
//!
//! The design splits into two layers:
//! - [`CommitEngine`] — the pure serialization logic (allocate a tick, validate,
//!   commit-or-abort, advance the watermark), with no tiles; directly testable.
//! - [`CommitOperator`] / `CommitProducer` — the tile adapter: it subscribes to a
//!   *writer input* (a stream of proposals), drains it into the engine on each
//!   `get`, and renders the store tile. The writer input is wired through a
//!   `writer_input_setter` so that, in a cyclic graph, the writer can read the
//!   store back (the operator's own output) before proposing — the cyclic-`FanOut`
//!   feedback idiom. The store the writer reads carries a watermark, and the
//!   writer reports the timestamp it observed as its proposal's snapshot.
//!
//! Both the **engine** and the **operator** are multi-key. The store is
//! `Position ⇀ {key: value}`, held in the engine as one changelog per key; the in-engine
//! read is `read_as_of(t, key)` (the key's latest change at or below `t`), and the
//! whole-store render is
//! [`CommitEngine::render_full_store_tile`]. Disjoint write sets never conflict;
//! decided-absence is where a tick that wrote other keys is absent for this key,
//! though decided — its value holding from the latest earlier change.
//!
//! The operator's output is the full store as a [`Tile::Store`]: one **changelog per
//! key**, holding the ticks that wrote it against the values written. The writers *fold*
//! a changelog ([`store_current`] / [`store_value_at`]) when they read the store back
//! through the cycle — the step function, never mistaken for a directly-indexed
//! `DataFunction`. A tick's write set spanning several keys is one tick in each of their
//! changelogs, so heterogeneity across ticks needs no encoding of its own.
//!
//! A writer's *proposal*, unlike the store, carries its read and write sets as map cells:
//! each rides a [`map_to_value`] `Value::Function` in a `ColumnValue::Variants` column, so
//! the proposal stream is `step → {snap, reads, writes}` with `reads`/`writes` map-valued.
//! Their key sets are the writer's **static** footprint — a decision writes every carry key
//! of the store consuming it, and the read set names every key the writer reads, omitting
//! one the store has no value for yet. The cell is the representation they have, not one
//! the shape requires.
//!
//! # Concurrency is logical
//!
//! The interpreter is single-threaded dataflow. "Concurrent writers" means
//! multiple input domains the operator interleaves — the order in which
//! [`CommitEngine::attempt`] is called. There is no parallelism; serialization
//! semantics are validated deterministically.

use bit_set::BitSet;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ops::Bound::{Excluded, Unbounded};

use crate::ccl::F_WRITES;
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, CurryLevel, Extent, FunctionGuard, Path, Position, Predicate,
    Scheduler, SharedConsumer, Tile, TileGuard, Tiling, Value, WakeupQueue, forwarding_consumer,
    shared_consumer,
    tile_operators::{
        CycleSlot, CyclicSequencingProducer, Memo, ProducerBase, TileOperator, TileProducer,
        materialize_collections, materialized_row,
    },
    tuple_field,
};
use crate::pretty_graph::VizOptions;
use crate::pretty_tree::InspectNode;

use crate::interpreter::operator_conversion::{store_key, store_key_name};
use crate::interpreter::operator_graph::{EdgeRole, InputEdgeSpec, value, value_keyed, value_late};
use crate::interpreter::tile_operators::{
    OperatorBase, column_of_rows, impl_operator_base, impl_producer_base, stored_value_tile,
    with_values_at,
};
use crate::interpreter::tiling::{domain_prefix, running_frontier, store_frontier_rows};

/// A transaction proposal, evaluated against a snapshot.
///
/// A writer produces one of these by reading some keys at a decided snapshot and
/// deciding what to write. `reads`/`writes` are the read set and write set. A
/// read-only transaction (a guard that denies and writes nothing) is a *local*
/// decision by the writer and never becomes a proposal — only writes reach the
/// engine, so `writes` is non-empty in practice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    /// The committed prefix the writer read — a decided timestamp.
    pub snapshot: Position,
    /// Keys observed at `snapshot`, with the values seen (the read set).
    pub reads: HashMap<Value, Value>,
    /// Keys to update, with their new values (the write set).
    pub writes: HashMap<Value, Value>,
}

/// The outcome of a commit attempt under **allocate-on-commit**: a valid
/// proposal consumes the next tick and writes; a stale one consumes nothing and
/// the writer retries by re-reading and re-proposing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommitOutcome {
    Committed { ts: Position },
    Stale,
}

/// The pure serialization engine: no tiles, directly unit-testable.
///
/// **Allocate-on-commit**: a tick is consumed only by a successful commit, so
/// the timestamp domain is dense and a stale proposal leaves no trace. Validates
/// the read set with backward validation against each key's changelog.
pub struct CommitEngine {
    /// The store's value before any change: every key's initial value. Held beside
    /// the changelog rather than at a position of it, because a position-keyed
    /// changelog has no position below its first — see [`Tile::Store`]'s `seed`.
    /// A key absent here has no value until its first change (a collection-valued
    /// key, whose log starts empty).
    seed: HashMap<Value, Value>,
    /// Per key, its **changelog**: the positions that wrote it, against the values written.
    /// A position a key's changelog omits is decided-absent for that key, its value holding
    /// from the key's latest earlier change or from [`seed`](Self::seed). A key absent here
    /// has never been written, or has had its changelog reclaimed.
    ///
    /// Held per key because every question asked of it is about one key — a fold, a
    /// commit's staleness check, which versions a reclaim keeps — and the rendered store
    /// is one changelog per key too. A write set spanning several keys lands at one
    /// position in each of their changelogs.
    changes: HashMap<Value, BTreeMap<Position, Value>>,
    /// The decided frontier: every position `≤ decided` is decided. `None` before
    /// anything is decided.
    ///
    /// Bounds [`decided_positions`](Self::decided_positions) without being one of them: a
    /// store resuming its predecessor's run is decided through positions it never ran, and
    /// a reclaim trims the domain while the frontier stays.
    decided: Option<Position>,
    /// The positions this engine has decided, ascending — the store's **domain**, the
    /// set `changes` is sparse against. A position it holds that `changes` omits is
    /// a **carry**: decided, holding the latest earlier value, and recorded nowhere
    /// else. The frontier bounds this set but cannot enumerate it, and a domain whose
    /// positions are not a dense integer range cannot be enumerated from its type at
    /// all, so the engine records what it was driven at rather than leaving a reader
    /// to reconstruct it.
    ///
    /// Reclaimed with the changelog by [`gc_released_prefix`](Self::gc_released_prefix).
    /// The watermark is `decided`, which a reclaim leaves alone, so trimming this loses no
    /// bound.
    decided_positions: Vec<Position>,
}

impl CommitEngine {
    /// Create a **transactional** engine holding `init` before any commit.
    ///
    /// The commit clock's least tick is `0` — the state after no transaction — and
    /// it is decided from the start, so a writer reads the seed at a snapshot of `0`
    /// and the first commit allocates tick `1`.
    pub fn new(init: HashMap<Value, Value>) -> Self {
        Self {
            seed: init,
            changes: HashMap::new(),
            decided: Some(commit_clock_start()),
            decided_positions: vec![commit_clock_start()],
        }
    }

    /// Create an **induction** engine holding `init` before any position, decided
    /// through `resumed_after` — the last position a predecessor store reached, or
    /// `None` for one starting from the beginning.
    ///
    /// A store replacing one in a running program starts where its predecessor had
    /// reached, so everything up to `resumed_after` is already decided. This store has
    /// no record of what those positions held, so they are not its domain: a read of the
    /// store as it stands folds to the seed, which is the value the predecessor handed
    /// over.
    pub fn seeded_at(resumed_after: Option<Position>, init: HashMap<Value, Value>) -> Self {
        Self {
            decided: resumed_after,
            // The predecessor's positions are decided but this store holds no record of
            // them, so they are not its domain: a reader is offered what this store ran,
            // and the positions it inherited are ones its consumers have already taken.
            decided_positions: Vec::new(),
            ..Self::new(init)
        }
    }

    /// An engine holding nothing: no value before any position, no change, undecided.
    ///
    /// What a store that is waiting for its seed renders as, and the state the `step`/carry
    /// unit tests exercise directly. A store that has a seed opens at it through
    /// [`seeded_at`](Self::seeded_at) instead.
    pub fn unopened() -> Self {
        Self {
            seed: HashMap::new(),
            changes: HashMap::new(),
            decided: None,
            decided_positions: Vec::new(),
        }
    }

    /// The watermark frontier: all ticks `≤ watermark()` are decided. `None`
    /// before anything is decided (an induction engine before its first
    /// [`step`](Self::step); a transactional engine is decided at tick `0` from
    /// the start).
    pub fn decided_watermark(&self) -> Option<&Position> {
        self.decided.as_ref()
    }

    /// The watermark frontier of a **transactional** engine, which is decided from
    /// the start. Panics on an induction engine that has not stepped.
    fn watermark(&self) -> &Position {
        self.decided
            .as_ref()
            .expect("a transactional engine is decided at its clock's first tick from the start")
    }

    /// Position-driven induction step (the sequential, no-conflict dual of
    /// [`attempt`](Self::attempt)): advance the decided frontier to `position`
    /// **unconditionally** — every iteration position is decided — and record a
    /// write there iff `writes` is `Some`. A `None` is a **carry**: no change, the
    /// accumulator holds from the latest earlier write or from the seed. The
    /// changelog is therefore sparse in position space while the frontier tracks the
    /// whole extent — so a store with a trailing run of carries still reports the
    /// right decided region. There is no conflict/retry: a single writer visits each
    /// position once in order.
    pub fn step(&mut self, position: Position, writes: Option<HashMap<Value, Value>>) {
        debug_assert!(
            self.decided.as_ref().is_none_or(|w| position > *w),
            "induction positions advance strictly monotonically (got {position}, watermark {:?})",
            self.decided
        );
        self.decided = Some(position.clone());
        self.decided_positions.push(position.clone());
        if let Some(w) = writes {
            self.write_at(&position, w);
        }
        self.debug_check();
    }

    /// Land `writes` at `position`, one entry in each key's changelog.
    fn write_at(&mut self, position: &Position, writes: HashMap<Value, Value>) {
        for (key, value) in writes {
            self.changes
                .entry(key)
                .or_default()
                .insert(position.clone(), value);
        }
    }

    /// The position `key` was last written at, or `None` where it stands at its seed.
    fn latest_write(&self, key: &Value) -> Option<&Position> {
        self.changes
            .get(key)
            .and_then(|log| log.last_key_value())
            .map(|(position, _)| position)
    }

    /// The invariants no type holds: the domain ascends, it lies within the frontier, and
    /// no change lands above the frontier.
    fn debug_check(&self) {
        debug_assert!(
            self.decided_positions.windows(2).all(|w| w[0] < w[1]),
            "a store's decided positions ascend: {:?}",
            self.decided_positions
        );
        debug_assert!(
            self.decided_positions
                .last()
                .is_none_or(|last| self.decided.as_ref().is_some_and(|w| last <= w)),
            "a store's decided positions lie within its frontier {:?}: {:?}",
            self.decided,
            self.decided_positions
        );
        debug_assert!(
            self.changes.values().all(|log| log
                .last_key_value()
                .is_none_or(|(p, _)| self.decided.as_ref().is_some_and(|w| p <= w))),
            "no change lands above a store's frontier {:?}",
            self.decided
        );
        // A change is made at a position the store decided. A reclaim drops positions from
        // the domain but keeps, per key, the latest change at or before the earliest live
        // one, since a live position folds to it: that one carry source may lie below
        // the domain, and nothing else outside it.
        #[cfg(debug_assertions)]
        {
            let stray: Vec<(&Value, Vec<&Position>)> = self
                .changes
                .iter()
                .map(|(key, log)| {
                    let outside: Vec<&Position> = log
                        .keys()
                        .filter(|p| self.decided_positions.binary_search(p).is_err())
                        .collect();
                    (key, outside)
                })
                .filter(|(_, outside)| {
                    outside.len() > 1
                        || outside.iter().any(|p| {
                            self.decided_positions
                                .first()
                                .is_some_and(|first| *p > first)
                        })
                })
                .collect();
            debug_assert!(
                stray.is_empty(),
                "a store's changes lie at its decided positions, bar one carry source per key \
                 below them: {stray:?} outside {:?}",
                self.decided_positions
            );
        }
    }

    /// Validate and (if valid) commit one proposal. Allocate-on-commit: a valid
    /// proposal consumes the next tick and applies its write set; a stale one
    /// consumes no tick and returns [`CommitOutcome::Stale`], leaving the writer
    /// to retry.
    pub fn attempt(&mut self, p: Proposal) -> CommitOutcome {
        debug_assert!(
            p.snapshot <= *self.watermark(),
            "proposal snapshot {} is beyond the watermark {}",
            p.snapshot,
            self.watermark()
        );
        debug_assert!(
            p.reads
                .iter()
                .all(|(k, v)| self.read_as_of(&p.snapshot, k).as_ref() == Some(v)),
            "a proposal read does not match the store at its snapshot"
        );

        // Backward validation: no key the writer read may have been overwritten
        // by a commit after the snapshot. Disjoint write sets never conflict.
        let stale = p
            .reads
            .keys()
            .any(|k| self.latest_write(k).is_some_and(|t| *t > p.snapshot));
        if stale {
            return CommitOutcome::Stale;
        }
        // Allocate-on-commit on a dense clock: the watermark is the last allocated
        // tick, so the next one follows it.
        let c = next_commit_tick(self.watermark());
        self.decided = Some(c.clone());
        self.decided_positions.push(c.clone());
        self.write_at(&c, p.writes);
        self.debug_check();
        CommitOutcome::Committed { ts: c }
    }

    /// The value of `key` as of timestamp `t` — the latest write to `key` at a
    /// tick `≤ t`, folding past ticks that wrote other keys, and the seed where
    /// there is none — or `None` if `t` is beyond the watermark or `key` has
    /// neither a write at or below `t` nor a seed.
    pub fn read_as_of(&self, t: &Position, key: &Value) -> Option<Value> {
        if self.decided.as_ref().is_none_or(|w| t > w) {
            return None;
        }
        self.changes
            .get(key)
            .and_then(|log| log.range(..=t).next_back())
            .map(|(_, value)| value.clone())
            .or_else(|| self.seed.get(key).cloned())
    }

    /// Read-side commit-log GC: reclaim the committed versions at positions `≤ through`,
    /// keeping each key's **carry source** where a position can still fold back to it.
    ///
    /// A key's carry source is its latest write at or below `through`. It is kept where the
    /// key has no write above `through`, since every later position reads it, including
    /// positions not run yet; and where the earliest live position lies below the key's next
    /// write above `through`. Otherwise every live position reads a write of its own, and the
    /// entry goes. Keeping the key's latest write overall instead would be wrong: a key
    /// written at positions 1 and 5 and released through 3 still answers position 4 from the
    /// write at 1. At most one entry per key survives from the prefix, whichever reason
    /// keeps it.
    ///
    /// The decided domain loses the released positions and the frontier stays: see
    /// `src/interpreter/design-operators.md`, "Reclaiming the changelog". Soundness rests
    /// on the caller passing only a region every consumer has released (the `FanOut`'s
    /// meet), so nothing dropped here is read again.
    pub fn gc_released_prefix(&mut self, through: &Position) {
        #[cfg(debug_assertions)]
        let (keys, live) = (
            self.changes
                .keys()
                .chain(self.seed.keys())
                .cloned()
                .collect::<Vec<_>>(),
            self.decided_positions
                .iter()
                .filter(|p| *p > through)
                .chain(self.decided.iter())
                .cloned()
                .collect::<Vec<_>>(),
        );
        #[cfg(debug_assertions)]
        let before = self.folds_at(&keys, &live);
        // Read before the domain is trimmed: whether a key's carry source is reachable is
        // asked against the earliest position still live.
        let earliest_live = self
            .decided_positions
            .iter()
            .find(|p| *p > through)
            .cloned();
        // The released positions leave the domain. The watermark is `decided`, which a
        // release leaves alone: it says a position will not be read at again, not that the
        // store never ran it.
        self.decided_positions.retain(|p| p > through);
        for log in self.changes.values_mut() {
            // The latest write in the prefix is the carry source of every position below
            // the key's next write above the boundary. A write of its own supersedes it from
            // there on, and every position the store has yet to run is above that too, so
            // only a live position below it still folds back past it. With nothing above
            // the boundary, the entry is the key's value for the rest of the run.
            let reachable = match log.range((Excluded(through), Unbounded)).next() {
                Some((next, _)) => earliest_live.as_ref().is_some_and(|live| live < next),
                None => true,
            };
            let carry_source = reachable
                .then(|| log.range(..=through).next_back())
                .flatten()
                .map(|(p, v)| (p.clone(), v.clone()));
            log.retain(|p, _| p > through);
            if let Some((p, v)) = carry_source {
                log.insert(p, v);
            }
        }
        self.changes.retain(|_, log| !log.is_empty());
        self.debug_check();
        #[cfg(debug_assertions)]
        debug_assert!(
            self.folds_at(&keys, &live) == before,
            "a reclaim changes no fold still reachable: reclaiming through {through} changed \
             the value of some key at a live position or the frontier ({live:?})"
        );
    }

    /// Every key's value at every one of `positions`, for the check that a reclaim leaves
    /// each reachable fold as it was.
    #[cfg(debug_assertions)]
    fn folds_at(&self, keys: &[Value], positions: &[Position]) -> Vec<Option<Value>> {
        keys.iter()
            .flat_map(|key| positions.iter().map(|p| self.read_as_of(p, key)))
            .collect()
    }

    /// Render the full store as a [`Tile::Store`] over `tiling`: one changelog per key,
    /// holding the ticks at which the engine committed a write to it against the values
    /// written, with `frontier` the watermark. A consumer reads state by *folding* a
    /// changelog ([`store_value_at`] / [`store_snapshot_at`], latest tick `≤ t`); a tick
    /// a changelog omits is decided-absent for that key, its value holding from the
    /// latest earlier change. This is the multi-key operator's output — the writers read
    /// it back through the cycle, and it is the step function, not a `DataFunction`, so the
    /// fold cannot be mistaken for direct indexing.
    ///
    /// The key space comes from `tiling` rather than from the commits, so a key the
    /// engine has never written is present with an empty changelog. That is what a fold
    /// needs to distinguish "written nothing yet" from "not a key of this store".
    pub fn render_full_store_tile(&self, tiling: &Tiling) -> Tile {
        store_tile(&[self], tiling, false)
    }

    /// The decided frontier as a predicate: the watermark, or `False` for an induction
    /// engine that has not stepped yet. It is `at_or_below(w)` even when the latest
    /// position(s) carried no write, so a trailing run of carries stays decided — a
    /// changelog is sparse but the frontier is not.
    fn frontier_predicate(&self) -> Predicate {
        match self.decided_watermark() {
            Some(w) => Predicate::at_or_below(w.value().clone()),
            None => Predicate::False,
        }
    }
}

/// A recurrence as a tile: one [`Tile::Store`] per open store, under one collection level
/// per row level above it.
///
/// Walks the nesting rather than reconstructing it. Each store's changelog, seed and
/// decided set come from its own engine, so the rendered tile is the engine structure with
/// its levels vectorized — the two shapes agree by construction instead of by a
/// partitioning step that has to agree with them both.
///
/// `complete` is one predicate per level of the body's decision stream, outermost first:
/// the row levels above the stores, then the positions within one. That is the drive's to
/// say, from its source, because a row has to be answerable while it is still the one being
/// run, and every level answers for its own rows. A carrier with no rows above it has one
/// level and one store.
fn render_carrier_tile(engines: &Engines, tiling: &Tiling, complete: &[Predicate]) -> Tile {
    // A level's predicate means complete at every depth beneath it, so the outermost
    // saying `True` says the whole carrier is done: every level below is complete too, and
    // every store in the render is terminal. Spread here rather than at each level, so a
    // consumer reading one level does not have to re-derive it from the level above.
    let done = complete.first().is_some_and(Predicate::is_true);
    let spread;
    let complete = if done {
        spread = vec![Predicate::True; complete.len()];
        &spread[..]
    } else {
        complete
    };
    render_carrier_level(engines, tiling, complete, done)
}

/// One level of [`render_carrier_tile`]'s walk, with `terminal` the whole carrier's.
fn render_carrier_level(
    engines: &Engines,
    tiling: &Tiling,
    complete: &[Predicate],
    terminal: bool,
) -> Tile {
    let (level_complete, beneath) = complete.split_first().unwrap_or_else(|| {
        unreachable!("a carrier states completion at every level of its decision stream")
    });
    let Tiling::DataFunction {
        domain: enclosing,
        codomain: store_tiling,
    } = tiling
    else {
        // No rows above, so the whole tile is the one store and `level_complete` is the
        // positions within it — the degenerate case of the level below, reached directly
        // because there is no level above it to be reached from.
        debug_assert!(
            beneath.is_empty(),
            "a carrier with no rows above it states completion once, got {complete:?}"
        );
        let Engines::Store(engine) = engines else {
            panic!("a carrier with no rows above it holds one store, got a level")
        };
        // One store, whether or not its seed has arrived: there is no level above to key it
        // by, so the node exists from the start and an unopened one renders as what it
        // holds — an undecided frontier, no change, no value before any position.
        // Terminal only once open: a store's value before any position is its seed, so a
        // loop that ran no position answers with it, and a store without one has not
        // answered yet.
        let unopened = CommitEngine::unopened();
        return store_tile(
            &[engine.as_ref().unwrap_or(&unopened)],
            tiling,
            terminal && engine.is_some(),
        );
    };
    let Engines::Rows(rows) = engines else {
        panic!("a carrier with rows above it holds one engine per row, got a bare store")
    };
    // A **standing** level: each of its rows holds a carrier of its own, rendered by the
    // same walk, and answering for its own rows out of the same per-level statement.
    // A level called complete is complete at every depth beneath it, which is why the
    // carrier level below can state its own for the running row alone.
    if store_tiling.is_data_function() {
        let mut starts = Vec::with_capacity(rows.len());
        let mut merged: Option<Tile> = None;
        for (_, below) in rows {
            let piece = render_carrier_level(below, store_tiling, beneath, terminal);
            starts.push(merged.as_ref().map_or(0, |t| match t {
                Tile::DataFunction { domain, .. } => domain.len(),
                _ => 0,
            }));
            match &mut merged {
                None => merged = Some(piece),
                // One standing row's carrier follows the previous one's rather than
                // describing the same rows: two standing rows key their carriers
                // independently, so running them together makes one row whose keys
                // descend where the second restarts.
                Some(acc) => acc.merge_rows(piece),
            }
        }
        let enclosing_rows: Vec<Value> = rows.iter().map(|(row, _)| row.clone()).collect();
        let Some(Tile::DataFunction {
            domain: below_keys,
            codomain: below_values,
            domain_predicate: below_pred,
            deleted: below_deleted,
            ..
        }) = merged
        else {
            // No enclosing row opened yet, so there is nothing beneath to assemble. The
            // whole tiling's empty tile, not the level below's: a standing level short
            // here is a tile that does not match what it declares.
            //
            // It still carries what every level calls complete. A carrier that opened no
            // row has still been told which rows will gain no position — the source put
            // none under them — and `empty_tile` says `False` at every level, which is the
            // other thing: a level that has delivered nothing and may yet. Dropped, the
            // reduction above never answers a row and the loop around it waits forever.
            return empty_carrier(tiling, complete, terminal);
        };
        return Tile::data_function(
            ColumnValue::from_values(enclosing_rows, enclosing),
            Box::new(Tile::grouped(
                ColumnValue::UInts(starts),
                below_keys,
                below_values,
                below_pred,
                below_deleted,
            )),
            level_complete.clone(),
            BitSet::new(),
        );
    }
    let per_row: Vec<&CommitEngine> = rows
        .iter()
        .map(|(row, at)| match at {
            Engines::Store(Some(engine)) => engine,
            Engines::Store(None) => {
                unreachable!("a row exists once its store is opened, so row {row} holds one")
            }
            Engines::Rows(_) => {
                unreachable!("a standing level is rendered above, so these rows hold stores")
            }
        })
        .collect();
    Tile::data_function(
        ColumnValue::from_values(rows.iter().map(|(row, _)| row.clone()).collect(), enclosing),
        Box::new(store_tile(&per_row, store_tiling, terminal)),
        level_complete.clone(),
        BitSet::new(),
    )
}

/// The [`Tile::Store`] a run of engines renders to: one changelog per key, holding the
/// positions at which an engine committed a write to it against the values written, with
/// `frontier` the watermark. A consumer reads state by *folding* a changelog
/// ([`store_value_at`] / [`store_snapshot_at`], latest position `≤ t`); a position a
/// changelog omits is decided-absent for that key, its value holding from the latest
/// earlier change. This is not a `DataFunction`, so the fold cannot be mistaken for direct
/// indexing.
///
/// `engines` are the stores this node stands over — one per row of the level above it, or
/// the single store of a carrier with no rows above it. Their changelogs run together
/// CSR-wise under one node per key, because a changelog is a collection whose rows are the
/// stores; a lone store is the one-row case of that and needs no separate shape.
///
/// The key space comes from `tiling` rather than from the commits, so a key no engine has
/// written is present with an empty changelog. That is what a fold needs to distinguish
/// "written nothing yet" from "not a key of this store".
fn store_tile(engines: &[&CommitEngine], tiling: &Tiling, terminal: bool) -> Tile {
    let Tiling::Record(logs) = tiling.store_state() else {
        unreachable!("a store's state tiling is a record of per-key changelogs")
    };
    let domain = tiling
        .domain_extent()
        .expect("a store tiling names its domain");
    debug_assert!(
        engines
            .iter()
            .flat_map(|e| e.changes.keys().chain(e.seed.keys()))
            .all(|key| { store_key_name(key).is_some_and(|name| logs.contains_key(name)) }),
        "a write or seed names a key outside the store's declared key space, so \
         rendering would drop it: declared {:?}",
        logs.keys().collect::<Vec<_>>(),
    );
    // The changelogs and the frontiers are each store's **own** positions. A changelog's
    // own predicate is one statement for the whole level, so it says what the store still
    // running has decided — the only open one, the drive being sequential — and each row's
    // watermark is its own entry of `frontier`.
    let open_frontier = engines
        .last()
        .map_or(Predicate::False, |engine| engine.frontier_predicate());
    let mut seed_fields = HashMap::with_capacity(logs.len());
    let state = logs
        .into_iter()
        .map(|(key, log)| {
            let Tiling::DataFunction { codomain, .. } = log else {
                unreachable!("a store key's changelog tiling is a collection")
            };
            let runtime = store_key(&key, Value::Unit);
            let mut starts = Vec::with_capacity(engines.len());
            let mut positions: Vec<Value> = Vec::new();
            let mut written: Vec<Value> = Vec::new();
            for engine in engines {
                starts.push(positions.len());
                for (pos, v) in engine.changes.get(&runtime).into_iter().flatten() {
                    positions.push(pos.value().clone());
                    written.push(v.clone());
                }
            }
            // A seed column is read **per row**, so it holds one value per row — or none
            // at all, which is how a key the seed omits (a collection-valued one, whose
            // log starts empty) is spelled. Anything between attributes every seed past
            // the gap to the wrong row, which is a wrong answer rather than a crash: the
            // column carries no keys of its own to disagree with.
            let seeds: Vec<Value> = engines
                .iter()
                .filter_map(|engine| engine.seed.get(&runtime).cloned())
                .collect();
            assert!(
                seeds.is_empty() || seeds.len() == engines.len(),
                "a store key's seed is one value per row or none at all: `{key}` has {} \
                 over {} rows",
                seeds.len(),
                engines.len()
            );
            seed_fields.insert(
                key.clone(),
                Tile::Scalar(ColumnValue::from_values(seeds, &codomain.extent())),
            );
            let tile = Tile::grouped(
                ColumnValue::UInts(starts),
                ColumnValue::from_values(positions, &domain),
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    written,
                    &codomain.extent(),
                ))),
                // A changelog holds every write its engine has committed, so it is decided
                // exactly where that store is. The store's own `frontier` is what a
                // consumer reads; this keeps the sub-tile self-describing.
                open_frontier.clone(),
                BitSet::new(),
            );
            (key, tile)
        })
        .collect();
    let decided: Vec<Vec<Position>> = engines
        .iter()
        .map(|engine| engine.decided_positions.clone())
        .collect();
    Tile::Store {
        state: Box::new(Tile::Record(state)),
        seed: Box::new(Tile::Record(seed_fields)),
        decided: Box::new(decided_positions_tile(&decided, &domain)),
        frontier: Box::new(store_frontier_rows(
            engines
                .iter()
                .map(|engine| engine.decided.as_ref().map(|w| w.value().clone())),
            &domain,
        )),
        terminal,
        closed_keys: Vec::new(),
    }
}

/// `tiling`'s empty tile, carrying `complete` — one predicate per level, outermost first —
/// and `terminal` on the store beneath them.
///
/// [`Tiling::empty_tile`] states `False` at every level, which says a level has delivered
/// nothing and may yet. A carrier that opened no row says something else at the levels its
/// drive has heard about: those rows will gain no position at all.
fn empty_carrier(tiling: &Tiling, complete: &[Predicate], terminal: bool) -> Tile {
    let mut tile = tiling.empty_tile();
    for (level, pred) in complete.iter().enumerate() {
        if let Tile::DataFunction {
            domain_predicate, ..
        } = tile.values_at_mut(CurryLevel::new(level))
        {
            *domain_predicate = pred.clone();
        }
    }
    if let Tile::Store { terminal: t, .. } = tile.values_at_mut(CurryLevel::values_of(tiling)) {
        *t = terminal;
    }
    tile
}

/// A recurrence's engines, nested one node per collection level above the store.
///
/// This is the shape of the tile it renders to — a [`Tile::Store`] under as many
/// [`Tile::DataFunction`] levels as the carrier has — so the two do not have to be held in
/// step by hand. A flat store is [`Engines::Store`] alone; a nested carrier is one
/// [`Engines::Rows`] over its enclosing rows; a carrier beneath a standing level is two,
/// and a third needs no arm added. That is what makes nesting unbounded here rather than
/// a depth the code counts.
///
/// **Positions are a store's own.** A composite `(enclosing, inner)` position exists only
/// to tell a flat map which nest a position belongs to; the nesting says it instead, and a
/// path is the row values down to a store plus a position inside it.
pub enum Engines {
    /// One store's state, `None` until its seed arrives.
    ///
    /// A store holds a value before any of its positions, so it cannot exist before that
    /// value does: a carry at its first position folds to the seed, and an engine opened
    /// without one answers a value the recurrence never held.
    Store(Option<CommitEngine>),
    /// One node per row of this level, in the order the drive opened them.
    ///
    /// A list rather than a map: the drive is sequential, so the row being added to is the
    /// last, and rendering wants them in that order anyway.
    Rows(Vec<(Value, Engines)>),
}

impl Engines {
    /// The tree a carrier of `tiling` starts with: a row set per collection level above
    /// its stores, and nothing opened.
    ///
    /// The shape is read off the tiling rather than off a depth the caller counts, so the
    /// tree and the tile it renders to cannot disagree.
    pub fn unopened(tiling: &Tiling) -> Engines {
        if tiling.is_data_function() {
            Engines::Rows(Vec::new())
        } else {
            Engines::Store(None)
        }
    }

    /// The rows of this level, or `&[]` at a store.
    pub fn rows(&self) -> &[(Value, Engines)] {
        match self {
            Engines::Store(_) => &[],
            Engines::Rows(rows) => rows,
        }
    }

    /// The store at `path`, opening the rows along the way where they do not exist yet and
    /// seeding the one at the end with `seed`.
    ///
    /// Opening on the way down is what lets the drive reach a row without a separate
    /// announcement: a row exists once a position of it is decided, which is the same
    /// moment the tile gains it. `seed` runs at most once per call — only where `path`
    /// named a store that was not open — so the caller closes over the path rather than
    /// being handed it back.
    pub fn store_at(
        &mut self,
        path: &[Value],
        seed: &mut dyn FnMut() -> CommitEngine,
    ) -> &mut CommitEngine {
        let Some((row, rest)) = path.split_first() else {
            let Engines::Store(engine) = self else {
                panic!("a path that names no further row ends at a store, got a level")
            };
            return engine.get_or_insert_with(seed);
        };
        let Engines::Rows(rows) = self else {
            panic!("a path naming row {row} descends a level, got a store")
        };
        let at = match rows.iter().position(|(r, _)| r == row) {
            Some(at) => at,
            None => {
                debug_assert!(
                    rows.last().is_none_or(|(last, _)| {
                        Position::new(row.clone()) > Position::new(last.clone())
                    }),
                    "a level's rows open in ascending order: opening row {row} at or below \
                     {:?}, the last row opened",
                    rows.last().map(|(last, _)| last)
                );
                let opened = if rest.is_empty() {
                    Engines::Store(None)
                } else {
                    Engines::Rows(Vec::new())
                };
                rows.push((row.clone(), opened));
                rows.len() - 1
            }
        };
        rows[at].1.store_at(rest, seed)
    }

    /// The store at `path`, or `None` where no row along it has been opened.
    pub fn get(&self, path: &[Value]) -> Option<&CommitEngine> {
        match (self, path.split_first()) {
            (Engines::Store(engine), None) => engine.as_ref(),
            (Engines::Rows(rows), Some((row, rest))) => {
                rows.iter().find(|(r, _)| r == row)?.1.get(rest)
            }
            _ => None,
        }
    }

    /// Every open store, with the path of rows that reaches it — the empty path for a
    /// carrier with no rows above it.
    ///
    /// A callback rather than an iterator: the path is rebuilt as the walk descends, so
    /// handing it out would mean allocating one per store.
    pub fn for_each_store_mut(&mut self, visit: &mut dyn FnMut(&[Value], &mut CommitEngine)) {
        fn walk(
            at: &mut Engines,
            path: &mut Vec<Value>,
            visit: &mut dyn FnMut(&[Value], &mut CommitEngine),
        ) {
            match at {
                Engines::Store(Some(engine)) => visit(path, engine),
                Engines::Store(None) => {}
                Engines::Rows(rows) => {
                    for (row, below) in rows {
                        path.push(row.clone());
                        walk(below, path, visit);
                        path.pop();
                    }
                }
            }
        }
        walk(self, &mut Vec::new(), visit);
    }

    /// Drop every row the guard covers whole, leaving the rest untouched.
    ///
    /// The render walks this tree, so a row the release names whole has to leave the tree in
    /// the same step: dropped from the render alone, the next render would rebuild it from
    /// the engine still holding it. A row is named whole once every branch of the carrier's
    /// `FanOut` names it — the drive for each row it has finished, a per-row reduction for
    /// each row its consumer has taken.
    pub fn remove_covered(&mut self, guard: &TileGuard) {
        fn walk(at: &mut Engines, path: &mut Vec<Value>, guard: &TileGuard) {
            let Engines::Rows(rows) = at else { return };
            rows.retain_mut(|(row, below)| {
                path.push(row.clone());
                let covered = guard.covers_path(path);
                if !covered {
                    walk(below, path, guard);
                }
                path.pop();
                !covered
            });
        }
        walk(self, &mut Vec::new(), guard);
    }
}

/// The commit clock's least position — the state after no transaction, which is
/// decided from the moment a transactional store exists.
///
/// The `Txn` domain is the runtime's monotonic commit counter, so its positions are
/// `UInt` and its successor is the next integer. An induction store's domain is the
/// loop extent instead, whose positions come from the source, which is why these two
/// are the commit side's alone.
pub fn commit_clock_start() -> Position {
    Position::new(Value::UInt(0))
}

/// The commit clock tick after `t`, allocated by a successful commit.
fn next_commit_tick(t: &Position) -> Position {
    let Value::UInt(n) = t.value() else {
        panic!("the commit clock is a UInt counter, so its watermark is a UInt: {t}")
    };
    Position::new(Value::UInt(n + 1))
}

/// Why one pull of a seed stream carries no value.
enum SeedNotReady {
    /// A value-shaped tile holding no row: nothing has arrived under it yet, and a later
    /// pull may carry it.
    Empty,
    /// A tile that is not yet the whole seed — a collection whose key set is still open,
    /// or a shape no value has been folded out of.
    Undecided,
}

/// One pull of a seed stream as the value the store holds before any of its positions.
///
/// A seed is one value per key however the producer that supplied it was shaped: a scalar,
/// a struct-of-arrays record, or a collection-valued variable's whole map
/// ([`materialized_row`] is what reads each as one). Only a **decided** collection is the
/// whole of it — an open one would seed the store with whichever keys had arrived, which
/// is a partial map presented as the value before any position.
fn seed_value(tile: &Tile) -> Result<Value, SeedNotReady> {
    if !is_whole_value(tile) {
        return Err(SeedNotReady::Undecided);
    }
    match tile {
        // A decided collection is a value at every row it has, the empty map included, so
        // there is no emptiness to test past the domain being closed.
        Tile::DataFunction { .. } => Ok(materialized_row(tile.clone())),
        Tile::Scalar(_) | Tile::Record(_) => {
            let column = materialize_collections(tile.clone());
            if column.is_empty() {
                Err(SeedNotReady::Empty)
            } else {
                Ok(column.index_at(0))
            }
        }
        // A store, an aggregation or a grouping is not something a store holds: whatever
        // reduces it to a value has not run yet.
        _ => Err(SeedNotReady::Undecided),
    }
}

/// Whether every collection in a one-row value tile is complete, so the tile is the whole
/// value rather than part of it. Completeness is downward-closed, so a collection closed at
/// its outermost level is closed beneath; a record's fields stand over the same row, so each
/// must be whole on its own.
fn is_whole_value(tile: &Tile) -> bool {
    match tile {
        Tile::DataFunction {
            domain_predicate, ..
        } => matches!(domain_predicate, Predicate::True),
        Tile::Scalar(_) => true,
        Tile::Record(fields) => fields.values().all(is_whole_value),
        _ => false,
    }
}

/// The watermark of a store tile's `frontier` predicate (the decode behind
/// [`store_frontier`]). A store always carries its watermark as `at_or_below(w)`
/// — terminality is a separate flag, never a `True` frontier that would discard
/// `w` — so the watermark reads directly and counts trailing carries. `None` for
/// an undecided/empty changelog.
fn frontier_from_domain(domain_predicate: &Predicate) -> Option<Position> {
    domain_predicate.as_at_or_below().map(Position::new)
}

// ── Step-function reads over a `Tile::Store` changelog ────────────────────────
//
// A `Tile::Store` *is* its changelogs: key `k`'s holds the ticks that wrote `k`,
// strictly ascending, against the values written there, with `frontier` the decided
// watermark. These four functions are the sanctioned way to read a store's value — a
// plain index into a changelog is meaningless, because a tick absent from it is
// *decided-absent* (its value holds from the latest earlier change), not unknown. They
// fold with right-continuous step interpolation, and are the single tile-level store
// read: the writers (`store_current`) and the value-stream projection both route through
// them, the tile-side counterpart of the engine's own `read_as_of` fold over its BTreeMap.

/// The decided frontier tick of a store tile, from its `frontier` predicate. `None` if
/// `tile` is not a [`Tile::Store`] or is undecided. A store with no change at all is
/// decided wherever its frontier says: the changelog is sparse, so an empty one is a
/// run of carries over the seed rather than an absence of decisions.
/// Mirrors [`frontier_from_domain`]: `at_or_below(w)` reads the watermark directly.
pub fn store_frontier(tile: &Tile) -> Option<Position> {
    let Tile::Store { frontier, .. } = tile else {
        return None;
    };
    frontier_from_domain(&running_frontier(frontier))
}

/// `key`'s value as of commit time `t`: the latest change at a tick `≤ t` whose
/// delta wrote `key`, folding past ticks that wrote only other keys. `None` if
/// `tile` is not a store or `key` was never written at or below `t`. The
/// tile-level analog of [`CommitEngine::read_as_of`] (which folds the engine's
/// `BTreeMap`); this folds the rendered changelog a consumer holds.
pub fn store_value_at(tile: &Tile, t: &Position, key: &Value) -> Option<Value> {
    let (written, values) = changelog(tile, key)?;
    // Scan newest-first: the last position `≤ t` in `key`'s changelog is its value as
    // of `t` (positions ascending, so once one is `≤ t` every earlier index is too).
    // With no change at or below `t` the key still stands at the store's seed.
    (0..written.len())
        .rev()
        .find(|i| Position::new(written.index_at(*i)) <= *t)
        .map(|i| changelog_value(values, i))
        .or_else(|| store_seed_value(tile, key))
}

/// `key`'s value before any change — the store's seed. `None` if `tile` is not a
/// store, `key` is outside its key space, or the key has no value until its first
/// change (a collection-valued one, whose log starts empty).
pub fn store_seed_value(tile: &Tile, key: &Value) -> Option<Value> {
    Some(tile.store_seed(store_key_name(key)?)?.index_at(0))
}

/// `key`'s value written **at exactly** tick `t` — the delta at tick `t` if it
/// names `key`, else `None`. Unlike [`store_value_at`] (which carries the latest
/// write ≤ `t` forward), this reads only the change *at* `t`: the per-position
/// event a reply tap is, so a position that did not fire the tap yields `None`
/// (and the dense read omits it).
pub fn store_delta_at(tile: &Tile, t: &Position, key: &Value) -> Option<Value> {
    let (written, values) = changelog(tile, key)?;
    (0..written.len())
        .find(|i| &written.index_at(*i) == t.value())
        .map(|i| changelog_value(values, i))
}

/// Fold `key`'s value at changelog tick `t` under the store's **carry policy** —
/// the one place the carry-vs-tap distinction lives, shared by both changelog
/// readers ([`StoreValueStream`] over commit ticks and [`StoreDenseRead`] over
/// loop positions):
///
/// - a **carry** (`carry_forward: true`) holds its latest write
///   forward — the value as-of `t` is the latest write ≤ `t` ([`store_value_at`]);
/// - a **reply tap** (`carry_forward: false`) is a per-tick event — a value only
///   at the tick that actually wrote it ([`store_delta_at`]), `None` elsewhere.
///
/// Both readers differ in *which* ticks they fold and how they label the domain
/// (commit clock vs loop position), but the per-tick fold is this.
pub fn fold_changelog_key(
    tile: &Tile,
    t: &Position,
    key: &Value,
    carry_forward: bool,
) -> Option<Value> {
    if carry_forward {
        store_value_at(tile, t, key)
    } else {
        store_delta_at(tile, t, key)
    }
}

/// A store's decided positions at `row` of its enclosing level, ascending.
///
/// The positions are the collection's *keys*: a set is a collection holding nothing, so
/// the values are [`ColumnValue::Units`] and only the keys carry information.
pub fn store_decided_positions(decided: &Tile, row: usize) -> Vec<Position> {
    let Tile::DataFunction { domain, .. } = decided else {
        return Vec::new();
    };
    let (from, to) = decided.row_run(row);
    (from..to)
        .map(|i| Position::new(domain.index_at(i)))
        .collect()
}

/// The decided-position collection for a store over `rows.len()` enclosing rows.
fn decided_positions_tile(rows: &[Vec<Position>], domain: &Extent) -> Tile {
    let mut starts = Vec::with_capacity(rows.len());
    let mut positions = Vec::new();
    for row in rows {
        starts.push(positions.len());
        positions.extend(row.iter().map(|p| p.value().clone()));
    }
    let len = positions.len();
    Tile::grouped(
        ColumnValue::UInts(starts),
        ColumnValue::from_values(positions, domain),
        Box::new(Tile::Scalar(ColumnValue::Units(len))),
        Predicate::True,
        BitSet::new(),
    )
}

/// Fold `key` over an **ascending** sequence of `query_ticks` in a single
/// O(changes + queries) pass — the incremental form of [`fold_changelog_key`],
/// so a full-stream reader folding every tick is linear, not O(changes ×
/// queries) (a per-tick [`fold_changelog_key`] each re-scans the whole log). Both
/// changelog readers ([`StoreValueStream`], [`StoreDenseRead`]) share it.
///
/// Result element `i` is the fold at `query_ticks[i]` under the carry policy: the
/// latest write ≤ the tick (`carry_forward: true`, an accumulator carried across
/// ticks that did not write `key`), or the exact-tick delta (`carry_forward:
/// false`, a reply tap — `None` where the tick did not write `key`). Requires
/// `changes` ascending (the render invariant) and `query_ticks` ascending; the
/// cursor advances monotonically and never rewinds.
pub fn fold_changelog_key_ascending(
    tile: &Tile,
    query_positions: impl IntoIterator<Item = Position>,
    key: &Value,
    carry_forward: bool,
) -> Vec<Option<Value>> {
    let queries: Vec<Position> = query_positions.into_iter().collect();
    let Some((written, values)) = changelog(tile, key) else {
        return vec![None; queries.len()];
    };
    let n = written.len();
    let mut idx = 0usize; // next unprocessed change index (monotonic)
    // The running latest write ≤ the current query, starting at the store's seed —
    // the value every key holds before its first change.
    let mut carry: Option<Value> = store_seed_value(tile, key);
    let mut out = Vec::with_capacity(queries.len());
    for t in queries {
        let mut exact: Option<Value> = None;
        while idx < n {
            let position = Position::new(written.index_at(idx));
            if position > t {
                break;
            }
            let v = changelog_value(values, idx);
            if position == t {
                exact = Some(v.clone());
            }
            carry = Some(v);
            idx += 1;
        }
        out.push(if carry_forward { carry.clone() } else { exact });
    }
    out
}

/// The full snapshot record as of commit time `t`: every key's latest change at
/// a tick `≤ t`, folded oldest-to-newest so later writes win. Empty if `tile` is
/// not a store or has no change `≤ t`. This is the multi-key,
/// **snapshot-consistent** read — one fold yields a coherent record across all
/// keys at a single commit time, which a bank of independent per-key
/// `DataFunction` reads (the source of the read-skew divergence) cannot.
pub fn store_snapshot_at(tile: &Tile, t: &Position) -> HashMap<Value, Value> {
    tile.store_keys()
        .filter_map(|name| {
            let key = store_key(name, Value::Unit);
            Some((key.clone(), store_value_at(tile, t, &key)?))
        })
        .collect()
}

/// `key`'s value as the store currently stands: its latest change at or below the
/// decided frontier, or the seed when the store has decided nothing. `None` only
/// where the store holds no value for `key` at all.
///
/// This is the read that asks what a variable *is*, as against
/// [`store_current`], which asks what it is at a position the store has decided.
/// A store that has decided nothing still holds its seed, and a store resumed from
/// a retired version holds that version's value there.
pub fn store_value_now(tile: &Tile, key: &Value) -> Option<Value> {
    match store_frontier(tile) {
        Some(f) => store_value_at(tile, &f, key),
        None => store_seed_value(tile, key),
    }
}

/// `key`'s current value — its latest change at or below the decided frontier —
/// with the frontier tick. `None` if the store is undecided/empty or `key` was
/// never written. Unlike an `ExtractFinal` over a `DataFunction`, this is
/// defined *without the stream ever terminating*: it reads the decided frontier,
/// which a live store advances on every commit. This is the read the writers
/// perform on the store they read back through the cycle.
pub fn store_current(tile: &Tile, key: &Value) -> Option<(Position, Value)> {
    let f = store_frontier(tile)?;
    store_value_at(tile, &f, key).map(|v| (f, v))
}

/// A compacting prefix watermark over a monotone domain.
///
/// Several commit-store readers/producers emit an append-only stream and, as a
/// consumer releases a prefix, must stop re-emitting positions at or below the
/// released edge (a re-emit would duplicate a domain position through a `Memo`
/// merge, or re-latch a frozen `AsOf` snapshot). Each one otherwise hand-rolls
/// the same watermark plus the monotone-max fold and the "≤ watermark" test; this
/// centralizes that state and those two operations. The callers keep whatever
/// *extra* work rides their release (forwarding the release upstream, compacting a
/// `latched` set) — only the watermark itself lives here.
#[derive(Default)]
struct PrefixReleaseCursor {
    /// What has been released: nothing, a prefix through a position, or the whole
    /// domain. A domain has no greatest position to stand for "all" — a `UInt`
    /// clock has `usize::MAX` but a pair domain has none — so the terminal release
    /// is its own case rather than a saturating watermark.
    through: ReleasedExtent,
}

impl PrefixReleaseCursor {
    /// Advance the watermark to at least `pos` (monotone: never retreats).
    fn advance_to(&mut self, pos: Position) {
        self.through = match std::mem::replace(&mut self.through, ReleasedExtent::Nothing) {
            ReleasedExtent::All => ReleasedExtent::All,
            ReleasedExtent::Through(r) => ReleasedExtent::Through(r.max(pos)),
            ReleasedExtent::Nothing => ReleasedExtent::Through(pos),
        };
    }

    /// Mark the entire domain released — the terminal (`True`) release, after
    /// which no position may re-emit.
    fn release_all(&mut self) {
        self.through = ReleasedExtent::All;
    }

    /// Whether `pos` is at or below the released watermark.
    fn is_released(&self, pos: &Position) -> bool {
        match &self.through {
            ReleasedExtent::All => true,
            ReleasedExtent::Through(r) => pos <= r,
            ReleasedExtent::Nothing => false,
        }
    }

    /// Advance the watermark from a released domain predicate, centralizing the
    /// one decision every commit-store reader shares. A fully-decided (`True`)
    /// release covers the whole domain — `release_all`, since no finite tick
    /// bounds it and a bare `max_released_position` of `None` there would be misread
    /// as "release nothing". A bounded release advances to its max released tick.
    /// Anything else releases no prefix. Returns the extent so the caller can do
    /// its own release-driven work (forward the release upstream, compact a
    /// latched set) without re-deriving this classification — the gap that let one
    /// reader silently drop the terminal case while the other handled it.
    fn advance_from(&mut self, pred: &Predicate) -> ReleasedExtent {
        if pred.as_bool() == Some(true) {
            self.release_all();
            ReleasedExtent::All
        } else if let Some(w) = pred.max_released_position() {
            self.advance_to(w.clone());
            ReleasedExtent::Through(w)
        } else {
            ReleasedExtent::Nothing
        }
    }
}

/// The prefix a domain-predicate release covers, as classified by
/// [`PrefixReleaseCursor::advance_from`]: nothing, a bounded prefix `≤ tick`, or
/// the whole (terminal) domain.
#[derive(Default)]
enum ReleasedExtent {
    #[default]
    Nothing,
    Through(Position),
    All,
}

/// The tiling a store read hands out for `value_extent`, one level deeper when the value
/// is a collection.
///
/// A store holds one value per key per tick, so a collection-valued key is a map in a cell.
/// Handing its keys out as a level is what lets a consumer fold the elements directly,
/// rather than reading a column of maps something downstream has to open first.
pub(crate) fn read_tiling(position: Extent, value_extent: &Extent) -> Tiling {
    Tiling::data_function(position, Tiling::from_extent(value_extent))
}

/// The tile for [`read_tiling`]: one value per position, opened to match
/// [`Tiling::from_extent`].
pub(crate) fn read_tile(
    positions: ColumnValue,
    values: Vec<Value>,
    value_extent: &Extent,
    domain_predicate: Predicate,
) -> Tile {
    let mut tile = Tile::data_function(
        positions,
        Box::new(stored_value_tile(values, value_extent)),
        domain_predicate,
        BitSet::new(),
    );
    tile.qualify_codomain_by_keys();
    tile
}

/// Encode a `Key ⇀ Value` map (a read set, write set, or store delta) as a
/// `Value::Function` — a collection of `key ↦ value` bindings. This is how a map
/// rides in a single tile cell: a column of these is a `ColumnValue::Variants`
/// (row-wise, heterogeneous), so per-tick write sets and per-proposal read/write
/// sets can have *different* key sets without a fixed `Record` extent or a
/// `DataFunction` CSR layout. The multi-key operator and the E4 proposal
/// wrapper both use this encoding.
pub fn map_to_value(map: &HashMap<Value, Value>) -> Value {
    Value::Function(
        map.iter()
            .map(|(k, v)| crate::interpreter::FuncBinding {
                input: k.clone(),
                output: v.clone(),
            })
            .collect(),
    )
}

/// Decode a [`map_to_value`]-encoded map back to a `HashMap`.
///
/// A non-`Function` cell is `unreachable!`, not a runtime error: every map cell
/// this decodes rode a `ColumnValue::Variants` column whose extent is a
/// [`map_extent`] (`Key ⇀ Value`). That holds for proposal read/write sets —
/// inference's `emit_transact_writer` types the proposal codomain's `reads`/`writes`
/// fields as map-valued, and the writer renders them via [`map_to_value`]. A
/// non-`DataFunction` value would be a `Variants` cell holding something other than its
/// declared map extent — impossible by construction.
pub fn value_to_map(v: &Value) -> HashMap<Value, Value> {
    match v {
        Value::Function(bindings) => bindings
            .iter()
            .map(|b| (b.input.clone(), b.output.clone()))
            .collect(),
        other => unreachable!(
            "a Variants map cell is a Value::Function (its map_extent is Key ⇀ Value, \
             guaranteed by render_full_store_tile / emit_transact_writer); got {other:?}"
        ),
    }
}

/// The extent of a `Key ⇀ Value` map cell — a [`map_to_value`] `Value::Function`
/// carried in a `Variants` column. This is a **proposal's** read and write sets, which is
/// where the encoding survives: the store's own state is a record keyed by the same keys
/// ([`full_store_tiling`]), and a proposal's key sets are as static as the store's.
fn map_extent(key_extent: &Extent, value_extent: &Extent) -> Extent {
    Extent::Function {
        domain: Box::new(key_extent.clone()),
        codomain: Box::new(value_extent.clone()),
    }
}

/// The full multi-key store tiling: a [`Tiling::Store`] step function
/// `CommitTimestamp ⇀ {key: value}`, whose codomain names every key the store holds
/// with that key's own value tiling. The `Store` tiling (not `DataFunction`) is what marks
/// the output as a changelog to be folded, not a function to be indexed.
///
/// `values` is one entry per store key — a mutable variable or a reply tap — under the
/// key's [`store_key`] name. Carrying each key's tiling is what lets the keys differ: a
/// single shared codomain could only describe a heterogeneous store as the union of its
/// keys' extents, which names what any key might hold rather than what each one does.
pub fn full_store_tiling(domain: Extent, values: HashMap<String, Tiling>) -> Tiling {
    Tiling::Store {
        domain,
        codomain: Box::new(Tiling::Record(values)),
    }
}

/// A **nested** carrier's store tiling: one store per enclosing position.
///
/// A nested recurrence is a store per enclosing row rather than one store over
/// `(enclosing, inner)` pairs. Two things follow, and both are why the pair form was
/// wrong rather than merely awkward. A row's carry starts at **that row's seed**, where a
/// flat log would inherit the previous row's last write — a different value whenever
/// anything is written between the loops. And which rows are complete is the collection
/// level's own `domain_predicate`, in the enclosing domain's own vocabulary, rather than a
/// statement about a product domain that a predicate over pairs cannot make.
pub fn nested_store_tiling(
    enclosing: Extent,
    inner: Extent,
    values: HashMap<String, Tiling>,
) -> Tiling {
    Tiling::data_function(enclosing, full_store_tiling(inner, values))
}

/// The enclosing and inner components of a pair position domain.
pub fn split_pair_domain(domain: &Extent) -> Option<(Extent, Extent)> {
    let Extent::Record(fields) = domain else {
        return None;
    };
    Some((
        fields.get(&tuple_field(0))?.clone(),
        fields.get(&tuple_field(1))?.clone(),
    ))
}

/// The store a nested carrier is currently adding to — its last enclosing row.
///
/// A flat store is returned unchanged, so a reader that does not care which it has may
/// call this unconditionally. An empty collection answers with the empty store it tiles
/// as, which folds to nothing rather than to a wrong value.
pub fn current_row_store(store: &Tile) -> Tile {
    let Tile::DataFunction {
        domain, codomain, ..
    } = store
    else {
        return store.clone();
    };
    match domain.len() {
        0 => codomain.as_ref().clone(),
        // A level whose values are another level stands above the carrier: the store sits beneath
        // it, so the descent continues into the last row's group rather than stopping at
        // the collection standing there.
        n if codomain.is_data_function() => current_row_store(&last_row_group(store, n - 1)),
        n => store_row(codomain, n - 1, n),
    }
}

/// Row `row`'s group of the level directly beneath `level`.
///
/// [`Tile::group_at`] states it for a tile read from the top; this is the same operation
/// one level down, which is how the store descent and the frontier walk step.
fn last_row_group(level: &Tile, row: usize) -> Tile {
    level
        .group_at(CurryLevel::new(1), row)
        .unwrap_or_else(|| unreachable!("row {row} is one this level holds: {level:?}"))
        .into_owned()
}

/// The **path** a carrier has decided through: its last row at each level, and that
/// store's last position.
///
/// A carrier with no rows above it answers with a path of one component, its own frontier.
/// The path is a record here and in the drive's cursor, and nowhere else — neither is a
/// tile key, so no predicate is written over it.
pub fn frontier_path(store: &Tile) -> Option<Path> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = store
    else {
        return Some(Path::from(vec![store_frontier(store)?.into_value()]));
    };
    let rows = domain.len();
    if rows == 0 {
        return None;
    }
    // The last row is the one still running, the drive being sequential, so the frontier
    // descends it. A level beneath is another level of rows, which recurs; the level above
    // a store is where the positions are.
    let last = domain.index_at(rows - 1);
    let below = if codomain.is_data_function() {
        frontier_path(&last_row_group(store, rows - 1))?.to_vec()
    } else {
        vec![store_frontier(&store_row(codomain, rows - 1, rows))?.into_value()]
    };
    Some(Path::from([vec![last], below].concat()))
}

/// A source's items, keyed by the path that reaches each one.
///
/// The source arrives curried — one inner collection per row above it — which is the shape
/// that states per-row completeness. The path is rebuilt here only as the drive's own
/// cursor for picking what to run next; it is never a tile key.
///
/// `levels` is how long a path is: the row levels above the carrier's stores, then the
/// position within one. A carrier with no rows above it has one. It is the carrier's own
/// statement rather than a count of the source's levels, because an item that is itself a
/// collection carries its own levels beneath the positions, and counting those names a
/// path too deep.
///
/// Sorted, because an async source's domain arrives unordered and the drive takes
/// positions in path order.
fn decode_source_paths(tile: &Tile, levels: usize) -> Vec<(Path, Tile)> {
    #[allow(clippy::too_many_arguments)]
    fn walk(
        level: &Tile,
        run: std::ops::Range<usize>,
        below: usize,
        complete_above: bool,
        prefix: &mut Vec<Value>,
        items: &Tile,
        out: &mut Vec<(Path, Tile)>,
    ) {
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = level
        else {
            return;
        };
        for k in run {
            prefix.push(domain.index_at(k));
            // Completeness is downward-closed: a path some level calls complete is
            // complete at every depth beneath it, whatever those levels state.
            let complete = complete_above || domain_predicate.contains_path(prefix);
            if below == 0 {
                // An item is a value in its own right, so its statements are restated over
                // its own paths ([`Predicate::within`]); whoever places it again qualifies
                // them by where it goes. One under a complete path is whole, and taken out
                // on its own it has no level above to read that from, so it says so itself,
                // as [`Tile::group_at`]'s group does.
                let mut item = items.select_rows(&[k]);
                item.map_level_predicates(&mut |depth, pred| match complete {
                    true => Predicate::True,
                    false => pred.within(prefix, depth),
                });
                out.push((Path::from(prefix.clone()), item));
            } else {
                let (from, to) = codomain.row_run(k);
                walk(codomain, from..to, below - 1, complete, prefix, items, out);
            }
            prefix.pop();
        }
    }
    assert!(levels > 0, "a source's path names at least a position");
    let Tile::DataFunction { domain, .. } = tile else {
        return Vec::new();
    };
    // The item column sits under the positions level, `levels` levels in. An item is one
    // row of it, and a row of a tile is a tile: an item holding a collection keeps its
    // levels rather than becoming a map in a cell, which is the shape the body's input
    // declares for it ([`body_input_tiling`]).
    let mut under = tile;
    for _ in 0..levels {
        let Tile::DataFunction { codomain, .. } = under else {
            return Vec::new();
        };
        under = codomain;
    }
    if matches!(under, Tile::Aggregation { .. } | Tile::Store { .. }) {
        return Vec::new();
    }
    let mut out = Vec::new();
    walk(
        tile,
        0..domain.len(),
        levels - 1,
        false,
        &mut Vec::new(),
        under,
        &mut out,
    );
    out.sort_by(|(a, _), (b, _)| a.cmp(b));
    out
}

/// One enclosing row's store, projected out of a nested carrier's collection of them.
///
/// Every field of a vectorized store is per row the way every other tile's is, so this is
/// the ordinary row retain — which is what lets the fold, the frontier and the seed
/// machinery read a nested row with no second implementation of any of them.
pub fn store_row(store: &Tile, row: usize, rows: usize) -> Tile {
    let Tile::Store {
        state,
        seed,
        decided,
        frontier,
        terminal,
        closed_keys,
    } = store
    else {
        // Every caller has descended to the level whose values are the stores, and a
        // `Tiling::Store` renders as a `Tile::Store` even when empty. Returning the input
        // unchanged instead hands back the *whole* level, which reads as a one-row answer
        // and silently folds one enclosing row's writes into the next.
        unreachable!("store_row takes a row of a vectorized store, got {store:?}")
    };
    let keep = bit_vec::BitVec::from_fn(rows, |i| i == row);
    let retained = |t: &Tile| {
        let mut t = t.clone();
        t.retain_rows(&keep);
        Box::new(t)
    };
    Tile::Store {
        state: retained(state),
        seed: retained(seed),
        decided: retained(decided),
        frontier: retained(frontier),
        terminal: *terminal,
        closed_keys: closed_keys.clone(),
    }
}

/// The commit clock as a store domain: the `Txn` sequencing order, a `UInt` counter.
pub fn commit_clock_domain() -> Extent {
    Extent::Base(BaseType::UInt)
}

/// The changelog of store key `key`: the commit ticks that wrote it, ascending, against
/// the values written there. `None` for a tile that is not a store, for a value that is
/// not a store key, and for a key outside this store's key space.
fn changelog<'a>(tile: &'a Tile, key: &Value) -> Option<(&'a ColumnValue, &'a Tile)> {
    tile.store_changelog(store_key_name(key)?)
}

/// The value a changelog holds at index `i`.
///
/// A store key's value is one whole [`Value`]: the engine folds in values and the writers
/// propose in them, so a compound accumulator materializes its fields into a single record cell
/// rather than spreading them over a tile. The changelog's values are therefore a column.
fn changelog_value(values: &Tile, i: usize) -> Value {
    match values {
        Tile::Scalar(column) => column.index_at(i),
        other => panic!("a store key's changelog holds one value per tick; got {other:?}"),
    }
}

/// Every commit tick at which the store recorded a write, ascending and deduplicated: the
/// union of its keys' changelogs. A carry-forward read emits a position at each of these,
/// because a tick that wrote some other key still carries this one forward.
pub fn store_change_positions(tile: &Tile) -> Vec<Position> {
    let mut ticks = std::collections::BTreeSet::new();
    for key in tile.store_keys() {
        let Some((written, _)) = tile.store_changelog(key) else {
            continue;
        };
        ticks.extend((0..written.len()).map(|i| Position::new(written.index_at(i))));
    }
    ticks.into_iter().collect()
}

/// Field names of the proposal-stream codomain record. `F_WRITES` is shared with
/// the CCL side: it names the writer decision's `commit`-payload write tuple (the
/// contract between the letrec phase, inference, and this engine) and is reused
/// here for the proposal's write-set map.
const F_SNAP: &str = "snap";
const F_READS: &str = "reads";

/// The expected tiling of a proposal-stream input: `step → {snap, reads, writes}`,
/// where `reads`/`writes` are map-valued (`Key ⇀ Value`) cells.
pub fn proposal_stream_tiling(key_extent: &Extent, value_extent: &Extent) -> Tiling {
    let map = map_extent(key_extent, value_extent);
    Tiling::data_function(
        Extent::Base(BaseType::UInt),
        Tiling::Record(HashMap::from([
            (
                F_SNAP.to_string(),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
            (F_READS.to_string(), Tiling::Scalar(map.clone())),
            (F_WRITES.to_string(), Tiling::Scalar(map)),
        ])),
    )
}

/// A commit operator over a multi-key store `CommitTimestamp ⇀ (Key ⇀ Value)`,
/// fed by `n_writers` concurrent writers.
///
/// Each writer input — a proposal stream `step → {snap, reads, writes}` with
/// map-valued read/write sets — is wired after construction via
/// [`CommitOperator::writer_input_setter`]. That ordering is what allows the
/// cycle: a writer is built around a branch of the operator's own (store)
/// output, so it reads the store before proposing.
///
/// On each `get` the operator drains every writer's new proposals in writer-index
/// order. A valid proposal commits (allocate-on-commit) and the operator
/// `release`s that step back to the writer — the writer reads the release as
/// "your transaction committed; advance". A stale proposal consumes no tick and
/// is not released; the writer re-reads the advanced store and retries (or, if
/// it now denies, decides locally and never re-proposes). Disjoint write sets
/// from different writers commit on consecutive ticks without conflict.
pub struct CommitOperator {
    /// The concrete part of the tick-0 store state (the [`Self::new`] seed, used
    /// by engine-level tests). Computed scalar keys are layered on top from
    /// `seed_ops`.
    seed: HashMap<Value, Value>,
    /// Per scalar key, the stream producing its tick-0 value — the value the key
    /// stands at before any commit. A literal init is a constant; a collection key
    /// has no entry (its log starts empty). This is the op-conversion seeding
    /// path, and it is the same field [`InductionStore`] carries: a seed is
    /// ordinary dataflow either side, read per pull until it settles.
    seed_ops: Vec<(Value, Box<dyn TileOperator>)>,
    base: OperatorBase,
    writer_inputs: Vec<CycleSlot<dyn TileOperator>>,
    /// Per writer, the keys it may write — its **static** footprint, so a
    /// conditionally-written key still counts. This is what lets the store close
    /// a key when the writers that can touch it finish, rather than only when
    /// every writer does: a key nobody can still write is final even while the
    /// store keeps committing other keys.
    writer_write_keys: Vec<Vec<Value>>,
}

/// Graph edges for a store's per-key tick-0 operators, keyed by the store key.
impl CommitOperator {
    /// Create a commit operator whose store starts at `init` (the tick-0 state),
    /// holding the keys `values` names with the value tiling it gives each.
    ///
    /// `writer_write_keys[k]` is writer `k`'s **static** write footprint — every
    /// key that writer might write, whether or not it does on a given attempt.
    /// Its length is the writer count. See [`Self::writer_write_keys`].
    pub fn new(
        init: HashMap<Value, Value>,
        values: HashMap<String, Tiling>,
        writer_write_keys: Vec<Vec<Value>>,
    ) -> Self {
        let output_tiling = full_store_tiling(commit_clock_domain(), values);
        Self {
            seed: init,
            seed_ops: Vec::new(),
            base: OperatorBase::new(output_tiling),
            writer_inputs: (0..writer_write_keys.len())
                .map(|_| CycleSlot::new())
                .collect(),
            writer_write_keys,
        }
    }

    /// Create a commit operator whose scalar keys' tick-0 values are produced by
    /// `seed_ops`, one stream per key. This is the op-conversion path for
    /// `Mut(V, Txn)` keys; a literal init is a constant, and a collection key
    /// contributes no entry (its log starts empty). ([`Self::new`] is the
    /// concrete-map constructor used by engine-level tests.)
    pub fn with_seed_ops(
        seed_ops: Vec<(Value, Box<dyn TileOperator>)>,
        values: HashMap<String, Tiling>,
        writer_write_keys: Vec<Vec<Value>>,
    ) -> Self {
        let output_tiling = full_store_tiling(commit_clock_domain(), values);
        Self {
            seed: HashMap::new(),
            seed_ops,
            base: OperatorBase::new(output_tiling),
            writer_inputs: (0..writer_write_keys.len())
                .map(|_| CycleSlot::new())
                .collect(),
            writer_write_keys,
        }
    }

    /// Wire writer `k`'s input. Call after the operator is boxed, so the writer
    /// can be built around a branch of the operator's store output (the cycle).
    pub fn writer_input_setter(&self, k: usize) -> impl FnOnce(Box<dyn TileOperator>) + use<> {
        self.writer_inputs[k].setter()
    }
}

impl TileOperator for CommitOperator {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (key, op) in &self.seed_ops {
            visit(value_keyed(key.to_string(), &**op));
        }
        // A writer arrives through its slot after this store was built, which is
        // what makes its edge the deferred one and the cycle cuttable there.
        for (i, slot) in self.writer_inputs.iter().enumerate() {
            slot.peek(&mut |op| visit(value_late(EdgeRole::Positional(i), op)));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Wake this operator's consumer whenever any writer's (live) source
        // delivers a new item: the arrival drives a commit, and that commit must
        // propagate to a downstream reader of a store key or `__to_<defer>` tap (a
        // live cross-endpoint read — a read-only transaction's reply). This is the
        // same both-inputs-wake wiring `AsOf` uses; without it the sink reading a
        // tap off a live commit store would never be notified and would hang.
        // Kick once immediately to start the drain loop.
        let consumer = shared_consumer(consumer);
        consumer.borrow_mut().notify();
        // A seed forwards, rather than being drained here: it is ordinary dataflow, so a
        // seed computed from a loop settles over as many pulls as that loop takes, and the
        // pull it settles on is the one that opens the store. Draining at subscribe
        // instead bounds a program by how far its seed's input can advance before the
        // runtime has started ([`InductionStore::subscribe`] says the same).
        let seed_producers = std::mem::take(&mut self.seed_ops)
            .into_iter()
            .map(|(key, mut op)| {
                let g = op.tiling().universal_guard();
                (
                    key,
                    op.subscribe(
                        g,
                        forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                        scheduler,
                    ),
                )
            })
            .collect();
        let writer_producers = self
            .writer_inputs
            .iter()
            .enumerate()
            .map(|(k, slot)| {
                let mut input = slot.take().unwrap_or_else(|| {
                    panic!(
                        "CommitOperator: writer {k} is unwired at subscribe — either \
                         `writer_input_setter({k})` was never called, or this operator is \
                         being subscribed twice (the first subscribe takes the slot)"
                    )
                });
                let guard = input.tiling().universal_guard();
                input.subscribe(
                    guard,
                    forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                    scheduler,
                )
            })
            .collect::<Vec<_>>();
        let n = writer_producers.len();
        Box::new(CommitProducer {
            base: ProducerBase::new(CommitProducer::alloc_id(), self.tiling()),
            writer_producers,
            consumed: vec![0; n],
            writer_terminal: vec![false; n],
            writer_write_keys: self.writer_write_keys.clone(),
            seed: self.seed.clone(),
            seed_producers,
            engine: None,
            output_tiling: self.tiling().clone(),
            drain_start: 0,
            notifier: ChangeNotifier::new(consumer, scheduler),
            #[cfg(debug_assertions)]
            reported_closed: HashSet::new(),
        })
    }
}

struct CommitProducer {
    base: ProducerBase,
    writer_producers: Vec<Box<dyn TileProducer>>,
    /// Per writer, how many proposal-stream steps have already been processed.
    consumed: Vec<usize>,
    /// Per writer, whether its proposal stream is terminal (the writer has
    /// finished all its transactions). The store is terminal — fully decided,
    /// no more commits coming — once every writer is.
    writer_terminal: Vec<bool>,
    /// Per writer, the keys it may write ([`CommitOperator::writer_write_keys`]),
    /// aligned with [`Self::writer_terminal`]. The two together give per-key
    /// closure: a key is closed once every writer listing it is terminal.
    writer_write_keys: Vec<Vec<Value>>,
    /// The concrete part of the tick-0 state, which `seed_producers` completes.
    seed: HashMap<Value, Value>,
    /// Per scalar key, the stream giving its value before any commit.
    seed_producers: Vec<(Value, Box<dyn TileProducer>)>,
    /// The store's state, `None` until every key's seed has arrived.
    ///
    /// A store holds one value per key before any commit and is seeded once, so it opens
    /// only when the whole seed is in hand — a key whose own seed settles later would
    /// otherwise stand at no value at all, and nothing asks again.
    engine: Option<CommitEngine>,
    /// The full-store output tiling — for a debug-time shape check on the
    /// rendered store tile.
    output_tiling: Tiling,
    /// Rotating writer index the per-`get` drain starts from — round-robin
    /// fairness. A fixed low-to-high order lets a busy low-index writer
    /// perpetually win a hot key and starve a higher-index contender; rotating
    /// the start each pull gives every writer periodic first pick. Any drain
    /// order is a valid serialization (OCC admits any serial order), so this
    /// changes only *which* transaction wins a race between conflicting writers,
    /// never correctness (conservation/non-negativity hold under any order).
    drain_start: usize,
    /// Wakes this store's readers when a pull changes what it answers.
    notifier: ChangeNotifier,
    /// Every key a render has reported in `closed_keys`, for the check that no commit
    /// writes one afterwards.
    #[cfg(debug_assertions)]
    reported_closed: HashSet<Value>,
}

/// A proposal-stream record field, as its scalar column. The proposal codomain
/// is `{snap, reads, writes}` with every field scalar-shaped (`snap` a UInt
/// column, `reads`/`writes` `Variants` map columns) — inference's
/// `emit_transact_writer` types it so, so a missing or non-`Scalar` field is
/// impossible.
fn record_field<'a>(fields: &'a HashMap<String, Tile>, name: &str) -> &'a ColumnValue {
    match fields.get(name) {
        Some(Tile::Scalar(cv)) => cv,
        other => unreachable!(
            "proposal record field {name} is scalar-shaped (the proposal codomain \
             {{snap, reads, writes}} is typed by emit_transact_writer); got {other:?}"
        ),
    }
}

impl CyclicSequencingProducer for CommitProducer {
    fn debug_assert_position_invariant(&self) {
        // The per-writer cursors are positionally aligned with the writers and
        // grow monotonically (a writer's `consumed` only advances, and once
        // `writer_terminal` it stays so). The store history is append-only by
        // construction (the engine appends one immutable version per commit).
        debug_assert_eq!(
            self.consumed.len(),
            self.writer_producers.len(),
            "per-writer consumed cursors align with the writer set (one cursor per writer)"
        );
        debug_assert_eq!(
            self.writer_terminal.len(),
            self.writer_producers.len(),
            "per-writer terminal flags align with the writer set (one flag per writer)"
        );
    }
}

impl CommitProducer {
    /// The store's state, which every path past the seed check at the head of
    /// [`get_impl`](TileProducer::get_impl) has already opened.
    fn open_engine(&mut self) -> &mut CommitEngine {
        self.engine
            .as_mut()
            .expect("the store is open past the seed check at the head of the pull")
    }
}

impl TileProducer for CommitProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let store = self.drain();
        self.notifier.notify_if_changed(store)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Read-side commit-log GC. The store sits behind a cyclic `FanOut`, so
        // this guard is the **intersection** of what every consumer (the writers
        // *and* the readers) has released — exactly the prefix safe to reclaim
        // (tile monotonicity: only `release` shrinks). Drop those committed
        // versions, keeping the carry source a live position reads. A live `AsOf` reader
        // *does* release the prefix below its latched frontier (`AsOfProducer::
        // get_impl`), so a store with a writing endpoint still sheds its
        // superseded history through this branch — the intersection just also
        // waits on that reader's own released prefix.
        // Through the end of the prefix the meet covers, not its highest point: a tick the
        // meet skips is still read, and so is everything after it.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(engine) = &mut self.engine
            && let Some(through) = engine
                .decided_positions
                .iter()
                .take_while(|tick| pred.contains(tick.value()))
                .last()
                .cloned()
        {
            engine.gc_released_prefix(&through);
        }
    }
}

impl CommitProducer {
    /// Open the store once its seed is in hand, commit what the writers propose, and render
    /// the store — one pull's worth of the cycle.
    fn drain(&mut self) -> Tile {
        self.debug_assert_position_invariant();
        // Open the store on the pull its whole seed has arrived. Until then it is
        // undecided — no tick 0, so no frontier — and a writer reads nothing to build an
        // attempt against, which is why nothing is drained below either.
        if self.engine.is_none() {
            let mut seed = self.seed.clone();
            let mut resolved = 0;
            for (key, producer) in &mut self.seed_producers {
                if let Ok(value) = seed_value(&producer.get(producer.tiling().universal_guard())) {
                    seed.insert(key.clone(), value);
                    resolved += 1;
                }
            }
            if resolved == self.seed_producers.len() {
                self.engine = Some(CommitEngine::new(seed));
                // The seed is read once, at the store's opening, so it is released there.
                for (_, producer) in &mut self.seed_producers {
                    producer.release(producer.tiling().universal_guard());
                }
            }
        }
        let Some(engine) = &mut self.engine else {
            return CommitEngine::unopened().render_full_store_tile(self.tiling());
        };
        let _ = engine;
        // Drain each writer's new proposals. Within a pull the drain order is the
        // serialization order (an earlier-drained writer's commit can make a
        // later one's same-pull proposal stale), and the **start index rotates**
        // each pull (`drain_start`) for round-robin fairness — a fixed order lets
        // a busy low-index writer perpetually win a hot key and starve a
        // higher-index contender. Rotation changes only *which* serialization a
        // race resolves to (any order is valid under OCC), never correctness.
        //
        // Under sustained contention a losing writer re-proposes its stuck item at
        // each new frontier; the writer bounds that to O(1) by dropping its
        // superseded proposals for the item before re-emitting (see
        // `TransactWriterProducer::drop_superseded`), so `emitted` does not grow
        // with the retry count. Every proposal is a pure function of its snapshot,
        // and `consumed` blocks any proposal from committing twice.
        let n = self.writer_producers.len();
        for off in 0..n {
            let k = (self.drain_start + off) % n;
            let guard = self.writer_producers[k].tiling().universal_guard();
            let tile = self.writer_producers[k].get(guard);
            let Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } = tile
            else {
                continue;
            };
            // A writer is terminal once its proposal stream is — every
            // transaction has been emitted and (by the retry/advance protocol)
            // committed. Monotonic: writers don't un-finish, so latch with `|=`
            // rather than `=` (a transient non-`True` pull after terminality must
            // not un-set it — the store's terminality gates output convergence).
            self.writer_terminal[k] |= matches!(domain_predicate, Predicate::True);
            // The proposal-stream codomain is a record `{snap, reads, writes}` —
            // `proposal_stream_tiling` declares it so and inference's
            // `emit_transact_writer` types the writer's output to match, so a
            // non-`Record` value on a collection proposal tile is
            // impossible.
            let Tile::Record(fields) = *codomain else {
                unreachable!(
                    "the proposal stream's codomain is a {{snap, reads, writes}} record \
                     (proposal_stream_tiling / emit_transact_writer); got a non-Record codomain"
                );
            };
            let snaps = record_field(&fields, F_SNAP);
            let reads = record_field(&fields, F_READS);
            let writes = record_field(&fields, F_WRITES);
            // The proposal tile is an offset window: its domain carries the
            // absolute step values (the writer compacts its released prefix), so
            // read the step from the domain column and index the codomain by
            // column position `j`. `consumed[k]` is the absolute count of steps
            // already attempted — a step value, not a column position.
            for j in 0..domain.len() {
                // The proposal-stream domain extent is `Base(UInt)`
                // (proposal_stream_tiling), so a step is always a UInt.
                let Value::UInt(step) = domain.index_at(j) else {
                    unreachable!(
                        "proposal step is a UInt (the proposal-stream domain extent is \
                         Base(UInt))"
                    );
                };
                if step < self.consumed[k] {
                    continue; // attempted on an earlier pull (below the live edge)
                }
                // `snap` is a position of the commit clock, typed `Scalar(UInt)` by
                // emit_transact_writer to match it.
                let snapshot = Position::new(snaps.index_at(j));
                debug_assert!(
                    matches!(snapshot.value(), Value::UInt(_)),
                    "a proposal's snapshot is a commit-clock position, which is a UInt \
                     (the snap field is typed Scalar(UInt) by emit_transact_writer); got \
                     {snapshot}"
                );
                let write_set = value_to_map(&writes.index_at(j));
                #[cfg(debug_assertions)]
                let written: Vec<Value> = write_set.keys().cloned().collect();
                let outcome = self.open_engine().attempt(Proposal {
                    snapshot,
                    reads: value_to_map(&reads.index_at(j)),
                    writes: write_set,
                });
                self.consumed[k] = step + 1;
                if let CommitOutcome::Committed { .. } = outcome {
                    #[cfg(debug_assertions)]
                    {
                        debug_assert!(
                            written
                                .iter()
                                .all(|w| self.writer_write_keys[k].contains(w)),
                            "a committed write stays inside its writer's declared footprint: \
                             writer {k} wrote {written:?}, declaring {:?}",
                            self.writer_write_keys[k]
                        );
                        debug_assert!(
                            written.iter().all(|w| !self.reported_closed.contains(w)),
                            "no commit writes a key the store has reported closed: writer {k} \
                             wrote {written:?}, closed {:?}",
                            self.reported_closed
                        );
                    }
                    // Acknowledge the commit by releasing this step (and any
                    // earlier stale ones) back to the writer — its signal to
                    // advance and to compact its proposal window. A stale
                    // proposal is left unreleased.
                    self.writer_producers[k].release(TileGuard::Function(FunctionGuard::Domain(
                        Predicate::at_or_below(Value::UInt(step)),
                    )));
                }
            }
        }
        // Rotate the drain start for the next pull (round-robin fairness). Guard
        // `n == 0`: a store with no writers never drains, and `% 0` would panic.
        if n > 0 {
            self.drain_start = (self.drain_start + 1) % n;
        }
        let tiling = self.tiling().clone();
        let mut store = self.open_engine().render_full_store_tile(&tiling);
        // Signal terminality once every writer is done: the store is then fully
        // decided (no more commits), so the watermark `at_or_below(w)` becomes
        // `True`. A downstream `read`/output gates on this to know the cycle has
        // converged (the harness re-pulls a non-terminal output to drive it).
        // A store with **no** writers is trivially terminal (no commit can ever
        // happen) — `all()` over the empty writer set is `true`, which is what we
        // want, so there is no `is_empty()` guard.
        if let Tile::Store {
            terminal,
            closed_keys,
            ..
        } = &mut store
        {
            if self.writer_terminal.iter().all(|&t| t) {
                // Close the frontier (no more commits), keeping its numeric watermark.
                *terminal = true;
            }
            // Per-key closure: a key is closed once every writer whose write set
            // contains it is terminal, which is no later than the whole store and
            // earlier whenever some other writer is still running. This is what lets
            // `await_final(x)` settle while a store-mate
            // is still committing — nothing can write `x` again, so its final
            // value is fixed. Reported even when the store is terminal, so a
            // consumer never has to check both axes.
            let mut closed: Vec<Value> = Vec::new();
            for k in self.writer_write_keys.iter().flatten() {
                let done = self
                    .writer_write_keys
                    .iter()
                    .zip(&self.writer_terminal)
                    .all(|(keys, &t)| t || !keys.contains(k));
                if done && !closed.contains(k) {
                    closed.push(k.clone());
                }
            }
            #[cfg(debug_assertions)]
            self.reported_closed.extend(closed.iter().cloned());
            *closed_keys = closed;
        }
        debug_assert!(
            store.check_from(&self.output_tiling),
            "rendered store tile does not match the full-store tiling"
        );
        store
    }
}

/// [`decode_source_paths`] over a source with no rows above its positions, read back as
/// the positions they are.
///
/// An **async** source's domain arrives *unordered* (it enumerates a set of arrived keys)
/// and *compacts* as its consumed prefix is released, so a column index is neither a
/// domain position nor stable across a release. Pairing each item with its actual domain
/// position gives a driver a name for an item that outlives the view it was read from —
/// which the recurrence needs to run `x₀, x₁, …` in order, and the transaction driver
/// needs to say which items it has finished. A finite list is the special case (its domain
/// is already `[0, 1, …]`).
fn decode_source_positioned(tile: &Tile) -> Vec<(Position, Tile)> {
    decode_source_paths(tile, 1)
        .into_iter()
        .map(|(path, item)| {
            let [only] = &path[..] else {
                unreachable!("a path of one level names one position, got {path:?}")
            };
            (Position::new(only.clone()), item)
        })
        .collect()
}

/// A pair-keyed stream's values, keyed by the path that reaches each one.
///
/// The standing levels contribute their own keys and the pair at the bottom contributes
/// both of its components, so the path names the same place the curried source's does —
/// one component per level, with nothing left composed into a value. Without that the
/// drive would be holding two spellings of one position and matching neither.
fn decode_pairs_pathed(tile: &Tile, standing: usize) -> Vec<(Path, Tile)> {
    fn walk(tile: &Tile, depth: usize, prefix: &mut Vec<Value>, out: &mut Vec<(Path, Tile)>) {
        if depth == 0 {
            for (key, value) in decode_source_positioned(tile) {
                let Value::Record(pair) = key.value() else {
                    unreachable!(
                        "a pair-keyed stream's keys are `(enclosing, position)` records; \
                         got {key}"
                    )
                };
                let (Some(row), Some(inner)) =
                    (pair.get(&tuple_field(0)), pair.get(&tuple_field(1)))
                else {
                    unreachable!("a pair-keyed stream's key names both components; got {key}")
                };
                let path = [prefix.as_slice(), &[row.clone(), inner.clone()]].concat();
                out.push((Path::from(path), value));
            }
            return;
        }
        let Tile::DataFunction { domain, .. } = tile else {
            return;
        };
        for k in 0..domain.len() {
            prefix.push(domain.index_at(k));
            if let Some(group) = tile.group_at(CurryLevel::new(1), k) {
                walk(&group, depth - 1, prefix, out);
            }
            prefix.pop();
        }
    }
    let mut out = Vec::new();
    walk(tile, standing, &mut Vec::new(), &mut out);
    out
}

/// `path` as a pair-keyed stream names it: the row and the position within it, its last two
/// components, composed back into the `(enclosing, position)` record the stream is keyed
/// by. The inverse of the explosion [`decode_pairs_pathed`] does.
fn pair_keyed(path: &Path) -> Vec<Value> {
    let (rows, position) = path
        .split_position()
        .unwrap_or_else(|| unreachable!("a pair-keyed path names a position"));
    let (row, standing) = rows
        .split_last()
        .unwrap_or_else(|| unreachable!("a pair-keyed path names its position's row: {path}"));
    let pair = Value::Record(HashMap::from([
        (tuple_field(0), row.clone()),
        (tuple_field(1), position.clone()),
    ]));
    [standing, std::slice::from_ref(&pair)].concat()
}

/// A seed stream's value for each row it seeds.
///
/// `rows_above` is how many collection levels stand above the carrier's stores, so it is
/// how many components of a path name a row. A carrier with none is one store over the
/// whole extent, and the whole tile is its one seed, at the empty path. A carrier with
/// rows was compiled against the `(enclosing, position)` pairs its body takes, so its seed
/// is keyed by pairs under the standing levels; the seed is a morphism of the row, so the
/// pair's position component is dropped and the first `rows_above` components remain.
///
/// A seed a pull does not carry is absent rather than reported: the row it would open
/// opens on a later pull instead, which is the same thing a row the drive has not reached
/// does.
fn decode_row_seeds(tile: &Tile, rows_above: usize) -> Vec<(Path, Value)> {
    let Some(standing) = rows_above.checked_sub(1) else {
        return seed_value(tile)
            .map(|value| (Path::default(), value))
            .into_iter()
            .collect();
    };
    decode_pairs_pathed(tile, standing)
        .into_iter()
        .filter_map(|(path, value)| {
            let (row, _) = path.split_position()?;
            // A seed holding a collection still arriving is part of a value, not one: the
            // row opens once it is whole, as it does once a missing seed arrives.
            if !is_whole_value(&value) {
                return None;
            }
            Some((Path::from(row.to_vec()), materialized_row(value)))
        })
        .collect()
}

/// A nested carrier's output tiling: one [`Tile::Store`] per row of `enclosing`, under the
/// levels `standing` leaves above it.
///
/// The standing levels stand above the carrier: a nest three deep is this same carrier
/// replicated per row of the loop around it, not a carrier that counts its own depth.
/// `pair_domain` is the `(enclosing, inner)` domain the driver sequences positions in; the
/// store splits it, keeping the enclosing component as the collection level above it.
pub fn nested_carrier_tiling(
    standing: &Tiling,
    depth: usize,
    pair_domain: &Extent,
    values: HashMap<String, Tiling>,
) -> Tiling {
    let (enclosing, inner) = split_pair_domain(pair_domain).unwrap_or_else(|| {
        panic!("a nested carrier sequences its positions as pairs, got {pair_domain}")
    });
    with_values_at(
        standing,
        CurryLevel::new(depth),
        nested_store_tiling(enclosing, inner, values),
    )
}

/// A **position-driven induction store** (a `mut` loop accumulator, plain or with
/// a conditional write `if p: total += x`) built on the same [`CommitEngine`] +
/// [`Tile::Store`] changelog machinery as the concurrent [`CommitOperator`], but
/// driven by *iteration position* rather than by concurrent proposals.
///
/// There is exactly one writer, visiting each iteration position once in order:
/// no proposals, no conflicts, no retries. The store is the *consuming* half of
/// the recurrence — it reads the body's `` {`commit{writes} | `abort} ``
/// decision ([`body_decision_at`] decodes the union tag) and
/// [`step`](CommitEngine::step)s the engine, a `` `commit `` appending a change
/// and an `` `abort `` (a failed guard) **carrying** (no change; the value
/// inherits). Its cycle partner [`InductionDriver`] produces the body's
/// `(prev…, item)` input from the changelog this store emits, read back through
/// a `FanOut::new_cyclic` — so the accumulator crosses between them as a tile,
/// like every other operator-to-operator value.
///
/// A plain (unconditional) `mut` loop is the degenerate `` `commit ``-everywhere
/// case (a dense changelog); a conditional write is sparse in position space
/// (`` `abort `` positions append nothing) while the frontier still tracks the whole extent.
pub struct InductionStore {
    /// The writer body `` λ (prev…, item) → {`commit{writes(, __to_<defer>…)} | `abort} ``,
    /// compiled around an [`InductionDriver`]. Filled after construction through
    /// [`body_input_setter`](Self::body_input_setter): the body reads the driver,
    /// which reads this store back through the cycle, so it cannot exist yet
    /// when the store is built.
    body_input: CycleSlot<dyn TileOperator>,
    /// Keys written, in decision-`writes` order: the accumulator mutable variables, then
    /// any reply-tap (`__to_<defer>`) keys.
    write_keys: Vec<Value>,
    /// The last position a predecessor store reached, or `None` for one starting
    /// from the beginning of its source.
    resumed_after: Option<Position>,
    /// Reply-tap decision fields, appended to each write set (see
    /// [`body_decision_at`]). Empty for a store with no feed.
    tap_fields: Vec<String>,
    /// Per accumulator key, the stream giving each row's value **before** any of its
    /// positions.
    ///
    /// A carry at a row's first position folds to this, so a store cannot open without it.
    /// A carrier with no rows above it has one store and so one seed, keyed by the empty
    /// path; a nested one restarts per row, and its driver reads the same stream to
    /// snapshot the body — the store needs it because a *fold* resolves there too, and a
    /// position that writes nothing is exactly the case the two disagree on.
    seed_ops: Vec<(Value, Box<dyn TileOperator>)>,
    base: OperatorBase,
}

impl InductionStore {
    /// Assemble a carrier's store over `output_tiling` — a collection level per row above
    /// its stores, which [`full_store_tiling`] and [`nested_carrier_tiling`] build.
    ///
    /// `seed_ops` gives each accumulator's value before any position, keyed by the row it
    /// opens; `write_keys` follows the commit store's writer convention, the accumulators
    /// followed by tap keys. `resumed_after` is where a predecessor store stopped, which
    /// only a carrier with no rows above it has.
    pub fn new(
        seed_ops: Vec<(Value, Box<dyn TileOperator>)>,
        write_keys: Vec<Value>,
        tap_fields: Vec<String>,
        output_tiling: Tiling,
        resumed_after: Option<Position>,
    ) -> Self {
        assert!(
            resumed_after.is_none() || !output_tiling.is_data_function(),
            "a carrier with rows above it does not resume: the store around it is what \
             hands its variables on"
        );
        Self {
            body_input: CycleSlot::new(),
            write_keys,
            tap_fields,
            seed_ops,
            base: OperatorBase::new(output_tiling),
            resumed_after,
        }
    }

    /// Install the decision body, which reads this store back through the cyclic
    /// `FanOut` — the same late wiring [`CommitOperator::writer_input_setter`]
    /// performs, and for the same reason.
    pub fn body_input_setter(&self) -> impl FnOnce(Box<dyn TileOperator>) + use<> {
        self.body_input.setter()
    }
}

impl TileOperator for InductionStore {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (key, op) in &self.seed_ops {
            visit(value_keyed(key.to_string(), &**op));
        }
        self.body_input
            .peek(&mut |op| visit(value_late(EdgeRole::Named("body"), op)));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward body progress to this store's consumer. The body's input is
        // the driver, which forwards the loop source's arrivals, so an async
        // source's incremental delivery reaches a downstream reader and it
        // re-pulls. Without this the store stalls at whatever prefix arrived by
        // the first pull (a batch/list source is complete on the first pull, so
        // it never needed the wiring — an async source does). Kick once to start.
        let consumer = shared_consumer(consumer);
        consumer.borrow_mut().notify();
        let mut body_op = self.body_input.take().expect(
            "InductionStore: the decision body is unwired at subscribe — either \
                 `body_input_setter` was never called, or this store is being subscribed \
                 twice (the first subscribe takes the slot)",
        );
        let body_producer = {
            let g = body_op.tiling().universal_guard();
            body_op.subscribe(
                g,
                forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                scheduler,
            )
        };
        // A seed forwards, rather than being drained here: it is ordinary dataflow, so a
        // seed computed from a loop settles over as many pulls as that loop takes, and the
        // pull it settles on is the one that opens the store. Draining at subscribe
        // instead bounds a seed by how many positions its input can deliver before the
        // runtime has started.
        let seed_producers = std::mem::take(&mut self.seed_ops)
            .into_iter()
            .map(|(key, mut op)| {
                let g = op.tiling().universal_guard();
                (
                    key,
                    op.subscribe(
                        g,
                        forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                        scheduler,
                    ),
                )
            })
            .collect();
        Box::new(InductionStoreProducer {
            base: ProducerBase::new(InductionStoreProducer::alloc_id(), self.tiling()),
            seed_producers,
            complete_rows: vec![Predicate::False; self.tiling().levels() + 1],
            // Each store holds its accumulators' seeds as its own, so the changelog is
            // self-describing: `read_as_of`/`store_value_at` fold to the seed below
            // the first change (a leading carry) without an external default. The
            // changelog is keyed by the iteration positions themselves — the seed is
            // its base, not a position of it. A store that resumes is decided
            // strictly below the position it resumes at; one that starts with its
            // source is decided nowhere.
            engines: Engines::unopened(self.tiling()),
            resumed_after: self.resumed_after.clone(),
            body_producer,
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            output_tiling: self.tiling().clone(),
            notifier: ChangeNotifier::new(consumer, scheduler),
            #[cfg(debug_assertions)]
            stepped_through: None,
        })
    }
}

/// A producer's consumer, woken whenever a pull answers differently from the pull before.
///
/// A store changes on being pulled: it opens at a seed, decides a position or commits a
/// transaction, and closes. Every reader holds what it last read until told otherwise, and
/// the change is made inside a `get`, where the producers that must re-pull are still on
/// the stack, so the wake goes through the scheduler's queue ([`WakeupQueue`]).
struct ChangeNotifier {
    consumer: SharedConsumer,
    wakeups: WakeupQueue,
    last: Option<Tile>,
}

impl ChangeNotifier {
    fn new(consumer: SharedConsumer, scheduler: &Scheduler) -> Self {
        Self {
            consumer,
            wakeups: scheduler.wakeup_queue(),
            last: None,
        }
    }

    /// `tile`, with the consumer woken if it differs from the tile this last passed on.
    fn notify_if_changed(&mut self, tile: Tile) -> Tile {
        if self.last.as_ref() != Some(&tile) {
            self.wakeups.request(self.consumer.clone());
            self.last = Some(tile.clone());
        }
        tile
    }
}

struct InductionStoreProducer {
    /// Wakes this store's readers when a pull changes what it answers.
    notifier: ChangeNotifier,
    base: ProducerBase,
    /// Per accumulator key, the per-row seed stream. A carrier with no rows above it has
    /// one row, the empty path, so its seed arrives there.
    seed_producers: Vec<(Value, Box<dyn TileProducer>)>,
    /// What the body says is complete, one predicate per level of its decision stream,
    /// outermost first: the row levels above the stores, then the positions within one. The
    /// drive is what knows, from its source; the store carries it to the read. A carrier
    /// with no rows above it has the one entry — its positions.
    complete_rows: Vec<Predicate>,
    /// One engine per store, nested one level per collection level above it. A carrier
    /// with no rows above it is [`Engines::Store`]; a nested one is [`Engines::Rows`],
    /// each row holding its own seed and changelog rather than a share of one flat log.
    engines: Engines,
    /// The last position a predecessor store reached, which this one's store is decided
    /// through from the moment it opens. Only a carrier with no rows above it resumes —
    /// a nested one's rows belong to the store around it — so this is `None` wherever the
    /// engine tree has levels, and every row opens undecided.
    resumed_after: Option<Position>,
    body_producer: Box<dyn TileProducer>,
    write_keys: Vec<Value>,
    tap_fields: Vec<String>,
    /// The full-store output tiling — for a debug-time shape check on the rendered
    /// store tile.
    output_tiling: Tiling,
    /// The highest path this carrier has stepped, for the check that rows open in
    /// ascending path order and never reopen. Survives [`Engines::remove_covered`], which
    /// moves [`decided_path`](Self::decided_path) back when it drops the rows it names.
    #[cfg(debug_assertions)]
    stepped_through: Option<Path>,
}

impl InductionStoreProducer {
    /// The store at `row`, opened at `seed` if this is the pull that reaches it.
    ///
    /// Every store opens here, whatever its depth: `resumed_after` is a position of the
    /// carrier's own store and a nested carrier does not resume, so it is `None` wherever
    /// `row` names one.
    fn open_at(&mut self, row: &Path, seed: &HashMap<Value, Value>) -> &mut CommitEngine {
        debug_assert!(
            row.is_empty() || self.resumed_after.is_none(),
            "a carrier with rows above it does not resume, so its rows open undecided; \
             row {row:?} would open at {:?}",
            self.resumed_after
        );
        let resumed_after = self.resumed_after.clone();
        self.engines.store_at(row, &mut || {
            CommitEngine::seeded_at(resumed_after.clone(), seed.clone())
        })
    }

    /// The region of the body's decisions this store has consumed, as the guard that
    /// names it.
    ///
    /// A **prefix of the path**, because that is what a sequential drive delivers and so
    /// what has been consumed: the enclosing rows before the head entirely, and within the
    /// head row everything up to its last decided position. Saying it as a `Codomain`
    /// instead would claim that prefix in *every* row, including rows that have delivered
    /// nothing — and a release is a promise never to ask again.
    fn consumed_guard(&self, decided: &Path) -> TileGuard {
        domain_prefix(decided.to_vec())
    }

    /// Release the seed streams through `decided`, whose rows are open and so read no seed
    /// again.
    ///
    /// A nested carrier's seed streams are keyed by the body's `(enclosing, position)`
    /// pairs, so the region is the prefix of that pair-keyed domain ([`pair_keyed`]). The
    /// streams are shared with the drive's reseeds, and a `FanOut` passes on only what
    /// every branch has released, so a store holding them would pin the pair stream for
    /// the whole run. A carrier with no rows above it reads one seed, whole, and releases
    /// it when the body goes terminal.
    fn release_seeds_through(&mut self, decided: &Path) {
        if decided.len() < 2 {
            return;
        }
        let guard = domain_prefix(pair_keyed(decided));
        for (_, producer) in &mut self.seed_producers {
            producer.release(guard.clone());
        }
    }

    /// The path this carrier has decided through: the last row it opened at each level,
    /// down to that store's watermark. `None` before anything is decided.
    ///
    /// The drive is sequential, so the last row of a level is the one still running and
    /// every row before it is complete — which is what makes one path the whole cursor.
    fn decided_path(&self) -> Option<Path> {
        fn walk(at: &Engines) -> Option<Vec<Value>> {
            match at {
                Engines::Store(engine) => {
                    Some(vec![engine.as_ref()?.decided_watermark()?.value().clone()])
                }
                Engines::Rows(rows) => {
                    let (row, below) = rows.last()?;
                    let mut path = vec![row.clone()];
                    path.extend(walk(below)?);
                    Some(path)
                }
            }
        }
        walk(&self.engines).map(Path::from)
    }

    /// Each row's value before any of its positions, read from the per-key seed streams.
    ///
    /// A seed stream is keyed the way the body it was compiled against is. A carrier with
    /// no rows above it takes the position alone, so its seed is one value and it seeds
    /// the empty path. A nested carrier's body takes the `(enclosing, position)` pair, so
    /// its seed is keyed by pairs under the standing levels and is constant in the
    /// position within a row — any position of a row carries that row's seed, and the
    /// position is dropped here.
    ///
    /// Read fresh each pull rather than latched. The stream releases behind the drive, but
    /// a row's seed is only ever wanted at the moment the row opens — which is the pull
    /// that delivers its first position, when the stream still carries it. Once open, the
    /// row's engine holds its own seed and nothing asks again.
    ///
    /// A row appears here only once **every** key has a value at it. A store holds one
    /// value per key before any position and is seeded once, so a row opened on the first
    /// seed to arrive would leave a key whose own seed settles later standing at no value
    /// at all — and nothing asks again. Two accumulators in one loop settle at different
    /// pulls whenever one of their seeds reads a loop and the other is a literal.
    fn row_seeds(&mut self) -> HashMap<Path, HashMap<Value, Value>> {
        let rows_above = self.tiling().levels();
        let keys = self.seed_producers.len();
        let mut seeds: HashMap<Path, HashMap<Value, Value>> = HashMap::new();
        for (key, producer) in &mut self.seed_producers {
            let tile = producer.get(producer.tiling().universal_guard());
            for (row, value) in decode_row_seeds(&tile, rows_above) {
                let at = seeds.entry(row.clone()).or_default();
                match at.get(key) {
                    Some(first) => debug_assert_eq!(
                        *first, value,
                        "a row has one seed: every position under row {row:?} carries the \
                         same seed for {key}"
                    ),
                    None => {
                        at.insert(key.clone(), value);
                    }
                }
            }
        }
        seeds.retain(|_, at| at.len() == keys);
        seeds
    }

    /// The delta a decision applies: every carry write, and only the taps that fired.
    ///
    /// A non-fired conditional feed is omitted, so its per-position read skips that
    /// position; a carry appends nothing at all and the accumulator holds from the seed
    /// or the latest earlier change.
    fn write_set(
        &self,
        commit: bool,
        writes: Vec<Value>,
        tap_fired: Vec<bool>,
    ) -> Option<HashMap<Value, Value>> {
        if !commit {
            return None;
        }
        debug_assert_eq!(
            writes.len(),
            self.write_keys.len(),
            "the decision's write set aligns with the store's write keys"
        );
        let n_carry = self.write_keys.len() - self.tap_fields.len();
        Some(
            self.write_keys
                .iter()
                .cloned()
                .zip(writes)
                .enumerate()
                .filter(|(i, _)| *i < n_carry || tap_fired[*i - n_carry])
                .map(|(_, kv)| kv)
                .collect(),
        )
    }

    /// This carrier's engines as a tile, each store `terminal` once the recurrence is final
    /// (the accumulator can no longer change, so a downstream `ExtractFinal` /
    /// `final_or_default` resolves).
    ///
    /// A store waiting for its seed contributes nothing: an undecided frontier, no change,
    /// and no value before any position. That is what it holds, and it is what the driver
    /// reads to know not to emit yet.
    fn render_store(&self) -> Tile {
        let store = render_carrier_tile(&self.engines, self.tiling(), &self.complete_rows);
        debug_assert!(
            store.check_from(&self.output_tiling),
            "rendered induction store tile does not match the carrier's tiling"
        );
        store
    }
}

impl TileProducer for InductionStoreProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Read the seeds before the body. A store opens the moment both its row and its
        // seed are known, and for the carrier's own store — the empty path — the row is
        // known from the start, so it opens here. It has to: the driver reads the
        // accumulator's value before the first position out of this store, and a store
        // that is not open carries none. A nested carrier's rows are named by decisions
        // instead, so none of its seeds lands at the empty path and they wait below.
        // An open store of its own has read its seed, and nothing more of it is wanted.
        let row_seeds = match &self.engines {
            Engines::Store(Some(_)) => HashMap::new(),
            _ => self.row_seeds(),
        };
        if let Some(seed) = row_seeds.get(&Path::default()) {
            let seed = seed.clone();
            self.open_at(&Path::default(), &seed);
            // The seed is read once, at the store's opening, so it is released there.
            for (_, producer) in &mut self.seed_producers {
                producer.release(producer.tiling().universal_guard());
            }
        }
        let body_tile = self
            .body_producer
            .get(self.body_producer.tiling().universal_guard());
        // Consume the body's decisions **in ascending position order**, starting past
        // the last position decided and stopping at the first the body has not
        // decided. The next position need not be the next integer: a restricted loop
        // source skips the extent positions its filter excluded, and the store
        // decides only the positions it iterates. The decision gates commit (append
        // the change) vs carry (`step(_, None)` — the value inherits from the seed
        // or the latest earlier change). The driver emits one position per pull, so
        // this normally steps once; consuming a run costs nothing extra and keeps
        // the store's rule independent of that rate.
        let started_at = self.decided_path();
        // A decision names the store it belongs to and the position within it, as the path
        // down the levels the recurrence is indexed by. A carrier with no rows above it
        // has paths of one component, which is the whole of that statement at depth zero:
        // one store, at the empty path.
        let Tile::Scalar(union_col) = body_tile.deepest_values().clone() else {
            return self.notifier.notify_if_changed(self.render_store());
        };
        for (path, idx) in decided_paths(&body_tile) {
            let Some((rows, inner)) = path.split_position() else {
                unreachable!("a decision's path names a store and a position in it")
            };
            let (row, inner) = (Path::from(rows.to_vec()), Position::new(inner.clone()));
            if self
                .engines
                .get(&row)
                .and_then(CommitEngine::decided_watermark)
                .is_some_and(|d| inner <= *d)
            {
                continue;
            }
            // Carry writes lead, taps follow (the layout `build_induction_store_single`
            // sets). A committing position applies every carry write but only the taps
            // that *fired* on its route — a non-fired conditional feed is omitted from the
            // delta, so its per-position read (`store_delta_at`) skips this position.
            // `commit` is true whenever a tap fires (the letrec phase folds feed-fire paths
            // into the commit gate), so a fired tap always rides an appended change. A
            // carry appends nothing at all, whatever a tap's tag there says.
            let Some((commit, writes, tap_fired)) =
                decision_at_index(&union_col, idx, &self.write_keys, &self.tap_fields)
            else {
                break;
            };
            // A row with no seed yet is left for a later pull rather than opened at
            // nothing: the carry at its first position folds to the seed, so opening
            // without one answers a value the row never held. An open row needs no seed,
            // and the seeds of the positions it has decided are released below.
            let seed = match self.engines.get(&row) {
                Some(_) => HashMap::new(),
                None => match row_seeds.get(&row) {
                    Some(seed) => seed.clone(),
                    None => break,
                },
            };
            #[cfg(debug_assertions)]
            {
                debug_assert!(
                    self.stepped_through
                        .as_ref()
                        .is_none_or(|high| path > *high),
                    "a carrier steps its decisions in ascending path order and never reopens \
                     a row: stepping {path:?} at or below {:?}, the highest path already \
                     stepped",
                    self.stepped_through
                );
                self.stepped_through = Some(path.clone());
            }
            let write_set = self.write_set(commit, writes, tap_fired);
            let engine = self.open_at(&row, &seed);
            engine.step(inner.clone(), write_set);
            debug_assert_eq!(
                engine.decided_watermark(),
                Some(&inner),
                "a step at position {inner} advances the row's watermark to it"
            );
        }
        // Reclaim the decisions just consumed. This release travels back through
        // the body to the driver, which compacts its emitted window and releases
        // the loop source in turn — the whole reclamation chain, on ordinary
        // edges.
        if let Some(decided) = self.decided_path()
            && Some(&decided) != started_at.as_ref()
        {
            self.body_producer.release(self.consumed_guard(&decided));
            self.release_seeds_through(&decided);
        }
        // The body says what is complete at every level of its decision stream, and the
        // store publishes each level on its own so a read can answer a row as a whole. Every
        // level is read: a standing level's rows are not the carrier's, the loop around a
        // standing level waits on that level's own last row, and the innermost level is the
        // positions a store will gain no more of.
        //
        // The outermost level saying `True` is what closes a store's frontier (`terminal`),
        // so a downstream `ExtractFinal`/`final_or_default` resolves — a level's predicate
        // means complete at every depth beneath it. The frontier keeps its `at_or_below(w)`
        // watermark, which spans the whole extent including a trailing run of carries, so
        // `len`/`store_frontier` do not undercount to the latest change position when the
        // tail is all carry. The driver closes its body-input domain once a complete source
        // has been fully emitted, and that rides the body chain down to here.
        for level in 0..self.complete_rows.len() {
            let Tile::DataFunction {
                domain_predicate, ..
            } = body_tile.values_at(CurryLevel::new(level))
            else {
                continue;
            };
            self.complete_rows[level] = self.complete_rows[level].union(domain_predicate);
        }
        // Reading a terminal body stream as "the whole extent is decided" rests on
        // the loop above having consumed all of it. It stops at the first position it
        // cannot decode as a decision, so a terminal stream with an undecodable row
        // and decisions past it would close the frontier early and drop them without
        // a sound.
        // Undecided is a **path**, not a position: an inner position repeats across rows,
        // so only the path says which decision is meant. `decided_paths` is in drive order,
        // so the first past the cursor is the lowest.
        let through = self.decided_path();
        let undecided = decided_paths(&body_tile)
            .into_iter()
            .map(|(path, _)| path)
            .find(|path| through.as_ref().is_none_or(|d| path > d));
        debug_assert!(
            !body_tile.is_terminal() || undecided.is_none(),
            "induction store: the body's decision stream is terminal but still decides \
             {undecided:?}, past the watermark {through:?}"
        );
        // A nested carrier's rows open as they are decided and release their seeds as they
        // go (`release_seeds_through`); the rest go once the body is done, since a row that
        // ran no position answers from the enclosing row's default instead. The carrier's
        // own store released its seed when it opened.
        if body_tile.is_terminal() && matches!(self.engines, Engines::Rows(_)) {
            for (_, producer) in &mut self.seed_producers {
                producer.release(producer.tiling().universal_guard());
            }
        }
        self.notifier.notify_if_changed(self.render_store())
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Changelog GC (mirrors [`CommitProducer::release_impl`]). The store sits behind a
        // `FanOut`, so this guard is the **meet** of what every branch has released — the
        // drive, the dense and tap reads, a settled read — and so the region safe to
        // reclaim. `gc_released_prefix` keeps the carry source a position can still fold
        // back to, including the one the drive folds at the frontier, so the GC never
        // strands the recurrence and a never-terminating loop's changelog stays at
        // O(keys) plus the slowest reader's lag.
        //
        // A release names a region of the carrier, one arm per level ([`domain_prefix`]),
        // so the prefix each store may reclaim is its own: the positions of that store the
        // guard covers. Asked of the store's own decided positions rather than of the
        // predicate, because a qualified predicate answers about a **path** and a
        // watermark is a value — which is why [`Predicate::max_released_position`] declines
        // one. A carrier with no rows above it is the same walk over one store at the empty
        // path, where the guard is unqualified and every decided position it covers is a
        // prefix.
        let mut at: Vec<Value> = Vec::new();
        self.engines.for_each_store_mut(&mut |rows, engine| {
            at.clear();
            at.extend_from_slice(rows);
            at.push(Value::Unit);
            // The reclaimable prefix ends at the first decided position the guard does not
            // cover: one past it is still read by someone, and so is its carry source, so a
            // position covered beyond it is not a prefix to reclaim through. The decided
            // positions ascend, so the walk is in order.
            let mut through: Option<Position> = None;
            for decided in &engine.decided_positions {
                let last = at.len() - 1;
                at[last] = decided.value().clone();
                if !obsolete_guard.covers_path(&at) {
                    break;
                }
                through = Some(decided.clone());
            }
            if let Some(through) = through {
                engine.gc_released_prefix(&through);
            }
        });
        // A row the meet names whole is released outright, not reclaimed position by
        // position: nothing under it can be asked for again, so it leaves the tree and
        // the render together.
        self.engines.remove_covered(&obsolete_guard);
    }
}

/// The `Transact`'s external output: `key`'s **commit-value stream**
/// `Txn ⇀ Value` — one entry per commit tick (tick 0 being the initial
/// value), the per-key projection of the store's full history.
///
/// This is the store modelled as what it is: a value that changes over commit
/// time. Each entry is an immutable committed value at a tick, so the stream is
/// genuinely monotonic (append-only) and needs **no terminal gate** — every
/// commit is observable the instant it lands, not held back until all writers
/// finish. Its `domain_predicate` is `at_or_below(watermark)` while the stream is
/// still growing and `True` once it is closed — which of the store's two closure
/// axes closes it is decided by `carry_forward`, below.
///
/// Two readers, fixed per key by its registration:
///
/// - the **in-block reply tap** (`out << e` inside a block — `carry_forward:
///   false`), holding only the ticks that wrote it and closing as soon as its own
///   writers do ([`Tile::Store`]'s `closed_keys`);
/// - the **read-your-writes mutable variable carry** (`carry_forward: true`, the
///   latest write ≤ each tick), which gains a position at every tick and so
///   closes only with the whole store.
///
/// Two other reads of a transactional key do not come through here. A read fed
/// *out* of a block folds the store as-of via [`AsOf`], sampling an arbitrary commit
/// position, and a surface `await_final(x)` is a [`StoreFinalRead`], sampling the key
/// once its writers have drained. Which read a program gets is selected by the term
/// it wrote, never inferred from the reading loop.
pub struct StoreValueStream {
    base: OperatorBase,
    store_op: Box<dyn TileOperator>,
    key: Value,
    value_extent: Extent,
    /// Whether the key's value persists across commit ticks that don't write it.
    /// A **carry** (`true`) holds its latest committed value forward — reading
    /// it at any tick yields the latest write ≤ that tick. A **reply tap**
    /// (`false`) is a per-commit event: it appears only at the tick that wrote it,
    /// so two writers' taps to one defer don't smear each other's values across
    /// the shared commit clock.
    carry_forward: bool,
}

impl StoreValueStream {
    pub fn new(
        store_op: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
        carry_forward: bool,
    ) -> Self {
        // Checked here so a mis-wiring names the tiling that is wrong, as
        // [`StoreDenseRead::new`] and [`ExtractFinal::new`] do for theirs. `get_impl`
        // reads the tile as a `Tile::Store` and has nothing to answer with otherwise.
        assert!(
            matches!(store_op.tiling(), Tiling::Store { .. }),
            "StoreValueStream reads a store, got {}",
            store_op.tiling()
        );
        Self {
            base: OperatorBase::new(read_tiling(Extent::Base(BaseType::UInt), &value_extent)),
            store_op,
            key,
            value_extent,
            carry_forward,
        }
    }
}

impl TileOperator for StoreValueStream {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward store progress to this stream's consumer: a new commit on the
        // store (e.g. a live cross-endpoint read-only transaction committing its
        // reply tap) must wake the downstream sink so it re-pulls and sees the new
        // value. Without this, a tap/key reader off a live commit store is only
        // woken once (the kick) and never again. The store starts at its tick-0
        // value, so kick once to start the drain loop.
        let consumer = shared_consumer(consumer);
        consumer.borrow_mut().notify();
        let g = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.subscribe(
            g,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        );
        Box::new(StoreValueStreamProducer {
            base: ProducerBase::new(StoreValueStreamProducer::alloc_id(), self.tiling()),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            carry_forward: self.carry_forward,
            release_cursor: PrefixReleaseCursor::default(),
        })
    }
}

struct StoreValueStreamProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    key: Value,
    value_extent: Extent,
    /// See [`StoreValueStream::carry_forward`]: carry (hold the latest value
    /// across ticks that don't write the key) vs. reply tap (emit only at the
    /// tick that wrote it).
    carry_forward: bool,
    /// Highest commit tick a consumer has released. The store's commit log only
    /// grows, so `get` emits each tick exactly once: only ticks beyond this
    /// cursor. A re-reading consumer that never releases leaves it empty and sees
    /// the full projection every pull (and must *replace*, not merge); an
    /// accumulating consumer (`Memo`, the reply-tap path) releases what it has
    /// merged, so the next pull is the delta — without this, re-emitting merged
    /// ticks would double them in the consumer's cache. (A `True`/terminal release
    /// is "all ticks released", not "no tick" — see [`PrefixReleaseCursor::
    /// advance_from`]; missing that was the reply-tap duplication bug.)
    release_cursor: PrefixReleaseCursor,
}

impl TileProducer for StoreValueStreamProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Sample the store's current tile once and re-fold the whole changelog
        // (consumer-driven; no producer-side drive-to-fixpoint). The store's writer
        // steps one commit per pull and re-arms itself on the wakeup queue, which
        // fans through the cyclic `FanOut` to re-pull this stream as commits land;
        // terminality flows through the store's closure flags below.
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // Fold the changelog directly. A closed stream yields a `True` output
        // domain predicate so a downstream terminal read resolves; a live one
        // carries the store's `at_or_below` watermark through.
        let Tile::Store {
            frontier,
            terminal,
            closed_keys,
            ..
        } = &store
        else {
            unreachable!("StoreValueStream's constructor requires a store source; got {store:?}")
        };
        // Which closure axis applies follows from the projection, with no mode flag to
        // set. A **change** stream (`carry_forward: false`) holds only the ticks that
        // wrote `key`, so it gains nothing once `key` is closed — it may close on the
        // per-key axis, which is what lets `await_final(x)` settle while a store-mate
        // still commits. A **carry** stream gains a position at every tick, including
        // ticks that wrote some other key, so per-key closure would report terminal
        // while positions are still arriving; only the whole store closing can close
        // it.
        let closed = if self.carry_forward {
            *terminal
        } else {
            *terminal || closed_keys.contains(&self.key)
        };
        let domain_predicate = if closed {
            Predicate::True
        } else {
            running_frontier(frontier)
        };
        // Fold the changelog to `key`'s value under the carry policy
        // ([`fold_changelog_key_ascending`], shared with the induction
        // `StoreDenseRead`): a carry holds the latest write ≤ the tick; a
        // reply tap emits only the tick that wrote it (carrying it forward would
        // smear one writer's reply across another's commit ticks on the shared
        // clock). One O(changes) ascending pass folds every tick — the released
        // prefix is still walked so the carry is built correctly, then dropped at
        // emit time (the accumulating consumer has already merged it). The ticks are
        // the store's, not this key's: a carry gains a position wherever any key was
        // written.
        // Every tick the engine decided — its domain, which on the commit clock is its
        // start (the state after no transaction, holding the seed and occupied by no
        // commit) followed by one per commit. A carry read folds the seed at the start;
        // a change read finds no delta there and drops it.
        let Tile::Store { decided, .. } = &store else {
            unreachable!("StoreValueStream's constructor requires a store source; got {store:?}")
        };
        // A reclaim takes the prefix of the clock the readers have released, keeping each
        // key's carry source, so the ticks start at the clock's start or where the reclaim
        // stopped, and run one commit apart from there.
        let all_ticks: Vec<Position> = store_decided_positions(decided, 0);
        debug_assert!(
            all_ticks
                .windows(2)
                .all(|w| next_commit_tick(&w[0]) == w[1]),
            "the commit clock's decided ticks run one commit apart: {all_ticks:?}"
        );
        let folded = fold_changelog_key_ascending(
            &store,
            all_ticks.iter().cloned(),
            &self.key,
            self.carry_forward,
        );
        let mut ticks: Vec<Value> = Vec::with_capacity(all_ticks.len());
        let mut values: Vec<Value> = Vec::with_capacity(all_ticks.len());
        for (tick, v) in all_ticks.iter().zip(folded) {
            if self.release_cursor.is_released(tick) {
                continue;
            }
            if let Some(v) = v {
                ticks.push(tick.value().clone());
                values.push(v);
            }
        }
        read_tile(
            ColumnValue::from_values(ticks, &Extent::Base(BaseType::UInt)),
            values,
            &self.value_extent,
            domain_predicate.clone(),
        )
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Advance the emit cursor past every released commit tick (so we don't
        // re-emit a merged prefix — a re-fold that unions this tap at a later
        // frontier would otherwise duplicate a position through the `Memo` merge)
        // AND forward that prefix upstream to the store: a consumer that merged
        // commits `≤ max_tick` no longer needs them, so this read branch releases
        // them. The store reclaims a version only once *every* branch (this reader,
        // the writers) has released it — the cyclic `FanOut` intersects — so
        // forwarding here is safe and is what lets a long-lived collection log shed
        // its merged prefix. A terminal (`True`) release covers the whole
        // changelog.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard {
            let forward = match self.release_cursor.advance_from(pred) {
                ReleasedExtent::Nothing => None,
                ReleasedExtent::Through(max_tick) => {
                    Some(Predicate::at_or_below(max_tick.into_value()))
                }
                ReleasedExtent::All => Some(Predicate::True),
            };
            if let Some(pred) = forward {
                self.store_producer
                    .release(TileGuard::Function(FunctionGuard::Domain(pred)));
            }
        }
    }
}

/// The **terminal read** of a store key: `key`'s value where the store closes it — where
/// a transactional variable's own writers finish, or where an induction loop ends — or
/// the store's seed if nothing wrote it.
///
/// A Txn read samples the key's carried value; this one's position is where the key
/// closes. It takes the same sample [`AsOf`] does, through the same
/// [`store_current`] — the difference is what fixes the position: a trigger arrival
/// there, the store's own closure here. So it is neither a reduction nor a
/// projection of the history, and needs no seed operand, because the store holds its
/// seed beside its changelog.
pub struct StoreFinalRead {
    /// Output tiling `Scalar(V)` — a terminal read is one value, not a stream.
    base: OperatorBase,
    /// The commit store (a [`Tile::Store`] fan branch).
    store_op: Box<dyn TileOperator>,
    /// The key whose settled value this reads.
    key: Value,
    value_extent: Extent,
}

impl StoreFinalRead {
    pub fn new(store_op: Box<dyn TileOperator>, key: Value, value_extent: Extent) -> Self {
        Self {
            base: OperatorBase::new(Tiling::Scalar(value_extent.clone())),
            store_op,
            key,
            value_extent,
        }
    }
}

impl TileOperator for StoreFinalRead {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward store progress downstream, as [`StoreValueStream`] does: the key is
        // not settled until the store says so, and the consumer has to be woken to
        // re-pull when that happens. Kick once to start the drain loop.
        let consumer = shared_consumer(consumer);
        consumer.borrow_mut().notify();
        let g = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.subscribe(
            g,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        );
        Box::new(StoreFinalReadProducer {
            base: ProducerBase::new(StoreFinalReadProducer::alloc_id(), self.tiling()),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            released: false,
        })
    }
}

struct StoreFinalReadProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    key: Value,
    value_extent: Extent,
    /// Whether the consumer has released this read. A scalar has one position, so a
    /// release is total and the value must not come back out after it.
    released: bool,
}

impl TileProducer for StoreFinalReadProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        if self.released {
            return self.tiling().empty_tile();
        }
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // Release through the frontier. This read wants the key's value as the store
        // stands, and `gc_released_prefix` keeps each key's carry source where nothing above
        // the boundary supersedes it, so the fold below is never stranded. Without this
        // release the `FanOut`'s meet cannot advance past this branch until the read retires,
        // which holds every version of every key for the length of the loop.
        if let Some(frontier) = store_frontier(&store) {
            self.store_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(frontier.into_value()),
                )));
        }
        let settled = match &store {
            Tile::Store {
                terminal,
                closed_keys,
                ..
            } => *terminal || closed_keys.contains(&self.key),
            _ => false,
        };
        if !settled {
            // A writer that can write `key` may still commit, so there is no settled
            // value to report. An empty scalar is non-terminal, so the consumer pulls
            // again. The per-key disjunct is what lets this read settle while a
            // store-mate's writer is still committing.
            return self.tiling().empty_tile();
        }
        // The key's value as the store stands: its latest change at or below the
        // decided frontier, or the seed where nothing wrote it — and, for an induction
        // store that ran no position at all, where nothing is decided either.
        let value = store_value_now(&store, &self.key);
        Tile::Scalar(ColumnValue::from_values(
            value.into_iter().collect(),
            &self.value_extent,
        ))
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A universal release from the one consumer of a scalar retires this read, and
        // releasing the store branch with it is safe: every other reader of the store
        // holds its own guard through the fan, which the fan intersects, so the store
        // reclaims a version only once all of them have released it too.
        if obsolete_guard.is_universal() {
            self.released = true;
            self.store_producer
                .release(self.store_producer.tiling().universal_guard());
        }
    }
}

/// A **dense** induction-store read: `key`'s value at every position the store decided,
/// folded from its [`Tile::Store`] changelog into `Fun(D, V)`.
///
/// The positions are the store's own domain rather than an enumeration of the loop extent,
/// so a restricted source's read spans exactly the positions the recurrence ran at, in
/// ascending order — which a co-iterated read (`for r in …: cnt += 1; with begin(): store :=
/// store + cnt`) needs to align with its source through `zip_arms`. The fold reads the
/// changelog rather than the frontier, so a carry position takes the latest earlier write and
/// a leading carry takes the seed.
///
/// Under rows the read carries the same levels the store does, and produces one history per
/// row, each folded against that row's own store. A nested loop's trailing read is
/// [`ExtractFinal`](crate::interpreter::tile_operators::ExtractFinal) per row over it; a flat
/// loop's is [`StoreFinalRead`], which samples the settled store and does not come through
/// here.
///
/// This and [`StoreValueStream`] are the same changelog projection over different clocks:
/// loop positions here, commit ticks there. Both share the per-position fold, where a carry
/// holds and a tap is an event ([`fold_changelog_key`]).
pub struct StoreDenseRead {
    /// Output tiling [`read_tiling`] over `D`.
    base: OperatorBase,
    /// The induction store (a [`Tile::Store`] fan branch).
    store_op: Box<dyn TileOperator>,
    /// The key to project.
    key: Value,
    value_extent: Extent,
    /// Whether the key carries its value forward across positions that do not
    /// write it. An **accumulator** (`true`) folds the latest write ≤ each
    /// position (`store_value_at`), so every decided position has a value. A
    /// **reply tap** (`false`) is a per-position event: it appears only at the
    /// position whose changelog delta actually wrote it (`store_delta_at`), so the
    /// dense read emits the fired subset of positions.
    carry_forward: bool,
    /// The loop extent, for the position column the read emits.
    domain: Extent,
    /// The collection levels standing above the store, outermost first — empty for a
    /// flat carrier, its enclosing rows for a nested one, and those rows under the levels
    /// they in turn stand beneath for a carrier inside a deeper nest.
    enclosing: Vec<Extent>,
    /// The level of histories this read rebuilds: the store's own rows. Stated here, where
    /// the levels above the store are counted, because the read's tiling carries the
    /// position level beneath them too — so this is not its innermost level.
    level: Option<CurryLevel>,
}

impl StoreDenseRead {
    pub fn new(
        store_op: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
        carry_forward: bool,
    ) -> Self {
        // A nested carrier is a store per enclosing row, so its read is one history per
        // row — the shape the enclosing body consumes it at, produced here rather than
        // regrouped afterwards. Recovering the rows from a flat pair-keyed read is not
        // possible: which rows are complete is not a fact about pairs.
        //
        // However many levels stand above the store, the read carries the same ones: a
        // flat carrier has none, a nested one its enclosing rows, and one beneath an
        // standing level those too.
        let mut enclosing: Vec<Extent> = Vec::new();
        let mut at = store_op.tiling();
        while let Tiling::DataFunction { domain, codomain } = at {
            enclosing.push(domain.clone());
            at = codomain;
        }
        let Tiling::Store { domain, .. } = at else {
            panic!(
                "StoreDenseRead reads a store, or a collection of them, got {}",
                store_op.tiling()
            )
        };
        let domain = domain.clone();
        let tiling = enclosing
            .iter()
            .rev()
            .fold(read_tiling(domain.clone(), &value_extent), |inner, keys| {
                Tiling::data_function(keys.clone(), inner)
            });
        let level = CurryLevel::new(enclosing.len()).enclosing();
        Self {
            base: OperatorBase::new(tiling),
            store_op,
            key,
            value_extent,
            carry_forward,
            domain,
            enclosing,
            level,
        }
    }
}

impl TileOperator for StoreDenseRead {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Wake the consumer on store progress — a newly decided position is both a
        // position to emit and the value to emit there, so it is the only news this
        // read has. Kick once to start.
        let consumer = shared_consumer(consumer);
        consumer.borrow_mut().notify();
        let store_producer = {
            let g = self.store_op.tiling().universal_guard();
            self.store_op.subscribe(
                g,
                forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                scheduler,
            )
        };
        Box::new(StoreDenseReadProducer {
            base: ProducerBase::new(StoreDenseReadProducer::alloc_id(), self.tiling()),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            carry_forward: self.carry_forward,
            domain: self.domain.clone(),
            enclosing: self.enclosing.clone(),
            level: self.level,
            release_cursor: PrefixReleaseCursor::default(),
        })
    }
}

struct StoreDenseReadProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    carry_forward: bool,
    key: Value,
    value_extent: Extent,
    /// The loop extent, for the position column this read emits.
    domain: Extent,
    /// The collection levels standing above the store, outermost first.
    enclosing: Vec<Extent>,
    /// The level of histories this read rebuilds — see [`StoreDenseRead::level`].
    level: Option<CurryLevel>,
    /// Positions a consumer has released. The store holds its domain until *every* one
    /// of its readers has released a position, so dropping this reader's own released
    /// prefix is this reader's business — the same rule [`StoreValueStream`] follows on
    /// the commit clock.
    release_cursor: PrefixReleaseCursor,
}

impl StoreDenseReadProducer {
    /// A **nested** carrier's read: one inner history per enclosing row.
    ///
    /// Each row is folded against its own store — its own changelog and its own seed — so
    /// a position that writes nothing resolves to the value that row began with rather
    /// than to the previous row's last write. The enclosing level's `domain_predicate`
    /// comes straight from the store, which knows it because the drive is sequential: a
    /// row can gain no further position once the next row has one.
    fn read_per_row(&mut self, store: &Tile) -> Tile {
        // Standing levels stand above the carrier and are kept as they are; only the level
        // holding the stores becomes a level of histories. Beneath a standing level the
        // stores are one collection whose groups belong to different enclosing rows, and
        // folding across a group boundary would carry one row's last write into the
        // next — so each group is read on its own and the level put back together
        // (`group_at` / `regroup_beneath`).
        let level = self
            .level
            .unwrap_or_else(|| unreachable!("a per-row read has the store's own rows"));
        // The empty level carries what the store says about that level. A carrier that
        // opened no row has still been told which of its rows will gain no position, and
        // that statement is what a reader above needs to answer them from its own default.
        let mut empty_level = self.tiling().values_at(level).empty_at_no_rows();
        if let (
            Tile::DataFunction {
                domain_predicate: empty_pred,
                ..
            },
            Tile::DataFunction {
                domain_predicate: stored,
                ..
            },
        ) = (&mut empty_level, store.values_at(level))
        {
            *empty_pred = stored.clone();
        }
        let read = |group: &Tile| self.read_one_level(group);
        let mut out = store.regroup_beneath(level, empty_level, &mut |row| {
            let group = store
                .group_at(level, row)
                .expect("regroup_beneath enumerates the rows group_at has");
            read(&group)
        });
        // The read is re-derived from the store on every pull, so what a consumer has
        // released has to come back off each time: the store keeps a position until every
        // reader is done with it, and handing one back to a reader that already took it is
        // what the release contract forbids.
        out.remove_guarded(self.obsolete_guard().clone());
        out.compact();
        out
    }

    /// One carrier's worth: a history per enclosing row, from that row's own store.
    fn read_one_level(&self, store: &Tile) -> Tile {
        let Tile::DataFunction {
            domain: rows,
            codomain,
            domain_predicate,
            ..
        } = store
        else {
            unreachable!(
                "a nested carrier's read is entered only where the constructor found a \
                 collection of stores; got {store:?}"
            )
        };
        let n = rows.len();
        let mut starts = Vec::with_capacity(n);
        let mut positions: Vec<Value> = Vec::new();
        let mut folded_values: Vec<Value> = Vec::new();
        // A row's positions at or below its frontier are decided, so each is final: the
        // positions level is complete there under that row, and only there. Rows sharing
        // a frontier are stated together.
        let mut frontier_group: HashMap<Position, usize> = HashMap::new();
        let mut by_frontier: Vec<(Position, Vec<Value>)> = Vec::new();
        for row in 0..n {
            starts.push(positions.len());
            let row_store = store_row(codomain, row, n);
            if let Some(frontier) = store_frontier(&row_store) {
                let group = *frontier_group.entry(frontier.clone()).or_insert_with(|| {
                    by_frontier.push((frontier, Vec::new()));
                    by_frontier.len() - 1
                });
                by_frontier[group].1.push(rows.index_at(row));
            }
            let Tile::Store { decided, .. } = &row_store else {
                unreachable!("store_row answers with a store")
            };
            let decided = store_decided_positions(decided, 0);
            let folded = fold_changelog_key_ascending(
                &row_store,
                decided.iter().cloned(),
                &self.key,
                self.carry_forward,
            );
            for (p, v) in decided.iter().zip(folded) {
                if let Some(v) = v {
                    positions.push(p.value().clone());
                    folded_values.push(v);
                }
            }
        }
        let inner = Tile::grouped(
            ColumnValue::UInts(starts),
            ColumnValue::from_values(positions, &self.domain),
            Box::new(Tile::Scalar(ColumnValue::from_values(
                folded_values,
                &self.value_extent,
            ))),
            by_frontier
                .into_iter()
                .map(|(frontier, keys)| {
                    let rows = keys.into_iter().fold(Predicate::False, |all, key| {
                        all.union(&Predicate::point(key))
                    });
                    Predicate::qualified(rows, Predicate::at_or_below(frontier.value().clone()))
                })
                .fold(Predicate::False, |all, one| all.union(&one)),
            BitSet::new(),
        );
        Tile::data_function(
            rows.clone(),
            Box::new(inner),
            domain_predicate.clone(),
            BitSet::new(),
        )
    }
}

impl TileProducer for StoreDenseReadProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Sample the store (consumer-driven; no producer-side drive-to-fixpoint) and
        // fold `key` at each position it has decided. The cycle advances one position
        // per pull, so a batch source converges over several pulls rather than in one
        // sample — the read grows across pulls, and every position it emits is final,
        // because a decided position is one the recurrence has already run. Later
        // positions re-pull us through the store's own consumer.
        //
        // **The positions are the store's domain**, not a second enumeration of the
        // loop extent: the store was driven at exactly these, where the extent names
        // whatever its type admits — too many for a restricted source, and nothing at
        // all for a domain that is not a dense integer range.
        //
        // The changelog is keyed by those same positions, so position `p` reads at `p`
        // — the accumulator *after* iteration `p`. `store_value_at` scans changes ≤
        // `p`, so a carry position inherits the latest earlier write and a leading
        // carry folds to the store's seed: no external default, and never `None`. The
        // `store.is_terminal()` gate below keeps this read non-terminal until the
        // store is fully decided, so the consumer re-pulls.
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        if !self.enclosing.is_empty() {
            return self.read_per_row(&store);
        }
        let Tile::Store { decided, .. } = &store else {
            unreachable!(
                "a flat read is entered only where the constructor found a bare store; got \
                 {store:?}"
            )
        };
        // The store records its positions in the order it was driven, which is
        // ascending; a release compacts off the front and never reorders. Sorting is
        // therefore a no-op here and is asserted rather than performed — the output
        // domain must be position-ordered, because a scalar-final read is
        // `ExtractFinal` over this stream and takes its *final column*.
        let sorted: Vec<Position> = store_decided_positions(decided, 0);
        debug_assert!(
            sorted.windows(2).all(|w| w[0] < w[1]),
            "a store records its decided positions in the order it ran them: {sorted:?}"
        );
        // Fold `key` at every position in one ascending pass (the shared
        // [`fold_changelog_key_ascending`]): an accumulator carries the latest write
        // ≤ that position (every position resolves — the seed stands below the
        // first); a reply tap yields a value only where that position actually wrote
        // it, so a non-firing position is omitted (the feed's per-position stream
        // over exactly the fired positions). One O(changes + positions) pass, not an
        // O(changes)-per-position re-scan.
        let folded = fold_changelog_key_ascending(
            &store,
            sorted.iter().cloned(),
            &self.key,
            self.carry_forward,
        );
        debug_assert!(
            !self.carry_forward || folded.iter().all(Option::is_some),
            "the store's seed gives every accumulator a value, so the carry fold always resolves"
        );
        // The released prefix is folded, so a carry is built across it, and dropped
        // here: a consumer that has taken a position must not be handed it again, and
        // the store keeps the position until *every* reader has released it.
        let mut kept: Vec<Position> = Vec::with_capacity(sorted.len());
        let mut values: Vec<Value> = Vec::with_capacity(sorted.len());
        for (p, v) in sorted.iter().zip(folded) {
            if self.release_cursor.is_released(p) {
                continue;
            }
            if let Some(v) = v {
                kept.push(p.clone());
                values.push(v);
            }
        }
        let positions = ColumnValue::from_values(
            kept.into_iter().map(|p| p.into_value()).collect(),
            &self.domain,
        );
        // Once the store is terminal its domain is complete, so this read is too and
        // a downstream terminal read resolves. Before that it is decided over exactly
        // the positions emitted above — which are final, every one of them being a
        // position the recurrence has run — so report those rather than `False`: a
        // consumer may take the prefix, and a `Memo` may cache it, without waiting for
        // the loop to end.
        let domain_predicate = if store.is_terminal() {
            Predicate::True
        } else {
            Predicate::from_column_value(&positions)
        };
        read_tile(positions, values, &self.value_extent, domain_predicate)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A release of this read's output is a promise never to request it again, so
        // what the store no longer needs follows from the release alone — not from who
        // the consumer is, nor from which of the two shapes it reads. The iteration
        // source is not this read's to reclaim: the drive consumes it and releases it as
        // it folds each position in.
        //
        // Both read modes forward it whole, and so does either shape. A **tap** read
        // (`carry_forward: false`) reads only each position's own delta, so a released
        // position is dead outright. A **carry** read (`carry_forward: true`) reads the
        // latest write at or below each position, and the store keeps that: a live
        // position's carry source survives the reclaim by
        // [`CommitEngine::gc_released_prefix`]'s own rule, so the reader has no bound of
        // its own to compute. Under rows the guard names rows, which the carrier has too
        // — a row released whole leaves its engine tree and its render together
        // ([`Engines::remove_covered`]), so the arm means there what it means here.
        if self.enclosing.is_empty()
            && let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
        {
            // With no rows the released positions come off the render through this
            // cursor; under rows `remove_guarded` takes the whole region at once.
            self.release_cursor.advance_from(pred);
        }
        self.store_producer.release(obsolete_guard);
    }
}

/// As-of (temporal) join: for each position of a `trigger` stream, latch the
/// **current value** of the shared store's `key` at the moment that trigger
/// position is first observed.
///
/// `trigger : Fun(B, _)` (e.g. an HTTP request stream), `source` the shared
/// commit store (a [`Tile::Store`] fan branch), output `Fun(B, V)` — `key`'s
/// value as of each trigger position. This is **every fed-out mutable variable read**, not
/// only the live one: each reading transaction sees the store as of where it lands
/// in the commit order. The HTTP case ("a request arriving now sees the store as
/// committed by now" — the *live cross-endpoint read*) is the canonical instance,
/// but a finite loop or a standalone singleton reads the same way — an as-of read
/// at an arbitrary position. (The *completed* value is a different term,
/// `await_final`, reduced by
/// [`ExtractFinal`](crate::interpreter::tile_operators::ExtractFinal) over the key's
/// [`StoreValueStream`];
/// it never arrives here.) The reply is indexed
/// by the trigger (the reading loop) — an *outer-indexed* read, not commit-clock
/// indexed. The pairing is by *processing time* — the only ordering the tile model
/// exposes between two independent streams — which is exactly "a reader sees what's
/// committed as of its turn."
///
/// It folds the store directly ([`store_current`]) rather than through a
/// per-key [`StoreValueStream`]: the drive-to-frontier and latest-value logic
/// live in the step tiling now, so `AsOf` is the thin residual sampler — the
/// per-request latch — that remains once the fold is centralized.
///
/// **Tile-legal by construction.** The output grows monotonically over `B`: once
/// a trigger position `b` is latched (frozen to the store's then-current value),
/// it never changes; later commits only affect *later* trigger positions. The
/// different-value-per-request behaviour comes from `B` being a multi-position
/// domain — each position an immutable snapshot — not from a scalar that mutates
/// (which the immutability invariant forbids). It is the dual of a store's own
/// driver: a driver latches an accumulator per *source* step; `AsOf` latches the
/// store's current value per *trigger* step.
/// One field of a multi-variable [`AsOf`] snapshot: the record field the reply
/// projects (`snap.field`), the store's runtime key it samples, and its value
/// extent.
#[derive(Clone)]
pub struct AsOfField {
    pub field: String,
    pub key: Value,
    pub value_extent: Extent,
}

/// What an [`AsOf`] latches and emits per trigger position.
#[derive(Clone)]
enum AsOfOutput {
    /// A single mutable variable → `Fun(B, V)` — the bare or computed single-variable
    /// as-of read.
    Scalar { key: Value, value_extent: Extent },
    /// A whole-snapshot record → `Fun(B, Record{field: V})` — the multi-variable as-of
    /// read. Every field is folded from a single source render
    /// at one commit frontier (§I-c), so a reply reading several mutable variables sees a
    /// consistent snapshot.
    Record { fields: Vec<AsOfField> },
}

impl AsOfOutput {
    /// The store keys sampled, in field order (one for `Scalar`, N for `Record`).
    fn keys(&self) -> Vec<&Value> {
        match self {
            AsOfOutput::Scalar { key, .. } => vec![key],
            AsOfOutput::Record { fields } => fields.iter().map(|f| &f.key).collect(),
        }
    }
    /// The codomain tiling: each sampled value takes the tiling of its extent, as every
    /// store read's does ([`read_tiling`]), so a collection-valued one is a level
    /// (`src/interpreter/design-operators.md`, "A collection inside a value stays a tile").
    fn codomain_tiling(&self) -> Tiling {
        match self {
            AsOfOutput::Scalar { value_extent, .. } => Tiling::from_extent(value_extent),
            AsOfOutput::Record { fields } => Tiling::Record(
                fields
                    .iter()
                    .map(|f| (f.field.clone(), Tiling::from_extent(&f.value_extent)))
                    .collect(),
            ),
        }
    }
}

pub struct AsOf {
    /// Output tiling: `DataFunction { domain: B, codomain }` where `codomain` is
    /// [`AsOfOutput::codomain_tiling`].
    base: OperatorBase,
    /// The trigger stream `Fun(B, _)` — drives one output position each.
    trigger: Box<dyn TileOperator>,
    /// The shared commit store (a [`Tile::Store`] fan branch) — the sampled
    /// key(s)' current value(s) are latched per trigger position.
    source: Box<dyn TileOperator>,
    /// What to sample and emit — a single mutable variable or a whole snapshot record.
    output: AsOfOutput,
}

impl AsOf {
    /// `trigger : Fun(B, _)`, `source` the shared commit store (`Tiling::Store`),
    /// `key`/`value_extent` the mutable variable to sample → output
    /// `Fun(B, value_extent)`.
    pub fn new(
        trigger: Box<dyn TileOperator>,
        source: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
    ) -> Self {
        Self::build(trigger, source, AsOfOutput::Scalar { key, value_extent })
    }

    /// The multi-variable **snapshot** read: sample every `field`'s mutable variable at
    /// one commit snapshot → output `Fun(B, Record{field: V})`, from which
    /// the reply projects each mutable variable. This is the §I-c snapshot-consistent
    /// as-of read.
    pub fn new_snapshot(
        trigger: Box<dyn TileOperator>,
        source: Box<dyn TileOperator>,
        fields: Vec<AsOfField>,
    ) -> Self {
        Self::build(trigger, source, AsOfOutput::Record { fields })
    }

    fn build(
        trigger: Box<dyn TileOperator>,
        source: Box<dyn TileOperator>,
        output: AsOfOutput,
    ) -> Self {
        let Tiling::DataFunction { domain: b_ext, .. } = trigger.tiling() else {
            panic!("AsOf trigger must be a function, got {}", trigger.tiling());
        };
        debug_assert!(
            matches!(source.tiling(), Tiling::Store { .. }),
            "AsOf source must be a commit Store, got {}",
            source.tiling()
        );
        let tiling = Tiling::data_function(b_ext.clone(), output.codomain_tiling());
        Self {
            base: OperatorBase::new(tiling),
            trigger,
            source,
            output,
        }
    }
}

impl TileOperator for AsOf {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("trigger", &*self.trigger));
        visit(value("source", &*self.source));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Both inputs wake the consumer: a new *trigger* position needs a fresh
        // latch, and *source* progress (a new commit) is what lets an
        // already-seen trigger position finally latch a value — and, crucially,
        // re-pulls until the cyclic store converges (the source's first pull may
        // only propose; later pulls commit and render).
        let consumer = shared_consumer(consumer);
        let tg = self.trigger.tiling().universal_guard();
        let trigger = self.trigger.subscribe(
            tg,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        );
        let sg = self.source.tiling().universal_guard();
        let source = self.source.subscribe(
            sg,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        );
        let b_extent = match self.tiling() {
            Tiling::DataFunction { domain, .. } => domain.clone(),
            _ => unreachable!("AsOf tiles as a function"),
        };
        Box::new(AsOfProducer {
            base: ProducerBase::new(AsOfProducer::alloc_id(), self.tiling()),
            trigger,
            source,
            output: self.output.clone(),
            b_extent,
            latched: Vec::new(),
            seen: HashSet::new(),
            release_cursor: PrefixReleaseCursor::default(),
        })
    }
}

struct AsOfProducer {
    base: ProducerBase,
    trigger: Box<dyn TileProducer>,
    source: Box<dyn TileProducer>,
    /// What to sample per trigger position (folded via [`store_current`]).
    output: AsOfOutput,
    b_extent: Extent,
    /// `(b ↦ latched snapshot)` — each entry frozen at latch time; the inner
    /// `Vec<Value>` holds the sampled value per key, in `output.keys()` order (one
    /// for a scalar read, N for a snapshot). Grows as new triggers latch;
    /// compacted of released positions in `release_impl`, so it stays bounded to
    /// the live request window.
    latched: Vec<(Value, Vec<Value>)>,
    /// Trigger positions currently latched (so each is recorded once). Tracks
    /// `latched`'s keys; released positions are dropped from both together.
    seen: HashSet<Value>,
    /// Prefix release watermark: every trigger position at or below it has been
    /// released and must never re-latch (see `release_impl`). A request stream is
    /// a monotone `UInt` domain released as a prefix, so a single watermark
    /// captures the released region exactly.
    release_cursor: PrefixReleaseCursor,
}

impl AsOfProducer {
    /// Whether trigger position `b` lies at or below the released-prefix
    /// watermark — i.e. the consumer has already taken it and it must not
    /// re-latch.
    fn is_released(&self, b: &Value) -> bool {
        self.release_cursor.is_released(&Position::new(b.clone()))
    }

    /// Build the output tile from the currently-latched `(b ↦ snapshot)` pairs,
    /// under `domain_predicate`. The latched set is already compacted of released
    /// positions, so it emits exactly the live response window. The codomain is
    /// [`AsOfOutput::codomain_tiling`]'s, each value indexed by the emitted domain position.
    fn emit_latched(&self, domain_predicate: Predicate) -> Tile {
        let n_keys = self.output.keys().len();
        let mut bs = Vec::with_capacity(self.latched.len());
        let mut cols: Vec<Vec<Value>> = vec![Vec::with_capacity(self.latched.len()); n_keys];
        for (b, snap) in &self.latched {
            bs.push(b.clone());
            for (i, v) in snap.iter().enumerate() {
                cols[i].push(v.clone());
            }
        }
        let codomain = match &self.output {
            AsOfOutput::Scalar { value_extent, .. } => {
                stored_value_tile(cols.into_iter().next().unwrap_or_default(), value_extent)
            }
            AsOfOutput::Record { fields } => Tile::Record(
                fields
                    .iter()
                    .zip(cols)
                    .map(|(f, col)| (f.field.clone(), stored_value_tile(col, &f.value_extent)))
                    .collect(),
            ),
        };
        let mut tile = Tile::data_function(
            ColumnValue::from_values(bs, &self.b_extent),
            Box::new(codomain),
            // Terminality rides with the trigger: when no more requests will
            // arrive (trigger terminal) the response set is complete.
            domain_predicate,
            BitSet::new(),
        );
        tile.qualify_codomain_by_keys();
        tile
    }
}

impl TileProducer for AsOfProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("trigger", self.trigger.inspect(opts))
            .child("source", self.source.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Sample the store's **current** tile once (consumer-driven): a request
        // observes the store as of *this* pull's watermark — an arbitrary as-of
        // position, which the unordered transactional model permits. We do not
        // drive the store to a fixpoint here; the store's own writer steps one
        // commit per pull and re-arms itself on the wakeup queue, and that wakeup
        // fans through the cyclic `FanOut` to re-pull this reader as commits land.
        // A trigger position latched this pull freezes to the watermark it sees;
        // a later position, re-pulled after further commits, latches a later value.
        let sg = self.source.tiling().universal_guard();
        let source_tile = self.source.get(sg);
        // Fold the store snapshot **once**, at the current frontier, for every
        // sampled key — so a multi-variable read sees all its mutable variables at one
        // commit time (§I-c). `None` if *any* key has no decided value yet, which
        // makes the read all-or-nothing: a single missing key withholds the whole
        // snapshot and re-pulls. This is safe for the shapes reached here because
        // every scalar mutable variable has a seed (`init_ops`) and the store opens only once
        // every seed has arrived, so `store_current` always has a value once it is open — no
        // mutable variable can be perpetually absent. (A future snapshot read that folds a
        // key with a genuinely-empty log — e.g. an append-only collection with no
        // writes — would stay non-terminal forever on the terminality gate below;
        // revisit the coupling then.) The frontier bound is the same for every key,
        // so it also drives the release below.
        let frontier = store_frontier(&source_tile);
        let snapshot: Option<Vec<Value>> = self
            .output
            .keys()
            .iter()
            .map(|k| store_current(&source_tile, k).map(|(_, v)| v))
            .collect();
        let trigger_tile = self.trigger.get(self.trigger.tiling().universal_guard());
        let trigger_pred = match &trigger_tile {
            Tile::DataFunction {
                domain_predicate, ..
            } => domain_predicate.clone(),
            _ => Predicate::False,
        };
        let store_terminal = source_tile.is_terminal();
        // Every trigger position latches as of its own arrival — the watermark the
        // moment it is first observed — whatever the trigger's domain. Freeze-once:
        // a position is recorded in `seen` exactly once, so its latched value never
        // changes; new positions latch newer values as commits land across re-pulls.
        // The read a program gets is therefore an arbitrary as-of sample, uniformly,
        // which is what the unordered transactional model specifies (a program that
        // means the completed value writes `await_final`, whose reducer is
        // `ExtractFinal` over the key's [`StoreValueStream`], not this operator).
        //
        // If the store has no decided value yet, `snapshot` is `None` and we latch
        // nothing this round — the position is left un-seen and latches on a later
        // pull. Positions at or below the release watermark are skipped: the consumer
        // has already taken them, so they must never re-latch even if the trigger
        // re-presents one (a lazily-compacting trigger's domain still legally carries
        // the position until it compacts). That skip is what makes the `release_impl`
        // compaction safe.
        if let (Tile::DataFunction { domain, .. }, Some(snap)) = (&trigger_tile, &snapshot) {
            for i in 0..domain.len() {
                let b = domain.index_at(i);
                if self.is_released(&b) {
                    continue;
                }
                if self.seen.insert(b.clone()) {
                    self.latched.push((b, snap.clone()));
                }
            }
        }
        // Release the store *below* the decided frontier. AsOf needs only the
        // current snapshot — a future trigger latches the latest-as-of-its-time,
        // which is `>=` this — so the prefix is dead. Releasing it on this store
        // fan branch is what lets a live store reclaim superseded history:
        // `CommitProducer` GCs the `FanOut`-intersected prefix. The
        // release names the last change strictly below the frontier, so the frontier's
        // own change survives and the fold still finds each key's value.
        if let Some(f) = &frontier
            && let Some(below) = last_position_below(store_change_positions(&source_tile), f)
        {
            self.source
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(below.into_value()),
                )));
        }
        // Terminality gate. This reader samples one watermark per pull — it does not
        // drive the store to a fixpoint itself — and relies on being re-pulled (via the
        // writer's wakeup fanning through the cyclic `FanOut`) to converge. So it must stay
        // **non-terminal** until the store itself is terminal, or it could report "done"
        // while the store is still committing and freeze a store no other consumer drives.
        //
        // The unlatched-position half covers the one way a terminal store can still owe a
        // value: the snapshot above is all-or-nothing, so a key with no decided value
        // withholds it. Every present position latches on the pull that finds a snapshot,
        // which is why this is otherwise false by the time the gate reads it.
        let has_unlatched_position = matches!(&trigger_tile, Tile::DataFunction { domain, .. }
        if (0..domain.len()).any(|i| {
            let b = domain.index_at(i);
            !self.is_released(&b) && !self.seen.contains(&b)
        }));
        let emit_pred = if store_terminal && !has_unlatched_position {
            trigger_pred
        } else {
            Predicate::False
        };
        self.emit_latched(emit_pred)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Compact: a released trigger position will never re-emit, so drop it from
        // `latched`/`seen` outright rather than letting them grow for the
        // operator's lifetime. This bounds both memory and the per-`get` re-scan
        // of `latched` to the live request window — the motivating long-lived HTTP
        // request stream.
        //
        // Correctness rests on the released prefix being recorded so it can never
        // re-latch: dropping from `seen` alone would let a re-presented position
        // (a lazily-compacting trigger) re-insert and latch a *fresh* value,
        // violating the frozen-snapshot invariant. We instead advance a prefix
        // watermark (the release cursor) — request positions form a monotone
        // `UInt` domain released as a prefix, so a single watermark captures the
        // released region — and the `get_impl` latch loop skips anything at or
        // below it. The source is compacted in `get_impl` (released below its
        // latest decided position, the only value future triggers need), not here;
        // `release_impl` handles only the trigger side.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard {
            match self.release_cursor.advance_from(pred) {
                ReleasedExtent::Nothing => {}
                ReleasedExtent::All => {
                    // Terminal release: the consumer is done with the whole
                    // domain. Drop everything and latch nothing further (every
                    // position is below the watermark).
                    self.latched.clear();
                    self.seen.clear();
                }
                ReleasedExtent::Through(w) => {
                    self.latched.retain(|(b, _)| {
                        let drop = Position::new(b.clone()) <= w;
                        if drop {
                            self.seen.remove(b);
                        }
                        !drop
                    });
                }
            }
        }
        self.trigger.release(obsolete_guard);
    }
}

/// One emitted body-input row: the snapshot the decision reads, the source item
/// it is for, that item's source position, and the domain position the row
/// occupies.
///
/// The source position is what makes a release interpretable on the transaction
/// side (it says *which* item a reclaimed row belongs to). It is distinct from
/// `position` there — a retried item occupies several attempt positions — and equal
/// to it on the induction side, where a row's position *is* its source position.
struct DriverRow {
    snapshot: Vec<Value>,
    /// This row's item, as the **one-row tile** the source delivered it in. An item that
    /// holds a collection is a level here and stays one all the way to the body, which is
    /// what lets the body iterate it; materializing it into a cell would only have to be undone
    /// by [`render`](DriverWindow::render).
    item: Tile,
    /// The enclosing parameter this row's body reads beside its slots, for a **nested**
    /// writer; `None` for a top-level one, whose body takes the slots alone. A tile for
    /// the same reason `item` is.
    enclosing: Option<Tile>,
    /// The **rows** this position sits under, for a nested writer: one component per
    /// level above it, outermost first. Levels rather than components of the position,
    /// which is what keeps a position a plain value of its own domain.
    row: Option<Path>,
    item_position: Position,
    /// The row's absolute domain position, which the body's decision is looked
    /// up by ([`body_decision_at`]). Ascending across the window, and on the
    /// induction side not necessarily contiguous: a restricted loop source
    /// delivers a subset of its extent's positions and the recurrence runs over
    /// exactly those.
    position: Position,
}

impl DriverRow {
    /// The path this row stands at in the drive's output: the rows above it, then its
    /// position.
    fn path(&self) -> Vec<Value> {
        let mut path: Vec<Value> = self.row.as_ref().map_or(Vec::new(), |p| p.to_vec());
        path.push(self.position.value().clone());
        path
    }
}

/// The live window of emitted `(read…, item)` rows, and the body-input tile it
/// renders.
///
/// Both drivers own one. What differs between them is *which* position to emit
/// next — the induction driver takes it from its source's delivered positions,
/// the transaction driver counts attempts — not how a window of rows becomes the
/// body's input, how positions stay absolute across compaction, or what a release
/// reclaims. Those are here, once.
///
/// Positions are **absolute and ascending**, each carried on its row: released
/// rows compact off the front without renumbering the rest, because the body
/// looks a decision up by domain *value* ([`body_decision_at`]). They need not be
/// contiguous — a restricted induction source has positions its extent does not.
struct DriverWindow {
    /// The body-input domain — the loop extent for an induction drive, the
    /// attempt counter for a transactional one — for the position column.
    domain: Extent,
    /// The enclosing row and parameter a **nested** writer's body takes, and `None` for
    /// a top-level one. See [`body_input_tiling`].
    nested: Option<NestedBody>,
    read_extents: Vec<Extent>,
    /// The item slot's tiling, which is the source's own ([`source_item_tiling`]). Held
    /// so an empty window can still render the slot: with no rows there is no slice to
    /// take the shape from.
    item: Tiling,
    /// How many rows have ever been pushed — the transaction driver's next attempt
    /// position, its attempts being a contiguous `UInt` domain of its own. Held
    /// across compaction, so a window emptied by a release still knows where it is.
    /// The induction driver takes its positions from its source instead and never
    /// reads this.
    attempts: usize,
    /// The last row and position pushed, for the ascending check. A domain need carry no
    /// successor, so the window records what it has rather than what comes next, and it
    /// records the **row** beside it: a nested carrier restarts its positions at each
    /// enclosing row, so the check is per row and the window's own contents cannot say
    /// which row that is — compaction empties them.
    highest_pushed: Option<(Option<Path>, Position)>,
    rows: Vec<DriverRow>,
    /// Highest absolute position a consumer has released. The body fans this
    /// input through a `Memo` that pulls it several times per round, so an
    /// already-released position must not re-emit — that would duplicate a
    /// domain position in the `Memo`'s append-merge.
    release_cursor: PrefixReleaseCursor,
}

impl DriverWindow {
    /// How many collection levels stand above the positions, and 0 for a drive whose rows
    /// are its positions. The paths such a drive indexes by are one longer — the row
    /// levels, then the position within the innermost.
    fn row_levels(&self) -> usize {
        self.nested.as_ref().map_or(0, |n| n.rows.len())
    }

    fn new(
        domain: Extent,
        nested: Option<NestedBody>,
        read_extents: Vec<Extent>,
        item: Tiling,
    ) -> Self {
        Self {
            domain,
            nested,
            read_extents,
            item,
            attempts: 0,
            highest_pushed: None,
            rows: Vec::new(),
            release_cursor: PrefixReleaseCursor::default(),
        }
    }

    /// The next attempt position of a driver whose positions are its own contiguous
    /// count — the transaction driver's.
    fn next_attempt(&self) -> Position {
        Position::new(Value::UInt(self.attempts))
    }

    /// Append a row at absolute position `position`.
    fn push(
        &mut self,
        snapshot: Vec<Value>,
        item: Tile,
        enclosing: Option<Tile>,
        row: Option<Path>,
        item_position: Position,
        position: Position,
    ) {
        debug_assert_eq!(
            snapshot.len(),
            self.read_extents.len(),
            "a body-input row carries one snapshot value per read key"
        );
        // Positions ascend **within a row**: a nested carrier restarts its positions at
        // each enclosing row, and the row is the level above rather than a component of
        // the position, so the two runs are independent.
        debug_assert!(
            self.highest_pushed
                .as_ref()
                .is_none_or(|(r, h)| *r != row || position > *h),
            "body-input positions ascend within a row: pushing {position} at or below the \
             highest already pushed ({:?})",
            self.highest_pushed
        );
        self.highest_pushed = Some((row.clone(), position.clone()));
        debug_assert_eq!(
            enclosing.is_some(),
            self.nested.is_some(),
            "a nested writer's body takes its enclosing parameter at every row, and a \
             top-level one at none"
        );
        debug_assert_eq!(
            row.is_some(),
            self.nested.is_some(),
            "a nested writer's rows each name the enclosing row they belong to"
        );
        self.rows.push(DriverRow {
            snapshot,
            item,
            enclosing,
            row,
            item_position,
            position,
        });
        self.attempts += 1;
    }

    /// Drop the rows a release names: whole rows of a level by `Domain`, and within
    /// whatever survives, the positions named by `Codomain`.
    ///
    /// The two arms are the shape `to_guard` emits for a collection of collections, and
    /// the only shape the guard algebra admits — a `Domain` and a `Codomain` cannot be
    /// intersected into one region. A window whose rows are its positions is the one-level
    /// case: the guard names positions and the paths it is read against are one component
    /// long. No cursor is needed to stop a reclaimed row coming back: the drive only ever
    /// moves forward, so a row it has passed is never pushed again.
    fn reclaim(&mut self, guard: &TileGuard) {
        match guard {
            TileGuard::Or(arms) => {
                for arm in arms {
                    self.reclaim(arm);
                }
            }
            // A row is named by its whole path — the rows it sits under, then its own
            // position — so the guard is read there rather than at one component of it.
            g => self.rows.retain(|r| {
                let mut path: Vec<Value> = r
                    .row
                    .as_ref()
                    .map(|p| p.as_ref().to_vec())
                    .unwrap_or_default();
                path.push(r.position.value().clone());
                !g.covers_path(&path)
            }),
        }
    }

    /// The newest live row with its absolute position, or `None` when the window
    /// is empty.
    fn newest(&self) -> Option<(&Position, &DriverRow)> {
        self.rows.last().map(|r| (&r.position, r))
    }

    /// Drop the prefix a release covers and report the extent, so a caller whose cursor
    /// advances on the release — the transaction driver's item cursor, moved by the
    /// commit-ack — reads the classification rather than re-deriving it. A driver that
    /// only reclaims uses [`reclaim`](Self::reclaim), which needs no cursor.
    fn acknowledge(&mut self, pred: &Predicate) -> ReleasedExtent {
        let extent = self.release_cursor.advance_from(pred);
        let drop_through = match extent {
            ReleasedExtent::Nothing => return extent,
            ReleasedExtent::All => self.rows.len(),
            // Positions ascend, so the released ones are a prefix of the window.
            ReleasedExtent::Through(ref w) => self.rows.partition_point(|r| r.position <= *w),
        };
        self.rows.drain(..drop_through);
        extent
    }

    /// The positions this window has emitted, each named under the enclosing row that
    /// emitted it.
    ///
    /// One statement per enclosing row the window holds — bounded by the window, which a
    /// release keeps short. The rows run in order, so the statements partition rather than
    /// overlap, and the union is exact.
    /// Every position the drive has emitted, as the prefix through the last one pushed.
    ///
    /// Beneath an enclosing row the positions restart, so the prefix is a path's: every
    /// position under each enclosing row before the last one's, at every level, and the
    /// positions up to the last one under that row itself. Reading the position column
    /// alone would say the same of a row the drive has not reached — over a nest of two,
    /// `(0,0) (0,1) (1,0)` holds positions `0, 1, 0`, and the keys alone claim position
    /// `1` under enclosing row `1` as well.
    fn emitted_prefix(&self) -> Predicate {
        let Some((row, position)) = &self.highest_pushed else {
            return Predicate::False;
        };
        let rows: &[Value] = row.as_ref().map_or(&[], |r| r.as_ref());
        let beneath = |region: Predicate, levels: usize| {
            (0..levels).fold(region, |r, _| Predicate::qualified(r, Predicate::True))
        };
        (0..rows.len())
            .map(|level| {
                let earlier = Predicate::qualified(
                    Predicate::exactly(&rows[..level]),
                    Predicate::below(rows[level].clone()),
                );
                beneath(earlier, rows.len() - level)
            })
            .chain(std::iter::once(Predicate::qualified(
                Predicate::exactly(rows),
                Predicate::at_or_below(position.value().clone()),
            )))
            .reduce(|a, b| a.union(&b))
            .unwrap_or(Predicate::False)
    }

    /// The window as the body's input tile, terminal once `done`, with the rows the drive
    /// knows are complete — one predicate per row level above the positions, outermost
    /// first, and none for a body whose rows are its positions.
    ///
    /// [`reclaim`](Self::reclaim) has already dropped what a release named, so every
    /// retained row is live: a re-pull within a round re-emits only what the body has not
    /// merged, and an already-released position cannot come back to duplicate a domain
    /// position in the body's `Memo`.
    fn render(&self, done: bool, complete_rows: &[Predicate]) -> Tile {
        // Column `i` is read key `i`'s snapshot, and the item's is the rows' own slices
        // run together. Same index that names the field, so the layout stays the tiling's.
        // Each row's item is a collection stated over its own paths, taken from the source
        // one position at a time, so its statements are qualified by that position's path as
        // the column stacks them ([`Predicate::beneath`]).
        let items = column_of_rows(
            self.rows.iter().map(|r| {
                let path = r.path();
                let mut item = r.item.clone();
                item.map_level_predicates(&mut |depth, pred| pred.beneath(&path, depth));
                item
            }),
            &self.item,
        );
        // The rows this window holds, by path: what a column of values built without its
        // keys ([`stored_value_tile`]) can be stating anything about.
        let held_rows = self
            .rows
            .iter()
            .map(|r| Predicate::exactly(&r.path()))
            .fold(Predicate::False, |all, one| all.union(&one));
        let fields = body_input_fields(&self.read_extents, items, |i, ext| {
            // A snapshot value comes from the store, which holds one value per key per
            // tick, so it is opened into the level the body reads it as. The column states
            // its values whole without knowing which rows it stands under, so it is qualified
            // by the rows it does.
            let mut column = stored_value_tile(
                self.rows.iter().map(|r| r.snapshot[i].clone()).collect(),
                ext,
            );
            column.map_level_predicates(&mut |depth, pred| pred.qualified_by(&held_rows, depth));
            column
        });
        let slots = Tile::Record(fields);
        let codomain = match &self.nested {
            None => slots,
            Some(n) => Tile::Record(HashMap::from([
                (
                    tuple_field(0),
                    column_of_rows(
                        self.rows.iter().map(|r| {
                            let mut enclosing = r
                                .enclosing
                                .clone()
                                .expect("a nested row carries its enclosing parameter");
                            let path = r.path();
                            enclosing.map_level_predicates(&mut |depth, pred| {
                                pred.beneath(&path, depth)
                            });
                            enclosing
                        }),
                        &Tiling::from_extent(&n.param),
                    ),
                ),
                (tuple_field(1), slots),
            ])),
        };
        let positions: Vec<Value> = self
            .rows
            .iter()
            .map(|r| r.position.value().clone())
            .collect();
        let domain = ColumnValue::from_values(positions, &self.domain);
        // A row is final once it is emitted: it was built from one `(item, frontier)` pair,
        // and a retry at a moved frontier is a fresh position. `push` asserts that by
        // refusing a position at or below the highest already pushed in its row, against a
        // `highest_pushed` that survives compaction, so the check spans pulls. Reporting the
        // emitted positions rather than `False` lets a fold over a field's own collection
        // settle per row. Waiting for the whole drive to finish would never end, since the
        // drive waits on the decision that fold feeds.
        //
        // The statement is the prefix through the last position pushed, not the positions
        // the window still holds: a release reclaims rows, and a completeness statement
        // read off what remains would take back what it had said. The drive is
        // sequential, so everything up to the last pushed path has been emitted.
        let complete_positions = if done {
            Predicate::True
        } else {
            self.emitted_prefix()
        };
        let Some(nested) = &self.nested else {
            return Tile::data_function(
                domain,
                Box::new(codomain),
                complete_positions,
                BitSet::new(),
            );
        };
        // One run per level above the positions, contiguous because the drive is
        // sequential — order-dependent logic is what these carriers exist for, so there is
        // nothing to reorder. A level's key begins a new run wherever the path down to it
        // differs from the previous row's, so a nest of any depth is one walk.
        let depth = nested.rows.len();
        let paths: Vec<&Path> = self
            .rows
            .iter()
            .map(|r| {
                r.row
                    .as_ref()
                    .expect("a nested row names the rows it sits under")
            })
            .collect();
        let mut keys: Vec<Vec<Value>> = vec![Vec::new(); depth];
        // `starts[d]` indexes `keys[d]`, one entry per key of the level above it; the top
        // level stands at the one row every tile has.
        let mut starts: Vec<Vec<usize>> = vec![Vec::new(); depth];
        starts[0].push(0);
        let mut position_starts: Vec<usize> = Vec::new();
        let mut prev: Option<&Path> = None;
        for (i, path) in paths.iter().enumerate() {
            for d in 0..depth {
                if prev.is_some_and(|q| q[..=d] == path[..=d]) {
                    continue;
                }
                match starts.get_mut(d + 1) {
                    Some(below) => below.push(keys[d + 1].len()),
                    None => position_starts.push(i),
                }
                keys[d].push(path[d].clone());
            }
            prev = Some(path);
        }
        // Which rows are complete is the drive's to say, from its source, at every level
        // it renders. Reading it off the window instead ("every row but the last") never
        // finishes the row being run, which is the one the enclosing body is waiting on —
        // and a standing level's last row is the one the loop around it waits for, so a
        // window-derived answer deadlocks the nest rather than merely lagging it.
        // A drive that is `done` says every level is complete, so it owes no per-level
        // statement — which is how the over-and-released end state renders without one.
        debug_assert!(
            done || complete_rows.len() == depth,
            "the drive states completion at each of the {depth} row levels it renders, got \
             {}",
            complete_rows.len()
        );
        let mut tile = Tile::grouped(
            ColumnValue::UInts(position_starts),
            domain,
            Box::new(codomain),
            complete_positions,
            BitSet::new(),
        );
        for d in (0..depth).rev() {
            let level_complete = if done {
                Predicate::True
            } else {
                complete_rows[d].clone()
            };
            tile = Tile::grouped(
                ColumnValue::UInts(std::mem::take(&mut starts[d])),
                ColumnValue::from_values(std::mem::take(&mut keys[d]), &nested.rows[d]),
                Box::new(tile),
                level_complete,
                BitSet::new(),
            );
        }
        tile
    }
}

/// The inputs every driver subscribes, wired the one way a driver's inputs are
/// wired.
///
/// The **source** forwards its arrivals to the driver's consumer: an async loop
/// source or a live request stream delivers over scheduler notifications, and
/// each arrival has to wake the cycle so the new positions get driven. The
/// **store** does not — it is the cyclic edge, and forwarding it would loop.
struct DriverInputs {
    consumer: SharedConsumer,
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
}

fn subscribe_driver_inputs(
    store_op: &mut dyn TileOperator,
    source_op: &mut dyn TileOperator,
    consumer: Box<dyn Consumer>,
    scheduler: &mut Scheduler,
) -> DriverInputs {
    let consumer = shared_consumer(consumer);
    let source_producer = {
        let g = source_op.tiling().universal_guard();
        source_op.subscribe(
            g,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        )
    };
    // The store's progress changes what the drive renders — the next position it may
    // emit, and which rows it calls complete — so the store's wakes reach the drive's
    // consumer like the source's arrivals do.
    let store_producer = {
        let g = store_op.tiling().universal_guard();
        store_op.subscribe(
            g,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        )
    };
    DriverInputs {
        consumer,
        store_producer,
        source_producer,
    }
}

/// What a **nested** drive carries and a top-level one does not.
///
/// Two facts, and nothing else: a nested body takes the enclosing parameter beside its
/// slots, and a nested accumulator restarts at each enclosing row. Everything else about
/// the drive is the same operation at a deeper path.
pub struct NestedDrive<T> {
    /// The enclosing rows and parameter the body input carries.
    pub body: NestedBody,
    /// `Fun((outer, inner), (ᴘ, Pos))` — each position's enclosing parameter, which the
    /// body reads and which the reseeds are compiled over.
    pub pairs: T,
    /// Per read key, `Fun((outer, inner), V)` — where that accumulator restarts at an
    /// enclosing row boundary.
    pub reseeds: Vec<T>,
}

/// A nested drive's inputs for one pull, keyed by the paths they answer at.
struct NestedAt {
    /// Each position's enclosing parameter, which the body takes beside its slots.
    pairs: HashMap<Path, Tile>,
    /// Per read key, where that accumulator restarts at an enclosing row boundary.
    reseeds: Vec<HashMap<Path, Value>>,
}

/// The induction body's input, produced from the store read back through the
/// cycle: `DataFunction(Pos → {_0: prev_{k₀}, …, _{r-1}: prev_{k_{r-1}}, _r: item})` — the
/// flat `(prev…, item)` tuple the body's `let kᵢ = p.i … let item = p.r` shape expects,
/// wrapped in the enclosing parameter where the body takes one.
///
/// The driver owns **no** part of the recurrence. The store's decided frontier
/// says which position to iterate next: [`CommitEngine::step`] advances the
/// watermark unconditionally (a carry decides its position without appending a
/// change), and the changelog is keyed by the positions themselves, so a frontier
/// of `w` means every position up to `w` is decided and the next delivered one may
/// go. The previous accumulator is that key's value *at* the frontier
/// ([`store_value_at`], one fold per read key), or the store's seed before the
/// first position. Folding at the frontier rather than taking the key's latest
/// write ([`store_current`]) is the honest read even though a contiguously driven
/// store makes the two agree: the position being fed *is* the frontier, so "as of
/// the position" is what the recurrence means. The emitted row is therefore a pure
/// function of the store tile and the source tile, with nothing cached that could
/// drift.
///
/// This is the [`InductionStore`]'s cycle partner: store → body → driver →
/// `FanOut::new_cyclic(store)`. Emitting only the frontier's position is what
/// makes the cycle well-founded — the body is never asked for a position whose
/// predecessor is undecided.
///
/// **A nested drive is this one at a deeper path.** Everything it indexes — the source's
/// items, the store's frontier, the window's rows, the region it has consumed — is named
/// by the path that reaches it, and a drive with no rows above it has paths of one
/// component. Its two additions ride [`NestedDrive`]:
///
/// - **It reseeds at each enclosing row.** A nested accumulator restarts where the
///   enclosing one had got to — `h(p, 0) = body(seed(p), item(p, 0))`, carrying within a
///   row as usual. That reads like a store that resets, and it is not one: the driver is
///   what feeds the body its snapshot, so at an enclosing boundary it takes that snapshot
///   from `reseeds` instead of from the store, and the store carries exactly as it always
///   did. A boundary is a position whose enclosing components differ from the last one
///   emitted, which is the whole test — and at depth zero that is the first position,
///   where the store already holds its seed and the two arms read the same value.
/// - **It passes the enclosing parameter through.** The body takes `((ᴘ, Pos), slots)`
///   where a top-level one takes `slots`, because parameter elimination gave it that and
///   rewriting it would leave each inner level's own type stale. `pairs` carries it.
///
/// The reseed being invisible in the base case is why it is worth stating: over
/// `for x in [1,2,3]: for y in [1,2]: total += x*y` each row's seed *equals* the previous
/// row's final, since the enclosing writer writes back exactly that. A loop that writes
/// between the two is where they part.
pub struct InductionDriver {
    base: OperatorBase,
    /// The store read back through the cyclic `FanOut`.
    store_op: Box<dyn TileOperator>,
    /// The iteration source — the items of each row's extent, curried one level per row
    /// above the positions.
    source_op: Box<dyn TileOperator>,
    /// `None` for a drive whose body takes the position alone.
    nested: Option<NestedDrive<Box<dyn TileOperator>>>,
    /// Accumulator keys the body reads, in body-parameter order.
    read_keys: Vec<Value>,
    read_extents: Vec<Extent>,
    /// The item slot's tiling, taken from the source ([`source_item_tiling`]).
    item: Tiling,
    /// The positions within one row, which is the body input's domain.
    positions: Extent,
    /// The last position a predecessor driver emitted, or `None` for one starting
    /// with its source. Both of the producer's cursors are seeded from it, in
    /// [`subscribe`](TileOperator::subscribe). Only a drive with no rows above it resumes,
    /// its predecessor being a drive of the same loop rather than of the one around it.
    resumed_after: Option<Position>,
}

impl InductionDriver {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        store_op: Box<dyn TileOperator>,
        source_op: Box<dyn TileOperator>,
        nested: Option<NestedDrive<Box<dyn TileOperator>>>,
        read_keys: Vec<Value>,
        read_extents: Vec<Extent>,
        item_extent: Extent,
        positions: Extent,
        resumed_after: Option<Position>,
    ) -> Self {
        assert_eq!(
            read_keys.len(),
            read_extents.len(),
            "each read key carries its own value extent"
        );
        assert!(
            nested
                .as_ref()
                .is_none_or(|n| n.reseeds.len() == read_keys.len()),
            "each accumulator says where it restarts at an enclosing boundary"
        );
        assert!(
            resumed_after.is_none() || nested.is_none(),
            "a drive with rows above it does not resume: its predecessor is the drive of \
             the loop around it, which resumes on its behalf"
        );
        let body = nested.as_ref().map(|n| &n.body);
        // The drive walks the rows above its positions and the positions themselves; the
        // item is what the source holds under all of those.
        let item = source_item_tiling(source_op.tiling(), body.map_or(0, |b| b.rows.len()) + 1);
        assert_eq!(
            item.extent(),
            item_extent,
            "the source delivers the items the drive was built for"
        );
        Self {
            base: OperatorBase::new(body_input_tiling(
                &positions,
                body,
                &read_extents,
                item.clone(),
            )),
            store_op,
            // **No [`Memo`] over the source.** This drive's release to it is its progress
            // record — `reclaim_consumed` reclaims the prefix it has emitted, and
            // [`FanOut::released_position`] reads that back to place a replacement drive
            // across a reload. A `Memo` releases what it has *cached* rather than what its
            // consumer has finished with, so one here reports the whole source consumed on
            // the first pull and the replacement starts past the end.
            source_op,
            nested,
            read_keys,
            read_extents,
            item,
            positions,
            resumed_after,
        }
    }

    /// A nested drive's own inputs, with the enclosing rows read off `pair_domain`.
    ///
    /// `standing` are the levels the carrier sits under and leaves standing; `pair_domain`
    /// is the `(enclosing, inner)` domain the writer sequences its positions in, whose
    /// enclosing component is the carrier's own row level.
    pub fn nested_parts(
        pairs_op: Box<dyn TileOperator>,
        reseed_ops: Vec<Box<dyn TileOperator>>,
        standing: Vec<Extent>,
        enclosing_extent: Extent,
        pair_domain: &Extent,
    ) -> (NestedDrive<Box<dyn TileOperator>>, Extent) {
        let (rows, inner) = split_pair_domain(pair_domain).unwrap_or_else(|| {
            panic!("a nested carrier sequences its positions as pairs, got {pair_domain}")
        });
        let nested = NestedDrive {
            body: NestedBody {
                rows: [standing.as_slice(), std::slice::from_ref(&rows)].concat(),
                param: enclosing_extent,
            },
            // Cached until they notify: these are read once per position, and the laps of
            // every enclosing level multiply. Unlike the source, nothing reads their
            // release as a position, so a `Memo` costs the drive nothing it owes.
            pairs: Box::new(Memo::new(pairs_op)) as Box<dyn TileOperator>,
            reseeds: reseed_ops
                .into_iter()
                .map(|seed| Box::new(Memo::new(seed)) as Box<dyn TileOperator>)
                .collect(),
        };
        (nested, inner)
    }
}

impl TileOperator for InductionDriver {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
        visit(value("source_op", &*self.source_op));
        if let Some(nested) = &self.nested {
            visit(value("pairs_op", &*nested.pairs));
            for (i, seed) in nested.reseeds.iter().enumerate() {
                visit(value_keyed(format!("seed_{i}"), &**seed));
            }
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let inputs = subscribe_driver_inputs(
            &mut *self.store_op,
            &mut *self.source_op,
            consumer,
            scheduler,
        );
        let consumer = inputs.consumer;
        let nested = self.nested.as_mut().map(|n| {
            let mut sub = |op: &mut Box<dyn TileOperator>| {
                let g = op.tiling().universal_guard();
                op.subscribe(
                    g,
                    forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
                    scheduler,
                )
            };
            NestedDrive {
                body: n.body.clone(),
                pairs: sub(&mut n.pairs),
                reseeds: n.reseeds.iter_mut().map(&mut sub).collect(),
            }
        });
        Box::new(InductionDriverProducer {
            base: ProducerBase::new(InductionDriverProducer::alloc_id(), self.tiling()),
            store_producer: inputs.store_producer,
            source_producer: inputs.source_producer,
            nested,
            consumer,
            wakeups: scheduler.wakeup_queue(),
            read_keys: self.read_keys.clone(),
            window: DriverWindow::new(
                self.positions.clone(),
                self.nested.as_ref().map(|n| n.body.clone()),
                self.read_extents.clone(),
                self.item.clone(),
            ),
            // A resuming driver has already emitted every position up to the one
            // its predecessor reached, whose rows are gone. The item cursor is where
            // that is said: it is what the next position to iterate is taken from,
            // and what the store's frontier is checked against. `None` for a driver
            // starting with its source, which has emitted nothing.
            emitted_through: self.resumed_after.clone().map(one_component),
            // And inherits the release cursor with it. A resuming driver has no
            // interest in the prefix below the position it starts at, which is
            // what this cursor records; leaving it empty would have this driver
            // re-release a prefix its predecessor already released, and would
            // read a position the source re-offers there as an out-of-order
            // arrival.
            source_released_through: self.resumed_after.clone().map(one_component),
            source_fully_released: false,
            source_complete: Vec::new(),
            stated: Vec::new(),
            #[cfg(debug_assertions)]
            reseeded: None,
        })
    }
}

/// A position of a drive with no rows above it, as the path that names it.
fn one_component(position: Position) -> Path {
    Path::from(vec![position.into_value()])
}

struct InductionDriverProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// `None` for a drive whose body takes the position alone.
    nested: Option<NestedDrive<Box<dyn TileProducer>>>,
    /// This driver's consumer, re-armed through [`wakeups`](Self::wakeups) while
    /// an iteration position remains to feed. The cycle is its own trigger: a
    /// position only becomes emittable once the store has decided its
    /// predecessor, and nothing outside the cycle announces that.
    consumer: SharedConsumer,
    /// The scheduler's deferred-wakeup queue — where a pull with pending work
    /// requests its own re-pull instead of looping inside `get`.
    wakeups: WakeupQueue,
    read_keys: Vec<Value>,
    /// The emitted rows and the body-input tile they render. This is the
    /// producer's own output, not recurrence state: a row is never read back to
    /// compute a later one.
    window: DriverWindow,
    /// The path of the highest position emitted, or `None` before the first. This is the
    /// item cursor, and it is not recoverable from the window, which a release compacts
    /// emitted rows away from.
    emitted_through: Option<Path>,
    /// Highest source path released back upstream. The driver never re-reads
    /// a position it has emitted, so that prefix is reclaimable; a co-iterated
    /// reader keeps its own positions live through the source's cross-producer
    /// release intersection.
    source_released_through: Option<Path>,
    /// Whether the whole source has been released (`True`) after the loop
    /// finished — the finite loop's `get_released_predicate() == True`
    /// end-state; issued once.
    source_fully_released: bool,
    /// What the source has called complete at each row level, accumulated across pulls.
    /// A complete path stays complete, but the source may stop saying so once this driver
    /// has released it, and the store can fold that row's last position after the
    /// release: the row's completeness is read here, not off the source's latest tile.
    source_complete: Vec<Predicate>,
    /// What the last pull stated complete: each row level, then the positions. A pull
    /// that states more has changed its output, and wakes its consumer as an emission
    /// does.
    stated: Vec<Predicate>,
    /// The last row this drive reseeded and the snapshot it reseeded it at, until the
    /// store's frontier enters that row, for the check that the reseed is the store's seed
    /// there.
    #[cfg(debug_assertions)]
    reseeded: Option<(Path, Vec<Value>)>,
}

impl InductionDriverProducer {
    /// The window rendered, less every region released so far.
    ///
    /// [`DriverWindow::reclaim`] drops the rows a release covers whole, which is all a
    /// release naming positions asks. A release can also name part of a row's value — the
    /// items of a nest whose elements are collections are collections, and a `Memo` in
    /// front of this driver releases whatever it has cached — and a row it only partly
    /// covers stays in the window, so its released part is stripped here.
    fn render(&self, done: bool, complete_rows: &[Predicate]) -> Tile {
        let mut tile = self.window.render(done, complete_rows);
        tile.remove_guarded(self.base().obsolete_guard.clone());
        tile
    }

    /// Reclaim the prefix this drive has consumed, in the store's changelog and in the
    /// source, and close the source once the drive is over.
    ///
    /// Both releases name a **path prefix** ([`domain_prefix`]) — the rows before the one
    /// being run entirely, and within that row everything up to the frontier — which is
    /// what a sequential drive has consumed at any depth. A drive with no rows above it
    /// has paths of one component, where that prefix is the watermark it always was.
    fn reclaim_consumed(&mut self, frontier: Option<&Path>, done: bool) {
        // The drive only ever folds at the *frontier*, and the store's GC preserves the
        // carry source a live position reads inside a released prefix — so releasing
        // through the frontier never strands the fold, and without it the store's
        // `FanOut`-intersected release watermark could never advance past this cycle
        // branch and the changelog would grow with the loop.
        if let Some(frontier) = frontier {
            self.store_producer
                .release(domain_prefix(frontier.to_vec()));
        }
        // The source prefix this drive has consumed. It only ever reads the position it is
        // about to emit and never re-reads an earlier one.
        if let Some(through) = self.emitted_through.clone()
            && !self
                .source_released_through
                .as_ref()
                .is_some_and(|r| *r >= through)
        {
            self.source_producer
                .release(domain_prefix(through.to_vec()));
            // The enclosing parameter and the reseeds are read at positions past the cursor
            // only, so their consumed prefix goes too. They are keyed by pairs, and a memo
            // over each answers every pull from its whole cache, so without this each pull
            // decodes the run so far.
            if let Some(nested) = self.nested.as_mut() {
                let guard = domain_prefix(pair_keyed(&through));
                for input in std::iter::once(&mut nested.pairs).chain(&mut nested.reseeds) {
                    input.release(guard.clone());
                }
            }
            self.source_released_through = Some(through);
        }
        if done && !self.source_fully_released {
            self.source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
            if let Some(nested) = self.nested.as_mut() {
                for input in std::iter::once(&mut nested.pairs).chain(&mut nested.reseeds) {
                    input.release(input.tiling().universal_guard());
                }
            }
            self.source_fully_released = true;
            // The close is itself news, and it is the one transition the re-arm rule does
            // not cover. A consumer that pulled earlier in this same pass has already
            // consumed its notification, and a cache-holding one
            // (`tile_operators::Notified`) answers from that pre-final cache until
            // something tells it otherwise. `source_fully_released` makes this fire once.
            self.wakeups.request(self.consumer.clone());
        }
    }
}

impl TileProducer for InductionDriverProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // The driver is over once it has universally released the source: pulling it
        // again would break that release's promise, and every position has already
        // been emitted, so the live window is the whole remaining answer. The driver
        // owns the source, so the obligation is its to keep.
        if self.source_fully_released {
            return self.render(true, &[]);
        }
        let src = self
            .source_producer
            .get(self.source_producer.tiling().universal_guard());
        let source_complete = src.is_terminal();
        // Everything the drive indexes is keyed by the **path** that reaches it: the
        // curried source names it as levels already, and the pair-keyed streams have their
        // pair exploded to match. Two spellings of one position would match neither.
        //
        // How many levels stand above the carrier's own rows is the carrier's own
        // statement, not a count of the source's levels: an item that is itself a
        // collection — a nest whose elements are collections — carries its own levels
        // beneath the positions, and counting those names a path one level too deep.
        let row_levels = self.window.row_levels();
        let by_path: HashMap<Path, Tile> = decode_source_paths(&src, row_levels + 1)
            .into_iter()
            .collect();
        // Invariant: a source delivers its positions in **ascending order** — a position
        // at or below one already emitted never arrives later. The driver takes the
        // smallest delivered path above its cursor and never looks back, so a late arrival
        // below the cursor would be dropped in silence. A path at or below the cursor is
        // still legitimate *here*: the release is what removes the consumed prefix, and
        // the source is free to honour it a pull late. The domain need not be contiguous —
        // a restricted source (`for l in [x for x in xs if p(x)]`) delivers a subset of
        // its extent's positions and the recurrence runs over exactly those.
        debug_assert!(
            by_path.keys().all(|p| {
                self.emitted_through.as_ref().is_none_or(|e| p > e)
                    || self
                        .source_released_through
                        .as_ref()
                        .is_some_and(|r| p <= r)
            }),
            "induction source delivered a position at or below the emitted cursor {:?} \
             that was never released: {:?}",
            self.emitted_through,
            {
                let mut ks: Vec<Path> = by_path.keys().cloned().collect();
                ks.sort();
                ks
            }
        );
        // The enclosing parameter and the reseeds, keyed by the same paths. A reseed
        // restarts an accumulator, so it stands beside the store reads in the same
        // snapshot column and is read the way the store holds one: as a value per key.
        let nested_at = self.nested.as_mut().map(|n| {
            let read = |p: &mut Box<dyn TileProducer>| {
                let tile = p.get(p.tiling().universal_guard());
                decode_pairs_pathed(&tile, row_levels - 1)
            };
            NestedAt {
                pairs: read(&mut n.pairs).into_iter().collect(),
                reseeds: n
                    .reseeds
                    .iter_mut()
                    .map(|p| {
                        read(p)
                            .into_iter()
                            .map(|(path, seed)| {
                                // The drive reaches a row only once the store has opened it,
                                // which it does on the row's whole seed.
                                debug_assert!(
                                    is_whole_value(&seed),
                                    "a reseed is a whole value: the reseed at {path:?} holds \
                                     a collection still arriving, got {seed:?}"
                                );
                                (path, materialized_row(seed))
                            })
                            .collect()
                    })
                    .collect(),
            }
        });
        let store = self
            .store_producer
            .get(self.store_producer.tiling().universal_guard());
        // A carrier is a collection of stores; the drive is sequential, so the one it is
        // adding to is the last, and at depth zero it is the only one. Its frontier is the
        // whole carrier's watermark — positions are sequenced across rows even though the
        // state is not. The drive's cursor is a path, so the frontier it compares against
        // must be one too: a row's own watermark says nothing about which row it belongs
        // to.
        let frontier = frontier_path(&store);
        let store = current_row_store(&store);
        // The store opens a row at its seed stream's value and the drive restarts the row's
        // accumulator at its reseed stream's, which is one stream behind a `FanOut`. The two
        // are visible together once the store's frontier is inside the row the drive
        // reseeded.
        #[cfg(debug_assertions)]
        if let Some((row, reseed)) = self.reseeded.take() {
            match frontier.as_ref().and_then(Path::split_position) {
                Some((rows, _)) if rows == &row[..] => {
                    let seeds: Vec<Option<Value>> = self
                        .read_keys
                        .iter()
                        .map(|k| store_seed_value(&store, k))
                        .collect();
                    debug_assert!(
                        seeds
                            .iter()
                            .zip(&reseed)
                            .all(|(s, r)| s.as_ref() == Some(r)),
                        "a drive's reseed at a row is the store's seed for that row: row \
                         {row:?} reseeded at {reseed:?}, the store seeded it at {seeds:?}"
                    );
                }
                Some((rows, _)) if Path::from(rows.to_vec()) > row => {}
                _ => self.reseeded = Some((row, reseed)),
            }
        }

        // The rows of one level the source will gain no more items beneath — one of the two
        // halves of a row being answerable as a whole, `folded` below being the other. Read
        // at the level itself: a standing level's rows are not the level beneath's, and
        // each level's completion is its own statement.
        for level in 0..self.source_producer.tiling().levels() {
            if let Tile::DataFunction {
                domain_predicate, ..
            } = src.values_at(CurryLevel::new(level))
            {
                match self.source_complete.get_mut(level) {
                    Some(known) => *known = known.union(domain_predicate),
                    None => self.source_complete.push(domain_predicate.clone()),
                }
            }
        }
        let known_complete = &self.source_complete;
        let source_complete_at = |level: CurryLevel| {
            known_complete
                .get(level.index())
                .cloned()
                .unwrap_or(Predicate::False)
        };
        let next_delivered = |after: Option<&Path>| -> Option<Path> {
            by_path
                .keys()
                .filter(|p| after.is_none_or(|e| *p > e))
                .min()
                .cloned()
        };
        debug_assert!(
            frontier.as_ref() <= self.emitted_through.as_ref(),
            "the store decided through {frontier:?} but the driver has only emitted \
             through {:?} — a decision cannot precede the input it decides",
            self.emitted_through
        );
        let mut emitted_now = false;
        if frontier == self.emitted_through
            && let Some(pos) = next_delivered(self.emitted_through.as_ref())
        {
            // **The reseed.** A position whose enclosing components differ from the last
            // one emitted opens a new row, so the accumulator restarts where that row's
            // reseed says rather than carrying from the row before. Everything else
            // carries, which is the store's own fold: the previous accumulator is that
            // key's value as of the frontier, the position the predecessor iteration's
            // decision occupies, or the store's seed before the first. A drive with no
            // rows above it has no reseed stream and reads the carry at every position,
            // its store opening at its own seed — the cycle hands back an unopened store
            // until then, and that tile carries no value, so this emits nothing rather
            // than feeding the body one it does not have.
            let boundary = self.emitted_through.as_ref().is_none_or(|e| {
                e.split_position().map(|(rows, _)| rows)
                    != pos.split_position().map(|(rows, _)| rows)
            });
            // Leaving a row is final: the drive never looks back, so a position the row
            // gains afterwards would be dropped. So the next row starts only once the source
            // calls this one complete, at its own level or any above it.
            let left_open = boundary
                && self
                    .emitted_through
                    .as_ref()
                    .and_then(|e| e.split_position())
                    .is_some_and(|(rows, _)| {
                        !(0..rows.len()).any(|level| {
                            source_complete_at(CurryLevel::new(level))
                                .contains_path(&rows[..=level])
                        })
                    });
            let snapshot: Option<Vec<Value>> = self
                .read_keys
                .iter()
                .enumerate()
                .map(|(i, k)| match nested_at.as_ref().filter(|_| boundary) {
                    Some(n) => n.reseeds[i].get(&pos).cloned(),
                    None => store_value_now(&store, k),
                })
                .collect();
            debug_assert!(
                snapshot.is_some() || frontier.is_none() || boundary,
                "a store that has decided a position carries every accumulator's value, \
                 so a carrying read of it resolves"
            );
            // A nested body takes its enclosing parameter at every position, so a position
            // whose pair has not arrived waits with the ones whose reseed has not.
            let enclosing = match &nested_at {
                None => Some(None),
                Some(n) => n.pairs.get(&pos).cloned().map(Some),
            };
            if !left_open
                && let (Some(snapshot), Some(item), Some(enclosing)) =
                    (snapshot, by_path.get(&pos), enclosing)
            {
                let (rows, at) = pos
                    .split_position()
                    .unwrap_or_else(|| unreachable!("a delivered path names a position"));
                let inner = Position::new(at.clone());
                let row = self.nested.is_some().then(|| Path::from(rows.to_vec()));
                #[cfg(debug_assertions)]
                if boundary && let Some(row) = &row {
                    self.reseeded = Some((row.clone(), snapshot.clone()));
                }
                self.window
                    .push(snapshot, item.clone(), enclosing, row, inner.clone(), inner);
                self.emitted_through = Some(pos);
                emitted_now = true;
            }
        }

        // A row's accumulator is final once the row has stopped gaining items **and** the
        // store has folded every one of them. Those come apart: a literal source is
        // complete over every row on the pull that delivers it, while the fold reaches one
        // position per pull, so publishing the source's predicate alone answers rows whose
        // positions are still being decided — and the reader that takes a row's final value
        // stops there, with the fold part-done.
        //
        // The drive is sequential, so the store's frontier splits every row level: at each
        // one, the rows before the one the frontier names are folded, and that row itself
        // once every position the source put under it is decided. Each level answers for
        // its own rows. A standing level left to say only "everything before the row still
        // running" never finishes its last row, and the loop around it is waiting on
        // exactly that row, so the nest stalls rather than lagging. Reading the frontier
        // here is not circular — `decided` advances from the body's decisions, which never
        // consult this predicate.
        //
        // Each level's keys are named **under the enclosing path the frontier is inside**.
        // A key value repeats once per enclosing row, so naming the keys alone would say
        // the same of a row the drive has not reached; the rows of this level under an
        // earlier enclosing path are answered by the level above, which has called that
        // path whole. A drive with no rows above it states none of this: its positions are
        // its own level, and the window renders their completion directly.
        let complete_rows: Vec<Predicate> = (0..row_levels)
            .map(|level| {
                let folded = match &frontier {
                    // Nothing decided, because there is nothing to decide: the source put
                    // no position under any row, and a row with no positions is folded as
                    // soon as it arrives. Left as `False` the nest never finishes a row,
                    // so the loop around it waits on one forever.
                    None if by_path.is_empty() => Predicate::True,
                    None => Predicate::False,
                    Some(f) => {
                        let (rows, _) = f
                            .split_position()
                            .unwrap_or_else(|| unreachable!("a store's frontier names a position"));
                        // What the source still holds, and what this drive has emitted: an
                        // emitted position is released back to the source, so the source no
                        // longer shows it while the store may not yet have decided it.
                        let under = by_path
                            .keys()
                            .chain(self.emitted_through.iter())
                            .filter(|p| {
                                p.split_position()
                                    .is_some_and(|(r, _)| r[..=level] == rows[..=level])
                            });
                        let keys = if under.clone().all(|p| p <= f) {
                            Predicate::at_or_below(rows[level].clone())
                        } else {
                            Predicate::below(rows[level].clone())
                        };
                        Predicate::qualified(Predicate::exactly(&rows[..level]), keys)
                    }
                };
                source_complete_at(CurryLevel::new(level)).intersect(&folded)
            })
            .collect();

        // Every position of a complete source has been emitted: the body input is final,
        // and that terminality propagates through the body's decision stream to close the
        // carrier's frontier. Positions arrive in ascending order, so "no delivered path
        // above the cursor" means "there is no next" — the question a restricted source
        // needs asked, since the position one past the cursor may simply not be in its
        // domain.
        //
        // Not "and the store has decided them all", though the store owes a decision on
        // whatever was emitted this pull. The store is this drive's caller — it pulls the
        // body, which pulls this — so a position emitted here is decided before that same
        // store pull renders, and waiting for the frontier to show it would cost a lap per
        // loop. The store asserts the other side of that (a terminal decision stream it
        // has not fully consumed), which is where a body that failed to decide is caught.
        //
        // The drive wakes its consumer when this pull changed its output — a row emitted, or
        // a level stated complete further — and at no other time. What it waits on
        // wakes it: the store wakes its readers, this drive among them, when it
        // decides, and the source when it delivers. A drive that woke itself while waiting
        // would keep a stuck nest looking busy.
        let pending = next_delivered(self.emitted_through.as_ref());
        let done = source_complete && pending.is_none();
        let stated: Vec<Predicate> = match done {
            true => vec![Predicate::True; complete_rows.len() + 1],
            false => complete_rows
                .iter()
                .cloned()
                .chain([self.window.emitted_prefix()])
                .collect(),
        };
        let states_more = stated.len() != self.stated.len()
            || self
                .stated
                .iter()
                .zip(&stated)
                .any(|(was, now)| !was.subsumes(now));
        if emitted_now || states_more {
            self.wakeups.request(self.consumer.clone());
        }
        self.stated = stated;
        self.reclaim_consumed(frontier.as_ref(), done);
        self.render(done, &complete_rows)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Retention only: this driver's cursor is the store's frontier, so a
        // release says nothing about progress — it only reclaims rows the body
        // has consumed and the store has decided.
        self.window.reclaim(&obsolete_guard);
    }
}

/// The transaction body's input, produced from the store read back through the
/// cycle: `DataFunction(UInt → {_0: snap_{k₀}, …, _{r-1}: snap_{k_{r-1}}, _r:
/// item})` — the [`InductionDriver`]'s sibling, differing only in how the item
/// advances.
///
/// An induction position is decided by the store's frontier; a transaction's is
/// not, because a commit is what *moves* the frontier. So the item cursor
/// advances on the **commit-ack**, delivered as a release — but a release from
/// the body alone would be wrong, because a body releases a row the moment it
/// consumes it, long before the attempt commits. The driver therefore sits behind
/// a `FanOut` with two branches, the body and [`TransactWriter`], and reads the
/// **intersection**: the body has consumed the row *and* the writer has finished
/// the attempt. Without that the driver would advance past an item still in
/// flight, or re-propose one that already committed — an attempt is emitted once
/// per `(item, frontier)`, and a commit is what changes the frontier.
///
/// A row is a pure function of `(item, frontier)`: each read key's value folds
/// out of the store at its decided frontier, so a retry at a new frontier is a
/// fresh position and a re-pull at an unchanged one emits nothing.
///
/// Both halves of that intersection are load-bearing for the window bound
/// ([`MAX_LIVE_ATTEMPTS`]), including the body's. A compiled body fans this input
/// through a `Memo`, which releases each row as it consumes it; a body chain that
/// released only when its own output was released would leave the intersection
/// standing at the writer's ack, and a superseded row could not be reclaimed
/// until its item finished — the window would grow one row per retry with the
/// writer's supersession release still in place. Measured both ways by
/// `a_contended_item_keeps_the_drive_window_flat`.
pub struct TransactDriver {
    base: OperatorBase,
    /// The first source position this drive attempts.
    ///
    /// `0` for a drive that starts with its source, whatever that source has
    /// already delivered: this drive finds its next item by scanning up from its
    /// cursor rather than being based at a position, so a position the source no
    /// longer offers costs it a comparison where an induction drive's window
    /// would stall. A drive continuing a retired one is told where its
    /// predecessor had reached, so it commits no position twice.
    resumed_after: Option<Position>,
    /// The store read back through the cyclic `FanOut`.
    store_op: Box<dyn TileOperator>,
    /// The transaction source — one item per transaction to attempt.
    source_op: Box<dyn TileOperator>,
    /// Runtime keys the body reads a snapshot of, in body-parameter order.
    read_keys: Vec<Value>,
    read_extents: Vec<Extent>,
    /// The item slot's tiling, taken from the source ([`source_item_tiling`]).
    item: Tiling,
}

impl TransactDriver {
    pub fn new(
        store_op: Box<dyn TileOperator>,
        source_op: Box<dyn TileOperator>,
        read_keys: Vec<Value>,
        read_extents: Vec<Extent>,
        item_extent: Extent,
        resumed_after: Option<Position>,
    ) -> Self {
        debug_assert_eq!(
            read_keys.len(),
            read_extents.len(),
            "each read key carries its own value extent"
        );
        let item = source_item_tiling(source_op.tiling(), 1);
        assert_eq!(
            item.extent(),
            item_extent,
            "the source delivers the items the drive was built for"
        );
        Self {
            base: OperatorBase::new(body_input_tiling(
                &Extent::Base(BaseType::UInt),
                None,
                &read_extents,
                item.clone(),
            )),
            store_op,
            source_op,
            read_keys,
            read_extents,
            item,
            resumed_after,
        }
    }
}

impl TileOperator for TransactDriver {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
        visit(value("source_op", &*self.source_op));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let inputs = subscribe_driver_inputs(
            &mut *self.store_op,
            &mut *self.source_op,
            consumer,
            scheduler,
        );
        Box::new(TransactDriverProducer {
            base: ProducerBase::new(TransactDriverProducer::alloc_id(), self.tiling()),
            store_producer: inputs.store_producer,
            source_producer: inputs.source_producer,
            consumer: inputs.consumer,
            wakeups: scheduler.wakeup_queue(),
            read_keys: self.read_keys.clone(),
            // A transaction driver's body-input domain is its own attempt counter, not
            // its source's positions: a retried item takes a fresh attempt position.
            window: DriverWindow::new(
                Extent::Base(BaseType::UInt),
                None,
                self.read_extents.clone(),
                self.item.clone(),
            ),
            current: self.resumed_after.clone(),
            latest_emit: None,
        })
    }
}

struct TransactDriverProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// This driver's consumer, re-armed through [`wakeups`](Self::wakeups) while a
    /// transaction remains to attempt — the one-step-per-pull cycle driver. The
    /// cycle is its own trigger: an attempt becomes emittable when the store's
    /// frontier moves, which nothing outside the cycle announces.
    consumer: SharedConsumer,
    /// The scheduler's deferred-wakeup queue — where a pull with pending work
    /// requests its own re-pull instead of looping inside `get`.
    wakeups: WakeupQueue,
    read_keys: Vec<Value>,
    /// The **absolute source position** of the highest item that has finished, or
    /// `None` before the first. The drive always attempts the lowest position the
    /// source still offers above it.
    ///
    /// Absolute rather than a count of the columns the source currently offers:
    /// a column count names a position in a view, so it means nothing to a drive
    /// that did not emit it, and a replacement drive taking over a running
    /// program would re-attempt every transaction the retired one committed.
    current: Option<Position>,
    /// The emitted rows — the attempts in flight, including superseded retries
    /// not yet reclaimed.
    ///
    /// O(1), not O(retries): the writer releases everything below the position it
    /// decides, so a superseded row is reclaimed on the next release rather than
    /// waiting for the item to finish. The distinction matters because the body
    /// re-renders this whole window each pull, so a window that grew with retries
    /// would make a contended item quadratic.
    window: DriverWindow,
    /// `(item, frontier)` of the latest emit — the retry-suppression key. A row
    /// is a pure function of that pair, so re-emitting at an unchanged pair would
    /// duplicate a domain position against the body's `Memo`.
    latest_emit: Option<(Position, Position)>,
}

/// The most rows this driver's live window may hold: the attempt the writer has
/// decided, plus at most one newer row emitted since it decided.
///
/// This bound *is* the O(1) claim the writer's supersession release exists for,
/// and it holds only because of it. Rows are added at most one per pull and only
/// for `current`; they leave on the release intersection. The writer contributes
/// two releases — everything below the position it decides (supersession) and
/// `≤ attempt` when the item finishes (the ack) — and it is the first that caps
/// the window. Drop it and the window instead holds one row per retry between
/// acks: O(retries) rows retained and, because the body re-renders the whole
/// window each pull, O(retries²) body rows evaluated.
const MAX_LIVE_ATTEMPTS: usize = 2;

impl TransactDriverProducer {
    /// The two standing facts about the live window, checked on both sides of the
    /// only two things that move it: an emit, and the release that advances the
    /// item cursor.
    ///
    /// It is **all one item**: rows are emitted only for the lowest unfinished
    /// source position, and `current` advances past it exactly when a release drops
    /// its rows. That is what lets the writer decide the newest position and treat
    /// every older live one as superseded — if the window ever spanned two items,
    /// that rule would abandon a real attempt.
    ///
    /// And it is **bounded** by [`MAX_LIVE_ATTEMPTS`], which no test asserts
    /// directly because this does: `sustained_contention_conserves_pool` runs a
    /// stuck item through many retries in a debug build, so an unbounded window
    /// trips here rather than passing quietly with the right answer.
    fn debug_assert_window_invariants(&self) {
        debug_assert!(
            self.window
                .rows
                .windows(2)
                .all(|w| w[0].item_position == w[1].item_position),
            "the driver's live window spans more than one item: {:?}",
            self.window
                .rows
                .iter()
                .map(|r| r.item_position.clone())
                .collect::<Vec<_>>(),
        );
        debug_assert!(
            self.window.rows.len() <= MAX_LIVE_ATTEMPTS,
            "the driver's live window holds {} attempts (bound {MAX_LIVE_ATTEMPTS}) — a \
             superseded row is not being reclaimed, so a contended item costs O(retries) \
             rows retained and O(retries²) body rows evaluated",
            self.window.rows.len()
        );
    }
}

impl TileProducer for TransactDriverProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Re-read the source each pull: a live source (an HTTP request stream)
        // grows over time, and positions are absolute, so `get` returns whatever
        // the source still offers under stable append-only positions. The drive
        // does release a prefix — `release_impl` withdraws each item as it
        // finishes — so what is offered shrinks off the front, which is why an
        // item is named by its domain position rather than by a column index.
        let src = self
            .source_producer
            .get(self.source_producer.tiling().universal_guard());
        // The source is *complete* only when its tile is terminal. A batch source
        // (a list) is terminal on the first pull; a live source (an HTTP request
        // stream) never is, so a momentarily drained one must not read as done.
        let source_complete = src.is_terminal();
        // Positioned, so an item is named by where it sits in the source's own
        // domain rather than by where it sits in the columns still on offer. The
        // lowest position at or above the cursor is the next item: the cursor is
        // the attempt in flight until its ack, and the ack both advances it and
        // withdraws the position from the source.
        let items = decode_source_positioned(&src);
        let next_item = items
            .iter()
            .find(|(pos, _)| self.current.as_ref().is_none_or(|c| pos > c));
        let store = self
            .store_producer
            .get(self.store_producer.tiling().universal_guard());
        // The snapshot the attempt is built against: the store's decided
        // frontier. A read key with no value yet (an *append* onto an empty
        // collection store) folds to nothing — the empty-store bootstrap.
        let frontier = store_frontier(&store);
        let olds: Vec<Option<Value>> = self
            .read_keys
            .iter()
            .map(|k| store_current(&store, k).map(|(_, v)| v))
            .collect();

        if let Some((pos, item)) = next_item
            && let Some(frontier) = frontier
            && self.latest_emit.as_ref() != Some(&(pos.clone(), frontier.clone()))
        {
            let (pos, item) = (pos.clone(), item.clone());
            // The body reads snapshot position `i` as `p.i`. A read key with no
            // value yet gets the item as a stand-in of the right extent. Load-
            // bearing assumption: a body that writes an *absent* key is
            // append-shaped, so it ignores the snapshot at that position and the
            // stand-in is never observed. (Even if it were, the writer's read set
            // omits the absent key, so the proposal cannot go stale on it.)
            //
            // A snapshot slot holds what the store holds, which is a value, so the
            // stand-in is read out of the item's row as one.
            let snap_in: Vec<Value> = olds
                .iter()
                .map(|o| o.clone().unwrap_or_else(|| materialized_row(item.clone())))
                .collect();
            // An attempt occupies the next contiguous position: a retried item
            // takes a fresh one, which is why a row's source position and its own
            // position are separate here.
            let attempt = self.window.next_attempt();
            self.window
                .push(snap_in, item, None, None, pos.clone(), attempt);
            self.latest_emit = Some((pos, frontier));
        }
        self.debug_assert_window_invariants();
        // Terminal once every item has been acked and no more can arrive. This is
        // the writer's completeness signal too: it owns no source of its own, so
        // "all transactions attempted" is exactly this tile closing. A live
        // window that is momentarily empty over an incomplete source stays
        // non-terminal — the drained-but-live case.
        let done = source_complete && next_item.is_none();
        // Re-arm while a transaction remains to attempt. It covers every
        // continuation uniformly: an attempt awaiting its commit-ack, a retry
        // waiting for the frontier to move, and the first pull of all — where the
        // cyclic fan's snapshot is still empty, so there is no frontier to build
        // an attempt against yet. A writer that is *drained but live* does not
        // re-arm: a future arrival wakes it through the source, so re-arming
        // would busy-poll an idle server.
        if next_item.is_some() {
            self.wakeups.request(self.consumer.clone());
        }
        // A release naming part of a row rather than the row leaves the row in the window
        // (`release_impl`), so what it names is withheld here.
        let mut tile = self.window.render(done, &[]);
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The commit-ack — but only because this producer sits behind a `FanOut`
        // whose branches are the body and the writer, so what arrives here is
        // their **intersection**. The body releases a row as soon as it has
        // *consumed* it, which is not an ack; the writer releases it when the
        // attempt has *finished* (committed, or denied without proposing). The
        // intersection of the two is the finish, and that is what advances the
        // item cursor. Superseded retries for the same item ride the same prefix
        // and give the same answer, so the rule is idempotent under any order.
        //
        // The window holds rows, so it acts on the rows the release names whole. What the
        // release names of a row's values is withheld from the output (`get_impl`).
        let pred = &obsolete_guard.whole_keys();
        // Only the **newest** live row's release is the item's finish. An older one
        // is a superseded retry, which the writer releases as soon as a newer
        // attempt replaces it — reclaiming that row must not advance the cursor past
        // an item still in flight, which is the same mistake as taking the body's
        // consume-release for an ack. The window is all one item, so the newest row
        // is the last, and superseded rows are exactly the prefix compacted below.
        if let Some((pos, row)) = self.window.newest()
            && pred.contains(pos.value())
        {
            let finished = row.item_position.clone();
            self.current = Some(match self.current.take() {
                Some(c) => c.max(finished.clone()),
                None => finished.clone(),
            });
            // A prefix release, which is sound because rows are emitted for the
            // lowest offered position only: everything at or below the one that
            // just finished has finished too. Releasing it is what makes the
            // source's own release state this drive's progress record, so a
            // replacement drive is offered what this one did not finish and
            // nothing it did — see `src/ccl/design/program-evolution.md`,
            // "Where a producer registering now starts".
            self.source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(finished.into_value()),
                )));
        }
        self.window.acknowledge(pred);
        self.debug_assert_window_invariants();
    }
}

/// The body-input tiling both writers' drivers produce: `UInt → {_0…_{r-1}:
/// read, _r: item}`.
///
/// A read slot is opened the way every other store read is ([`Tiling::from_extent`]), so a
/// collection-valued read reaches the body as a level rather than as a map in a cell — which
/// is what lets the body iterate it. A write goes the other way: a store write is one value
/// per key, so what the body computes materializes where it becomes the decision's payload.
///
/// The item slot is the source's own, [`source_item_tiling`] taking it from there rather
/// than re-deriving it from the item's extent — which would call a record of columns one
/// column of records, and leave the drive converting between the two on every pull.
fn body_input_tiling(
    domain: &Extent,
    nested: Option<&NestedBody>,
    read_extents: &[Extent],
    item: Tiling,
) -> Tiling {
    let slots = Tiling::Record(body_input_fields(read_extents, item, |_, ext| {
        Tiling::from_extent(ext)
    }));
    let per_position = Tiling::data_function(
        domain.clone(),
        wrap_enclosing_tiling(nested.map(|n| &n.param), slots),
    );
    match nested {
        None => per_position,
        // A nested carrier's body runs over a **path** — the enclosing row, then the
        // position within it — and the path is two levels rather than one encoded key.
        // Encoding it as a record position instead is what puts a product domain's
        // predicate on a sequenced one; a level is what the guards are already built for.
        Some(n) => n.rows.iter().rev().fold(per_position, |inner, rows| {
            Tiling::data_function(rows.clone(), inner)
        }),
    }
}

/// What a **nested** writer's body input carries beyond a flat one's.
#[derive(Clone, Debug)]
pub struct NestedBody {
    /// The collection levels above the positions, outermost first.
    ///
    /// The last is the carrier's own enclosing rows; anything before it **stands above** —
    /// levels the carrier sits under and leaves standing, which a nest deeper than two
    /// has. Depth lives in this list's length and nowhere in the code that walks it.
    pub rows: Vec<Extent>,
    /// The enclosing parameter `(ᴘ, Pos)` the body takes beside its slots.
    pub param: Extent,
}

/// A **nested** writer's body takes `((ᴘ, Pos), slots)` where a top-level one takes
/// `slots`: everything it reads from the enclosing row arrives as a slot, but the
/// parameter elimination gave it keeps the enclosing pair, so nothing is rewritten and
/// each level's body is exactly what the level above produced. This is that wrap, and
/// `None` is the top-level case.
fn wrap_enclosing_tiling(enclosing: Option<&Extent>, slots: Tiling) -> Tiling {
    match enclosing {
        None => slots,
        Some(ext) => Tiling::Record(HashMap::from([
            (tuple_field(0), Tiling::from_extent(ext)),
            (tuple_field(1), slots),
        ])),
    }
}

/// The tiling of the items a drive's source delivers: the source's codomain past the
/// `levels` the drive itself walks — one for a flat drive, and for a nested one its rows
/// and the positions beneath them.
///
/// The body's item slot is that tiling, so an item is handed on exactly as the source
/// shaped it. Deriving it from the item's extent instead lands somewhere else for a record:
/// [`Tiling::from_extent`] answers for a **store read**, where a record with no collection
/// in it is one column of record values, while a source delivers it as a column per field.
fn source_item_tiling(source: &Tiling, levels: usize) -> Tiling {
    let mut at = source;
    for _ in 0..levels {
        let Tiling::DataFunction { codomain, .. } = at else {
            panic!(
                "a drive's source is a collection at each of the {levels} levels it walks, got {at}"
            )
        };
        at = codomain;
    }
    at.clone()
}

/// The body-input codomain fields `{_0..._{r-1}: read, _r: item}`, built over either
/// tilings or tiles. `r = read_extents.len()`.
///
/// A read slot is built from its extent, which is what the store says a key holds; the
/// item is passed ready-made, because what the source delivers says its shape and no
/// extent does ([`source_item_tiling`]).
///
/// The layout — read fields in order, then the item — is the contract between the
/// tiling a driver declares and the tile it renders, so both go through here. Two
/// spellings of it could drift into a tile that does not match its own tiling.
fn body_input_fields<T>(
    read_extents: &[Extent],
    item: T,
    read: impl Fn(usize, &Extent) -> T,
) -> HashMap<String, T> {
    let mut fields: HashMap<String, T> = HashMap::with_capacity(read_extents.len() + 1);
    for (i, ext) in read_extents.iter().enumerate() {
        fields.insert(tuple_field(i), read(i, ext));
    }
    fields.insert(tuple_field(read_extents.len()), item);
    fields
}

/// The `commit` tag of the decision variant `` {`commit{𝑃} | `abort} ``. A union
/// column keys its arms by name, so the decode matches the tag the CCL side
/// built and neither end depends on the variant's arm order.
fn is_commit_tag(tag: &crate::ccl::FieldKey) -> bool {
    matches!(tag, crate::ccl::FieldKey::Name(n) if n == crate::ccl::V_COMMIT)
}

/// The `` `fired `` tag of a tap variant `` {`fired{𝑉} | `idle} ``. Matched by name
/// for the reason [`is_commit_tag`] is.
fn is_fired_tag(tag: &crate::ccl::FieldKey) -> bool {
    matches!(tag, crate::ccl::FieldKey::Name(n) if n == crate::ccl::V_FIRED)
}

/// The newest position present in a body-input tile — the attempt a writer is
/// currently deciding, superseding any older live one (see the caller). `None`
/// when the driver has emitted nothing live.
fn newest_body_position(tile: &Tile) -> Option<Position> {
    let Tile::DataFunction { domain, .. } = tile else {
        return None;
    };
    (0..domain.len())
        .map(|i| Position::new(domain.index_at(i)))
        .max()
}

/// The largest of `positions` strictly below `bound`, or `None` where none is.
///
/// A release names a prefix by a position that exists, so a consumer keeping `bound`
/// itself releases the last position under it rather than its predecessor: a domain
/// carries no predecessor operation, and the positions that exist are what a release
/// can name.
fn last_position_below(
    positions: impl IntoIterator<Item = Position>,
    bound: &Position,
) -> Option<Position> {
    positions.into_iter().filter(|p| p < bound).max()
}

/// Every position of a collection tile's domain. Empty for any other tile.
fn domain_positions(tile: &Tile) -> Vec<Position> {
    let Tile::DataFunction { domain, .. } = tile else {
        return Vec::new();
    };
    (0..domain.len())
        .map(|i| Position::new(domain.index_at(i)))
        .collect()
}

/// Every path a body has decided, in **drive order**, with the flat index of its decision
/// in the deepest level.
///
/// The path is one component per level of the tile — the rows down to a store, then the
/// position within it — read off the levels rather than composed into a value. The nesting
/// is the path, which is what keeps a product domain's predicate off a sequenced one, and
/// why a third level needs nothing added here. A body with one level answers paths of one
/// component, which is the whole of this at depth zero.
///
/// Sorted rather than taken in the tile's own order: an async source's domain arrives
/// unordered, and [`CommitEngine::step`] takes positions strictly ascending. [`Path`]
/// orders lexicographically with each component compared as a position of its level, which
/// is drive order.
fn decided_paths(tile: &Tile) -> Vec<(Path, usize)> {
    fn walk(
        level: &Tile,
        run: std::ops::Range<usize>,
        prefix: &mut Vec<Value>,
        out: &mut Vec<(Path, usize)>,
    ) {
        let Tile::DataFunction {
            domain, codomain, ..
        } = level
        else {
            return;
        };
        for k in run {
            prefix.push(domain.index_at(k));
            if codomain.is_data_function() {
                let (from, to) = codomain.row_run(k);
                walk(codomain, from..to, prefix, out);
            } else {
                out.push((Path::from(prefix.clone()), k));
            }
            prefix.pop();
        }
    }
    let Tile::DataFunction { domain, .. } = tile else {
        return Vec::new();
    };
    let mut out = Vec::new();
    walk(tile, 0..domain.len(), &mut Vec::new(), &mut out);
    out.sort_by(|(a, _), (b, _)| a.cmp(b));
    out
}

/// Extract a writer body's grant/deny *decision* at position `pos` of its input.
///
/// The body returns a **decision variant** `` {`commit{𝑃} | `abort} `` (see
/// [`crate::ccl::V_COMMIT`]/[`crate::ccl::V_ABORT`]): the codomain is a
/// `Scalar(Union)` column, one `Value::Union { tag, inner }` per position.
/// `abort` (any tag but `commit` — see [`is_commit_tag`]) is a whole-transaction deny — no writes, no
/// taps (carry / no proposal). `commit` carries the dense payload record `𝑃 =
/// {writes: {k: new…}, __to_<defer>*}`, each tap holding `` {`fired{𝑉} | `idle} ``.
///
/// Returns `(commit, writes, tap_fired)`: `commit` gates grant vs deny; `writes[j]`
/// is the new value for `write_keys[j]` (carry writes then tap values, in that
/// order); and `tap_fired[t]` says whether tap `tap_fields[t]` fires at this
/// position (its `` `fired ``/`` `idle `` tag).
/// A committing decision applies a carry write and a *fired* tap, but not a
/// non-fired tap.
fn body_decision_at(
    tile: &Tile,
    pos: &Position,
    write_keys: &[Value],
    tap_fields: &[String],
) -> Option<(bool, Vec<Value>, Vec<bool>)> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = tile
    else {
        return None;
    };
    let keys = &domain;
    // The decision codomain is a `Scalar(Union)` — one tagged variant per row.
    let Tile::Scalar(union_col) = codomain.as_ref() else {
        return None;
    };
    let row = (0..keys.len()).find(|&i| &keys.index_at(i) == pos.value())?;
    decision_at_index(union_col, row, write_keys, tap_fields)
}

/// [`body_decision_at`] once the row is known, which a **nested** body's decision stream
/// finds by walking its two levels rather than by looking a position up: an inner
/// position repeats across enclosing rows, so only the path identifies a decision.
fn decision_at_index(
    union_col: &ColumnValue,
    row: usize,
    write_keys: &[Value],
    tap_fields: &[String],
) -> Option<(bool, Vec<Value>, Vec<bool>)> {
    let Value::Union { tag, inner } = union_col.index_at(row) else {
        return None;
    };
    // `abort` — a whole-transaction deny: no proposal, no taps (carry).
    if !is_commit_tag(&tag) {
        return Some((false, Vec::new(), Vec::new()));
    }
    // `commit` — the payload record `{writes, __to_<defer>*}`. The union column
    // already carried the values materialized at this row, so they are read
    // straight off the record with no per-column extraction step.
    let Value::Record(payload) = *inner else {
        return None;
    };
    // The write set is keyed by the variable written, so it is read back by name,
    // in `write_keys` order — the order the caller aligns with. A store key is the
    // variable's name as a tag over the data key it holds (`store_key`), so the
    // name is the tag; the write set never keys by the data key, because a keyed
    // write commits the whole collection at `` `reg(unit) ``. The carry keys are
    // the ones it holds: `write_keys` is carry keys ++ tap keys (the layout
    // `build_induction_store_single` and `build_commit_store` both set), and a
    // tap's value rides the payload beside `writes` rather than inside it. Each
    // entry may itself be record-valued (a store holding a record).
    assert!(
        write_keys.len() >= tap_fields.len(),
        "write keys are the carry keys followed by one per tap: {} keys, {} taps",
        write_keys.len(),
        tap_fields.len(),
    );
    let n_carry = write_keys.len() - tap_fields.len();
    let mut writes = Vec::with_capacity(write_keys.len());
    match payload.get(F_WRITES)? {
        Value::Record(writes_rec) => {
            debug_assert_eq!(
                writes_rec.len(),
                n_carry,
                "a decision writes every carry key of the store consuming it",
            );
            for key in &write_keys[..n_carry] {
                let Value::Union {
                    tag: crate::ccl::FieldKey::Name(name),
                    ..
                } = key
                else {
                    return None;
                };
                writes.push(writes_rec.get(name.as_str())?.clone());
            }
        }
        // A read-only transaction's empty write set lowers to a unit value (not
        // a record): zero carry writes, only taps contribute.
        Value::Unit => {}
        _ => return None,
    }
    // Per tap, its value and whether it *fires* at this position. A tap holds
    // `` {`fired{𝑉} | `idle} ``, so the tag answers both at once: `` `fired ``
    // carries the fed value, and `` `idle `` is a position the tap's own route did
    // not admit — a sibling route's commit, which must not over-fire this reply.
    // An `` `idle `` position still occupies its slot in `writes`, because the
    // caller indexes that vector by `write_keys` and drops the non-fired entries
    // by `tap_fired`; `Unit` is the value nothing reads.
    let mut tap_fired = Vec::with_capacity(tap_fields.len());
    for tap in tap_fields {
        let value = payload.get(tap)?.clone();
        let Value::Union { tag, .. } = &value else {
            return None;
        };
        // The tag is the gate. The *value* goes to the store as it stands, tag and
        // all: the IR reads a tap through ``variant_project(`fired)``, so the
        // stream's restriction to fired positions happens there, on a value whose
        // type says what it is.
        tap_fired.push(is_fired_tag(tag));
        writes.push(value);
    }
    Some((true, writes, tap_fired))
}

/// A complete transaction writer over a multi-key [`CommitOperator`], fused into
/// one operator (the store read, the body application, and the proposal build)
/// so it has a *single* consumer — the `CommitProducer` — and emits a
/// **stable, append-only** proposal stream (positions never shift), exactly like
/// the hand-written `TokenWriter`. Fusing is load-bearing: a writer split across
/// fanned operators desyncs, because the `FanOut` compacts released positions
/// per-branch and the proposal positions would re-index out from under the
/// `CommitProducer`'s cursor.
///
/// Each pull: take the newest live position from the [`TransactDriver`] — which built
/// that row from `(item, frontier)`, one row per pair — pull the body for its decision,
/// and append the proposal `{snap: frontier, reads: {key ↦ old}, writes: {key ↦ new}}`.
/// Releasing the driver row acks the attempt's finish, so the driver advances to the next
/// item. Retries (a fresh attempt at a new frontier) append as new positions.
pub struct TransactWriter {
    base: OperatorBase,
    store_op: Box<dyn TileOperator>,
    body_op: Box<dyn TileOperator>,
    /// A second branch of the [`TransactDriver`] the body reads. The writer pulls
    /// it to learn which attempt is in flight, and **releases** it to ack the
    /// attempt's finish — the half of the driver's release intersection that a
    /// body's consume-release cannot supply.
    driver_op: Box<dyn TileOperator>,
    /// Runtime keys the body reads a snapshot of, in body-parameter order
    /// (snapshot position `i` ↦ `read_keys[i]`).
    read_keys: Vec<Value>,
    /// Runtime keys the body writes, aligned with the decision's `writes` tuple
    /// followed by the `tap_fields` taps (`write_keys[j]` ↦ the `j`-th committed
    /// value). A reply (`resps << e`) rides the writer body as a `__to_<defer>`
    /// decision field (a *tap*); op-conversion folds each tap into the committed
    /// write set as a write-only key, so the reply is committed atomically with
    /// the transaction and read back as a `Fun(Txn, V)` value-stream.
    write_keys: Vec<Value>,
    /// Decision-record field names of the reply taps, in `write_keys` tail order.
    /// Their values are appended to each committed write set (a tap commits iff
    /// its transaction does, so a denied request replies nothing).
    tap_fields: Vec<String>,
}

impl TransactWriter {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        store_op: Box<dyn TileOperator>,
        body_op: Box<dyn TileOperator>,
        driver_op: Box<dyn TileOperator>,
        read_keys: Vec<Value>,
        write_keys: Vec<Value>,
        tap_fields: Vec<String>,
        key_extent: Extent,
        value_extent: Extent,
    ) -> Self {
        Self {
            base: OperatorBase::new(proposal_stream_tiling(&key_extent, &value_extent)),
            store_op,
            body_op,
            driver_op,
            read_keys,
            write_keys,
            tap_fields,
        }
    }
}

impl TileOperator for TransactWriter {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
        visit(value("body_op", &*self.body_op));
        visit(value("driver_op", &*self.driver_op));
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // This writer re-arms nothing itself: the driver owns the transaction
        // source and re-arms while a transaction remains to attempt, which
        // subsumes every continuation this writer could want (an attempt is only
        // in flight while its item is unacked, so the driver's cursor has not
        // passed it). What the writer does need is for the driver's wakeups and
        // live arrivals to *reach* it, and through it the commit cycle and any
        // sink reading a store key or `__to_<defer>` tap — that is the forwarding
        // consumer on its driver branch below. The store and body inputs need no
        // notification: the writer pulls them on demand, and forwarding the
        // cyclic store would loop.
        let consumer = shared_consumer(consumer);
        let sg = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.subscribe(sg, Box::new(|| {}), scheduler);
        let bg = self.body_op.tiling().universal_guard();
        let body_producer = self.body_op.subscribe(bg, Box::new(|| {}), scheduler);
        // Forward the driver's notification to this writer's consumer: the driver
        // owns the transaction source, so a request arriving on a live source
        // reaches this writer, and through it the commit cycle, along this edge.
        let dg = self.driver_op.tiling().universal_guard();
        let driver_producer = self.driver_op.subscribe(
            dg,
            forwarding_consumer(&consumer, &scheduler.wakeup_queue()),
            scheduler,
        );
        Box::new(TransactWriterProducer {
            base: ProducerBase::new(TransactWriterProducer::alloc_id(), self.tiling()),
            store_producer,
            body_producer,
            driver_producer,
            read_keys: self.read_keys.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            last_decided_pos: None,
            driver_terminal: false,
            committed_base: 0,
            emitted: Vec::new(),
        })
    }
}

/// A proposal awaiting the operator's verdict.
///
/// The facts travel together because they are views of one attempt, and the
/// release that finishes it uses both: `snapshot`/`reads`/`writes` are what the
/// operator validates and commits, and `attempt` is the driver row to ack so the
/// driver advances past the item with it.
///
/// There is deliberately no item index here. The driver owns the transaction
/// source and therefore the item cursor; a copy of it in the writer would be a
/// second cursor advanced by a different rule, free to disagree with the real
/// one. The writer names an attempt by the driver position it came from, which is
/// the identity the driver itself uses.
struct InFlightProposal {
    /// The store frontier this proposal was built against — the read set is
    /// current iff no read key was overwritten after it.
    snapshot: Position,
    /// The multi-key read set. Omits a key with no value yet: an append onto an
    /// empty store reads nothing, so it can never go stale (the empty-store
    /// bootstrap).
    reads: HashMap<Value, Value>,
    /// The multi-key write set, mutable variable writes then fired taps.
    writes: HashMap<Value, Value>,
    /// The [`TransactDriver`] position this attempt was decided from. Acking it
    /// is how the driver learns the item is finished.
    attempt: Position,
}

struct TransactWriterProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    body_producer: Box<dyn TileProducer>,
    /// The driver branch this writer acks on (see [`TransactWriter::driver_op`]).
    driver_producer: Box<dyn TileProducer>,
    read_keys: Vec<Value>,
    write_keys: Vec<Value>,
    /// Reply-tap decision fields, appended to each write set (see
    /// [`TransactWriter::tap_fields`]).
    tap_fields: Vec<String>,
    /// The driver position whose decision this writer has already acted on, so a
    /// re-pull re-reads a *not-ready* decision without re-deciding a settled one.
    last_decided_pos: Option<Position>,
    /// Whether the driver has closed — every transaction attempted and acked over
    /// a source that can deliver no more. The writer owns no source; this is its
    /// completeness signal.
    driver_terminal: bool,
    /// Absolute proposal-stream position of `emitted[0]` — the number of leading
    /// proposals the consumer has committed-and-released, which `release_impl`
    /// has compacted away. The proposal stream is an **offset window**: its
    /// positions are absolute and consumer-indexed (`CommitProducer` reads them
    /// by value), so the released prefix is dropped without renumbering the live
    /// suffix. Bounds the writer's retained state on a long-lived store.
    committed_base: usize,
    /// Proposals not yet released — append-only within the live window. The
    /// entry at vector index `i` is absolute position `committed_base + i`.
    emitted: Vec<InFlightProposal>,
}

impl TransactWriterProducer {
    fn render(&self) -> Tile {
        let n = self.emitted.len();
        let reads: Vec<Value> = self
            .emitted
            .iter()
            .map(|p| map_to_value(&p.reads))
            .collect();
        let writes: Vec<Value> = self
            .emitted
            .iter()
            .map(|p| map_to_value(&p.writes))
            .collect();
        // Terminal only when the driver has closed — every transaction attempted
        // and acked, over a source that can deliver no more — *and* no proposal
        // is still in flight. The driver owns the source, so its closing is the
        // completeness signal; a live-source writer stays non-terminal when
        // momentarily drained, so the store (and any reply tap read off it) is
        // not prematurely declared complete.
        let terminal = self.driver_terminal && self.emitted.is_empty();
        Tile::data_function(
            // Absolute positions: the live window is `[committed_base, …)`; the
            // released prefix has been compacted away. Positions never renumber.
            ColumnValue::from_uints((self.committed_base..self.committed_base + n).collect()),
            Box::new(Tile::Record(HashMap::from([
                (
                    F_SNAP.to_string(),
                    Tile::Scalar(ColumnValue::from_values(
                        self.emitted
                            .iter()
                            .map(|p| p.snapshot.value().clone())
                            .collect(),
                        &Extent::Base(BaseType::UInt),
                    )),
                ),
                (
                    F_READS.to_string(),
                    Tile::Scalar(ColumnValue::Variants(reads)),
                ),
                (
                    F_WRITES.to_string(),
                    Tile::Scalar(ColumnValue::Variants(writes)),
                ),
            ]))),
            if terminal {
                Predicate::True
            } else {
                Predicate::False
            },
            BitSet::new(),
        )
    }

    /// Ack every attempt at or below `pos` — issued when an attempt finishes: a
    /// deny (no proposal to commit) or a commit-ack on the proposal it produced.
    ///
    /// It releases both driver branches this writer controls: its **own**, which
    /// is the half of the driver's release intersection meaning "finished" (the
    /// body's half only means "consumed"), and the body's decision prefix, which
    /// bounds the body sub-operator's caches. Positions are absolute, so the
    /// windows slide forward without renumbering.
    fn ack_through(&mut self, pos: &Position) {
        let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            pos.value().clone(),
        )));
        self.driver_producer.release(guard.clone());
        self.body_producer.release(guard);
    }

    /// Drop the live window's superseded proposals, which deciding driver position
    /// `attempt` makes dead — keeping writer state O(1) under sustained contention.
    ///
    /// The driver emits a fresh position for an item only at a *new* frontier (a
    /// retry after a stale grant, or a grant→deny flip), and its whole live window
    /// belongs to one item. So every proposal still here when a newer position is
    /// decided is provably dead: the `CommitProducer` owns this writer directly (no
    /// intervening fan-out), so it attempted every prior-pull proposal in the pull
    /// that rendered it; a *commit* would have released and prefix-compacted it
    /// away, so one still live went stale. Drop it and advance `committed_base`;
    /// the fresh proposal is appended at the next absolute position, so the
    /// consumer-indexed positions never renumber. Without this, a never-winning
    /// writer accumulates one lingering proposal per frontier for the store's
    /// lifetime, one lingering proposal per frontier it lost at.
    fn drop_superseded(&mut self, attempt: &Position) {
        debug_assert!(
            self.emitted.iter().all(|p| p.attempt < *attempt),
            "drop_superseded: live window holds a proposal at or past the position being \
             decided ({attempt}) — {:?}; a superseded proposal is one from a strictly \
             earlier attempt",
            self.emitted
                .iter()
                .map(|p| p.attempt.clone())
                .collect::<Vec<_>>()
        );
        let drop = self.emitted.len();
        if drop > 0 {
            self.emitted.clear();
            self.committed_base += drop;
        }
    }
}

impl CyclicSequencingProducer for TransactWriterProducer {
    fn debug_assert_position_invariant(&self) {
        // The proposal stream is append-only and consumer-indexed
        // (`CommitProducer` reads it by position), so a live window's entries stay
        // in emission order: each proposal is decided from a strictly later driver
        // position than the one before. A window that ever went backwards would
        // mean a position had shifted under the consumer's cursor. Driver positions
        // are the ordering because they are what the writer names an attempt by —
        // the driver's item cursor is the driver's, and the writer keeps no copy.
        debug_assert!(
            self.emitted.windows(2).all(|w| w[0].attempt < w[1].attempt),
            "the live proposal window is out of attempt order: {:?}",
            self.emitted
                .iter()
                .map(|p| p.attempt.clone())
                .collect::<Vec<_>>()
        );
    }
}

impl TileProducer for TransactWriterProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let store_tile = self
            .store_producer
            .get(self.store_producer.tiling().universal_guard());
        // The snapshot the proposal is built against: the store's decided frontier
        // (watermark). Each read key reads its value there; a key with no value
        // yet (an *append* onto an empty collection store) reads nothing — it is
        // omitted from the read set, the empty-store bootstrap that lets the first
        // `<<` commit (a collection store starts with no element).
        let snapshot = store_frontier(&store_tile);
        // Read each key's current value *and* the tick it was decided at — the
        // tick bounds this writer's store-branch release below.
        let olds_at: Vec<Option<(Position, Value)>> = self
            .read_keys
            .iter()
            .map(|k| store_current(&store_tile, k))
            .collect();
        let olds: Vec<Option<Value>> = olds_at
            .iter()
            .map(|o| o.as_ref().map(|(_, v)| v.clone()))
            .collect();
        // Store-branch GC release. The store reclaims a committed version only
        // once *every* consumer branch has released it (the cyclic `FanOut`
        // intersects the release guards; `gc_released_prefix` then drops the
        // released prefix, keeping the carry source a live position reads — the
        // carry-forward value a scalar read still needs). Two writer shapes
        // release here:
        //
        //  - **Empty read set** (a collection-append / overwrite writer, e.g.
        //    `<<` or `latest = msg`): it reads no tick's value, only the frontier,
        //    so it releases the whole decided prefix.
        //  - **Non-empty read set** (a carry drawdown, e.g. `pool = pool - r`):
        //    it releases strictly *below* the oldest tick it read this pull. This
        //    is the load-bearing INVARIANT — a writer never releases a version it
        //    read — so backward validation's `read_as_of` at any pending
        //    proposal's snapshot still finds that proposal's recorded reads, and
        //    because GC reclaims only the intersection of *all* consumers'
        //    releases, one writer's release can never strand another writer's (or
        //    a reader's) reads. Without this, a reading writer released nothing
        //    and pinned the commit log unbounded for its lifetime.
        //
        // A full-render `AsOf` reader (a live cross-endpoint read) still releases
        // nothing on its own branch, so the intersection — hence GC — stays
        // pinned while it is live; that is correct, as it may answer an as-of
        // query at any past request position.
        let release_through: Option<Position> = if self.read_keys.is_empty() {
            snapshot.clone()
        } else {
            olds_at
                .iter()
                .filter_map(|o| o.as_ref().map(|(t, _)| t.clone()))
                .min()
                .and_then(|oldest_read| {
                    last_position_below(store_change_positions(&store_tile), &oldest_read)
                })
        };
        if let Some(through) = release_through {
            self.store_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(through.into_value()),
                )));
        }
        // The decisions for every live attempt. Which one to act on is settled
        // below, off the driver: the driver emits a row once per `(item, frontier)`,
        // so a position appearing here is a distinct attempt, and re-pulling at an
        // unchanged pair adds none.
        let body_tile = self
            .body_producer
            .get(self.body_producer.tiling().universal_guard());
        // The attempt to decide is the newest live position on this writer's own
        // driver branch — the row the driver emitted for `(current, frontier)` this
        // pull, or the one still in flight from an earlier one. Reading it here
        // rather than counting positions independently keeps the writer and the
        // driver from inventing two numberings that could drift.
        let driver_tile = self
            .driver_producer
            .get(self.driver_producer.tiling().universal_guard());
        self.driver_terminal = driver_tile.is_terminal();
        let newest = newest_body_position(&driver_tile);
        // The writer decides only the *newest* live driver position, and that
        // **supersedes** every older live one. Sound because the driver's whole
        // live window belongs to one item — it emits only for the item it has not
        // yet acked (asserted in `TransactDriverProducer::get_impl`) — so an older
        // row is either an attempt already granted and awaiting its ack, or one
        // whose decision was not ready and has since been re-posed at a newer
        // frontier. Both are dead: the newer attempt reads a newer snapshot, and
        // the ack that finishes the item releases the whole prefix. This mirrors
        // `drop_superseded` on the proposal side.
        debug_assert!(
            newest
                .as_ref()
                .is_none_or(|n| self.last_decided_pos.as_ref().is_none_or(|d| n >= d)),
            "the driver's newest position {newest:?} went backwards past the decided watermark {:?}",
            self.last_decided_pos
        );
        // Reclaim what supersession abandons, on this writer's driver branch. Every
        // live position below `newest` is dead by the paragraph above, and saying so
        // *here* is what keeps a contended item's cost flat: without it the driver's
        // window grows one row per retry, and since the body re-renders its whole
        // live window each pull, K retries cost K rows retained and K² body rows
        // evaluated. The driver does not read this as the item's finish — only the
        // release of its newest live row is that (see
        // `TransactDriverProducer::release_impl`), which is what keeps the ack
        // meaning "the attempt finished" rather than "some row of it was reclaimed".
        if let Some(pos) = &newest
            && let Some(through) = last_position_below(domain_positions(&driver_tile), pos)
        {
            self.driver_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(through.into_value()),
                )));
        }
        // Decide a position once. A *new* newest position is a fresh attempt (a
        // new item, or a retry of this one at a moved frontier); an unchanged one
        // is either already decided — the driver suppresses re-emitting at an
        // unchanged `(item, frontier)` — or a not-ready decision to re-read.
        if let Some(pos) = newest
            && Some(&pos) != self.last_decided_pos.as_ref()
            && let Some(frontier) = snapshot
        {
            match body_decision_at(&body_tile, &pos, &self.write_keys, &self.tap_fields) {
                // Grant: propose the write set; the operator decides whether it
                // commits — its ack releases the driver row, which is what advances
                // the driver past this item — or is stale, leaving the item to be
                // re-attempted at the moved frontier. The read set omits
                // never-written keys (append → empty read).
                Some((true, new, tap_fired)) => {
                    let reads: HashMap<Value, Value> = self
                        .read_keys
                        .iter()
                        .zip(&olds)
                        .filter_map(|(k, o)| o.clone().map(|v| (k.clone(), v)))
                        .collect();
                    // `write_keys` and the decision's `new` write-set are two
                    // views of the same store keys, aligned by position. A
                    // length mismatch is a `transact_phase`/inference bug that
                    // `zip` would otherwise paper over by silently dropping the
                    // tail — committing a truncated write set. Assert the arity.
                    debug_assert_eq!(
                        self.write_keys.len(),
                        new.len(),
                        "commit operator: decision write-set arity ({}) disagrees with \
                         write_keys ({}) — zip would silently drop the tail",
                        new.len(),
                        self.write_keys.len()
                    );
                    // Carry writes lead; taps follow (the layout `build_commit_store`
                    // sets). A committed transaction applies every carry write but
                    // only the taps that *fired* on its route — a non-fired tap under
                    // cross-key routing is omitted from the delta, so it does not
                    // over-fire on a sibling route's commit.
                    // Layout invariant: `write_keys` = carry keys ++ tap keys, so
                    // the subtraction never underflows. Assert it — a break would wrap
                    // `n_carry` to a huge value in release and mis-index `tap_fired`.
                    debug_assert!(
                        self.write_keys.len() >= self.tap_fields.len(),
                        "commit operator: tap fields ({}) exceed write keys ({})",
                        self.tap_fields.len(),
                        self.write_keys.len()
                    );
                    let n_carry = self.write_keys.len() - self.tap_fields.len();
                    let writes: HashMap<Value, Value> = self
                        .write_keys
                        .iter()
                        .cloned()
                        .zip(new)
                        .enumerate()
                        .filter(|(i, _)| *i < n_carry || tap_fired[*i - n_carry])
                        .map(|(_, kv)| kv)
                        .collect();
                    // Re-proposing this item at a new frontier supersedes its
                    // prior stale proposal(s); drop them so the window stays O(1).
                    self.drop_superseded(&pos);
                    self.emitted.push(InFlightProposal {
                        snapshot: frontier,
                        reads,
                        writes,
                        attempt: pos.clone(),
                    });
                    self.last_decided_pos = Some(pos);
                    // The body-input row stays live until the commit-ack: it is
                    // the attempt in flight, and releasing it now would tell the
                    // driver this item is finished before it has committed.
                }
                // Deny: a purely local read-only decision (the body chose not to
                // write at this snapshot — e.g. `if pool >= r`). No proposal, no
                // tick consumed; advance past this item immediately, like the
                // hand-written `TokenWriter`'s `pool < cost` branch. Drop any
                // earlier grant-stale proposal for this item first (a grant→deny
                // flip on retry) so it is not orphaned in the window.
                Some((false, _, _)) => {
                    self.drop_superseded(&pos);
                    self.last_decided_pos = Some(pos.clone());
                    // A deny finishes the item without proposing, so there is no
                    // commit-ack to carry it: ack the attempt here, which is what
                    // advances the driver past this item.
                    self.ack_through(&pos);
                }
                None => {
                    // No decision at `pos`. If the body is **terminal**, the
                    // decision-body shape is genuinely unsupported (e.g. a reply
                    // tap fed a list-/function-valued expression) — retrying would
                    // re-read the same `None`, so fail loudly.
                    if body_tile.is_terminal() {
                        panic!(
                            "commit operator: decision body produced no scalar/record \
                             decision at position {pos} — unsupported decision-body tile shape"
                        );
                    }
                    // Otherwise the decision is **not ready**: it reads a broadcast
                    // cross-loop accumulator final still converging — its
                    // `ExtractFinal` is empty until the sibling loop's own cycle
                    // drains, one position per body pull. Leaving `last_decided_pos`
                    // unset is the whole handling: this position stays undecided, so
                    // nothing acks the driver row, so the driver's item cursor does not
                    // move and the driver keeps re-arming. Each re-pull advances the
                    // sibling loop one step until the decision fills in.
                }
            }
        }
        self.debug_assert_position_invariant();
        // A release naming part of a proposal rather than the proposal leaves it in the
        // window (`release_impl`), so what it names is withheld here.
        let mut tile = self.render();
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // commit-ack: advance past the item each released proposal was for, then
        // compact the released prefix out of the live window. Idempotent.
        self.debug_assert_position_invariant();
        //
        // The window holds rows, so it acts on the rows the release names whole. What the
        // release names of a row's values is withheld from the output (`get_impl`).
        let pred = &obsolete_guard.whole_keys();
        // The entry at vector index `i` is absolute position `committed_base + i`
        // (positions are stable; the consumer releases by that absolute value).
        // A committed proposal finishes its item, so ack the driver row it was
        // decided from — the driver is what advances the item cursor.
        let ack = self
            .emitted
            .iter()
            .enumerate()
            .filter(|(i, _)| pred.contains(&Value::UInt(self.committed_base + i)))
            .map(|(_, p)| p.attempt.clone())
            .max();
        if let Some(pos) = ack {
            self.ack_through(&pos);
        }
        // Drop the released leading prefix and advance the window base. Releases
        // are prefixes (`at_or_below(step)`, accumulated across commits), so the
        // released positions form a run from `committed_base` up. Dropping frees
        // the proposal records (their read/write maps) without renumbering the
        // live suffix — `CommitProducer` reads remaining positions by value.
        let mut drop = 0;
        while drop < self.emitted.len() && pred.contains(&Value::UInt(self.committed_base + drop)) {
            drop += 1;
        }
        if drop > 0 {
            self.emitted.drain(0..drop);
            self.committed_base += drop;
        }
    }
}

#[cfg(test)]
/// A store's decided positions as the one-row collection the tile holds.
fn one_row_decided(positions: ColumnValue) -> Tile {
    let len = positions.len();
    Tile::data_function(
        positions,
        Box::new(Tile::Scalar(ColumnValue::Units(len))),
        Predicate::True,
        BitSet::new(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tiling::row_frontier;
    // The consumer helpers own shared-cell construction for the operators here; the
    // fixtures below build their own recording cells, hence the direct imports.
    use crate::ccl::{FieldKey, TagMap, V_ABORT, V_COMMIT};
    use crate::interpreter::scheduler::pull_laps;
    use crate::interpreter::tile_operators::{Constant, FanOut, Memo};
    use crate::interpreter::validate_tile;
    use rstest::rstest;
    use std::{cell::RefCell, rc::Rc};

    /// A fixture producer's answer with the released region subtracted — the
    /// post-condition [`TileProducer::get`] asserts. A fixture stands in for a real
    /// source or body, and its consumers reclaim what they have consumed, so handing
    /// back the whole tile every time would not be an honest stand-in for one.
    fn honoring_release(tile: &Tile, released: &TileGuard) -> Tile {
        let mut t = tile.clone();
        t.remove_guarded(released.clone());
        t.compact();
        t
    }

    fn int(n: i64) -> Value {
        Value::Int(n)
    }

    /// A position of a store's domain, which every engine here runs on a `UInt`
    /// clock — an iteration position or a commit tick.
    fn pos(n: usize) -> Position {
        Position::new(Value::UInt(n))
    }

    /// A store key: the variable's name tagged over the data key it holds
    /// ([`store_key`](crate::interpreter::operator_conversion::store_key)), which is the
    /// shape `body_decision_at` reads the write set's names back from.
    fn acct(name: &str) -> Value {
        store_key(name, Value::Unit)
    }

    /// Build a read/write set or initial state from `(account, balance)` pairs.
    fn balances(pairs: &[(&str, i64)]) -> HashMap<Value, Value> {
        pairs.iter().map(|(k, v)| (acct(k), int(*v))).collect()
    }

    // ── Engines ──────────────────────────────────────────────────────────────

    /// The row a path names is opened on the way down, so a drive reaching a row needs no
    /// separate announcement: the row exists once one of its positions is decided.
    #[test]
    fn engines_open_a_row_at_the_first_position_of_it() {
        let mut engines = Engines::Rows(Vec::new());
        let row = Value::UInt(0);
        assert!(engines.get(std::slice::from_ref(&row)).is_none());
        engines.store_at(std::slice::from_ref(&row), &mut || {
            CommitEngine::seeded_at(None, balances(&[("acc", 7)]))
        });
        let engine = engines
            .get(std::slice::from_ref(&row))
            .expect("the row is open once a position of it is reached");
        assert_eq!(
            engine.decided_watermark(),
            None,
            "an induction row is undecided until it steps"
        );
    }

    /// Each row carries its own engine, so a write in one is not readable from another.
    /// That is the defect a flat log keyed by `(row, position)` pairs has: a row that
    /// writes nothing inherits the previous row's last write instead of its own seed.
    #[test]
    fn engines_keep_each_row_at_its_own_seed() {
        let mut engines = Engines::Rows(Vec::new());
        let seed = &mut || CommitEngine::seeded_at(None, balances(&[("acc", 0)]));
        engines
            .store_at(&[Value::UInt(0)], seed)
            .step(Position::new(Value::UInt(0)), Some(balances(&[("acc", 5)])));
        engines
            .store_at(&[Value::UInt(1)], seed)
            .step(Position::new(Value::UInt(0)), None);
        let untouched = engines
            .get(&[Value::UInt(1)])
            .expect("the second row is open");
        assert_eq!(
            untouched.read_as_of(&Position::new(Value::UInt(0)), &acct("acc")),
            Some(int(0)),
            "a row that wrote nothing holds its own seed, not its predecessor's write"
        );
    }

    /// Depth is not counted anywhere: a second level of rows is the same arm again, which
    /// is what lets a nest three deep reuse the carrier a nest two deep uses.
    #[test]
    fn engines_nest_to_any_depth_with_one_arm() {
        let mut engines = Engines::Rows(Vec::new());
        let path = [Value::UInt(0), Value::UInt(1), Value::UInt(2)];
        engines.store_at(&path, &mut || {
            CommitEngine::seeded_at(None, balances(&[("acc", 3)]))
        });
        assert!(
            engines.get(&path).is_some(),
            "three levels of rows need no third arm"
        );
        assert!(
            engines.get(&path[..2]).is_none(),
            "a path stopping at a level names no store"
        );
    }

    /// Writer write-sets where every writer may write every key the store is
    /// seeded with — true of each engine-level test here, whose writers all
    /// contend for the same accounts. Per-key closure then coincides with
    /// whole-store closure, which is what these tests assert on.
    fn all_writers_write(init: &HashMap<Value, Value>, n_writers: usize) -> Vec<Vec<Value>> {
        vec![init.keys().cloned().collect(); n_writers]
    }

    /// Position-driven induction: `x := 0; for i in [1,2,3,4]: if i > 2: x += i`.
    /// The guard (`i > 2`) fires at positions 2 and 3; positions 0 and 1 carry.
    /// Modelled as sparse `step`s over the iteration extent — a change only where
    /// the guard fires, a carry (`None`) elsewhere — the changelog stays sparse
    /// while the frontier tracks the whole extent, and folded reads recover the
    /// carry-forward accumulator `[0, 0, 3, 7]`.
    #[test]
    fn induction_conditional_write_folds_carry_forward() {
        let acc = acct("acc");
        let mut e = CommitEngine::unopened();
        // prev read defaults to init (0) below the earliest change; the write at a
        // committing position is prev + item.
        e.step(pos(0), None); // i=1, guard false → carry (x_0 = 0)
        e.step(pos(1), None); // i=2, guard false → carry (x_1 = 0)
        e.step(pos(2), Some(balances(&[("acc", 3)]))); // i=3 → x_2 = 0 + 3
        e.step(pos(3), Some(balances(&[("acc", 7)]))); // i=4 → x_3 = 3 + 4

        assert_eq!(
            e.decided_watermark(),
            Some(&pos(3)),
            "frontier reaches the final position, not the latest write"
        );
        // Folded reads: carries inherit (None → the reader's init default), writes resolve.
        assert_eq!(e.read_as_of(&pos(0), &acc), None); // carry → init 0
        assert_eq!(e.read_as_of(&pos(1), &acc), None); // carry → init 0
        assert_eq!(e.read_as_of(&pos(2), &acc), Some(int(3)));
        assert_eq!(e.read_as_of(&pos(3), &acc), Some(int(7))); // final total

        // The rendered store: a sparse changelog (2 change ticks) whose *length*
        // is the decided frontier region (4 positions), not the change count.
        let tile = e.render_full_store_tile(&store_tiling(&["acc"]));
        assert!(validate_tile(&tile));
        let Tile::Store { frontier, .. } = &tile else {
            panic!("induction render is a Store");
        };
        assert_eq!(
            store_change_positions(&tile).len(),
            2,
            "only the two committing positions are changes"
        );
        assert_eq!(
            row_frontier(frontier, 0),
            Predicate::at_or_below(Value::UInt(3))
        );
        assert_eq!(
            store_frontier(&tile).map(Position::into_value),
            Some(Value::UInt(3)),
            "a store's decided region is [0, 3], not the change count"
        );
    }

    /// A test iteration source: one terminal `DataFunction(pos → item)` tile
    /// over a fixed item list (the loop extent), mirroring a lowered `cast(iter,
    /// …)` loop source.
    struct ItemSource {
        tiling: Tiling,
        tile: Tile,
    }

    impl ItemSource {
        fn new(items: &[i64]) -> Self {
            let tiling =
                Tiling::data_function(Extent::Base(BaseType::UInt), Tiling::Scalar(value_extent()));
            let tile = Tile::data_function(
                ColumnValue::from_uints((0..items.len()).collect()),
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    items.iter().map(|n| int(*n)).collect(),
                    &value_extent(),
                ))),
                Predicate::True,
                BitSet::new(),
            );
            Self { tiling, tile }
        }
    }

    impl TileOperator for ItemSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(ProposalSourceProducer {
                base: ProducerBase::new(ProposalSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
            })
        }
    }

    /// The `commit` payload extent for a single-key writer: `{writes: {acc: value}}`.
    ///
    /// The write set is keyed by the variable written, so these fixtures name
    /// the key the same way the CCL side does.
    fn commit_payload_extent(key: &str) -> Extent {
        Extent::Record(HashMap::from([(
            F_WRITES.to_string(),
            Extent::Record(HashMap::from([(key.to_string(), value_extent())])),
        )]))
    }

    /// The decision variant extent `` {`commit{payload} | `abort} ``, keyed by tag —
    /// so these fixtures name the same arms the CCL side builds, and the order they
    /// are listed in is immaterial.
    fn decision_union_extent(payload: Extent) -> Extent {
        Extent::Union(TagMap::from_arms(vec![
            (FieldKey::Name(V_COMMIT.into()), payload),
            (FieldKey::Name(V_ABORT.into()), Extent::Base(BaseType::Unit)),
        ]))
    }

    /// A `` `commit({writes: {key: write}}) `` decision value. The write set is
    /// keyed by the variable written, so a fixture names its key the same way
    /// the writer consuming the decision does.
    fn commit_value(key: &str, write: Value) -> Value {
        let writes_rec = Value::Record(HashMap::from([(key.to_string(), write)]));
        Value::Union {
            tag: FieldKey::Name(V_COMMIT.into()),
            inner: Box::new(Value::Record(HashMap::from([(
                F_WRITES.to_string(),
                writes_rec,
            )]))),
        }
    }

    /// A `` `abort `` decision value (a carry / no proposal).
    fn abort_value() -> Value {
        Value::Union {
            tag: FieldKey::Name(V_ABORT.into()),
            inner: Box::new(Value::Unit),
        }
    }

    /// A single-key decision body: over its `(read, item)` input (a driver's tile),
    /// emits `` `commit({writes: {_0: read + item}}) `` where `item > threshold`,
    /// else `` `abort ``.
    ///
    /// Serves both drivers, because the body shape is the same on both sides: for
    /// induction it models `for i in xs: if guard(i): acc += i`, an `` `abort ``
    /// being a carry the accumulator holds through; for a transaction it is a
    /// drawdown of a negative item against the read snapshot, with `i64::MIN`
    /// making every attempt a grant so contention is the only thing under test.
    struct AddIfBody {
        input: Box<dyn TileOperator>,
        tiling: Tiling,
        /// The accumulator this body writes. The write set is keyed by the
        /// variable written, so a fixture has to name its key the same way the
        /// writer that consumes the decision does.
        key: String,
        /// The guard threshold: `commit` iff `item > threshold` (`i64::MIN` ⇒ an
        /// unconditional loop, `commit` everywhere).
        threshold: i64,
    }

    impl AddIfBody {
        fn new(input: Box<dyn TileOperator>, threshold: i64, key: &str) -> Self {
            // Decision variant `` {`commit{{writes: {_0}}} | `abort} `` — a
            // `Scalar(Union)` codomain (commit=0, abort=1).
            let tiling = Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(decision_union_extent(commit_payload_extent(key))),
            );
            Self {
                input,
                tiling,
                threshold,
                key: key.to_string(),
            }
        }
    }

    impl TileOperator for AddIfBody {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let input =
                self.input
                    .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
            Box::new(AddIfBodyProducer {
                key: self.key.clone(),
                base: ProducerBase::new(AddIfBodyProducer::alloc_id(), &self.tiling),
                input,
                threshold: self.threshold,
            })
        }
    }

    struct AddIfBodyProducer {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        threshold: i64,
        key: String,
    }

    impl TileProducer for AddIfBodyProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            let in_tile = self.input.get(self.input.tiling().universal_guard());
            let Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } = in_tile
            else {
                panic!("AddIfBody input is a collection");
            };
            let Tile::Record(fields) = *codomain else {
                panic!("AddIfBody input codomain is a Record {{_0: prev, _1: item}}");
            };
            let prev = record_field(&fields, &tuple_field(0));
            let item = record_field(&fields, &tuple_field(1));
            // Per row: `item > threshold` → `` `commit({writes: {_0: prev + item}}) ``,
            // else `` `abort `` (a carry). Builds the decision `Scalar(Union)` column.
            let mut rows = Vec::with_capacity(domain.len());
            for j in 0..domain.len() {
                let (Value::Int(p), Value::Int(i)) = (prev.index_at(j), item.index_at(j)) else {
                    panic!("AddIfBody prev/item are Ints");
                };
                rows.push(if i > self.threshold {
                    commit_value(&self.key, int(p + i))
                } else {
                    abort_value()
                });
            }
            Tile::data_function(
                domain,
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    rows,
                    &decision_union_extent(commit_payload_extent(&self.key)),
                ))),
                // A per-position decision map: the decision stream is final
                // exactly when its input is, as a compiled body's operator chain
                // propagates it. The store reads this to close its frontier.
                domain_predicate,
                BitSet::new(),
            )
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            // Forward the store's decision release to the driver, which compacts
            // its emitted window and releases the loop source in turn.
            self.input.release(obsolete_guard);
        }
    }

    /// Wire a single-accumulator induction cycle: store → body → driver → cyclic
    /// fan → store. Returns the fan (its branches are the store's readers) and
    /// the accumulator key.
    fn induction_cycle(items: &[i64], threshold: i64, init: i64) -> (Rc<FanOut>, Value) {
        let acc = acct("acc");
        let store = InductionStore::new(
            vec![(
                acc.clone(),
                Box::new(Constant::new(int(init), value_extent())),
            )],
            vec![acc.clone()],
            Vec::new(),
            full_store_tiling(Extent::uint_range(items.len()), store_values(&["acc"])),
            // A store built with its source, not one resuming a running program.
            None,
        );
        let set_body = store.body_input_setter();
        let fan = Rc::new(FanOut::new_cyclic(Box::new(store)));
        let driver = InductionDriver::new(
            fan.branch(),
            Box::new(ItemSource::new(items)),
            None,
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            Extent::uint_range(items.len()),
            None,
        );
        set_body(Box::new(AddIfBody::new(Box::new(driver), threshold, "acc")));
        (fan, acc)
    }

    /// Pull until the tile goes terminal. The cycle advances one iteration
    /// position per pull, so a converging read needs one pull per position (plus
    /// the closing one); the bound is generous and failing it means divergence.
    fn pull_to_terminal(sched: &mut Scheduler, producer: &mut Box<dyn TileProducer>) -> Tile {
        let tile = pull_laps(sched, &mut **producer, MAX_CYCLE_PULLS, Tile::is_terminal);
        assert!(
            tile.is_terminal(),
            "induction cycle did not converge within {MAX_CYCLE_PULLS} pulls"
        );
        tile
    }

    /// Convergence bound for the test cycles here — far above any test's
    /// iteration count, so exceeding it means the cycle stalled.
    const MAX_CYCLE_PULLS: usize = 64;

    /// Drive an `InductionStore` for a single-accumulator loop end-to-end through
    /// the tile protocol and return the converged store tile.
    fn drive_induction(items: &[i64], threshold: i64, init: i64) -> Tile {
        let (fan, _acc) = induction_cycle(items, threshold, init);
        let mut op = fan.branch();
        let guard = op.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut sched);
        pull_to_terminal(&mut sched, &mut producer)
    }

    /// `acc := 0; for i in [1,2,3,4]: if i > 2: acc += i` driven through the whole
    /// induction-store operator: the guard fires at positions 2,3 (items 3,4); the
    /// changelog carries a sparse two-change history but the accumulator folds to
    /// the carry-forward total `7`, and the frontier covers the full extent.
    #[test]
    fn induction_store_conditional_write_e2e() {
        let tile = drive_induction(&[1, 2, 3, 4], 2, 0);
        assert!(validate_tile(&tile));
        assert!(
            tile.is_terminal(),
            "a complete batch source drives the store terminal"
        );
        let acc = acct("acc");
        // Final accumulator value: 0 (carry) → 0 (carry) → 3 → 7.
        assert_eq!(store_current(&tile, &acc).map(|(_, v)| v), Some(int(7)));
        assert_eq!(
            store_change_positions(&tile),
            vec![pos(2), pos(3)],
            "the two firing positions (items 3, 4); the rest carry, and the init is the \
             store's seed rather than a change"
        );
    }

    /// A plain (unconditional) `mut` loop is the degenerate `commit`-everywhere
    /// case: `acc := 10; for i in [1,2,3]: acc += i` → 16, a dense changelog.
    #[test]
    fn induction_store_unconditional_write_e2e() {
        let tile = drive_induction(&[1, 2, 3], i64::MIN, 10);
        assert!(validate_tile(&tile));
        assert!(tile.is_terminal());
        assert_eq!(
            store_current(&tile, &acct("acc")).map(|(_, v)| v),
            Some(int(16))
        );
        assert_eq!(
            store_change_positions(&tile),
            vec![pos(0), pos(1), pos(2)],
            "every committing position (a dense changelog), with the init held as the \
             store's seed rather than a change"
        );
    }

    /// Releasing a reader's consumed prefix bounds the changelog: the store GCs
    /// the FanOut-intersected prefix, **keeping the carry source a live position reads**, so a
    /// long-lived loop's retained changelog is O(keys) rather than O(positions).
    /// `acc := 10; for i in [1,2,3]: acc += i` renders a 3-position dense changelog;
    /// after a reader releases through position 1, only the latest write survives —
    /// and the accumulator still reads its correct final value.
    #[test]
    fn induction_store_release_bounds_changelog_keeping_latest() {
        let (fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 10); // unconditional
        let mut op = fan.branch();
        let guard = op.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut sched);

        let full = pull_to_terminal(&mut sched, &mut producer);
        assert_eq!(
            store_change_positions(&full).len(),
            3,
            "full dense changelog: one write per position"
        );

        // A reader consumed loop positions ≤ 1.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(1)),
        )));

        let bounded = producer.get(producer.tiling().universal_guard());
        assert!(validate_tile(&bounded));
        assert_eq!(
            store_current(&bounded, &acc).map(|(_, v)| v),
            Some(int(16)),
            "the accumulator still reads its correct final value after GC"
        );
        assert_eq!(
            store_change_positions(&bounded).len(),
            1,
            "GC drops the superseded prefix (positions 0, 1), keeping only \
             the latest write (position 2) — the changelog no longer grows with positions"
        );
    }

    /// Build an `InductionStore` behind a fan and read `acc` densely over the loop
    /// extent via `StoreDenseRead`; return the dense `Fun(D, V)` values in order.
    fn dense_read(items: &[i64], threshold: i64, init: i64) -> Vec<i64> {
        let (fan, acc) = induction_cycle(items, threshold, init);
        let mut reader = StoreDenseRead::new(fan.branch(), acc, value_extent(), true);
        let guard = reader.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut sched);
        // The cycle advances one position per pull, so the dense read converges
        // over several pulls rather than one.
        let tile = pull_to_terminal(&mut sched, &mut producer);
        assert!(validate_tile(&tile));
        let Tile::DataFunction { codomain, .. } = tile else {
            panic!("dense read is a Function");
        };
        let Tile::Scalar(col) = *codomain else {
            panic!("dense read codomain is a scalar column");
        };
        (0..col.len())
            .map(|i| match col.index_at(i) {
                Value::Int(v) => v,
                other => panic!("dense read value is an Int, got {other:?}"),
            })
            .collect()
    }

    /// The dense per-position read of a **conditional** accumulator: the guard
    /// (`i > 2`) fires at positions 2, 3, so `acc` is `[0, 0, 3, 7]` — leading
    /// carries fold to the `init` (0), then the running total. This is the shape a
    /// co-iterated read (`zip(iter, acc)`) consumes, recovered from the sparse
    /// two-change changelog by folding at every extent position.
    #[test]
    fn dense_read_conditional_accumulator_carries_forward() {
        assert_eq!(dense_read(&[1, 2, 3, 4], 2, 0), vec![0, 0, 3, 7]);
    }

    /// The dense read of a plain (unconditional) accumulator: every position
    /// writes, so `acc := 10; acc += i` over `[1,2,3]` reads `[11, 13, 16]` — a
    /// dense function with no carries.
    #[test]
    fn dense_read_unconditional_accumulator() {
        assert_eq!(dense_read(&[1, 2, 3], i64::MIN, 10), vec![11, 13, 16]);
    }

    /// The shared single-pass fold ([`fold_changelog_key_ascending`]) agrees with
    /// the per-tick [`fold_changelog_key`] at every query tick, for both the carry
    /// and tap policies — the invariant the O(N) rewrite of both changelog readers
    /// rests on. Uses a *sparse* changelog (a key not written at every tick) so the
    /// carry-forward vs exact-delta distinction is exercised.
    #[test]
    fn fold_changelog_ascending_matches_per_tick() {
        let mut e = CommitEngine::new(balances(&[("acc", 0)]));
        e.attempt(Proposal {
            snapshot: pos(0),
            reads: balances(&[("acc", 0)]),
            writes: balances(&[("acc", 5)]),
        }); // tick 1: acc = 5
        e.attempt(Proposal {
            snapshot: pos(1),
            reads: HashMap::new(),
            writes: balances(&[("other", 9)]),
        }); // tick 2: a different key (acc carries)
        e.attempt(Proposal {
            snapshot: pos(2),
            reads: balances(&[("acc", 5)]),
            writes: balances(&[("acc", 8)]),
        }); // tick 3: acc = 8
        let store = e.render_full_store_tile(&store_tiling(&["acc", "other"]));
        let acc = acct("acc");
        let queries: Vec<usize> = (0..=4).collect();
        for carry in [true, false] {
            let batched =
                fold_changelog_key_ascending(&store, queries.iter().copied().map(pos), &acc, carry);
            let per_tick: Vec<Option<Value>> = queries
                .iter()
                .map(|t| fold_changelog_key(&store, &pos(*t), &acc, carry))
                .collect();
            assert_eq!(batched, per_tick, "ascending fold diverges (carry={carry})");
        }
    }

    /// A **carry** dense reader must not over-release the changelog. A sparse
    /// accumulator writes at position 0 (tick 1) and position 3 (tick 4), carrying
    /// positions 1, 2 from the *tick-1* write. Releasing the leading positions must
    /// not strand tick 1 (positions 1, 2's carry source): the reader forwards a
    /// store release that stops *below* the earliest still-needed carry source, so
    /// tick 1 survives and a re-read after releasing position 0 still folds
    /// positions 1, 2 to the tick-1 write (5), not the seed (0).
    #[test]
    fn carry_dense_reader_does_not_over_release_store() {
        // Writes iff `item > 3`: over [5, 1, 1, 9] that fires at positions 0 and 3.
        let (fan, acc) = induction_cycle(&[5, 1, 1, 9], 3, 0);
        let mut reader = StoreDenseRead::new(fan.branch(), acc, value_extent(), true);
        let guard = reader.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut sched);

        let mut read_values = |p: &mut Box<dyn TileProducer>| -> Vec<(usize, i64)> {
            // The cycle advances one position per pull, so the first full read
            // converges over several pulls; a later re-read is already terminal
            // and returns immediately.
            let tile = pull_to_terminal(&mut sched, p);
            let Tile::DataFunction {
                domain, codomain, ..
            } = tile
            else {
                panic!("dense read is a Function");
            };
            let Tile::Scalar(col) = *codomain else {
                panic!("dense read values is a scalar column");
            };
            (0..domain.len())
                .map(|i| match (domain.index_at(i), col.index_at(i)) {
                    (Value::UInt(p), Value::Int(v)) => (p, v),
                    other => panic!("unexpected dense read entry {other:?}"),
                })
                .collect()
        };

        // Full read: acc = 5 (pos 0), 5, 5 (carries), 14 (pos 3).
        assert_eq!(
            read_values(&mut producer),
            vec![(0, 5), (1, 5), (2, 5), (3, 14)]
        );
        // Release the leading position, then re-read. The carry source (tick 1)
        // must survive so positions 1, 2 still fold to 5 — not the seed 0.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(0)),
        )));
        let after = read_values(&mut producer);
        for (p, v) in [(1usize, 5i64), (2, 5), (3, 14)] {
            assert!(
                after.contains(&(p, v)),
                "position {p} must still read {v} after releasing position 0; got {after:?}"
            );
        }
    }

    /// Records the domain-release watermarks a producer receives — lets a test
    /// observe what `StoreDenseRead` forwards to the store *without* a second
    /// FanOut branch (which would perturb GC via the release intersection).
    /// A guard naming a row whole takes that row's store out of the tree, and leaves a
    /// row it names only part of alone. This is what keeps the render and the engines
    /// saying the same thing: the render walks the tree, so a row dropped here is a row
    /// the next render cannot rebuild.
    #[test]
    fn remove_covered_drops_the_rows_the_guard_names_whole() {
        let mut engines = Engines::Rows(Vec::new());
        let mut seed = || CommitEngine::new(balances(&[("n", 0)]));
        for row in 0..3u64 {
            engines.store_at(&[Value::UInt(row as usize)], &mut seed);
        }
        // Rows 0 and 1 whole; row 2 only at its first position, which names part of it.
        engines.remove_covered(&TileGuard::Or(vec![
            TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
                1,
            )))),
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                FunctionGuard::Domain(Predicate::qualified(
                    Predicate::point(Value::UInt(2)),
                    Predicate::at_or_below(Value::UInt(0)),
                )),
            )))),
        ]));
        let left: Vec<&Value> = engines.rows().iter().map(|(row, _)| row).collect();
        assert_eq!(left, vec![&Value::UInt(2)]);
    }

    /// A released prefix does not strand the carry it holds. Over `[5, 1, 1, 9]` gated by
    /// `item > 3`, `acc` writes at positions 0 and 3 and carries between, so positions 1
    /// and 2 read the write at position 0 — which a release of position 0 puts inside the
    /// reclaimed prefix. They still read 5, because the reclaim keeps the boundary carry
    /// source ([`CommitEngine::gc_released_prefix`]) rather than the reader holding a
    /// bound of its own back.
    #[test]
    fn a_released_prefix_does_not_strand_a_live_carry() {
        let (fan, acc) = induction_cycle(&[5, 1, 1, 9], 3, 0);
        let mut reader = StoreDenseRead::new(fan.branch(), acc, value_extent(), true);
        let guard = reader.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut sched);

        // The cycle advances one position per pull, so drive the fold to convergence.
        let tile = pull_to_terminal(&mut sched, &mut producer);
        assert_eq!(dense_values(&tile), vec![5, 5, 5, 14]);

        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(0)),
        )));
        let tile = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            dense_values(&tile),
            vec![5, 5, 14],
            "positions 1 and 2 carry the write at the released position 0"
        );

        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(2)),
        )));
        let tile = producer.get(producer.tiling().universal_guard());
        assert_eq!(dense_values(&tile), vec![14]);
    }

    /// Two writers touch the *same* key from the same snapshot: the first
    /// commits, the second is stale (no tick consumed) and must retry.
    #[test]
    fn overlapping_keys_conflict() {
        let mut e = CommitEngine::new(balances(&[("alice", 100)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 70)]),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        // B read alice @snap 0, but alice was written at tick 1 → stale.
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 50)]),
            }),
            CommitOutcome::Stale
        );
        assert_eq!(e.decided_watermark(), Some(&pos(1)));
        assert_eq!(e.read_as_of(&pos(1), &acct("alice")), Some(int(70)));
    }

    /// Two writers touch *disjoint* keys from the same snapshot: both commit, no
    /// conflict — concurrency for free.
    #[test]
    fn disjoint_keys_commit_concurrently() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 70)]),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        // B read/write bob @snap 0; A wrote alice, not bob → no conflict.
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("bob", 50)]),
                writes: balances(&[("bob", 80)]),
            }),
            CommitOutcome::Committed { ts: pos(2) }
        );
        assert_eq!(e.read_as_of(&pos(2), &acct("alice")), Some(int(70)));
        assert_eq!(e.read_as_of(&pos(2), &acct("bob")), Some(int(80)));
    }

    /// A per-key read folds past ticks that wrote *other* keys — those ticks are
    /// decided-absent for this key, their value holding from the latest earlier
    /// change.
    #[test]
    fn read_folds_past_other_keys() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        e.attempt(Proposal {
            snapshot: pos(0),
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: alice
        e.attempt(Proposal {
            snapshot: pos(1),
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("bob", 20)]),
        }); // tick 2: bob

        // alice as of 2 folds past tick 2 (which wrote bob) back to tick 1.
        assert_eq!(e.read_as_of(&pos(2), &acct("alice")), Some(int(70)));
        assert_eq!(e.read_as_of(&pos(2), &acct("bob")), Some(int(20)));

        // The rendered store confirms tick 2 is decided-absent for alice — the
        // frontier snapshot still folds her value forward from tick 1.
        let tile = e.render_full_store_tile(&store_tiling(&["alice", "bob"]));
        assert_eq!(
            store_current(&tile, &acct("alice")),
            Some((pos(2), int(70)))
        );
        assert_eq!(store_current(&tile, &acct("bob")), Some((pos(2), int(20))));
    }

    /// Read-side commit-log GC: `gc_released_prefix(through)` reclaims released
    /// versions at ticks `≤ through`, keeping the carry source a live position reads.
    /// This is the engine half of the long-lived-store bound — the same rule for a
    /// superseded scalar and a merged collection prefix.
    #[test]
    fn gc_released_prefix_keeps_latest_drops_released_history() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        // Three sequential writes — ticks 1, 2, 3 all write `n`.
        for i in 1..=3 {
            let snap = e
                .decided_watermark()
                .cloned()
                .expect("a commit engine is decided");
            assert_eq!(
                e.attempt(Proposal {
                    snapshot: snap.clone(),
                    reads: balances(&[("n", i - 1)]),
                    writes: balances(&[("n", i)]),
                }),
                CommitOutcome::Committed {
                    ts: pos(i as usize)
                }
            );
        }
        // Consumers released through tick 2. Tick 3 is above the release and stands, and
        // it is the only live position's own write, so the whole prefix goes — there is
        // no live position left that folds back into it.
        e.gc_released_prefix(&pos(2));
        assert_eq!(e.read_as_of(&pos(3), &acct("n")), Some(int(3)));
        // The released versions are gone from the changelog, so a read there folds back
        // to the seed. Reads at released ticks are out of contract — every consumer
        // promised never to ask again — and the seed is not reclaimable in any case,
        // being the base of the fold rather than a version of it.
        assert_eq!(e.read_as_of(&pos(2), &acct("n")), Some(int(0)));
        // Re-running with the same prefix is a no-op (idempotent).
        e.gc_released_prefix(&pos(2));
        assert_eq!(e.read_as_of(&pos(3), &acct("n")), Some(int(3)));
    }

    /// A key whose carry source lies inside the released prefix. The engine runs
    /// positions 1 to 5, writing `n` at 1 and 5 and carrying between; a release through 3
    /// leaves position 4 live, and position 4's value is the write at 1 — inside the
    /// released prefix, and not `n`'s latest.
    #[test]
    fn gc_released_prefix_keeps_a_live_positions_carry_source() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        for tick in 1..=5 {
            let write = match tick {
                1 => Some(balances(&[("n", 10)])),
                5 => Some(balances(&[("n", 50)])),
                _ => None,
            };
            e.step(pos(tick), write);
        }
        e.gc_released_prefix(&pos(3));
        assert_eq!(e.read_as_of(&pos(4), &acct("n")), Some(int(10)));
    }

    /// Every decided position released while the loop runs on. The key's last write is at
    /// or below the boundary, so the position the store runs next folds back to it — the
    /// case where "no live position reaches it" would be read off a domain that has not
    /// caught up rather than off one that never will.
    #[test]
    fn gc_released_prefix_keeps_a_carry_source_a_later_position_will_read() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        for tick in 1..=3 {
            e.step(pos(tick), Some(balances(&[("n", tick as i64 * 10)])));
        }
        e.gc_released_prefix(&pos(3));
        e.step(pos(4), None);
        assert_eq!(e.read_as_of(&pos(4), &acct("n")), Some(int(30)));
    }

    /// The same shape with nothing left to read the prefix entry: `n` is written at every
    /// position, so the earliest live position reads its own write and the carry source at
    /// the boundary is reachable from nowhere. It goes with the rest of the prefix.
    #[test]
    fn gc_released_prefix_drops_a_carry_source_no_live_position_reaches() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        for tick in 1..=5 {
            e.step(pos(tick), Some(balances(&[("n", tick as i64 * 10)])));
        }
        e.gc_released_prefix(&pos(3));
        assert_eq!(e.read_as_of(&pos(5), &acct("n")), Some(int(50)));
        assert_eq!(e.read_as_of(&pos(4), &acct("n")), Some(int(40)));
        // Nothing at or below the boundary survives: every live position writes its own.
        assert_eq!(e.read_as_of(&pos(3), &acct("n")), Some(int(0)));
    }

    /// Repeated writes to one key, each reading the prior commit: every attempt
    /// commits, so the timestamp domain stays dense — the uncontended degeneration
    /// of allocate-on-commit, where the tick sequence has no gaps because nothing
    /// ever goes stale.
    #[test]
    fn repeated_writes_to_one_key_are_dense() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        for i in 1..=4 {
            let snap = e
                .decided_watermark()
                .cloned()
                .expect("a commit engine is decided");
            let Value::Int(prev) = e.read_as_of(&snap, &acct("n")).unwrap() else {
                unreachable!()
            };
            assert_eq!(
                e.attempt(Proposal {
                    snapshot: snap.clone(),
                    reads: balances(&[("n", prev)]),
                    writes: balances(&[("n", prev + 1)]),
                }),
                CommitOutcome::Committed { ts: pos(i) }
            );
        }
        assert_eq!(e.decided_watermark(), Some(&pos(4)));
        assert_eq!(e.read_as_of(&pos(4), &acct("n")), Some(int(4)));
    }

    /// Serializability property (seeded, deterministic — no threads, no `rand`):
    /// drive the OCC engine with many random multi-writer schedules and assert
    /// the committed history is observationally equivalent to a **serial**
    /// execution. Every round takes one shared snapshot and proposes *all* pending
    /// transactions against it (concurrent writers racing from one frontier); the
    /// engine commits the winners and marks the rest stale to retry — the exact
    /// contention the hand-written cases can't cover. The oracle replays the
    /// committed transactions in commit-tick order against a fresh serial store
    /// and requires the final state to match, which is the "serial denotation,
    /// concurrent engine" invariant the whole design rests on.
    #[test]
    fn occ_serializable_under_random_schedules() {
        // Tiny xorshift64 PRNG — fully reproducible, no dependency.
        struct Rng(u64);
        impl Rng {
            fn next_u64(&mut self) -> u64 {
                let mut x = self.0;
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                self.0 = x;
                x
            }
            fn below(&mut self, n: u64) -> usize {
                (self.next_u64() % n) as usize
            }
        }

        const KEYS: u64 = 4;
        let key = |i: usize| store_key(&format!("k{i}"), Value::Unit);
        let read_int = |m: &HashMap<Value, Value>, k: usize| match &m[&key(k)] {
            Value::Int(n) => *n,
            other => unreachable!("key holds an int, got {other:?}"),
        };

        // A transaction's footprint: keys it reads and keys it writes. The body is
        // pure: each written key gets `1 + Σ(read values)`, so a write depends on
        // the reads and a concurrent commit to a read key genuinely invalidates it.
        struct Txn {
            reads: Vec<usize>,
            writes: Vec<usize>,
        }

        for seed in 1..=300u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);

            let n_txns = 3 + rng.below(7);
            let txns: Vec<Txn> = (0..n_txns)
                .map(|_| {
                    let nr = 1 + rng.below(3);
                    let nw = 1 + rng.below(3);
                    let reads: Vec<usize> = (0..nr).map(|_| rng.below(KEYS)).collect();
                    let writes: Vec<usize> = (0..nw).map(|_| rng.below(KEYS)).collect();
                    Txn { reads, writes }
                })
                .collect();

            let init: HashMap<Value, Value> = (0..KEYS as usize)
                .map(|i| (key(i), Value::Int(0)))
                .collect();
            let mut engine = CommitEngine::new(init.clone());

            // Drive to completion. Each round snapshots the frontier once and
            // proposes every pending txn against it; the first always validates
            // (nothing committed since the snapshot when it is attempted), so at
            // least one commits per round and the loop makes progress.
            let mut pending: Vec<usize> = (0..n_txns).collect();
            let mut commit_order: Vec<usize> = Vec::new();
            while !pending.is_empty() {
                let snap = engine.watermark();
                let proposals: Vec<(usize, Proposal)> = pending
                    .iter()
                    .map(|&ti| {
                        let t = &txns[ti];
                        let reads: HashMap<Value, Value> = t
                            .reads
                            .iter()
                            .map(|&k| (key(k), engine.read_as_of(snap, &key(k)).unwrap()))
                            .collect();
                        let sum: i64 = t.reads.iter().map(|&k| read_int(&reads, k)).sum();
                        let writes: HashMap<Value, Value> = t
                            .writes
                            .iter()
                            .map(|&k| (key(k), Value::Int(sum + 1)))
                            .collect();
                        (
                            ti,
                            Proposal {
                                snapshot: snap.clone(),
                                reads,
                                writes,
                            },
                        )
                    })
                    .collect();

                let mut next_pending = Vec::new();
                for (ti, p) in proposals {
                    match engine.attempt(p) {
                        CommitOutcome::Committed { .. } => commit_order.push(ti),
                        CommitOutcome::Stale => next_pending.push(ti),
                    }
                }
                assert!(
                    next_pending.len() < pending.len(),
                    "seed {seed}: a round made no progress (should be impossible)"
                );
                pending = next_pending;
            }

            // Oracle: replay the committed transactions serially in commit-tick
            // order against a fresh store. Backward validation guarantees each
            // committed txn read the same values it would read here, so the writes
            // recompute identically — the final states must match key for key.
            let mut serial = init.clone();
            for &ti in &commit_order {
                let t = &txns[ti];
                let sum: i64 = t.reads.iter().map(|&k| read_int(&serial, k)).sum();
                for &k in &t.writes {
                    serial.insert(key(k), Value::Int(sum + 1));
                }
            }

            let wm = engine.watermark();
            for i in 0..KEYS as usize {
                assert_eq!(
                    engine.read_as_of(wm, &key(i)),
                    Some(serial[&key(i)].clone()),
                    "seed {seed}, key {i}: engine state diverged from the serial replay"
                );
            }
        }
    }

    /// The full multi-key store renders as `CommitTimestamp ⇀ {key: value}`: one
    /// changelog per key, so a tick whose write set names some keys and not others is a
    /// tick those keys' changelogs carry and the rest omit. Heterogeneity per tick needs
    /// no encoding of its own — it is which changelogs a tick appears in.
    #[test]
    fn full_store_renders_heterogeneous_write_sets() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        e.attempt(Proposal {
            snapshot: pos(0),
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: writes only alice
        e.attempt(Proposal {
            snapshot: pos(0),
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("alice", 70), ("bob", 30)]),
        }); // tick 2: writes alice AND bob (different key set than tick 1)

        let tile = e.render_full_store_tile(&store_tiling(&["alice", "bob"]));
        assert!(validate_tile(&tile));
        let Tile::Store { frontier, .. } = &tile else {
            panic!("expected Store");
        };
        assert_eq!(
            row_frontier(frontier, 0),
            Predicate::at_or_below(Value::UInt(2))
        );
        // The init is the store's seed, not a change. Tick 1 = {alice}; tick 2 =
        // {alice, bob}. So alice's changelog carries every tick and bob's skips the
        // one that passed him over — the tick numbering is shared, the ticks held are
        // not.
        assert_eq!(seed_of(&tile, "alice"), Some(int(100)));
        assert_eq!(seed_of(&tile, "bob"), Some(int(50)));
        assert_eq!(
            changelog_of(&tile, "alice"),
            vec![(1, int(70)), (2, int(70))]
        );
        assert_eq!(changelog_of(&tile, "bob"), vec![(2, int(30))]);
    }

    /// A store key's seed — its value before any change.
    fn seed_of(tile: &Tile, key: &str) -> Option<Value> {
        store_seed_value(tile, &store_key(key, Value::Unit))
    }

    /// A store key's changelog as `(tick, value)` pairs.
    fn changelog_of(tile: &Tile, key: &str) -> Vec<(usize, Value)> {
        let (ticks, values) = tile.store_changelog(key).expect("a key of this store");
        (0..ticks.len())
            .map(|i| match ticks.index_at(i) {
                Value::UInt(t) => (t, changelog_value(values, i)),
                other => panic!("a change tick is a UInt; got {other:?}"),
            })
            .collect()
    }

    // --- The engine as a live tile operator ---------------------------------

    /// Keys are account names (strings); values are balances (ints). These type a
    /// *proposal's* read and write sets, which ride one cell per attempt.
    fn key_extent() -> Extent {
        Extent::Base(BaseType::String)
    }
    fn value_extent() -> Extent {
        Extent::Base(BaseType::Int)
    }

    /// A store's per-key value tilings over `accounts`: one key each, holding a balance.
    fn store_values(accounts: &[&str]) -> HashMap<String, Tiling> {
        accounts
            .iter()
            .map(|a| ((*a).to_string(), Tiling::Scalar(value_extent())))
            .collect()
    }

    /// The whole store tiling over `accounts`, which a render needs to name its keys.
    fn store_tiling(accounts: &[&str]) -> Tiling {
        full_store_tiling(commit_clock_domain(), store_values(accounts))
    }

    /// The store's per-key value tilings for exactly the keys `init` seeds.
    fn keyed_like(init: &HashMap<Value, Value>) -> HashMap<String, Tiling> {
        init.keys()
            .map(|k| {
                let name = store_key_name(k).expect("an initial state is keyed by store keys");
                (name.to_string(), Tiling::Scalar(value_extent()))
            })
            .collect()
    }

    /// The decoded store: per-tick delta maps, sorted by tick.
    type StoreEntries = Vec<(Position, HashMap<Value, Value>)>;

    /// Decode a full store tile into `(frontier, entries)`, or `None` if the
    /// store is not yet decided (empty / undecided). Reassembles the per-tick write sets
    /// from the per-key changelogs — the writer-side counterpart of
    /// [`CommitEngine::render_full_store_tile`].
    fn decode_store(tile: &Tile) -> Option<(Position, StoreEntries)> {
        let frontier = store_frontier(tile)?;
        // The store's value before any change leads the fold: on the commit clock the
        // seed is what tick 0 — the state after no transaction — holds.
        let seed: HashMap<Value, Value> = tile
            .store_keys()
            .filter_map(|name| {
                let key = store_key(name, Value::Unit);
                Some((key.clone(), store_seed_value(tile, &key)?))
            })
            .collect();
        let entries = std::iter::once((commit_clock_start(), seed))
            .chain(store_change_positions(tile).into_iter().map(|tick| {
                let delta = tile
                    .store_keys()
                    .filter_map(|name| {
                        let key = store_key(name, Value::Unit);
                        Some((key.clone(), store_delta_at(tile, &tick, &key)?))
                    })
                    .collect();
                (tick, delta)
            }))
            .collect();
        Some((frontier, entries))
    }

    /// Fold the per-tick deltas with `tick ≤ t` into the cumulative state map.
    /// Later ticks overwrite earlier keys; ticks that wrote only other keys are
    /// folded past (decided-absent for the keys they omit).
    fn state_as_of(
        entries: &[(Position, HashMap<Value, Value>)],
        t: &Position,
    ) -> HashMap<Value, Value> {
        let mut state = HashMap::new();
        for (tick, delta) in entries {
            if tick > t {
                break;
            }
            for (k, v) in delta {
                state.insert(k.clone(), v.clone());
            }
        }
        state
    }

    /// `(frontier, value of `key`)` from a full store tile — fold the cumulative
    /// state at the frontier and read `key` as an int. `None` if undecided or the
    /// key has no int value there.
    fn store_at(tile: &Tile, key: &Value) -> Option<(Position, i64)> {
        let (frontier, entries) = decode_store(tile)?;
        match state_as_of(&entries, &frontier).get(key) {
            Some(Value::Int(v)) => Some((frontier, *v)),
            _ => None,
        }
    }

    /// Wire `input` as the operator's single writer and subscribe, returning the
    /// store producer.
    fn subscribe_commit(
        input: Box<dyn TileOperator>,
        init: HashMap<Value, Value>,
    ) -> Box<dyn TileProducer> {
        let writes = all_writers_write(&init, 1);
        let mut op = CommitOperator::new(init.clone(), keyed_like(&init), writes);
        (op.writer_input_setter(0))(input);
        let guard = op.tiling().universal_guard();
        op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new())
    }

    /// A test source operator that emits a fixed proposal stream as one
    /// terminal `DataFunction(step → {snap, read, write})` tile.
    struct ProposalSource {
        tiling: Tiling,
        tile: Tile,
    }

    impl ProposalSource {
        fn new(proposals: &[EmittedProposal]) -> Self {
            Self {
                tiling: proposal_stream_tiling(&key_extent(), &value_extent()),
                tile: proposal_tile(proposals, 0, true),
            }
        }
    }

    impl TileOperator for ProposalSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(ProposalSourceProducer {
                base: ProducerBase::new(ProposalSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
            })
        }
    }

    struct ProposalSourceProducer {
        base: ProducerBase,
        tile: Tile,
    }

    impl TileProducer for ProposalSourceProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            honoring_release(&self.tile, self.obsolete_guard())
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// The conflict scenario, now driven end-to-end through the tile protocol:
    /// subscribe → get drains the map-encoded proposal stream into the engine →
    /// full store tile.
    #[test]
    fn live_producer_conflict() {
        // A: read pool 100, write 30; B: read pool 100, write 50 → conflict.
        let source = ProposalSource::new(&[
            (
                pos(0),
                balances(&[("pool", 100)]),
                balances(&[("pool", 30)]),
            ),
            (
                pos(0),
                balances(&[("pool", 100)]),
                balances(&[("pool", 50)]),
            ),
        ]);
        let mut producer = subscribe_commit(Box::new(source), balances(&[("pool", 100)]));

        let tile = producer.get(producer.tiling().universal_guard());
        assert!(validate_tile(&tile));
        let Tile::Store {
            frontier, terminal, ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        // Tick 1 (A) committed; B's grant was stale → no tick consumed. The
        // (materialized) writer is terminal, so the store is closed at watermark 1.
        assert_eq!(changelog_of(&tile, "pool"), vec![(1, int(30))]);
        assert_eq!(
            row_frontier(frontier, 0),
            Predicate::at_or_below(Value::UInt(1))
        );
        assert!(*terminal);
        assert_eq!(store_at(&tile, &acct("pool")), Some((pos(1), 30)));
    }

    /// Sequential (non-conflicting) writers drive a dense store through the operator.
    #[test]
    fn live_producer_sequential() {
        let source = ProposalSource::new(&[
            (
                pos(0),
                balances(&[("pool", 100)]),
                balances(&[("pool", 30)]),
            ),
            (pos(1), balances(&[("pool", 30)]), balances(&[("pool", 20)])),
        ]);
        let mut producer = subscribe_commit(Box::new(source), balances(&[("pool", 100)]));

        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::Store {
            frontier, terminal, ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        assert_eq!(seed_of(&tile, "pool"), Some(int(100)));
        assert_eq!(
            changelog_of(&tile, "pool"),
            vec![(1, int(30)), (2, int(20))]
        );
        // Both proposals committed and the writer is terminal → store closed at
        // watermark 2 (the frontier keeps its numeric watermark; terminality is
        // the separate flag).
        assert_eq!(
            row_frontier(frontier, 0),
            Predicate::at_or_below(Value::UInt(2))
        );
        assert!(*terminal);
        assert_eq!(store_at(&tile, &acct("pool")), Some((pos(2), 20)));
    }

    // --- The body↔store cycle -----------------------------------------------

    /// A test writer body that models a single-writer counter loop on one store
    /// `key`: each pull it folds the store to read `key`'s value and proposes
    /// `value + 1`, reporting the frontier it observed as its snapshot. Appends
    /// one proposal per pull, up to `n` steps. It reads the store through its
    /// `store_op` input — which, in the cycle, is a branch of the commit
    /// operator's own output.
    struct CounterBody {
        tiling: Tiling,
        store_op: Box<dyn TileOperator>,
        key: Value,
        n: usize,
    }

    impl CounterBody {
        fn new(store_op: Box<dyn TileOperator>, key: Value, n: usize) -> Self {
            Self {
                tiling: proposal_stream_tiling(&key_extent(), &value_extent()),
                store_op,
                key,
                n,
            }
        }
    }

    impl TileOperator for CounterBody {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let store_guard = self.store_op.tiling().universal_guard();
            let store_producer = self
                .store_op
                .subscribe(store_guard, Box::new(|| {}), scheduler);
            Box::new(CounterBodyProducer {
                base: ProducerBase::new(CounterBodyProducer::alloc_id(), &self.tiling),
                store_producer,
                key: self.key.clone(),
                window: ProposalWindow::new(),
                n: self.n,
            })
        }
    }

    struct CounterBodyProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        key: Value,
        /// Proposals appended and not yet committed-and-released.
        window: ProposalWindow,
        n: usize,
    }

    impl TileProducer for CounterBodyProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            if self.window.next_position() < self.n {
                let store = store_at(
                    &self
                        .store_producer
                        .get(self.store_producer.tiling().universal_guard()),
                    &self.key,
                );
                if let Some((frontier, v)) = store {
                    self.window.push((
                        frontier,
                        HashMap::from([(self.key.clone(), int(v))]),
                        HashMap::from([(self.key.clone(), int(v + 1))]),
                    ));
                }
            }
            self.window.tile(self.window.next_position() == self.n)
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.window.release(&obsolete_guard);
        }
    }

    /// A single writer reads the store and proposes increments through the
    /// commit operator, reading its own committed output back via a cyclic
    /// `FanOut`. Each pull advances the cycle one step (the first pull
    /// bootstraps: the body sees the empty cached store and proposes nothing).
    #[test]
    fn single_writer_cycle() {
        let init = balances(&[("n", 0)]);
        let writes = all_writers_write(&init, 1);
        let commit = CommitOperator::new(init.clone(), keyed_like(&init), writes);
        let set_writer = commit.writer_input_setter(0);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        // The body reads a branch of the store (the operator's own output).
        let body = CounterBody::new(store_fan.branch(), acct("n"), 3);
        set_writer(Box::new(body));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut sched);

        // Drive the cycle: bootstrap + 3 commits + a fixpoint pull, with margin.
        let latest = pull_laps(&mut sched, &mut *producer, 7, |_| false);
        // Store: init 0 @0, then 1@1, 2@2, 3@3 — the counter reached 3.
        assert_eq!(store_at(&latest, &acct("n")), Some((pos(3), 3)));
    }

    /// What a [`TransactDriver`] emitted over a run: the largest live window it
    /// ever rendered, and how many attempts it ever posted.
    ///
    /// Both read straight off the tile the driver hands its consumers — the live
    /// window *is* that tile's domain, and an attempt is one position of it — so
    /// the probe observes the invariant without standing in for any part of the
    /// release discipline that establishes it.
    #[derive(Default)]
    struct DriverObservation {
        max_window: usize,
        attempts: usize,
    }

    /// A pass-through in front of a driver that records each tile it emits.
    struct DriverProbe {
        inner: Box<dyn TileOperator>,
        seen: Rc<RefCell<DriverObservation>>,
    }

    struct DriverProbeProducer {
        base: ProducerBase,
        inner: Box<dyn TileProducer>,
        seen: Rc<RefCell<DriverObservation>>,
    }

    impl TileOperator for DriverProbe {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            self.inner.tiling()
        }
        fn subscribe(
            &mut self,
            intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let inner = self.inner.subscribe(intent_guard, consumer, scheduler);
            Box::new(DriverProbeProducer {
                base: ProducerBase::new(DriverProbeProducer::alloc_id(), self.inner.tiling()),
                inner,
                seen: self.seen.clone(),
            })
        }
    }

    impl TileProducer for DriverProbeProducer {
        impl_producer_base!();
        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            let tile = self.inner.get(projection_guard);
            if let Tile::DataFunction { domain, .. } = &tile {
                let mut seen = self.seen.borrow_mut();
                seen.max_window = seen.max_window.max(domain.len());
                // Positions are absolute and one per attempt, so the highest ever
                // seen counts the attempts even after the window compacts.
                if let Some(Value::UInt(top)) =
                    newest_body_position(&tile).map(Position::into_value)
                {
                    seen.attempts = seen.attempts.max(top + 1);
                }
            }
            tile
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.inner.release(obsolete_guard);
        }
    }

    /// Wire one real [`TransactDriver`]/[`TransactWriter`] pair per entry of
    /// `draws` against a shared single-key [`CommitOperator`], and return the
    /// store fan with each driver's observation handle.
    ///
    /// Every writer reads *and* writes the one key, so no two attempts can commit
    /// at the same frontier: each pull one writer wins and the rest go stale and
    /// re-attempt. That is the contention this exists to produce.
    fn contending_writer_cycle(
        init: i64,
        draws: &[&[i64]],
    ) -> (Rc<FanOut>, Vec<Rc<RefCell<DriverObservation>>>) {
        let pool = acct("pool");
        // Every writer's static footprint is the one shared key — which is what
        // makes them contend, and what keeps the store from closing `pool` until
        // the last of them finishes.
        let commit = CommitOperator::new(
            balances(&[("pool", init)]),
            store_values(&["pool"]),
            vec![vec![pool.clone()]; draws.len()],
        );
        let setters: Vec<_> = (0..draws.len())
            .map(|w| commit.writer_input_setter(w))
            .collect();
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        let mut seen = Vec::with_capacity(draws.len());
        for (items, set_writer) in draws.iter().zip(setters) {
            let observation = Rc::new(RefCell::new(DriverObservation::default()));
            let driver = TransactDriver::new(
                store_fan.branch(),
                Box::new(ItemSource::new(items)),
                vec![pool.clone()],
                vec![value_extent()],
                value_extent(),
                // A drive built with its source, not one resuming a running
                // program.
                None,
            );
            let driver_fan = Rc::new(FanOut::new(Box::new(DriverProbe {
                inner: Box::new(driver),
                seen: observation.clone(),
            })));
            // A compiled body fans its input through a `Memo`, and that is
            // load-bearing here rather than incidental: the `Memo` releases each
            // row as it consumes it, which is the eager half of the driver's
            // release intersection. Without it the intersection would be the
            // writer's ack alone, and a superseded row could not be reclaimed
            // before its item finished.
            let body = AddIfBody::new(Box::new(Memo::new(driver_fan.branch())), i64::MIN, "pool");
            set_writer(Box::new(TransactWriter::new(
                store_fan.branch(),
                Box::new(body),
                driver_fan.branch(),
                vec![pool.clone()],
                vec![pool.clone()],
                Vec::new(),
                key_extent(),
                value_extent(),
            )));
            seen.push(observation);
        }
        (store_fan, seen)
    }

    /// **A contended item costs a flat window, not one row per retry.**
    ///
    /// Six writers each draw 1 from a pool of 100, all through the same key, so
    /// every attempt conflicts: one writer commits per pull and the other five go
    /// stale and re-attempt at the advanced frontier. A writer therefore re-poses
    /// its single item several times before winning — which is the condition the
    /// end-to-end suite never reaches, because two alternating writers make the
    /// loser retry exactly once.
    ///
    /// Under that, the driver's live window must stay at [`MAX_LIVE_ATTEMPTS`]: the
    /// writer releases everything below the position it decides, so a superseded
    /// row is reclaimed on the next release rather than waiting for the item to
    /// finish. A window that instead grew with retries would be retained rows
    /// linear in the retry count and, because the body re-renders the whole window
    /// each pull, body rows quadratic in it.
    ///
    /// The retry assertion is not decoration. It is what stops this from passing
    /// vacuously if the drain order ever stopped producing contention — a flat
    /// window over zero retries proves nothing.
    #[test]
    fn a_contended_item_keeps_the_drive_window_flat() {
        const WRITERS: usize = 6;
        let draws: Vec<&[i64]> = vec![&[-1]; WRITERS];
        let (store_fan, seen) = contending_writer_cycle(100, &draws);

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut sched);
        let latest = pull_laps(&mut sched, &mut *producer, MAX_CYCLE_PULLS, |_| false);

        // Every draw committed exactly once: the pool conserves.
        assert_eq!(
            store_at(&latest, &acct("pool")).map(|(_, v)| v),
            Some(100 - WRITERS as i64),
            "each of the {WRITERS} draws commits exactly once"
        );

        let retries: Vec<usize> = seen
            .iter()
            .map(|o| o.borrow().attempts.saturating_sub(1))
            .collect();
        assert!(
            retries.iter().any(|&r| r >= 3),
            "the schedule produced no deeply contended item ({retries:?} retries per writer), \
             so the window bound below would hold vacuously"
        );
        for (w, observation) in seen.iter().enumerate() {
            let max_window = observation.borrow().max_window;
            assert!(
                max_window <= MAX_LIVE_ATTEMPTS,
                "writer {w} retried {} times and its driver's window reached {max_window} \
                 (bound {MAX_LIVE_ATTEMPTS}) — a superseded row is not being reclaimed",
                retries[w]
            );
        }
    }

    /// One accumulated proposal: `(snapshot, read set, write set)`.
    type EmittedProposal = (Position, HashMap<Value, Value>, HashMap<Value, Value>);

    /// A writer's live proposal window: the proposals it has appended and not
    /// yet had committed-and-released, together with the absolute position of
    /// the first of them.
    ///
    /// The test writers share the offset window that [`TransactWriterProducer`]
    /// implements for real, because they are subject to the same release
    /// contract: the commit acknowledgment releases a position, and a released
    /// position must never appear in a later tile. Positions are absolute and
    /// never shift — the released prefix is dropped, the live suffix keeps its
    /// numbering — which is what lets `CommitProducer` read them by value.
    struct ProposalWindow {
        /// Absolute position of `emitted[0]`: how many proposals have been
        /// committed and released out of the front of the window.
        committed_base: usize,
        emitted: Vec<EmittedProposal>,
    }

    impl ProposalWindow {
        fn new() -> Self {
            Self {
                committed_base: 0,
                emitted: Vec::new(),
            }
        }

        fn push(&mut self, proposal: EmittedProposal) {
            self.emitted.push(proposal);
        }

        /// The absolute position the next appended proposal would take — also
        /// the number of proposals ever emitted, which survives compaction.
        fn next_position(&self) -> usize {
            self.committed_base + self.emitted.len()
        }

        fn tile(&self, terminal: bool) -> Tile {
            proposal_tile(&self.emitted, self.committed_base, terminal)
        }

        /// Drop the released prefix. Only a leading run can go: the window is
        /// contiguous, and a release of a later position with an earlier one
        /// still live would leave a hole the absolute numbering cannot express.
        fn release(&mut self, obsolete_guard: &TileGuard) {
            let TileGuard::Function(FunctionGuard::Domain(pred)) = obsolete_guard else {
                panic!("proposal stream released with a non-domain guard: {obsolete_guard:?}")
            };
            while !self.emitted.is_empty() && pred.contains(&Value::UInt(self.committed_base)) {
                self.emitted.remove(0);
                self.committed_base += 1;
            }
        }
    }

    /// Build a proposal-stream tile `step → {snap, reads, writes}` from a live
    /// window of grants starting at absolute position `base`, with the
    /// map-valued read/write sets riding `Variants` columns ([`map_to_value`]).
    fn proposal_tile(emitted: &[EmittedProposal], base: usize, terminal: bool) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints((base..base + emitted.len()).collect()),
            Box::new(Tile::Record(HashMap::from([
                (
                    F_SNAP.to_string(),
                    Tile::Scalar(ColumnValue::from_values(
                        emitted.iter().map(|p| p.0.value().clone()).collect(),
                        &Extent::Base(BaseType::UInt),
                    )),
                ),
                (
                    F_READS.to_string(),
                    Tile::Scalar(ColumnValue::Variants(
                        emitted.iter().map(|p| map_to_value(&p.1)).collect(),
                    )),
                ),
                (
                    F_WRITES.to_string(),
                    Tile::Scalar(ColumnValue::Variants(
                        emitted.iter().map(|p| map_to_value(&p.2)).collect(),
                    )),
                ),
            ]))),
            if terminal {
                Predicate::True
            } else {
                Predicate::False
            },
            BitSet::new(),
        )
    }

    /// A test writer that processes a stream of token-pool requests (`costs`),
    /// one at a time. Each pull, for the current request, it reads the store: if
    /// `pool >= cost` it proposes a grant (`write = pool - cost`); if `pool < cost`
    /// it denies *locally* (a read-only decision — no proposal) and advances to
    /// the next request. A `release` from the operator means the current grant
    /// committed, which also advances. Stale grants stay unreleased while it
    /// retries the current request against the advancing store.
    struct TokenWriter {
        tiling: Tiling,
        store_op: Box<dyn TileOperator>,
        key: Value,
        costs: Vec<i64>,
    }

    impl TokenWriter {
        fn new(store_op: Box<dyn TileOperator>, key: Value, costs: Vec<i64>) -> Self {
            Self {
                tiling: proposal_stream_tiling(&key_extent(), &value_extent()),
                store_op,
                key,
                costs,
            }
        }
    }

    impl TileOperator for TokenWriter {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let store_guard = self.store_op.tiling().universal_guard();
            let store_producer = self
                .store_op
                .subscribe(store_guard, Box::new(|| {}), scheduler);
            Box::new(TokenWriterProducer {
                base: ProducerBase::new(TokenWriterProducer::alloc_id(), &self.tiling),
                store_producer,
                key: self.key.clone(),
                costs: self.costs.clone(),
                current: 0,
                window: ProposalWindow::new(),
            })
        }
    }

    struct TokenWriterProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        key: Value,
        costs: Vec<i64>,
        /// Index of the request currently being attempted.
        current: usize,
        window: ProposalWindow,
    }

    impl TileProducer for TokenWriterProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            if self.current < self.costs.len() {
                let store = self
                    .store_producer
                    .get(self.store_producer.tiling().universal_guard());
                if let Some((frontier, pool)) = store_at(&store, &self.key) {
                    let cost = self.costs[self.current];
                    if pool < cost {
                        self.current += 1; // deny — a local read-only decision
                    } else {
                        // grant: read pool, write pool - cost
                        self.window.push((
                            frontier,
                            HashMap::from([(self.key.clone(), int(pool))]),
                            HashMap::from([(self.key.clone(), int(pool - cost))]),
                        ));
                    }
                }
            }
            let done = self.current >= self.costs.len();
            self.window.tile(done)
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            // The operator released our outstanding grant → the current request
            // committed → advance to the next request, and drop the committed
            // proposal out of the live window.
            self.current += 1;
            self.window.release(&obsolete_guard);
        }
    }

    /// Two concurrent writers draw from a shared pool of 100: A wants 70, B wants
    /// 50. They read the same snapshot and both propose grants; the operator
    /// commits A and finds B stale (no tick). B retries, now sees pool = 30 < 50,
    /// and denies locally. The pool never goes negative: it ends at 30.
    #[test]
    fn token_pool_two_writers() {
        let pool_init = balances(&[("pool", 100)]);
        let commit = CommitOperator::new(
            pool_init.clone(),
            store_values(&["pool"]),
            all_writers_write(&pool_init, 2),
        );
        let set_a = commit.writer_input_setter(0);
        let set_b = commit.writer_input_setter(1);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_a(Box::new(TokenWriter::new(
            store_fan.branch(),
            acct("pool"),
            vec![70],
        )));
        set_b(Box::new(TokenWriter::new(
            store_fan.branch(),
            acct("pool"),
            vec![50],
        )));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut sched);

        let latest = pull_laps(&mut sched, &mut *producer, 7, |_| false);
        // Exactly one draw commits: 100−70=30 < 50 and 100−50=50 < 70, so
        // whichever commits first, the other denies. The round-robin drain picks
        // the winner, so the resting value is schedule-dependent (30 or 50) but
        // always a valid, non-negative outcome — exactly one commit either way.
        let (frontier, pool) = store_at(&latest, &acct("pool")).expect("pool decided");
        assert_eq!(frontier, pos(1), "exactly one commit");
        assert!(
            pool == 30 || pool == 50,
            "one draw committed; pool = {pool}"
        );
    }

    /// Two writers each handle a *stream* of requests against a shared pool of
    /// 100, exercising per-request advancement via `release`. A = [70, 40],
    /// B = [50, 30]. Under the round-robin drain the serialization — hence which
    /// draws fit — is schedule-dependent (e.g. A's 70 then B's 30, ending 0; or
    /// B's 50 then A's 40, ending 10). The invariant that holds under *every*
    /// serialization is the token-pool safety property: a draw commits only when
    /// it fits the pool it read, so the pool never goes negative or exceeds 100.
    #[test]
    fn token_pool_multi_request() {
        let pool_init = balances(&[("pool", 100)]);
        let commit = CommitOperator::new(
            pool_init.clone(),
            store_values(&["pool"]),
            all_writers_write(&pool_init, 2),
        );
        let set_a = commit.writer_input_setter(0);
        let set_b = commit.writer_input_setter(1);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_a(Box::new(TokenWriter::new(
            store_fan.branch(),
            acct("pool"),
            vec![70, 40],
        )));
        set_b(Box::new(TokenWriter::new(
            store_fan.branch(),
            acct("pool"),
            vec![50, 30],
        )));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut sched);

        let latest = pull_laps(&mut sched, &mut *producer, 11, |_| false);
        // Which draws fit (and in what order) is schedule-dependent under the
        // round-robin drain, but the token-pool safety invariant holds under every
        // serialization: the pool is never oversold (≥ 0) and never exceeds its
        // initial 100 — a draw commits only when it fits the pool it read.
        let (_, pool) = store_at(&latest, &acct("pool")).expect("pool decided");
        assert!(
            (0..=100).contains(&pool),
            "pool stays within [0, 100]; got {pool}"
        );
    }

    // --- Prefix-reactive read (`read as of t`) ------------------------------

    /// A reader that resolves to `key`'s value as of `t` once the watermark
    /// covers `t`, and is empty (non-terminal) until then. Folding `state_as_of`
    /// at `t` walks past ticks that wrote *other* keys (decided-absent for this
    /// key) — the multi-key store is where that fold does real work. Reads the
    /// store through a branch of the commit operator's output; pulling it also
    /// drives the cycle.
    struct StoreReadAsOf {
        tiling: Tiling,
        store_op: Box<dyn TileOperator>,
        key: Value,
        t: usize,
    }

    impl StoreReadAsOf {
        fn new(store_op: Box<dyn TileOperator>, key: Value, t: usize) -> Self {
            Self {
                tiling: Tiling::Scalar(value_extent()),
                store_op,
                key,
                t,
            }
        }
    }

    impl TileOperator for StoreReadAsOf {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let store_guard = self.store_op.tiling().universal_guard();
            let store_producer = self
                .store_op
                .subscribe(store_guard, Box::new(|| {}), scheduler);
            Box::new(StoreReadAsOfProducer {
                base: ProducerBase::new(StoreReadAsOfProducer::alloc_id(), &self.tiling),
                store_producer,
                key: self.key.clone(),
                t: self.t,
            })
        }
    }

    struct StoreReadAsOfProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        key: Value,
        t: usize,
    }

    impl TileProducer for StoreReadAsOfProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            let store = self
                .store_producer
                .get(self.store_producer.tiling().universal_guard());
            // ⊥ (empty) until the watermark covers `t`; then `key`'s value there.
            let resolved = match decode_store(&store) {
                Some((frontier, entries)) if frontier >= pos(self.t) => {
                    match state_as_of(&entries, &pos(self.t)).get(&self.key) {
                        Some(Value::Int(v)) => Some(*v),
                        _ => None,
                    }
                }
                _ => None,
            };
            match resolved {
                Some(v) => Tile::Scalar(ColumnValue::from_ints(vec![v])),
                None => Tile::Scalar(ColumnValue::from_ints(vec![])),
            }
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// A read as of timestamp 2 against a counter that climbs to 3: it stays
    /// empty until the watermark reaches 2, then resolves to the value at tick 2
    /// without waiting for the writer to finish.
    #[test]
    fn read_as_of_resolves_at_watermark() {
        let init = balances(&[("n", 0)]);
        let writes = all_writers_write(&init, 1);
        let commit = CommitOperator::new(init.clone(), keyed_like(&init), writes);
        let set_writer = commit.writer_input_setter(0);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_writer(Box::new(CounterBody::new(store_fan.branch(), acct("n"), 3)));

        let mut reader = StoreReadAsOf::new(store_fan.branch(), acct("n"), 2);
        let guard = reader.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut sched);

        // Pulling the reader drives the cycle. Before the watermark reaches 2 the
        // read is ⊥ (empty); once it does, it resolves to the value at tick 2.
        let latest = pull_laps(&mut sched, &mut *producer, 8, |_| false);
        let Tile::Scalar(cv) = &latest else { panic!() };
        assert_eq!(cv.as_single(), Some(int(2)));
    }

    // --- Multi-key cycle: a bank ledger -------------------------------------

    /// A test writer that processes a stream of transfers `(from, to, amount)`
    /// against a multi-key ledger. Each pull, for the current transfer, it folds
    /// the store to read both balances: if `from ≥ amount` it proposes a
    /// two-key write set `{from: from-amount, to: to+amount}` over the read set
    /// `{from, to}`; if `from < amount` it denies *locally* and advances. A
    /// `release` means the current transfer committed → advance. Transfers over
    /// disjoint account pairs commit concurrently; overlapping ones conflict and
    /// the loser retries against the advanced store.
    struct BankWriter {
        tiling: Tiling,
        store_op: Box<dyn TileOperator>,
        transfers: Vec<(Value, Value, i64)>,
    }

    impl BankWriter {
        fn new(store_op: Box<dyn TileOperator>, transfers: Vec<(Value, Value, i64)>) -> Self {
            Self {
                tiling: proposal_stream_tiling(&key_extent(), &value_extent()),
                store_op,
                transfers,
            }
        }
    }

    impl TileOperator for BankWriter {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            let store_guard = self.store_op.tiling().universal_guard();
            let store_producer = self
                .store_op
                .subscribe(store_guard, Box::new(|| {}), scheduler);
            Box::new(BankWriterProducer {
                base: ProducerBase::new(BankWriterProducer::alloc_id(), &self.tiling),
                store_producer,
                transfers: self.transfers.clone(),
                current: 0,
                window: ProposalWindow::new(),
            })
        }
    }

    struct BankWriterProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        transfers: Vec<(Value, Value, i64)>,
        current: usize,
        window: ProposalWindow,
    }

    impl TileProducer for BankWriterProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            if self.current < self.transfers.len() {
                let store = self
                    .store_producer
                    .get(self.store_producer.tiling().universal_guard());
                if let Some((frontier, entries)) = decode_store(&store) {
                    let state = state_as_of(&entries, &frontier);
                    let (from, to, amount) = &self.transfers[self.current];
                    if let (Some(Value::Int(fb)), Some(Value::Int(tb))) =
                        (state.get(from), state.get(to))
                    {
                        if *fb >= *amount {
                            self.window.push((
                                frontier,
                                HashMap::from([(from.clone(), int(*fb)), (to.clone(), int(*tb))]),
                                HashMap::from([
                                    (from.clone(), int(fb - amount)),
                                    (to.clone(), int(tb + amount)),
                                ]),
                            ));
                        } else {
                            self.current += 1; // deny — insufficient funds
                        }
                    }
                }
            }
            let done = self.current >= self.transfers.len();
            self.window.tile(done)
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.current += 1;
            self.window.release(&obsolete_guard);
        }
    }

    /// Drive a two-writer bank cycle to a fixpoint and return the final store
    /// tile (the external store branch).
    fn run_bank_cycle(
        init: HashMap<Value, Value>,
        a: Vec<(Value, Value, i64)>,
        b: Vec<(Value, Value, i64)>,
        pulls: usize,
    ) -> Tile {
        let writes = all_writers_write(&init, 2);
        let commit = CommitOperator::new(init.clone(), keyed_like(&init), writes);
        let set_a = commit.writer_input_setter(0);
        let set_b = commit.writer_input_setter(1);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_a(Box::new(BankWriter::new(store_fan.branch(), a)));
        set_b(Box::new(BankWriter::new(store_fan.branch(), b)));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut sched);

        pull_laps(&mut sched, &mut *producer, pulls + 1, |_| false)
    }

    /// Two writers transfer over *disjoint* account pairs — A: alice→bob 30,
    /// B: carol→dave 40 — through the cyclic commit operator. Disjoint write
    /// sets never conflict, so both commit (on consecutive ticks). The full
    /// multi-key store flows through the cycle and is folded per key.
    #[test]
    fn bank_transfer_disjoint_commit() {
        let store = run_bank_cycle(
            balances(&[("alice", 100), ("bob", 100), ("carol", 100), ("dave", 100)]),
            vec![(acct("alice"), acct("bob"), 30)],
            vec![(acct("carol"), acct("dave"), 40)],
            8,
        );
        assert!(validate_tile(&store));
        assert_eq!(store_at(&store, &acct("alice")), Some((pos(2), 70)));
        assert_eq!(store_at(&store, &acct("bob")), Some((pos(2), 130)));
        assert_eq!(store_at(&store, &acct("carol")), Some((pos(2), 60)));
        assert_eq!(store_at(&store, &acct("dave")), Some((pos(2), 140)));
    }

    /// Two writers whose transfers *overlap* on `alice` — A: alice→bob 30,
    /// B: alice→carol 50 — both read alice at the same snapshot. A commits
    /// first; B's read of alice is now stale, so B retries against the advanced
    /// store and commits second. Conservation holds and alice never overdraws.
    #[test]
    fn bank_transfer_overlap_conflict_and_retry() {
        let store = run_bank_cycle(
            balances(&[("alice", 100), ("bob", 100), ("carol", 100)]),
            vec![(acct("alice"), acct("bob"), 30)],
            vec![(acct("alice"), acct("carol"), 50)],
            10,
        );
        assert!(validate_tile(&store));
        // A: alice 100→70, bob 100→130 (tick 1). B retries: alice 70→20,
        // carol 100→150 (tick 2). Total conserved at 300.
        assert_eq!(store_at(&store, &acct("alice")), Some((pos(2), 20)));
        assert_eq!(store_at(&store, &acct("bob")), Some((pos(2), 130)));
        assert_eq!(store_at(&store, &acct("carol")), Some((pos(2), 150)));
    }

    // --- StoreValueStream (projecting the store log to one key's value stream) ---

    /// A test source returning a fixed tile on every pull.
    struct FixedSource {
        tiling: Tiling,
        tile: Tile,
    }
    struct FixedSourceProducer {
        base: ProducerBase,
        tile: Tile,
    }
    impl TileOperator for FixedSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(FixedSourceProducer {
                base: ProducerBase::new(FixedSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
            })
        }
    }
    impl TileProducer for FixedSourceProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            honoring_release(&self.tile, self.obsolete_guard())
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// `StoreValueStream` projects the store's history to `key`'s commit-value
    /// stream (`Txn ⇀ Value`), observable as it commits — no terminal gate — with
    /// terminality flowing through from the store. This checks the projection
    /// (both values visible while still committing) and that `ExtractFinal`
    /// composes over it once terminal — the mechanism a surface `await_final` read
    /// compiles to, exercised here at the operator level. (A *fed-out* mutable variable read
    /// is `AsOf` over the same stream, not `ExtractFinal`.)
    #[test]
    fn store_value_stream_projects_committed_values() {
        let value_ext = Extent::Base(BaseType::Int);
        let acc = acct("acc");
        let mut engine = CommitEngine::new(HashMap::from([(acc.clone(), int(100))]));
        engine.attempt(Proposal {
            snapshot: pos(0),
            reads: HashMap::new(),
            writes: HashMap::from([(acc.clone(), int(60))]),
        });
        let store_tiling = store_tiling(&["acc"]);
        let mut store_tile = engine.render_full_store_tile(&store_tiling);

        // While committing, the stream is non-terminal but already carries both
        // the tick-0 init (100) and the committed value (60) — observable now.
        let mut stream = StoreValueStream::new(
            Box::new(FixedSource {
                tiling: store_tiling.clone(),
                tile: store_tile.clone(),
            }),
            acc.clone(),
            value_ext.clone(),
            true, // carry: hold the committed value forward
        );
        let g = stream.tiling().universal_guard();
        let mut p = stream.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        let t = p.get(p.tiling().universal_guard());
        assert!(!t.is_terminal());
        let Tile::DataFunction { codomain, .. } = &t else {
            panic!("expected a value stream")
        };
        let Tile::Scalar(cv) = codomain.as_ref() else {
            panic!("expected scalar codomain")
        };
        let vals: Vec<Value> = (0..cv.len()).map(|i| cv.index_at(i)).collect();
        assert_eq!(vals, vec![int(100), int(60)]);

        // Once the store is terminal, so is the stream — and `ExtractFinal` over
        // it gives the final value 60 (the latest committed entry).
        if let Tile::Store { terminal, .. } = &mut store_tile {
            *terminal = true;
        }
        let stream = StoreValueStream::new(
            Box::new(FixedSource {
                tiling: store_tiling,
                tile: store_tile,
            }),
            acc.clone(),
            value_ext.clone(),
            true, // carry: hold the committed value forward
        );
        let default = Box::new(FixedSource {
            tiling: Tiling::Scalar(value_ext.clone()),
            tile: Tile::Scalar(ColumnValue::single(int(100))),
        });
        let mut extract =
            crate::interpreter::tile_operators::ExtractFinal::new(Box::new(stream), default);
        let g = extract.tiling().universal_guard();
        let mut p = extract.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        let t = p.get(p.tiling().universal_guard());
        let Tile::Scalar(cv) = &t else { panic!() };
        assert_eq!(cv.as_single(), Some(int(60)));
    }

    // --- Engine render → step-function fold ---------------------------------

    /// A rendered [`Tile::Store`] folds consistently whether live or terminal.
    /// Terminality is a *separate* flag from the watermark: the numeric `frontier`
    /// predicate `≤ w` is kept in both states, and setting the `terminal` flag
    /// only signals "no more writes" — it does not rewrite the frontier.
    #[test]
    fn render_folds_consistently_live_and_terminal() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        e.attempt(Proposal {
            snapshot: pos(0),
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: alice
        e.attempt(Proposal {
            snapshot: pos(1),
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("bob", 20)]),
        }); // tick 2: bob

        // Live: `frontier` carries the watermark `≤ 2`. `carol` is a key of the store
        // that nothing has written, so her changelog is present and empty.
        let live = e.render_full_store_tile(&store_tiling(&["alice", "bob", "carol"]));
        assert_eq!(store_frontier(&live), Some(pos(2)));
        // `store_current` folds past tick 2 (which wrote only bob) back to tick 1
        // for alice, and reads bob directly at tick 2.
        assert_eq!(
            store_current(&live, &acct("alice")),
            Some((pos(2), int(70)))
        );
        assert_eq!(store_current(&live, &acct("bob")), Some((pos(2), int(20))));
        assert_eq!(store_current(&live, &acct("carol")), None); // never written
        // The frontier snapshot is cross-key consistent.
        assert_eq!(
            store_snapshot_at(&live, &pos(2)),
            balances(&[("alice", 70), ("bob", 20)])
        );

        // Terminal: closing the whole domain (the numeric frontier `≤ 2` is kept, not
        // rewritten) must fold identically.
        let mut terminal = live.clone();
        if let Tile::Store { terminal, .. } = &mut terminal {
            *terminal = true;
        }
        assert_eq!(store_frontier(&terminal), Some(pos(2)));
        assert_eq!(
            store_current(&terminal, &acct("alice")),
            Some((pos(2), int(70)))
        );
    }

    /// A non-store / undecided tile reads to `None` (the fallback every store
    /// read relies on).
    #[test]
    fn store_reads_reject_non_store_and_undecided() {
        assert_eq!(
            store_frontier(&Tile::Scalar(ColumnValue::from_ints(vec![1]))),
            None
        );
        // A store nothing has written yet is undecided → no frontier.
        let undecided = store_tiling(&["alice"]).empty_tile();
        assert_eq!(store_frontier(&undecided), None);
    }

    /// `seed_value` distinguishes a value-shaped tile that is carrying nothing yet from a
    /// collection whose key set is still open — a store seeded from either would hold a
    /// value the program never had.
    #[test]
    fn seed_value_reports_why_a_pull_carries_no_value() {
        // A non-empty scalar is the value.
        assert!(
            matches!(seed_value(&Tile::Scalar(ColumnValue::from_ints(vec![7]))), Ok(v) if v == int(7))
        );
        // An empty one has not arrived.
        assert!(matches!(
            seed_value(&Tile::Scalar(ColumnValue::from_ints(vec![]))),
            Err(SeedNotReady::Empty)
        ));
        // A collection is the whole map only once its domain is closed: an open one is a
        // partial map presented as the value before any position.
        let open = Tile::data_function(
            ColumnValue::from_uints(vec![1]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10]))),
            Predicate::at_or_below(Value::UInt(1)),
            BitSet::new(),
        );
        assert!(matches!(seed_value(&open), Err(SeedNotReady::Undecided)));
        let closed = Tile::data_function(
            ColumnValue::from_uints(vec![1]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10]))),
            Predicate::True,
            BitSet::new(),
        );
        let Ok(Value::Function(bindings)) = seed_value(&closed) else {
            panic!("a decided collection seeds as the one map it is")
        };
        assert_eq!(bindings.len(), 1);
        // A decided collection with no keys is the empty map, which is a value.
        let empty_map = Tile::data_function(
            ColumnValue::from_uints(vec![]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![]))),
            Predicate::True,
            BitSet::new(),
        );
        assert!(matches!(seed_value(&empty_map), Ok(Value::Function(b)) if b.is_empty()));
    }

    /// A settled read reclaims the history below the store's frontier on every pull.
    ///
    /// It reads the key's value as the store *stands*, so it needs the latest write and
    /// nothing before it. The store's release watermark is the `FanOut` intersection over
    /// its readers, so a reader that holds its branch until it retires keeps every version
    /// of every key for the length of the run — measured at 180 retained entries over a
    /// 90-position loop against 4 with this release.
    #[test]
    fn a_settled_read_releases_the_history_below_the_frontier() {
        let mut sched = Scheduler::new();
        let live = store_tile(
            &["alice"],
            &[("alice", 100)],
            &[(1, &[("alice", 70)]), (2, &[("alice", 40)])],
            Predicate::at_or_below(Value::UInt(2)),
        );
        let recorder = Rc::new(RefCell::new(Vec::new()));
        let mut read = StoreFinalRead::new(
            Box::new(RecordingSource {
                tiling: store_tiling(&["alice"]),
                tile: live,
                released: recorder.clone(),
            }),
            acct("alice"),
            value_extent(),
        );
        let g = read.tiling().universal_guard();
        let mut producer = read.subscribe(g, Box::new(|| {}), &mut sched);
        let _ = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            recorder.borrow().as_slice(),
            [TileGuard::Function(FunctionGuard::Domain(
                Predicate::at_or_below(Value::UInt(2))
            ))],
            "the read releases through the frontier it folded at"
        );
    }

    /// A [`FixedSource`] that records what its consumer released.
    struct RecordingSource {
        tiling: Tiling,
        tile: Tile,
        released: Rc<RefCell<Vec<TileGuard>>>,
    }
    struct RecordingProducer {
        base: ProducerBase,
        tile: Tile,
        released: Rc<RefCell<Vec<TileGuard>>>,
    }
    impl TileOperator for RecordingSource {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(RecordingProducer {
                base: ProducerBase::new(RecordingProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                released: self.released.clone(),
            })
        }
    }
    impl TileProducer for RecordingProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.borrow_mut().push(obsolete_guard);
        }
    }

    /// A record-valued map's seed reads the same from either representation of
    /// its codomain: boxed, as a `Tile::Scalar` over `ColumnValue::Records`, or
    /// struct-of-arrays, as a `Tile::Record`. A value carried whole arrives
    /// boxed and a comprehension over that value arrives struct-of-arrays, so a
    /// drain taking only one of them never settles on the other.
    #[test]
    fn a_record_valued_map_seeds_the_same_either_way() {
        let seed = |codomain: Tile| {
            let tile = Tile::data_function(
                ColumnValue::from_values(
                    vec![Value::String("btc".into()), Value::String("eth".into())],
                    &Extent::Base(BaseType::String),
                ),
                Box::new(codomain),
                Predicate::True,
                BitSet::new(),
            );
            let Ok(value) = seed_value(&tile) else {
                panic!("a decided seed is a value");
            };
            value
        };

        fn field<T>(t: T) -> HashMap<String, T> {
            HashMap::from([("units".to_string(), t)])
        }
        // A column of record values, and a record of columns over the fields.
        let units = ColumnValue::from_ints(vec![2, 1]);
        let boxed = seed(Tile::Scalar(ColumnValue::Records(field(units.clone()))));
        let struct_of_arrays = seed(Tile::Record(field(Tile::Scalar(units))));

        // The seed is a map, so its bindings carry no order; compare the entries.
        let entries = |seed: Value| {
            let Value::Function(bindings) = seed else {
                panic!("a map seeds as a function from keys to values");
            };
            let mut out: Vec<(String, i64)> = bindings
                .into_iter()
                .map(|b| match (b.input, b.output) {
                    (Value::String(k), Value::Record(fields)) => match fields["units"] {
                        Value::Int(n) => (k.to_string(), n),
                        ref other => panic!("`units` is an Int, got {other:?}"),
                    },
                    other => panic!("expected String to a record, got {other:?}"),
                })
                .collect();
            out.sort();
            out
        };
        let expected = vec![("btc".to_string(), 2), ("eth".to_string(), 1)];
        assert_eq!(entries(boxed), expected);
        assert_eq!(entries(struct_of_arrays), expected);
    }

    // ── Tile::Store step-function reads (Stage 2) ─────────────────────────────

    /// Build a `Tile::Store` over `accounts` from `(tick, &[(account, balance)])` write
    /// sets (ticks must be strictly ascending), holding `seed` before any of them and
    /// decided through `frontier`.
    ///
    /// `accounts` is the key space, spelled out because it is static: two fragments of
    /// one store hold the same keys whatever either of them has been written, which is
    /// what lets them merge. A fragment that is not the first passes an empty `seed`,
    /// the way a store's later tiles carry no seed of their own.
    fn store_tile(
        accounts: &[&str],
        seed: &[(&str, i64)],
        entries: &[(usize, &[(&str, i64)])],
        frontier: Predicate,
    ) -> Tile {
        let mut written: HashMap<&str, Vec<(usize, i64)>> =
            accounts.iter().map(|a| (*a, Vec::new())).collect();
        for (tick, writes) in entries {
            for (account, balance) in *writes {
                written
                    .get_mut(account)
                    .unwrap_or_else(|| panic!("{account} is not one of this store's keys"))
                    .push((*tick, *balance));
            }
        }
        let state = written
            .into_iter()
            .map(|(account, log)| {
                let tile = Tile::data_function(
                    ColumnValue::from_uints(log.iter().map(|(t, _)| *t).collect()),
                    Box::new(Tile::Scalar(ColumnValue::from_ints(
                        log.iter().map(|(_, b)| *b).collect(),
                    ))),
                    frontier.clone(),
                    BitSet::new(),
                );
                (account.to_string(), tile)
            })
            .collect();
        let seed_record = accounts
            .iter()
            .map(|a| {
                let column = match seed.iter().find(|(k, _)| k == a) {
                    Some((_, v)) => ColumnValue::from_ints(vec![*v]),
                    None => ColumnValue::from_ints(vec![]),
                };
                ((*a).to_string(), Tile::Scalar(column))
            })
            .collect();
        let tile = Tile::Store {
            state: Box::new(Tile::Record(state)),
            seed: Box::new(Tile::Record(seed_record)),
            // The domain a hand-built store stands over: its change positions, since
            // these fixtures record no carry.
            decided: Box::new(one_row_decided(ColumnValue::from_uints(
                entries.iter().map(|(t, _)| *t).collect(),
            ))),
            frontier: Box::new(one_row_decided(match frontier.as_at_or_below() {
                Some(Value::UInt(w)) => ColumnValue::from_uints(vec![w]),
                _ => ColumnValue::from_uints(vec![]),
            })),
            terminal: false,
            closed_keys: Vec::new(),
        };
        assert!(validate_tile(&tile), "store_tile built an invalid tile");
        tile
    }

    /// A three-tick store: the seed holds both accounts, tick 1 writes only
    /// `alice`, tick 2 writes only `bob`. Decided through the watermark `w`.
    fn skew_store(w: usize) -> Tile {
        store_tile(
            &["alice", "bob"],
            &[("alice", 100), ("bob", 50)],
            &[(1, &[("alice", 70)]), (2, &[("bob", 40)])],
            Predicate::at_or_below(Value::UInt(w)),
        )
    }

    #[test]
    fn store_frontier_reads_watermark_and_terminal() {
        let live = skew_store(2);
        assert_eq!(store_frontier(&live), Some(pos(2)));
        // A terminal store keeps its `at_or_below(w)` watermark (terminality is the
        // separate flag), so `store_frontier` reads `w` directly — even when the
        // watermark is *past the latest change tick* (trailing carries). Here the
        // latest change is at tick 3 but the decided watermark is 5: the frontier is
        // 5, not 3 (the former `True`-reconstruction undercounted to the latest
        // change).
        let done = store_tile(
            &["alice"],
            &[("alice", 100)],
            &[(3, &[("alice", 70)])],
            Predicate::at_or_below(Value::UInt(5)),
        );
        assert_eq!(store_frontier(&done), Some(pos(5)));
        // The decided region spans the trailing carries at ticks 4 and 5 — the frontier
        // is 5, not the latest change tick (3) the former `True`-reconstruction would
        // have given.
        assert_eq!(store_change_positions(&done), vec![pos(3)]);
        // A store that has recorded no change at all is decided wherever its frontier
        // says: the changelog is sparse, so an empty one is a run of carries over the
        // seed. Only an undecided frontier, and a tile that is not a store, have none.
        assert_eq!(
            store_frontier(&store_tile(
                &["alice"],
                &[("alice", 100)],
                &[],
                Predicate::at_or_below(Value::UInt(4))
            )),
            Some(pos(4))
        );
        assert_eq!(
            store_frontier(&store_tile(&["alice"], &[], &[], Predicate::False)),
            None
        );
        assert_eq!(
            store_frontier(&Tile::Scalar(ColumnValue::Ints(vec![1]))),
            None
        );
    }

    #[test]
    fn store_value_at_folds_step_interpolation() {
        let s = skew_store(2);
        // `alice`: the seed's 100 below tick 1, 70 from tick 1 on.
        assert_eq!(store_value_at(&s, &pos(0), &acct("alice")), Some(int(100)));
        assert_eq!(store_value_at(&s, &pos(1), &acct("alice")), Some(int(70)));
        assert_eq!(store_value_at(&s, &pos(2), &acct("alice")), Some(int(70)));
        // `bob`: the seed's 50 holds across tick 1 (which wrote only alice), 40 from
        // tick 2.
        assert_eq!(store_value_at(&s, &pos(0), &acct("bob")), Some(int(50)));
        assert_eq!(store_value_at(&s, &pos(1), &acct("bob")), Some(int(50)));
        assert_eq!(store_value_at(&s, &pos(2), &acct("bob")), Some(int(40)));
        // A key outside the store's key space is absent regardless of `t`.
        assert_eq!(store_value_at(&s, &pos(2), &acct("carol")), None);
    }

    #[test]
    fn store_snapshot_at_is_cross_key_consistent() {
        let s = skew_store(2);
        // Each snapshot is a coherent record at one commit time — the property a
        // bank of independent per-key reads (read-skew) cannot guarantee.
        assert_eq!(
            store_snapshot_at(&s, &pos(0)),
            balances(&[("alice", 100), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, &pos(1)),
            balances(&[("alice", 70), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, &pos(2)),
            balances(&[("alice", 70), ("bob", 40)])
        );
    }

    #[test]
    fn store_current_reads_a_live_undecided_store() {
        // The C1 property: `store_current` resolves against the *decided*
        // frontier of a store that is still live (watermark predicate, not the
        // terminal `True`) — where an `ExtractFinal` would hang waiting for
        // termination that never comes.
        let live = skew_store(2);
        assert!(!live.is_terminal(), "watermark store must not be terminal");
        assert_eq!(
            store_current(&live, &acct("alice")),
            Some((pos(2), int(70)))
        );
        assert_eq!(store_current(&live, &acct("bob")), Some((pos(2), int(40))));
        // An undecided store (nothing committed yet) has no current value.
        let undecided = store_tile(&["alice"], &[("alice", 100)], &[], Predicate::False);
        assert_eq!(store_current(&undecided, &acct("alice")), None);
    }

    #[test]
    fn decode_source_positioned_pairs_by_domain_and_sorts() {
        // An async source's domain arrives unordered (it enumerates a set of
        // arrived keys), and the codomain aligns to the domain *column*, not to
        // position. Decoding must pair each item with its actual domain position
        // and sort — otherwise the position-driven driver reads the wrong item at
        // each tick, and a scalar-final `ExtractFinal` over the dense read (which
        // relies on the highest position being last) picks a mid-loop value.
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![2, 0, 1]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![30, 10, 20]))),
            Predicate::True,
            BitSet::new(),
        );
        // Each item is its own one-row slice of the codomain, so the column order the
        // domain arrived in is gone by the time the driver reads it.
        assert_eq!(
            decode_source_positioned(&tile),
            vec![
                (pos(0), Tile::Scalar(ColumnValue::from_ints(vec![10]))),
                (pos(1), Tile::Scalar(ColumnValue::from_ints(vec![20]))),
                (pos(2), Tile::Scalar(ColumnValue::from_ints(vec![30]))),
            ],
            "items must be paired with their domain position and sorted ascending"
        );
    }

    #[test]
    fn store_merge_appends_changes_and_advances_frontier() {
        // Two changelog fragments — a decided prefix and a later commit — merge
        // by appending ticks and unioning the frontier to the larger watermark.
        let mut s = store_tile(
            &["alice", "bob"],
            &[("alice", 100), ("bob", 50)],
            &[(1, &[("alice", 70)])],
            Predicate::at_or_below(Value::UInt(1)),
        );
        s.merge(store_tile(
            &["alice", "bob"],
            &[],
            &[(2, &[("bob", 40)])],
            Predicate::at_or_below(Value::UInt(2)),
        ));
        // The merged changelog reads identically to a store built in one shot
        // (compared semantically — delta cells are `map_to_value` of a `HashMap`,
        // whose binding order is not significant).
        assert_eq!(store_frontier(&s), Some(pos(2)));
        assert_eq!(
            store_snapshot_at(&s, &pos(0)),
            balances(&[("alice", 100), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, &pos(1)),
            balances(&[("alice", 70), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, &pos(2)),
            balances(&[("alice", 70), ("bob", 40)])
        );
        assert_eq!(store_current(&s, &acct("bob")), Some((pos(2), int(40))));
    }

    #[test]
    fn validate_tile_rejects_malformed_store() {
        // Built as literals: `Tile::data_function` validates what it builds, so a malformed
        // changelog cannot be constructed through it.
        let log = |ticks: Vec<usize>, values: Vec<i64>| Tile::DataFunction {
            row_starts: ColumnValue::from_uints(vec![0]),
            domain: ColumnValue::from_uints(ticks),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_ints(values))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };
        let store = |state: Tile| Tile::Store {
            state: Box::new(state),
            seed: Box::new(Tile::Record(HashMap::new())),
            decided: Box::new(one_row_decided(ColumnValue::from_uints(vec![]))),
            frontier: Box::new(one_row_decided(ColumnValue::from_uints(vec![]))),
            terminal: false,
            closed_keys: Vec::new(),
        };
        let one_key = |log: Tile| store(Tile::Record(HashMap::from([("a".to_string(), log)])));
        // Non-ascending change ticks.
        assert!(!validate_tile(&one_key(log(vec![2, 1], vec![1, 2]))));
        // More values than ticks to hold them.
        assert!(!validate_tile(&one_key(log(vec![0], vec![1, 2]))));
        // A state that is not a record of changelogs.
        assert!(!validate_tile(&store(Tile::Scalar(
            ColumnValue::from_ints(vec![1])
        ))));
        // A position decided above the frontier, and one decided with no frontier at all.
        let decided_through = |decided: Vec<usize>, frontier: Vec<usize>| Tile::Store {
            state: Box::new(Tile::Record(HashMap::new())),
            seed: Box::new(Tile::Record(HashMap::new())),
            decided: Box::new(one_row_decided(ColumnValue::from_uints(decided))),
            frontier: Box::new(one_row_decided(ColumnValue::from_uints(frontier))),
            terminal: false,
            closed_keys: Vec::new(),
        };
        assert!(validate_tile(&decided_through(vec![0, 1], vec![1])));
        assert!(!validate_tile(&decided_through(vec![0, 2], vec![1])));
        assert!(!validate_tile(&decided_through(vec![0], vec![])));
    }
    /// Two memo'd readers of one cyclic store both end at the final state, in whichever
    /// order they are pulled.
    ///
    /// The recurrence advances on the **pull**, not on the wakeup, so the reader whose
    /// pull closes the cycle decides what its sibling was holding at that moment. A memo
    /// whose input has not notified it answers from its cache, so a sibling left with a
    /// pre-final cache and no further wakeup would answer the stale tile forever. The
    /// wakeup the driver requests on its `done` transition is what rules that out;
    /// this pins the property that makes it necessary — the order is not the runtime's
    /// to choose.
    #[rstest]
    #[case::laggard_first(true)]
    #[case::leader_first(false)]
    fn both_memo_readers_of_one_cycle_reach_the_final_state(#[case] laggard_first: bool) {
        let (fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 0); // unconditional
        let mut sched = Scheduler::new();
        let subscribe = |sched: &mut Scheduler| {
            let reader = StoreDenseRead::new(fan.branch(), acc.clone(), value_extent(), true);
            let mut memo = Memo::new(Box::new(reader));
            let guard = memo.tiling().universal_guard();
            memo.subscribe(guard, Box::new(|| {}), sched)
        };
        let mut lagging = subscribe(&mut sched);
        let mut leading = subscribe(&mut sched);
        let guard = lagging.tiling().universal_guard();

        // Both readers pull each lap, in the order under test, until the one pulled
        // second closes the cycle.
        let mut closing = leading.get(guard.clone());
        for _ in 0..MAX_CYCLE_PULLS {
            if closing.is_terminal() {
                break;
            }
            sched.check_for_notifications();
            if laggard_first {
                let _ = lagging.get(guard.clone());
                closing = leading.get(guard.clone());
            } else {
                closing = leading.get(guard.clone());
                let _ = lagging.get(guard.clone());
            }
        }
        assert!(closing.is_terminal(), "the closing reader converged");

        // The sibling now gets only what the runtime would deliver — no further pull of
        // the other reader to drive the cycle on its behalf.
        let mut lagged = lagging.get(guard.clone());
        for _ in 0..MAX_CYCLE_PULLS {
            if lagged.is_terminal() {
                break;
            }
            sched.check_for_notifications();
            lagged = lagging.get(guard.clone());
        }
        assert_eq!(
            dense_values(&lagged),
            vec![1, 3, 6],
            "the sibling answered a pre-final cache the closing pull left it holding"
        );
    }

    /// The `Int` codomain of a dense read, in domain order.
    fn dense_values(tile: &Tile) -> Vec<i64> {
        let Tile::DataFunction { codomain, .. } = tile else {
            panic!("dense read is a Function");
        };
        let Tile::Scalar(col) = codomain.as_ref() else {
            panic!("dense read codomain is a scalar column");
        };
        (0..col.len())
            .map(|i| match col.index_at(i) {
                Value::Int(v) => v,
                other => panic!("unexpected dense value {other:?}"),
            })
            .collect()
    }

    /// A `Memo` over a dense read of a *live* store must never cache a value the
    /// store has not decided yet.
    ///
    /// The composition is the hazard: `Memo` merges each pull's tile and then
    /// *releases* what it merged, and the dense read forwards that release to its
    /// trigger — so a position emitted once is never offered again. If the read
    /// emitted undecided positions, the very first pull would hand over every
    /// position folded to the seed, the `Memo` would latch those, and the store
    /// going terminal later would publish the stale cache as complete. The store
    /// advances one position per pull, so nothing else prevents that.
    #[test]
    fn a_memo_over_a_live_dense_read_caches_only_decided_positions() {
        let (fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 0); // unconditional
        let reader = StoreDenseRead::new(fan.branch(), acc, value_extent(), true);
        let mut memo = Memo::new(Box::new(reader));
        let guard = memo.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = memo.subscribe(guard, Box::new(|| {}), &mut sched);
        let tile = pull_to_terminal(&mut sched, &mut producer);
        let Tile::DataFunction { codomain, .. } = &tile else {
            panic!("dense read is a Function");
        };
        let Tile::Scalar(col) = codomain.as_ref() else {
            panic!("dense read codomain is a scalar column");
        };
        let got: Vec<i64> = (0..col.len())
            .map(|i| match col.index_at(i) {
                Value::Int(v) => v,
                other => panic!("unexpected dense value {other:?}"),
            })
            .collect();
        assert_eq!(
            got,
            vec![1, 3, 6],
            "the memo cached partially-decided folds instead of the accumulator"
        );
    }

    /// A fixture whose tile the test changes between pulls.
    struct SharedSource {
        tiling: Tiling,
        tile: Rc<RefCell<Tile>>,
    }
    struct SharedSourceProducer {
        base: ProducerBase,
        tile: Rc<RefCell<Tile>>,
    }
    impl TileOperator for SharedSource {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(SharedSourceProducer {
                base: ProducerBase::new(SharedSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
            })
        }
    }
    impl TileProducer for SharedSourceProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            honoring_release(&self.tile.borrow(), self.obsolete_guard())
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// A nested drive stays in a row until the source calls it complete: a position the row
    /// gains after the drive left it would be below the cursor and never run.
    #[test]
    fn a_nested_drive_stays_in_a_row_until_it_is_complete() {
        let acc = acct("acc");
        let uint = Extent::Base(BaseType::UInt);
        let pair_extent = Extent::Record(HashMap::from([
            (tuple_field(0), uint.clone()),
            (tuple_field(1), uint.clone()),
        ]));
        let pair = |r: usize, p: usize| {
            Value::Record(HashMap::from([
                (tuple_field(0), Value::UInt(r)),
                (tuple_field(1), Value::UInt(p)),
            ]))
        };
        // The curried source: rows 0 and 1, one position each, no row complete yet.
        let source_of = |row0: Vec<usize>, items0: Vec<i64>| {
            let n0 = row0.len();
            let mut positions = row0;
            positions.push(0);
            let mut items = items0;
            items.push(10);
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::grouped(
                    ColumnValue::UInts(vec![0, n0]),
                    ColumnValue::from_uints(positions),
                    Box::new(Tile::Scalar(ColumnValue::from_ints(items))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )
        };
        let source_tiling = Tiling::data_function(
            uint.clone(),
            Tiling::data_function(uint.clone(), Tiling::Scalar(value_extent())),
        );
        let source = Rc::new(RefCell::new(source_of(vec![0], vec![1])));
        let pairs_tile = |values: Vec<i64>| {
            Tile::data_function(
                ColumnValue::from_values(vec![pair(0, 0), pair(0, 1), pair(1, 0)], &pair_extent),
                Box::new(Tile::Scalar(ColumnValue::from_ints(values))),
                Predicate::True,
                BitSet::new(),
            )
        };
        let pairs_tiling =
            Tiling::data_function(pair_extent.clone(), Tiling::Scalar(value_extent()));
        let store_tiling = nested_store_tiling(uint.clone(), uint.clone(), store_values(&["acc"]));
        let mut engines = Engines::unopened(&store_tiling);
        let render = |e: &Engines| {
            render_carrier_tile(e, &store_tiling, &[Predicate::False, Predicate::False])
        };
        let store = Rc::new(RefCell::new(render(&engines)));
        let (nested, inner) = InductionDriver::nested_parts(
            Box::new(SharedSource {
                tiling: pairs_tiling.clone(),
                tile: Rc::new(RefCell::new(pairs_tile(vec![100, 100, 200]))),
            }),
            vec![Box::new(SharedSource {
                tiling: pairs_tiling,
                tile: Rc::new(RefCell::new(pairs_tile(vec![0, 0, 0]))),
            })],
            Vec::new(),
            value_extent(),
            &pair_extent,
        );
        let mut driver = InductionDriver::new(
            Box::new(SharedSource {
                tiling: store_tiling.clone(),
                tile: store.clone(),
            }),
            Box::new(SharedSource {
                tiling: source_tiling,
                tile: source.clone(),
            }),
            Some(nested),
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            inner,
            None,
        );
        let g = driver.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = driver.subscribe(g, Box::new(|| {}), &mut sched);
        let emitted = |t: &Tile| -> Vec<Vec<Value>> {
            decided_paths(t)
                .into_iter()
                .map(|(p, _)| p.to_vec())
                .collect()
        };
        let first = producer.get(producer.tiling().universal_guard());
        assert_eq!(emitted(&first), vec![vec![Value::UInt(0), Value::UInt(0)]]);
        // The store decides (0, 0).
        engines
            .store_at(&[Value::UInt(0)], &mut || {
                CommitEngine::seeded_at(None, HashMap::from([(acc.clone(), int(0))]))
            })
            .step(pos(0), Some(HashMap::from([(acc.clone(), int(1))])));
        *store.borrow_mut() = render(&engines);
        sched.check_for_notifications();
        let second = producer.get(producer.tiling().universal_guard());
        let paths = emitted(&second);
        assert!(
            !paths.contains(&vec![Value::UInt(1), Value::UInt(0)]),
            "the drive entered row 1 while the source had not called row 0 complete: {paths:?}"
        );
    }

    /// A seed stand-in counting its pulls and recording what it was released.
    struct CountingSeed {
        tiling: Tiling,
        value: Value,
        gets: Rc<RefCell<usize>>,
        released: Rc<RefCell<Vec<TileGuard>>>,
    }
    struct CountingSeedProducer {
        base: ProducerBase,
        value: Value,
        gets: Rc<RefCell<usize>>,
        released: Rc<RefCell<Vec<TileGuard>>>,
    }
    impl TileOperator for CountingSeed {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(CountingSeedProducer {
                base: ProducerBase::new(CountingSeedProducer::alloc_id(), &self.tiling),
                value: self.value.clone(),
                gets: self.gets.clone(),
                released: self.released.clone(),
            })
        }
    }
    impl TileProducer for CountingSeedProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            *self.gets.borrow_mut() += 1;
            if self.obsolete_guard().is_universal() {
                return self.tiling().empty_tile();
            }
            Tile::Scalar(ColumnValue::single(self.value.clone()))
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.borrow_mut().push(obsolete_guard);
        }
    }

    type Counters = (Rc<RefCell<usize>>, Rc<RefCell<Vec<TileGuard>>>);

    fn counting_seed(init: i64) -> (CountingSeed, Counters) {
        let gets = Rc::new(RefCell::new(0));
        let released = Rc::new(RefCell::new(Vec::new()));
        (
            CountingSeed {
                tiling: Tiling::Scalar(value_extent()),
                value: int(init),
                gets: gets.clone(),
                released: released.clone(),
            },
            (gets, released),
        )
    }

    /// A flat induction store reads its seed once, when it opens, and releases it there.
    #[test]
    fn an_open_induction_store_reads_and_releases_its_seed_once() {
        let items = [1, 2, 3, 4, 5, 6];
        let acc = acct("acc");
        let (seed, (gets, released)) = counting_seed(0);
        let store = InductionStore::new(
            vec![(acc.clone(), Box::new(seed))],
            vec![acc.clone()],
            Vec::new(),
            full_store_tiling(Extent::uint_range(items.len()), store_values(&["acc"])),
            None,
        );
        let set_body = store.body_input_setter();
        let fan = Rc::new(FanOut::new_cyclic(Box::new(store)));
        let driver = InductionDriver::new(
            fan.branch(),
            Box::new(ItemSource::new(&items)),
            None,
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            Extent::uint_range(items.len()),
            None,
        );
        set_body(Box::new(AddIfBody::new(Box::new(driver), i64::MIN, "acc")));
        let mut op = fan.branch();
        let guard = op.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut sched);
        // Pull until the store is open and has decided at least one position, but is
        // not yet terminal.
        let mut pulls_after_open = 0;
        let mut gets_at_open = None;
        for _ in 0..MAX_CYCLE_PULLS {
            sched.check_for_notifications();
            let t = producer.get(producer.tiling().universal_guard());
            if store_frontier(&t).is_some() {
                gets_at_open.get_or_insert(*gets.borrow());
                pulls_after_open += 1;
            }
            if t.is_terminal() {
                break;
            }
        }
        let after = *gets.borrow() - gets_at_open.expect("the store opened");
        assert_eq!(
            after, 0,
            "an open store reads its seed again on every pull ({after} extra reads over \
             {pulls_after_open} pulls)"
        );
        assert!(
            !released.borrow().is_empty(),
            "an open store never released its seed stream"
        );
    }

    /// A commit store releases its seed stream once it has opened on it.
    #[test]
    fn an_open_commit_store_releases_its_seed() {
        let acc = acct("acc");
        let (seed, (gets, released)) = counting_seed(7);
        let mut op = CommitOperator::with_seed_ops(
            vec![(acc.clone(), Box::new(seed))],
            store_values(&["acc"]),
            Vec::new(),
        );
        let g = op.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(g, Box::new(|| {}), &mut sched);
        let mut last = None;
        for _ in 0..4 {
            sched.check_for_notifications();
            last = Some(producer.get(producer.tiling().universal_guard()));
        }
        let last = last.unwrap();
        assert!(last.is_terminal(), "a store with no writers is terminal");
        assert_eq!(store_value_now(&last, &acc), Some(int(7)));
        assert!(
            !released.borrow().is_empty(),
            "a terminal commit store has never released its seed stream (pulled {} times)",
            gets.borrow()
        );
    }

    /// A reclaim takes the prefix of decided positions the meet covers and stops at the
    /// first it does not: a reader that released positions 0 and 2 still reads 1.
    #[test]
    fn a_reclaim_stops_at_the_first_position_still_read() {
        let (fan, _acc) = induction_cycle(&[1, 2, 3, 4], i64::MIN, 0);
        let mut reader = fan.branch();
        let guard = reader.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut sched);
        let tile = pull_to_terminal(&mut sched, &mut producer);
        let Tile::Store { decided, .. } = &tile else {
            panic!("a store")
        };
        assert_eq!(
            store_decided_positions(decided, 0),
            vec![pos(0), pos(1), pos(2), pos(3)]
        );
        // The drive has released through the frontier; this reader releases 0 and 2.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::from_column_value(&ColumnValue::from_uints(vec![0, 2])),
        )));
        sched.check_for_notifications();
        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::Store { decided, .. } = &tile else {
            panic!("a store")
        };
        let now = store_decided_positions(decided, 0);
        assert!(
            now.contains(&pos(1)),
            "position 1 was never released by this reader but left the domain: {now:?}"
        );
    }

    /// A commit store's value stream reads a store whose clock prefix was reclaimed.
    #[test]
    fn a_commit_value_stream_reads_a_reclaimed_store() {
        let acc = acct("acc");
        let mut engine = CommitEngine::new(HashMap::from([(acc.clone(), int(100))]));
        for v in [60, 50] {
            let snap = engine.decided_watermark().unwrap().clone();
            engine.attempt(Proposal {
                snapshot: snap,
                reads: HashMap::new(),
                writes: HashMap::from([(acc.clone(), int(v))]),
            });
        }
        engine.gc_released_prefix(&pos(1));
        let store_tiling = store_tiling(&["acc"]);
        let tile = engine.render_full_store_tile(&store_tiling);
        let mut stream = StoreValueStream::new(
            Box::new(FixedSource {
                tiling: store_tiling,
                tile,
            }),
            acc,
            Extent::Base(BaseType::Int),
            true,
        );
        let g = stream.tiling().universal_guard();
        let mut p = stream.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        let _ = p.get(p.tiling().universal_guard());
    }

    /// A record seed is the whole value only once each of its collection fields is complete.
    #[test]
    fn a_record_seed_waits_for_its_open_collection_field() {
        let open = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10]))),
            Predicate::at_or_below(Value::UInt(0)),
            BitSet::new(),
        );
        let seed = Tile::Record(HashMap::from([
            (tuple_field(0), open),
            (
                tuple_field(1),
                Tile::Scalar(ColumnValue::from_ints(vec![0])),
            ),
        ]));
        let got = seed_value(&seed);
        assert!(
            got.is_err(),
            "a record seed with an open collection field seeded as {:?}",
            got.ok()
        );
    }

    /// A row's seed holding a collection is ready once the collection is whole, which a
    /// complete key above says as well as its own level would: row 0's pair key is
    /// complete, so its seed is whole though its own level states nothing; row 1's is not
    /// and waits.
    #[test]
    fn a_row_seed_holding_a_collection_waits_until_it_is_whole() {
        let pairs = |rows: Vec<usize>| {
            let n = rows.len();
            ColumnValue::Records(HashMap::from([
                (tuple_field(0), ColumnValue::from_uints(rows)),
                (tuple_field(1), ColumnValue::from_uints(vec![0; n])),
            ]))
        };
        let seeds = |complete: Predicate| {
            Tile::data_function(
                pairs(vec![0, 1]),
                Box::new(Tile::grouped(
                    ColumnValue::from_uints(vec![0, 1]),
                    ColumnValue::from_uints(vec![0, 0]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                complete,
                BitSet::new(),
            )
        };
        let rows = |tile: &Tile| -> Vec<Path> {
            let mut rows: Vec<Path> = decode_row_seeds(tile, 1)
                .into_iter()
                .map(|(row, _)| row)
                .collect();
            rows.sort();
            rows
        };
        let row = |r: usize| Path::from(vec![Value::UInt(r)]);
        assert_eq!(rows(&seeds(Predicate::True)), vec![row(0), row(1)]);
        let first = Predicate::from_column_value(&pairs(vec![0]));
        assert_eq!(rows(&seeds(first)), vec![row(0)]);
        assert_eq!(rows(&seeds(Predicate::False)), Vec::<Path>::new());
    }
}

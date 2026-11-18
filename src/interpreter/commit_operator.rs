//! The commit operator: a transaction engine as a tile operator.
//!
//! Implements the transactional time-domain machinery from
//! `src/ccl/design/mutability.md` ("The runtime engines"): concurrent
//! writers propose transactions against a shared variable, and this operator
//! serializes them onto one commit-time clock, validating read sets
//! and emitting the store with a watermark.
//!
//! # Structure
//!
//! The design splits into two layers:
//! - [`CommitEngine`] — the pure serialization logic (allocate a tick, validate,
//!   commit-or-abort, advance the watermark), with no tiles; directly testable.
//! - [`CommitOperator`] / `CommitProducer` — the tile adapter: it subscribes to a *writer input* (a
//!   stream of proposals), which the dispatcher queues as work packages. Each package it consumes
//!   steps the engine (`consume_impl`), and `get` answers the published store tile without
//!   advancing a writer. The writer input is wired through a `writer_input_setter` so that, in a
//!   cyclic graph, the writer can read the store back (the operator's own output) before proposing
//!   — the cyclic-`FanOut` feedback idiom. The store the writer reads carries a watermark, and the
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
//! the proposal stream is `step → {snap, reads, writes, pos}` with `reads`/`writes` map-valued.
//! Their key sets vary from one decision to the next: a write set holds every carry key of
//! the store consuming it and only the taps that fired, and a read set omits a key the
//! store holds no value for yet.
//!
//! # Concurrency is logical
//!
//! The interpreter is single-threaded dataflow. "Concurrent writers" means
//! multiple input domains the operator interleaves — the order in which
//! [`CommitEngine::attempt`] is called. There is no parallelism; serialization
//! semantics are validated deterministically.

#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
use bit_set::BitSet;
use smol_str::SmolStr;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Bound::{Excluded, Unbounded};

use crate::ccl::{F_WRITES, Label};
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, CurryLevel, Extent, FunctionGuard, Path, Position, Predicate,
    Projection, Restates, SharedConsumer, SubscribeContext, Tile, TileGuard, Tiling, Value,
    WriterTakes, forwarding_consumer_keeping_keys, shared_consumer,
    tile_operators::{
        Breaker, BreakingProducer, Cycle, CycleSlot, Memo, ProducerBase, TileOperator,
        TileProducer, guard_minus, materialize_collections, materialized_row, subscribe_forwarding,
        subscribe_forwarding_keeping_keys,
    },
    tuple_field, uint_of_row,
};

use crate::interpreter::operator_conversion::{store_key, store_key_name};
use crate::interpreter::operator_graph::{EdgeRole, InputEdgeSpec, value, value_keyed, value_late};
use crate::interpreter::tile_operators::InputId;
use crate::interpreter::tile_operators::{
    OperatorBase, ProducerStateInfo, column_of_rows, impl_operator_base, impl_producer_base,
    read_again_toward, stored_value_tile, with_values_at,
};
use crate::interpreter::tiling::{
    domain_prefix_over, row_watermark, running_frontier, store_frontier_rows,
};

/// The domains of `tiling`'s levels, outermost first, down to and including a store's
/// positions: what a path through an induction store or its source runs through.
fn path_levels(tiling: &Tiling) -> Vec<Extent> {
    let mut levels = Vec::new();
    let mut at = tiling;
    loop {
        match at {
            Tiling::DataFunction { domain, codomain } => {
                levels.push(domain.clone());
                at = codomain;
            }
            Tiling::Store { domain, .. } => {
                levels.push(domain.clone());
                return levels;
            }
            _ => return levels,
        }
    }
}

/// A transaction proposal, evaluated against a snapshot.
///
/// A writer produces one of these by reading some keys at a decided snapshot and
/// deciding what to write. `reads`/`writes` are the read set and write set. Every
/// transaction proposes, a deny and a grant that writes nothing included, so `writes` may
/// be empty: such a tick is a decided position no key's changelog holds
/// (`src/ccl/design/mutability.md`, "Every transaction takes a tick").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    /// The committed prefix the writer read — a decided timestamp.
    pub snapshot: Position,
    /// Keys observed at `snapshot`, with the values seen (the read set).
    pub reads: HashMap<Value, Value>,
    /// Keys to update, with their new values (the write set).
    pub writes: HashMap<Value, Value>,
}

/// The outcome of a commit attempt under **allocate-on-validate**: a valid
/// proposal consumes the next tick and writes; a stale one consumes nothing and
/// the writer retries by re-reading and re-proposing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommitOutcome {
    Committed { ts: Position },
    Stale,
}

/// The pure serialization engine: no tiles, directly unit-testable.
///
/// **Allocate-on-validate**: a tick is consumed only by a valid proposal, whatever it
/// writes, so the timestamp domain is dense and a stale proposal leaves no trace. Validates
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
    /// The values this engine holds: each key's seed, every change it keeps, and the
    /// positions it decided.
    pub fn held_values(&self) -> usize {
        self.seed.len()
            + self.changes.values().map(BTreeMap::len).sum::<usize>()
            + self.decided_positions.len()
    }

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
            debug_assert!(
                !w.is_empty(),
                "an induction write writes at least one key; a position that writes nothing \
                 is a carry, `None`"
            );
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

    /// Validate and (if valid) commit one proposal. Allocate-on-validate: a valid
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
        // Allocate-on-validate on a dense clock: the watermark is the last allocated
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
        store_tile(&[(Vec::new(), self)], tiling, false)
    }

    /// The decided frontier as a predicate: the watermark, or `False` for an induction
    /// engine that has not stepped yet. It is `at_or_below(w)` even when the latest
    /// position(s) carried no write, so a trailing run of carries stays decided — a
    /// changelog is sparse but the frontier is not.
    fn frontier_predicate(&self, domain: &Extent) -> Predicate {
        match self.decided_watermark() {
            Some(w) => Predicate::at_or_below_in(w.value().clone(), domain),
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
/// run, and every level answers for its own rows. An induction store with no rows above it has one
/// level and one store.
fn render_engines(engines: &Engines, tiling: &Tiling, complete: &[Predicate]) -> Tile {
    // A level's predicate means complete at every depth beneath it, so the outermost
    // saying `True` says the whole induction store is done: every level below is complete too, and
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
    render_engines_level(engines, tiling, complete, done, &[])
}

/// One level of [`render_engines`]'s walk, with `terminal` the whole induction store's and
/// `above` the path of the row this level stands under.
fn render_engines_level(
    engines: &Engines,
    tiling: &Tiling,
    complete: &[Predicate],
    terminal: bool,
    above: &[Value],
) -> Tile {
    let (level_complete, beneath) = complete.split_first().unwrap_or_else(|| {
        unreachable!("an induction store states completion at every level of its decision stream")
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
            "an induction store with no rows above it states completion once, got {complete:?}"
        );
        let Engines::Store(engine) = engines else {
            panic!("an induction store with no rows above it holds one store, got a level")
        };
        // One store, whether or not its seed has arrived: there is no level above to key it
        // by, so the node exists from the start and an unopened one renders as what it
        // holds — an undecided frontier, no change, no value before any position.
        // Terminal only once open: a store's value before any position is its seed, so a
        // loop that ran no position answers with it, and a store without one has not
        // answered yet.
        let unopened = CommitEngine::unopened();
        return store_tile(
            &[(above.to_vec(), engine.as_ref().unwrap_or(&unopened))],
            tiling,
            terminal && engine.is_some(),
        );
    };
    let Engines::Rows(rows) = engines else {
        panic!("an induction store with rows above it holds one engine per row, got a bare store")
    };
    // A **standing** level: each of its rows holds the engines of the levels beneath it,
    // rendered by the same walk and answering for its own rows out of the same per-level
    // statement. A level called complete is complete at every depth beneath it, which is why
    // the level below can state its own for the running row alone.
    if store_tiling.is_data_function() {
        let mut starts = Vec::with_capacity(rows.len());
        let mut merged: Option<Tile> = None;
        for (row, below) in rows {
            let path = [above, std::slice::from_ref(row)].concat();
            let piece = render_engines_level(below, store_tiling, beneath, terminal, &path);
            starts.push(merged.as_ref().map_or(0, |t| match t {
                Tile::DataFunction { domain, .. } => domain.len(),
                _ => 0,
            }));
            match &mut merged {
                None => merged = Some(piece),
                // One standing row's induction store follows the previous one's rather than
                // describing the same rows: two standing rows key their induction stores
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
            // No enclosing position opened yet, so there is nothing beneath to assemble. The
            // whole tiling's empty tile, not the level below's: a standing level short
            // here is a tile that does not match what it declares.
            //
            // It still carries what every level calls complete. An induction store that opened no
            // row has still been told which rows will gain no position — the source put
            // none under them — and `empty_tile` says `False` at every level, which is the
            // other thing: a level that has delivered nothing and may yet. Dropped, the
            // reduction above never answers a row and the loop around it waits forever.
            return empty_engines_tile(tiling, complete, terminal);
        };
        return Tile::data_function(
            ColumnValue::from_values(enclosing_rows, enclosing),
            Box::new(Tile::grouped(
                starts,
                below_keys,
                below_values,
                below_pred,
                below_deleted,
            )),
            level_complete.clone(),
            BitSet::new(),
        );
    }
    let per_row: Vec<(Vec<Value>, &CommitEngine)> = rows
        .iter()
        .map(|(row, at)| match at {
            Engines::Store(Some(engine)) => ([above, std::slice::from_ref(row)].concat(), engine),
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
/// the single store of an induction store with no rows above it — each with the path of the row it
/// stands at, which the empty path is for a lone store. Their changelogs run together
/// CSR-wise under one node per key, because a changelog is a collection whose rows are the
/// stores; a lone store is the one-row case of that and needs no separate shape.
///
/// The key space comes from `tiling` rather than from the commits, so a key no engine has
/// written is present with an empty changelog. That is what a fold needs to distinguish
/// "written nothing yet" from "not a key of this store".
fn store_tile(engines: &[(Vec<Value>, &CommitEngine)], tiling: &Tiling, terminal: bool) -> Tile {
    let Tiling::Record(logs) = tiling.store_state() else {
        unreachable!("a store's state tiling is a record of per-key changelogs")
    };
    let domain = tiling
        .domain_extent()
        .expect("a store tiling names its domain");
    debug_assert!(
        engines
            .iter()
            .flat_map(|(_, e)| e.changes.keys().chain(e.seed.keys()))
            .all(|key| { store_key_name(key).is_some_and(|name| logs.contains_key(&name)) }),
        "a write or seed names a key outside the store's declared key space, so \
         rendering would drop it: declared {:?}",
        logs.keys().collect::<Vec<_>>(),
    );
    // What the changelogs and the decided set call complete: under each store's own row,
    // the positions at or below its watermark, where no later commit lands. The rows restart
    // their positions, so a statement naming positions alone would say one row's watermark
    // of every row, including one whose positions are still to be decided. A terminal store
    // decides nothing more anywhere.
    let decided_through = match terminal {
        true => Predicate::True,
        false => engines
            .iter()
            .map(|(row, engine)| {
                Predicate::qualified(Predicate::exactly(row), engine.frontier_predicate(&domain))
            })
            .fold(Predicate::False, |all, one| all.union(&one)),
    };
    let mut seed_fields = HashMap::with_capacity(logs.len());
    let state = logs
        .into_iter()
        .map(|(key, log)| {
            let Tiling::DataFunction { codomain, .. } = log else {
                unreachable!("a store key's changelog tiling is a collection")
            };
            let runtime = store_key(&Label::from_runtime_key(&key));
            let mut starts = Vec::with_capacity(engines.len());
            let mut positions: Vec<Value> = Vec::new();
            let mut written: Vec<Value> = Vec::new();
            for (_, engine) in engines {
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
                .filter_map(|(_, engine)| engine.seed.get(&runtime).cloned())
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
                starts,
                ColumnValue::from_values(positions, &domain),
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    written,
                    &codomain.extent(),
                ))),
                // A changelog holds every write its engine has committed, so it is complete
                // exactly where that store has decided.
                decided_through.clone(),
                BitSet::new(),
            );
            (key, tile)
        })
        .collect();
    let decided: Vec<Vec<Position>> = engines
        .iter()
        .map(|(_, engine)| engine.decided_positions.clone())
        .collect();
    Tile::Store {
        state: Box::new(Tile::record(state)),
        seed: Box::new(Tile::record(seed_fields)),
        decided: Box::new(decided_positions_tile(&decided, &domain, decided_through)),
        frontier: Box::new(store_frontier_rows(
            engines
                .iter()
                .map(|(_, engine)| engine.decided.as_ref().map(|w| w.value().clone())),
            &domain,
            match terminal {
                true => Predicate::True,
                false => Predicate::False,
            },
        )),
        terminal,
        closed_keys: Vec::new(),
        writer_takes: Vec::new(),
    }
}

/// `tiling`'s empty tile, carrying `complete` — one predicate per level, outermost first —
/// and `terminal` on the store beneath them.
///
/// [`Tiling::empty_tile`] states `False` at every level, which says a level has delivered
/// nothing and may yet. An induction store that opened no row says something else at the levels its
/// drive has heard about: those rows will gain no position at all.
fn empty_engines_tile(tiling: &Tiling, complete: &[Predicate], terminal: bool) -> Tile {
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

/// What a store keeps to run as a pipeline breaker: the handle on its cyclic fan-out, whether a
/// dispatcher drives it, and the store as its last step rendered it.
/// See `src/interpreter/design-operators.md`, "A store as a breaker".
#[derive(Default)]
struct BreakerState {
    /// The handle on the cyclic fan-out the store is the input of, whose cycle a consume has read
    /// again before each step and which it publishes each step's snapshot through.
    cycle: Option<Cycle>,
    /// The store as the last consumed step rendered it.
    snapshot: Option<Tile>,
    /// How many of the store's inputs have finished: the store settles at the last of them
    /// ([`finish_store`]).
    last_finishes: usize,
}

impl BreakerState {
    fn enter_cycle(&mut self, cycle: Cycle) {
        debug_assert!(
            self.cycle.is_none(),
            "a store is the input of one cyclic fan-out, which hands it its cycle once"
        );
        self.cycle = Some(cycle);
    }

    fn terminal(&self) -> bool {
        self.snapshot.as_ref().is_some_and(Tile::is_terminal)
    }

    /// Everything once the store is terminal, and nothing before: a reader pulls the store tile,
    /// which `restrict_to` cannot cut to the positions decided so far.
    fn held(&self, tiling: &Tiling) -> TileGuard {
        match self.terminal() {
            true => tiling.universal_guard(),
            false => tiling.empty_guard(),
        }
    }

    fn offer(&self) -> Tile {
        self.snapshot
            .clone()
            .expect("a consuming store's first consume renders it")
    }
}

/// A store that steps itself as a pipeline breaker, an induction store or a transaction store:
/// its own step, and the state [`consume_store`] and [`finish_store`] keep for it.
trait SteppedStore: BreakingProducer {
    type State;
    const STORE: &'static str;
    fn breaker(state: &Self::State) -> &BreakerState;
    fn breaker_mut(state: &mut Self::State) -> &mut BreakerState;
    fn step_store(&self, state: &mut Self::State, input: InputId) -> Tile;
    fn settle(&self, _state: &mut Self::State) {}
    fn input_released_in_state(&self, state: &mut Self::State, input: InputId) -> TileGuard;
    fn inputs_in_state(&self, state: &mut Self::State) -> usize;
    fn read_cycle_inputs(&self, state: &mut Self::State, cycle: &Cycle);
}

/// Step `store` until its input `input` has released `guard`. Before each step the store has the
/// operators inside its cycle read again ([`SteppedStore::read_cycle_inputs`]), and after it publishes the
/// snapshot a re-entrant pull reads. The first consume opens the store with a step, so a pull
/// answers from the snapshot from then on, whatever the morsel names.
///
/// A step wakes no reader outside the cycle. Such a reader is a pipeline, which takes what a step
/// decides from the store's pushes, or an inline operator inside the cycle of a loop around
/// this one, which that loop's rounds have read again. The planner refuses a store read inside the
/// cycle of a store that steps itself (`Planner::beneath_cycle`).
///
/// # Panics
///
/// For a store that is no cyclic fan-out's input, whose cycle no step can read again or publish
/// to, and for a step that changes neither the store nor its input's release: the positions
/// `guard` names have not arrived, and a store is queued a morsel only once its input can release
/// it.
fn consume_store<S: SteppedStore>(
    store: &S,
    state: &mut S::State,
    input: InputId,
    guard: TileGuard,
) {
    let cycle = S::breaker(state).cycle.clone().unwrap_or_else(|| {
        panic!(
            "{} steps itself only as its cyclic fan-out's input",
            S::STORE
        )
    });
    let step = |state: &mut S::State| {
        store.read_cycle_inputs(state, &cycle);
        let tile = store.step_store(state, input);
        cycle.publish(&tile);
        tile
    };
    if S::breaker(state).snapshot.is_none() {
        let tile = step(state);
        S::breaker_mut(state).snapshot = Some(tile);
    }
    loop {
        let released = store.input_released_in_state(state, input);
        if guard_minus(&guard, &released).is_empty() {
            return;
        }
        let tile = step(state);
        let progressed = S::breaker(state).snapshot.as_ref() != Some(&tile)
            || store.input_released_in_state(state, input) != released;
        assert!(
            progressed,
            "{} is consumed only for positions its input releases: {guard:?} names positions beyond {released:?}, which a step does not reach",
            S::STORE
        );
        S::breaker_mut(state).snapshot = Some(tile);
    }
}

/// Finish one of `store`'s inputs: push what the store has decided. At the finish of the last
/// input to finish, the store settles first ([`SteppedStore::settle`]).
///
/// # Panics
///
/// At the finish of the last input to finish, where the store is not terminal: nothing steps
/// the store after it.
fn finish_store<S: SteppedStore>(store: &S, state: &mut S::State) {
    S::breaker_mut(state).last_finishes += 1;
    let settled = S::breaker(state).last_finishes == store.inputs_in_state(state);
    if settled {
        store.settle(state);
    }
    assert!(
        !settled || S::breaker(state).terminal(),
        "{} finishes the run terminal: it stands at {:?}",
        S::STORE,
        S::breaker(state).snapshot.as_ref().and_then(store_frontier)
    );
}

impl SteppedStore for InductionStoreProducer {
    type State = InductionState;
    const STORE: &'static str = "an induction store";
    fn breaker(state: &Self::State) -> &BreakerState {
        &state.breaker
    }
    fn breaker_mut(state: &mut Self::State) -> &mut BreakerState {
        &mut state.breaker
    }
    fn input_released_in_state(&self, state: &mut Self::State, input: InputId) -> TileGuard {
        InductionStoreProducer::input_released_in_state(self, state, input)
    }
    fn inputs_in_state(&self, _state: &mut Self::State) -> usize {
        InductionStoreProducer::inputs_in_state(self)
    }
    fn read_cycle_inputs(&self, state: &mut Self::State, cycle: &Cycle) {
        InductionStoreProducer::read_cycle_inputs(self, state, cycle);
    }
    fn step_store(&self, state: &mut Self::State, input: InputId) -> Tile {
        debug_assert_eq!(input.0, 0, "an induction store has one input, its body");
        self.step(state)
    }
}

/// An induction store consumes its body's decision stream. Planned requests retain their guards
/// in per-run control; ordered step packages consume one settled round at a time. Nested requests
/// cover one row and include a closing round before releasing that row. See
/// `src/interpreter/design-dispatcher.md`, "A loop in rounds".
impl Breaker for InductionStoreProducer {
    /// A loop runs its positions in order, and takes a request none of whose positions is next as
    /// one that only closes positions absent from its source. The store's pipeline and every
    /// pipeline it reads, transitively, therefore publish in position order: each has one package
    /// in flight (`order_inputs_of_ordered_breakers`). The store's step and the body it reads are
    /// not ordered by this.
    fn requires_ordered_input(&self) -> bool {
        true
    }

    fn begin_run(&mut self) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.breaker.last_finishes = 0;

        drop(state_guard);
        self.begin_loop_run();
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.body_producer.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.body_producer.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    /// A planned run finishes after its body and step pipelines, so it only checks terminality
    /// and pushes. An unplanned breaker finishes through [`finish_store`].
    fn finish(&mut self, _input: InputId, pushes: &mut crate::interpreter::dispatcher::Pushes<'_>) {
        if self.run.is_some() {
            assert!(
                self.final_guard().is_universal(),
                "{} finishes the run terminal",
                self.name()
            );
            pushes.push_final(self);
            return;
        }

        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        finish_store(self, state);
        drop(state_guard);
        pushes.push_final(self);
    }

    /// Steps the store until the body has released `guard` ([`consume_store`]).
    ///
    /// # Panics
    ///
    /// As [`consume_store`].
    fn consume_impl(&self, input: InputId, guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        consume_store(self, state, input, guard);
    }
}
impl InductionStoreProducer {
    fn input_released_in_state(&self, state: &InductionState, _: InputId) -> TileGuard {
        state.body_producer.obsolete_guard().clone()
    }
}

impl BreakingProducer for InductionStoreProducer {
    /// Everything once the store is terminal. Before it is terminal, the positions the store has
    /// run and decided, which its pushes name as its rounds decide them, so a feed read from the
    /// store streams: a store that resumed its predecessor's run holds none of the positions
    /// through `resumed_after`, since its consumers took those from the predecessor
    /// ([`CommitEngine::seeded_at`]). A nested store publishes completed enclosing rows;
    /// a store over concatenation's tagged positions publishes only at terminality.
    fn final_guard(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if matches!(state.engines, Engines::Rows(_)) && !state.breaker.terminal() {
            return TileGuard::flatten_or(
                state
                    .complete_rows
                    .iter()
                    .take(self.tiling().levels())
                    .enumerate()
                    .map(|(level, complete)| {
                        CurryLevel::new(level).wrap_guard(TileGuard::Function(
                            FunctionGuard::Domain(complete.clone()),
                        ))
                    })
                    .collect(),
            );
        }
        if state.breaker.terminal() || !pushes_complete_positions(self.tiling()) {
            return state.breaker.held(self.tiling());
        }
        let decided = self.complete_in_state(state);
        match &self.resumed_after {
            Some(resumed) => guard_minus(
                &decided,
                &TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
                    resumed.value().clone(),
                ))),
            ),
            None => decided,
        }
    }

    fn seed_placements(&self) -> Vec<crate::interpreter::dispatcher::Placement> {
        self.seed_placements.clone()
    }

    /// The positions the last step decided, row by row under rows: the store tile's own
    /// statement (`Tile::to_guard`).
    fn complete(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match &state.breaker.snapshot {
            Some(tile) => tile.to_guard(),
            None => self.tiling().empty_guard(),
        }
    }

    /// The store publishes decided positions or completed enclosing rows after each round
    /// its loop's scope consumes ([`final_guard`](BreakingProducer::final_guard)).
    fn pushes_while_consuming(&self) -> bool {
        true
    }
}
impl InductionStoreProducer {
    fn complete_in_state(&self, state: &InductionState) -> TileGuard {
        match &state.breaker.snapshot {
            Some(tile) => tile.to_guard(),
            None => self.tiling().empty_guard(),
        }
    }
}

/// Whether an induction store over `tiling` pushes its positions as it decides them: a flat store
/// over positions a prefix of which has a spelling. A nested store publishes completed rows
/// instead. A concatenation's tagged positions require the domain's tags to spell a prefix.
pub(crate) fn pushes_complete_positions(tiling: &Tiling) -> bool {
    fn tagged(extent: &Extent) -> bool {
        match extent {
            Extent::Union(_) => true,
            Extent::Restricted { base, .. } => tagged(base),
            Extent::Record(fields) => fields.values().any(tagged),
            _ => false,
        }
    }
    matches!(tiling, Tiling::Store { domain, .. } if !tagged(domain))
}

/// The source of the transaction drive under `producer`, a writer of a transaction store: the
/// collection the transaction iterates. The walk follows the writer's drive, through the fan-out
/// slot the writer reads it through, to the drive's `source`.
fn drive_source<R>(
    producer: &dyn TileProducer,
    f: &mut Option<
        impl FnOnce(&dyn TileProducer, Option<crate::interpreter::dispatcher::Placement>) -> R,
    >,
) -> Option<R> {
    // Inspect owner metadata before visiting inputs: a stateful producer may hold
    // its state lock while invoking the visitor.
    let source_entry = producer.input_entry("source");
    let mut found = None;
    producer.visit_input_producers(&mut |role, input| {
        if found.is_some() {
            return;
        }
        found = match role {
            "source" => f.take().map(|f| f(input, source_entry.clone())),
            "driver" | "input" | "breaker" => drive_source(input, f),
            _ => None,
        };
    });
    found
}

/// The tiling of a store's seed input: one value, since the store reads every seed whole when it
/// opens, so a push of any seed names the input whole.
fn seed_input_tiling() -> Tiling {
    Tiling::Scalar(Extent::Base(BaseType::Unit))
}

/// `op`, a store's seed, subscribed in front of `consumer` behind an unplaced entry of the seed
/// input's tiling, and the entry's placement, which a planner sets to the pipeline that reads the
/// store's seeds. A push of the seed names the input whole ([`seed_input_tiling`]).
fn subscribe_seed(
    op: &std::sync::Arc<dyn TileOperator>,
    cx: &mut SubscribeContext,
) -> (
    Box<dyn TileProducer>,
    crate::interpreter::dispatcher::Placement,
) {
    let (entry, placement) = crate::interpreter::dispatcher::Entry::unplaced(seed_input_tiling());
    let seed = op.clone().subscribe(
        op.tiling().universal_guard(),
        crate::interpreter::notifications::widening(Box::new(entry)),
        cx,
    );
    (seed, placement)
}

impl CommitProducer {
    /// The writer whose source is input `input`, and `None` for the seed input: input 0 where the
    /// store has seed streams, ahead of every writer's, since the store opens before it steps.
    pub(crate) fn writer_of(&self, input: InputId) -> Option<usize> {
        match self.seed_placements.is_empty() {
            true => Some(input.0),
            false => input.0.checked_sub(1),
        }
    }

    /// The input writer `writer` reads: the inverse of [`writer_of`](Self::writer_of).
    pub(crate) fn writer_input(&self, writer: usize) -> InputId {
        InputId(writer + usize::from(!self.seed_placements.is_empty()))
    }

    /// Call `f` with the source of writer `writer`'s drive, which the store consumes as its input
    /// `writer`, or `writer + 1` where it has a seed input.
    fn writer_source<R>(
        &self,
        state: &CommitState,
        writer: usize,
        f: impl FnOnce(&dyn TileProducer) -> R,
    ) -> R {
        drive_source(
            &*state.writer_producers[writer],
            &mut Some(|source: &dyn TileProducer, _| f(source)),
        )
        .expect("a transaction writer reads its drive, which reads a source")
    }
}

impl SteppedStore for CommitProducer {
    type State = CommitState;
    const STORE: &'static str = "a transaction store";
    fn breaker(state: &Self::State) -> &BreakerState {
        &state.breaker
    }
    fn breaker_mut(state: &mut Self::State) -> &mut BreakerState {
        &mut state.breaker
    }
    fn input_released_in_state(&self, state: &mut Self::State, input: InputId) -> TileGuard {
        CommitProducer::input_released_in_state(self, state, input)
    }
    fn inputs_in_state(&self, state: &mut Self::State) -> usize {
        CommitProducer::inputs_in_state(self, state)
    }
    fn read_cycle_inputs(&self, state: &mut Self::State, cycle: &Cycle) {
        CommitProducer::read_cycle_inputs(self, state, cycle);
    }
    fn step_store(&self, state: &mut Self::State, input: InputId) -> Tile {
        match self.writer_of(input) {
            Some(_) => unreachable!("writer attempts are dispatcher pipelines"),
            None => {
                if self.open_store(state) {
                    // The tile the open publishes states `writer_takes`, which every writer's
                    // first decision reads.
                    #[cfg(debug_assertions)]
                    {
                        state.takes_published = true;
                    }
                }
                self.render_store(state)
            }
        }
    }
    fn settle(&self, state: &mut Self::State) {
        self.settle_ready(state);
    }
}

/// A transaction store driven as a pipeline breaker: input `k` is writer `k`'s source, and a
/// morsel of it is a run of that writer's items. Each writer's cycle, the store, the writer, its
/// drive and its body, is one pipeline, all of them sharing the store; the operators inside it
/// read their inputs within that pipeline. The store takes and validates each ready decision,
/// including an empty-write proposal, which takes a tick when it commits
/// (`src/interpreter/design-operators.md`, "Ready transaction decisions").
impl Breaker for CommitProducer {
    /// A transaction's driver holds one item in its live window, the next its source delivers, so
    /// the store's requests arrive in position order: the store's pipeline and every pipeline it
    /// reads, transitively, have one package in flight (`order_inputs_of_ordered_breakers`), as
    /// a loop's store has ([`InductionStoreProducer`]).
    fn requires_ordered_input(&self) -> bool {
        true
    }

    #[cfg(debug_assertions)]
    fn holds_unsettled_decisions(&self) -> bool {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.queued.iter().any(|queued| !queued.is_empty())
            || state.again.iter().any(|again| !again.is_empty())
    }

    fn begin_run(&mut self) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.breaker.last_finishes = 0;
        if state.breaker.snapshot.is_none() && state.seed_producers.is_empty() {
            assert!(self.open_store(state), "constant seeds open without input");
            let tile = self.render_store(state);
            if let Some(cycle) = &state.breaker.cycle {
                cycle.publish(&tile);
            }
            state.breaker.snapshot = Some(tile);
            #[cfg(debug_assertions)]
            {
                state.takes_published = true;
            }
        }
    }

    fn inputs(&self) -> usize {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.writer_producers.len() + usize::from(!self.seed_placements.is_empty())
    }

    fn input_tiling(&self, input: InputId) -> Tiling {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match self.writer_of(input) {
            Some(writer) => self.writer_source(state, writer, |source| source.tiling().clone()),
            None => seed_input_tiling(),
        }
    }

    /// The source positions of writer `input`'s items the store holds a decision for or has
    /// committed, and those the drive read past: the drive releases an item from its source at
    /// the take.
    /// For the seed input, all of it once the store has opened, and nothing before.
    fn input_released(&self, input: InputId) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match self.writer_of(input) {
            Some(writer) => {
                self.writer_source(state, writer, |source| source.obsolete_guard().clone())
            }
            None => match state.engine.is_some() {
                true => seed_input_tiling().universal_guard(),
                false => seed_input_tiling().empty_guard(),
            },
        }
    }

    /// The writer's drive, and every producer between it and the range over `source`, read the
    /// source again ([`read_again_toward`]): the drive decodes its source only once told it gained
    /// items.
    fn read_source_again(
        &mut self,
        source: &std::sync::Arc<
            std::sync::RwLock<dyn crate::interpreter::DataSourceDomainExtentImpl>,
        >,
    ) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        self.read_inputs_again(state, &|producer| {
            producer
                .data_sources()
                .iter()
                .any(|read| std::sync::Arc::ptr_eq(read, source))
                .then_some(true)
        });
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    /// As [`finish_store`].
    fn finish(&mut self, input: InputId, pushes: &mut crate::interpreter::dispatcher::Pushes<'_>) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if let Some(writer) = self.writer_of(input) {
            assert!(
                state.queued[writer].is_empty(),
                "a finished writer has no uncommitted decisions"
            );
            state.writer_terminal[writer] = true;
            let tile = self.render_store(state);
            state
                .breaker
                .cycle
                .as_ref()
                .expect("a store's cyclic fan-out")
                .publish(&tile);
            state.breaker.snapshot = Some(tile);
        }
        finish_store(self, state);
        drop(state_guard);
        pushes.push_final(self);
    }

    /// Steps the store until writer `input`'s drive has released `guard` ([`consume_store`]).
    ///
    /// # Panics
    ///
    /// As [`consume_store`].
    fn consume_impl(&self, input: InputId, guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        assert!(
            self.writer_of(input).is_none(),
            "writer requests run through their transaction scope"
        );
        consume_store(self, state, input, guard);
    }
}
impl CommitProducer {
    fn inputs_in_state(&self, state: &CommitState) -> usize {
        state.writer_producers.len() + usize::from(!self.seed_placements.is_empty())
    }
}
impl CommitProducer {
    fn input_released_in_state(&self, state: &CommitState, input: InputId) -> TileGuard {
        match self.writer_of(input) {
            Some(writer) => {
                self.writer_source(state, writer, |source| source.obsolete_guard().clone())
            }
            None => match state.engine.is_some() {
                true => seed_input_tiling().universal_guard(),
                false => seed_input_tiling().empty_guard(),
            },
        }
    }
}

impl BreakingProducer for CommitProducer {
    fn completed_keys(&self) -> Vec<Value> {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match state.breaker.snapshot.as_ref() {
            Some(Tile::Store { closed_keys, .. }) => closed_keys.clone(),
            _ => Vec::new(),
        }
    }

    /// The commit ticks the store has decided, through its watermark, and everything once it is
    /// terminal. A reader of the store's changelog (`StoreValueStream`) takes the ticks as they are
    /// decided, and a reader of its final value takes it once the store is terminal
    /// (`Dispatcher::read_whole`).
    fn complete(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if state.breaker.terminal() {
            return self.tiling().universal_guard();
        }
        match state.breaker.snapshot.as_ref().and_then(store_frontier) {
            Some(watermark) => TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
                watermark.into_value(),
            ))),
            None => self.tiling().empty_guard(),
        }
    }

    /// What the store holds, whatever its readers released.
    fn final_guard(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        self.complete_in_state(state)
    }

    /// The store pushes the ticks each consume decides.
    fn pushes_while_consuming(&self) -> bool {
        true
    }

    fn entry_placement(&self, input: InputId) -> Option<crate::interpreter::dispatcher::Placement> {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match self.writer_of(input) {
            Some(writer) => drive_source(
                &*state.writer_producers[writer],
                &mut Some(|_: &dyn TileProducer, entry| entry),
            )
            .flatten()
            .map(Some)
            .expect("a transaction writer's drive exposes its source entry"),
            None => self.seed_placements.first().cloned(),
        }
    }

    fn entry_placements(&self, input: InputId) -> Vec<crate::interpreter::dispatcher::Placement> {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        match self.writer_of(input) {
            Some(_) => self
                .entry_placement_in_state(state, input)
                .into_iter()
                .collect(),
            None => self.seed_placements.clone(),
        }
    }
}
impl CommitProducer {
    fn complete_in_state(&self, state: &CommitState) -> TileGuard {
        if state.breaker.terminal() {
            return self.tiling().universal_guard();
        }
        match state.breaker.snapshot.as_ref().and_then(store_frontier) {
            Some(watermark) => TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
                watermark.into_value(),
            ))),
            None => self.tiling().empty_guard(),
        }
    }
}
impl CommitProducer {
    fn entry_placement_in_state(
        &self,
        state: &CommitState,
        input: InputId,
    ) -> Option<crate::interpreter::dispatcher::Placement> {
        match self.writer_of(input) {
            Some(writer) => drive_source(
                &*state.writer_producers[writer],
                &mut Some(|_: &dyn TileProducer, entry| entry),
            )
            .flatten()
            .map(Some)
            .expect("a transaction writer's drive exposes its source entry"),
            None => self.seed_placements.first().cloned(),
        }
    }
}

/// A recurrence's engines, nested one node per collection level above the store.
///
/// This is the shape of the tile it renders to — a [`Tile::Store`] under as many
/// [`Tile::DataFunction`] levels as the induction store has — so the two do not have to be held in
/// step by hand. A flat store is [`Engines::Store`] alone; a nested store is one
/// [`Engines::Rows`] over its enclosing positions; an induction store beneath a standing level is
/// two, and a third needs no arm added. That is what makes nesting unbounded here rather than
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
    /// The values every store in the tree holds ([`CommitEngine::held_values`]).
    pub fn held_values(&self) -> usize {
        match self {
            Engines::Store(engine) => engine.as_ref().map_or(0, CommitEngine::held_values),
            Engines::Rows(rows) => rows.iter().map(|(_, below)| below.held_values()).sum(),
        }
    }

    /// The tree an induction store of `tiling` starts with: a row set per collection level above
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
        // The drive reaches rows in ascending order and a released row leaves, so the row
        // asked for is almost always the last.
        let at = match rows.iter().rposition(|(r, _)| r == row) {
            Some(at) => at,
            None => {
                assert!(
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
    /// induction store with no rows above it.
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
    /// the engine still holding it. A row is named whole once every slot of the induction store's
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
        Tile::Scalar(_) | Tile::Record { .. } => {
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
        // A row holding no cell of a field gave that cell back, so the value is not whole.
        Tile::Record { fields, absent } => absent.is_empty() && fields.values().all(is_whole_value),
        _ => false,
    }
}

// ── Step-function reads over a `Tile::Store` changelog ────────────────────────
//
// A `Tile::Store` is its seed and its changelogs: key `k`'s holds the positions that
// wrote `k`, strictly ascending, against the values written there, with `frontier` each
// row's decided watermark. These functions are the sanctioned way to read a store's value.
// A plain index into a changelog is meaningless, because a position absent from it is
// decided-absent (its value holds from the latest earlier change, or the seed), not
// unknown. They
// fold with right-continuous step interpolation, and are the single tile-level store
// read: the writers (`store_current`) and the value-stream projection both route through
// them, the tile-side counterpart of the engine's own `read_as_of` fold over its BTreeMap.

/// The watermark of a store tile's running row, the last one ([`running_frontier`]). `None`
/// if `tile` is not a [`Tile::Store`] or that row is undecided. A store with no change at all is
/// decided wherever its frontier says: the changelog is sparse, so an empty one is a
/// run of carries over the seed rather than an absence of decisions.
///
/// The watermark is read off the frontier's own entry rather than decoded from the predicate
/// `at_or_below(w)` would state: over a record or a union position that predicate is a
/// staircase, with no single bound to read back.
pub fn store_frontier(tile: &Tile) -> Option<Position> {
    let Tile::Store { frontier, .. } = tile else {
        return None;
    };
    match frontier.rows() {
        0 => None,
        rows => row_watermark(frontier, rows - 1).map(Position::new),
    }
}

/// `key`'s value as of position `t`: the latest change at a position `≤ t` whose delta
/// wrote `key`, folding past positions that wrote only other keys, and the store's seed
/// where there is none. `None` if `tile` is not a store, or `key` has neither a change at
/// or below `t` nor a seed (a collection-valued key before its first write). The
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
    Some(tile.store_seed(&store_key_name(key)?)?.index_at(0))
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

/// The decided-position collection for a store over `rows.len()` enclosing positions, stating
/// `complete`: a row's decided set is final where the row has decided.
fn decided_positions_tile(rows: &[Vec<Position>], domain: &Extent, complete: Predicate) -> Tile {
    let mut starts = Vec::with_capacity(rows.len());
    let mut positions = Vec::new();
    for row in rows {
        starts.push(positions.len());
        positions.extend(row.iter().map(|p| p.value().clone()));
    }
    let len = positions.len();
    Tile::grouped(
        starts,
        ColumnValue::from_values(positions, domain),
        Box::new(Tile::Scalar(ColumnValue::Units(len))),
        complete,
        BitSet::new(),
    )
}

/// Fold `key` over an **ascending** sequence of `query_positions` in a single
/// O(changes + queries) pass, so a full-stream reader folding every position is
/// linear, not O(changes × queries) as a per-position [`store_value_at`] or
/// [`store_delta_at`], each re-scanning the whole log, would be. Both changelog
/// readers ([`StoreValueStream`], [`StoreDenseRead`]) share it.
///
/// Result element `i` is the fold at `query_positions[i]` under the carry policy: the
/// latest write ≤ the position (`carry_forward: true`, an accumulator carried across
/// positions that did not write `key`), or the exact-position delta (`carry_forward:
/// false`, a reply tap — `None` where the position did not write `key`). Requires
/// `changes` ascending (the render invariant) and `query_positions` ascending; the
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

/// The full snapshot record as of position `t`: every key's value there
/// ([`store_value_at`]), a key with neither a change `≤ t` nor a seed omitted. Empty if
/// `tile` is not a store. This is the multi-key,
/// **snapshot-consistent** read — one fold yields a coherent record across all
/// keys at a single commit time, which a bank of independent per-key
/// `DataFunction` reads (the source of the read-skew divergence) cannot.
pub fn store_snapshot_at(tile: &Tile, t: &Position) -> HashMap<Value, Value> {
    tile.store_keys()
        .filter_map(|name| {
            let key = store_key(&Label::from_runtime_key(name));
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
/// or its seed where nothing wrote it, with the frontier position. `None` if the store is
/// undecided, or `key` has no value there at all ([`store_value_at`]). Unlike an `ExtractFinal` over a `DataFunction`, this is
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
/// merge). Each one otherwise hand-rolls the same watermark plus the monotone-max
/// fold and the "≤ watermark" test; this centralizes that state and those two
/// operations. The callers keep whatever *extra* work rides their release
/// (forwarding the release upstream) — only the watermark itself lives here.
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
/// fields as map-valued, and the writer renders them via [`map_to_value`]. A value other
/// than a `Value::Function` would be a `Variants` cell holding something other than its
/// declared map extent — impossible by construction.
pub fn value_to_map(v: &Value) -> HashMap<Value, Value> {
    match v {
        Value::Function(bindings) => bindings
            .iter()
            .map(|b| (b.input.clone(), b.output.clone()))
            .collect(),
        other => unreachable!(
            "a Variants map cell is a Value::Function (its map_extent is Key ⇀ Value, \
             guaranteed by emit_transact_writer); got {other:?}"
        ),
    }
}

/// The extent of a `Key ⇀ Value` map cell — a [`map_to_value`] `Value::Function`
/// carried in a `Variants` column. This is a **proposal's** read and write sets, whose key
/// sets vary per decision; the store's own state is one changelog per key
/// ([`full_store_tiling`]).
fn map_extent(key_extent: &Extent, value_extent: &Extent) -> Extent {
    Extent::Function {
        domain: Box::new(key_extent.clone()),
        codomain: Box::new(value_extent.clone()),
    }
}

/// The full multi-key store tiling: a [`Tiling::Store`] step function
/// `Position ⇀ {key: value}`, whose codomain names every key the store holds
/// with that key's own value tiling. The `Store` tiling (not `DataFunction`) is what marks
/// the output as a changelog to be folded, not a function to be indexed.
///
/// `values` is one entry per store key — a mutable variable or a reply tap — under the
/// key's [`store_key`] name. Carrying each key's tiling is what lets the keys differ: a
/// single shared codomain could only describe a heterogeneous store as the union of its
/// keys' extents, which names what any key might hold rather than what each one does.
pub fn full_store_tiling(domain: Extent, values: HashMap<SmolStr, Tiling>) -> Tiling {
    Tiling::Store {
        domain,
        codomain: Box::new(Tiling::Record(values)),
    }
}

/// A **nested** induction store's store tiling: one store per enclosing position.
///
/// One store over `(enclosing, inner)` pairs does not work, for two reasons. A row's carry
/// starts at that row's seed, where one log over pairs carries the previous row's last write
/// into it, a different value whenever anything is written between the loops. And which rows
/// are complete is the collection level's own `domain_predicate`, which a predicate over pairs
/// cannot state.
pub fn nested_store_tiling(
    enclosing: Extent,
    inner: Extent,
    values: HashMap<SmolStr, Tiling>,
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

/// The store a nested store is currently adding to — its last enclosing position.
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
        // A level whose values are another level stands above the induction store: the store sits
        // beneath it, so the descent continues into the last row's group rather than stopping at
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

/// The **path** an induction store has decided through: its last row at each level, and that
/// store's last position.
///
/// An induction store with no rows above it answers with a path of one component, its own frontier.
/// The path is the drive's cursor and nothing else's: it is not a tile key, so no predicate
/// is written over it.
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
/// `levels` is how long a path is: the row levels above the induction store's stores, then the
/// position within one. An induction store with no rows above it has one. It is the induction
/// store's own statement rather than a count of the source's levels, because an item that is itself
/// a collection carries its own levels beneath the positions, and counting those names a
/// path too deep.
///
/// Sorted, because an async source's domain arrives unordered and the drive takes
/// positions in path order. A row the source marks deleted is no item.
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
            deleted,
            ..
        } = level
        else {
            return;
        };
        for k in run {
            // A restricted source still carries its extent's keys, the filtered ones
            // deleted. Reading them makes the drive run an item the source does not have.
            if deleted.contains(k) {
                continue;
            }
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
    // A path names one item. The two drivers resolve a repeated one differently (the
    // induction driver's map keeps the last, the transaction driver's search the first), so
    // a source delivering a surviving path twice has no single meaning here.
    debug_assert!(
        out.windows(2).all(|w| w[0].0 < w[1].0),
        "an iteration source delivered a surviving path twice: {:?}",
        out.iter().map(|(p, _)| p).collect::<Vec<_>>()
    );
    out
}

/// One enclosing position's store, projected out of a nested store's collection of them.
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
        writer_takes,
    } = store
    else {
        // Every caller has descended to the level whose values are the stores, and a
        // `Tiling::Store` renders as a `Tile::Store` even when empty. Returning the input
        // unchanged instead hands back the *whole* level, which reads as a one-row answer
        // and silently folds one enclosing position's writes into the next.
        unreachable!("store_row takes a row of a vectorized store, got {store:?}")
    };
    let keep = (0..rows).map(|i| i == row).collect::<Vec<bool>>();
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
        writer_takes: writer_takes.clone(),
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
    tile.store_changelog(&store_key_name(key)?)
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

/// Field names of the proposal-stream codomain record. `F_WRITES` is shared with
/// the CCL side: it names the writer decision's write set (the contract between the
/// letrec phase, inference, and this engine) and is reused here for the proposal's
/// write-set map.
const F_SNAP: &str = "snap";
const F_READS: &str = "reads";
/// The source position of the item a proposal is for, which a consuming store keys its take
/// by (`src/interpreter/design-operators.md`, "Ready transaction decisions").
const F_POS: &str = "pos";
/// The tiling of a writer's proposal stream: `step → {snap, reads, writes, pos}`,
/// where `reads`/`writes` are map-valued (`Key ⇀ Value`) cells and
/// `pos` is a position of `item_positions`, the transaction source's.
pub fn proposal_stream_tiling(
    key_extent: &Extent,
    value_extent: &Extent,
    item_positions: &Extent,
) -> Tiling {
    proposal_rows_tiling(key_extent, value_extent, item_positions)
}

/// The rows of a writer's proposal stream: `step → {snap, reads, writes, pos}`.
fn proposal_rows_tiling(
    key_extent: &Extent,
    value_extent: &Extent,
    item_positions: &Extent,
) -> Tiling {
    let map = map_extent(key_extent, value_extent);
    Tiling::data_function(
        Extent::Base(BaseType::UInt),
        Tiling::Record(HashMap::from([
            (
                SmolStr::from(F_SNAP),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
            (SmolStr::from(F_READS), Tiling::Scalar(map.clone())),
            (F_WRITES.runtime_key(), Tiling::Scalar(map)),
            (SmolStr::from(F_POS), Tiling::Scalar(item_positions.clone())),
        ])),
    )
}

/// A commit operator over a multi-key store `Position ⇀ (Key ⇀ Value)`,
/// fed by `n_writers` concurrent writers.
///
/// Each writer input — a proposal stream `step → {snap, reads, writes, pos}` with
/// map-valued read/write sets — is wired after construction via
/// [`CommitOperator::writer_input_setter`]. That ordering is what allows the
/// cycle: a writer is built around a slot of the operator's own (store)
/// output, so it reads the store before proposing.
///
/// Dispatcher packages drive each writer. The store takes ready decisions and arbitrates their
/// proposals; a stale proposal consumes no tick and is retried against the current snapshot.
/// Reads return the published snapshot without advancing a writer.
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
    seed_ops: Vec<(Value, std::sync::Arc<dyn TileOperator>)>,
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
        values: HashMap<SmolStr, Tiling>,
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
        seed_ops: Vec<(Value, std::sync::Arc<dyn TileOperator>)>,
        values: HashMap<SmolStr, Tiling>,
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
    /// can be built around a slot of the operator's store output (the cycle).
    pub fn writer_input_setter(
        &self,
        k: usize,
    ) -> impl FnOnce(std::sync::Arc<dyn TileOperator>) + use<> {
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let consumer = shared_consumer(consumer);

        // A seed stays subscribed rather than being drained here: it is ordinary dataflow, so a
        // seed computed from a loop settles over as many pulls as that loop takes, and the
        // pull it settles on is the one that opens the store. Draining at subscribe
        // instead bounds a program by how far its seed's input can advance before the
        // runtime has started ([`InductionStore::subscribe`] says the same). As a pipeline
        // breaker the store reads its seeds as its input 0, before any writer's: each seed is
        // subscribed behind an entry a planner places in that input's pipeline, and a push of a
        // seed queues the input whole, since the store reads every seed whole when it opens.
        let mut seed_placements = Vec::new();
        let seed_producers = self
            .seed_ops
            .iter()
            .map(|(key, op)| {
                let (seed, placement) = subscribe_seed(op, cx);
                seed_placements.push(placement);
                (key.clone(), seed)
            })
            .collect();
        // A writer is the store's input as a pipeline breaker, so it is subscribed behind an
        // entry, as an induction store's body is: the entry stops every push from beneath before
        // a planner places the store's pipeline.
        let mut placements = Vec::new();
        let writer_producers = self
            .writer_inputs
            .iter()
            .enumerate()
            .map(|(k, slot)| {
                let input = slot.get().unwrap_or_else(|| {
                    panic!(
                        "CommitOperator: writer {k} is unwired at subscribe — either \
                         `writer_input_setter({k})` was never called"
                    )
                });
                let (producer, placement) = subscribe_behind_entry(&input, cx);
                placements.push(placement);
                producer
            })
            .collect::<Vec<_>>();
        let n = writer_producers.len();
        let base = ProducerBase::new(CommitProducer::alloc_id(), self.tiling(), self.clone(), cx);
        // The store runs as a pipeline breaker of one pipeline per writer, each placed through
        // its writer's entry, beside one for its seeds where it has any; its own placement is
        // its first writer's.
        let base = match placements.first() {
            Some(placement) => base.breaking(consumer.clone(), placement.clone()),
            None => base,
        };
        Box::new(CommitProducer {
            base,
            seed_placements,
            writer_write_keys: self.writer_write_keys.clone(),
            state: std::sync::Mutex::new(CommitState {
                queued: (0..n).map(|_| BTreeMap::new()).collect(),
                #[cfg(debug_assertions)]
                takes_published: false,
                settled: vec![Predicate::False; n],
                again: vec![BTreeSet::new(); n],
                writer_producers,
                consumed: vec![0; n],
                writer_terminal: vec![false; n],
                seed: self.seed.clone(),
                seed_producers,
                engine: None,
                drain_start: 0,
                breaker: BreakerState::default(),
                #[cfg(debug_assertions)]
                reported_closed: std::collections::HashSet::new(),
            }),
            run: None,
        })
    }
}

#[doc(hidden)]
pub struct CommitProducer {
    base: ProducerBase,
    /// Per seed stream, the placement of the entry it is subscribed behind, which a planner sets
    /// to the pipeline of the store's input 0 ([`Self::writer_of`]). Empty where the store has no
    /// seed stream, and then it has no seed input.
    seed_placements: Vec<crate::interpreter::dispatcher::Placement>,
    /// Per writer, the keys it may write ([`CommitOperator::writer_write_keys`]),
    /// aligned with [`Self::writer_terminal`]. The two together give per-key
    /// closure: a key is closed once every writer listing it is terminal.
    writer_write_keys: Vec<Vec<Value>>,
    state: std::sync::Mutex<CommitState>,
    pub(crate) run: Option<crate::interpreter::dispatcher::transaction_scope::TransactionRun>,
}
struct CommitState {
    writer_producers: Vec<Box<dyn TileProducer>>,
    /// Per writer, the decisions a consuming store has taken and not committed, by the source
    /// position of the item each is for ([`take`](Self::take)).
    queued: Vec<BTreeMap<Position, Proposal>>,
    /// Whether the last tile the store published states [`WriterTakes`]: from the first step
    /// after the store opened while taking ahead. A writer hands a decision that proposes
    /// nothing to the store only where it reads them.
    #[cfg(debug_assertions)]
    takes_published: bool,
    /// Per writer, the exact region whose decisions committed or stood ([`WriterTakes::settled`]).
    settled: Vec<Predicate>,
    /// Per writer, the items whose decisions went stale, which its drive emits again
    /// ([`WriterTakes::again`]).
    again: Vec<BTreeSet<Position>>,
    /// Per writer, how many proposal-stream steps have already been processed.
    consumed: Vec<u64>,
    /// Per writer, whether its proposal stream is terminal (the writer has
    /// finished all its transactions). The store is terminal — fully decided,
    /// no more commits coming — once every writer is.
    writer_terminal: Vec<bool>,
    /// The concrete part of the tick-0 state, which `seed_producers` completes. Emptied once
    /// the store opens, since the engine holds the seed from then on.
    seed: HashMap<Value, Value>,
    /// Per scalar key, the stream giving its value before any commit.
    seed_producers: Vec<(Value, Box<dyn TileProducer>)>,
    /// The store's state, `None` until every key's seed has arrived.
    ///
    /// A store holds one value per key before any commit and is seeded once, so it opens
    /// only when the whole seed is in hand — a key whose own seed settles later would
    /// otherwise stand at no value at all, and nothing asks again.
    engine: Option<CommitEngine>,
    /// Rotating writer index the per-`get` drain starts from — round-robin
    /// fairness. A fixed low-to-high order lets a busy low-index writer
    /// perpetually win a hot key and starve a higher-index contender; rotating
    /// the start each pull gives every writer periodic first pick. Any drain
    /// order is a valid serialization (OCC admits any serial order), so this
    /// changes only *which* transaction wins a race between conflicting writers,
    /// never correctness (conservation/non-negativity hold under any order).
    drain_start: usize,
    /// What the store keeps to run as a pipeline breaker.
    breaker: BreakerState,
    /// Every key a render has reported in `closed_keys`, for the check that no commit
    /// writes one afterwards.
    #[cfg(debug_assertions)]
    reported_closed: std::collections::HashSet<Value>,
}

/// A proposal-stream record field, as its scalar column. The proposal codomain
/// is `{snap, reads, writes, pos}` with every field scalar-shaped (`snap` a UInt
/// column, `reads`/`writes` `Variants` map columns, `pos` a column of source
/// positions): `proposal_stream_tiling` declares it so and the writer renders it to
/// match, so a missing or non-`Scalar` field is impossible.
fn record_field<'a>(fields: &'a HashMap<SmolStr, Tile>, name: &str) -> &'a ColumnValue {
    match fields.get(name) {
        Some(Tile::Scalar(cv)) => cv,
        other => unreachable!(
            "proposal record field {name} is scalar-shaped (the proposal codomain \
             {{snap, reads, writes, pos}} is declared by proposal_stream_tiling); got {other:?}"
        ),
    }
}

impl CommitProducer {
    pub(crate) fn begin_delivery(&mut self, input: InputId) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        let writer = self.writer_of(input).expect("a writer request");
        let source = self.writer_source(state, writer, |source| {
            std::ptr::from_ref(source).cast::<()>()
        });
        read_again_toward(&mut *state.writer_producers[writer], &|producer| {
            (std::ptr::from_ref(producer).cast::<()>() == source).then_some(true)
        });
    }

    pub(crate) fn begin_attempt(&mut self) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        self.publish_commits(state);
    }

    /// Take what writer `writer`'s attempt proposed, commit every ready decision and publish the
    /// store. Answers whether the attempt changed the store, an input's release or the decisions
    /// to attempt again, which is what a later attempt can read differently.
    pub(crate) fn complete_attempt(&mut self, writer: usize) -> bool {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        let released = |state: &CommitState| -> Vec<TileGuard> {
            (0..self.inputs_in_state(state))
                .map(|input| self.input_released_in_state(state, InputId(input)))
                .collect()
        };
        let before = (released(state), state.again.clone());
        self.take(state, writer);
        self.commit_ready(state);
        self.publish_commits(state);
        let tile = self.render_store(state);
        let progressed = state.breaker.snapshot.as_ref() != Some(&tile)
            || (released(state), state.again.clone()) != before;
        state.breaker.snapshot = Some(tile);
        progressed
    }

    pub(crate) fn request_complete(&self, input: InputId, guard: &TileGuard) -> bool {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        let writer = self.writer_of(input).expect("a writer request");
        state.queued[writer].is_empty()
            && state.again[writer].is_empty()
            && guard_minus(guard, &self.input_released_in_state(state, input)).is_empty()
    }

    /// The store's state, which every path past the seed check at the head of
    /// [`get_impl`](TileProducer::get_impl) has already opened.
    fn open_engine<'a>(&self, state: &'a mut CommitState) -> &'a mut CommitEngine {
        state
            .engine
            .as_mut()
            .expect("the store is open past the seed check at the head of the pull")
    }
}

impl TileProducer for CommitProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        for writer in &state.writer_producers {
            visit("writer", &**writer);
        }
        for (key, seed) in &state.seed_producers {
            visit(&format!("seed {key}"), &**seed);
        }
    }

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(
            state.engine.as_ref().map_or(0, CommitEngine::held_values) + state.seed.len(),
        )
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if state.breaker.snapshot.is_none() {
            return CommitEngine::unopened().render_full_store_tile(self.tiling());
        }
        state.breaker.offer()
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let state = self
            .state
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        for writer in &mut state.writer_producers {
            visit("writer", &mut **writer);
        }
        for (key, seed) in &mut state.seed_producers {
            visit(&format!("seed {key}"), &mut **seed);
        }
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn enter_cycle(&mut self, cycle: Cycle) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.breaker.enter_cycle(cycle);
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // Read-side commit-log GC. The store sits behind a cyclic `FanOut`, so this guard is
        // the intersection of what every slot, the writers' and the readers', has released.
        // A writer releases no version a proposal in its own window read
        // (`TransactWriterProducer::get_impl`). A proposal the store has taken ahead of its
        // commit is in no slot's window, so the reclaim stops strictly below the oldest snapshot
        // a held proposal was built against, in every build: the store then still answers the
        // proposal's reads at its snapshot, which `attempt` checks in a debug build. Staleness
        // reads each key's latest change, which no reclaim drops. A held proposal retains its
        // snapshot until attempted. The reclaim drops the committed versions through the last
        // tick the meet covers from the start, not through its highest point, since a tick the
        // meet skips is still read, and so is everything after it; it keeps the carry source a
        // live position reads.
        //
        // A store's readers name its commit ticks, so a region of the store is a `Domain`
        // guard. Any other shape names nothing this store can reclaim, and ignoring it would
        // leave the store re-emitting what was released.
        let pred = match &obsolete_guard {
            TileGuard::Function(FunctionGuard::Domain(pred)) => pred,
            g if g.is_empty() => return,
            g if g.is_universal() => &Predicate::True,
            other => panic!(
                "a commit store is released by a region of its commit ticks, a `Domain` guard; \
                 got {other:?}"
            ),
        };
        let oldest_held = state
            .queued
            .iter()
            .flat_map(BTreeMap::values)
            .map(|proposal| &proposal.snapshot)
            .min()
            .cloned();
        if let Some(engine) = &mut state.engine
            && let Some(through) = engine
                .decided_positions
                .iter()
                .take_while(|tick| pred.contains(tick.value()))
                .take_while(|tick| oldest_held.as_ref().is_none_or(|oldest| *tick < oldest))
                .last()
                .cloned()
        {
            engine.gc_released_prefix(&through);
        }
    }

    fn as_transaction_store(&self) -> Option<&CommitProducer> {
        Some(self)
    }

    fn as_transaction_store_mut(&mut self) -> Option<&mut CommitProducer> {
        Some(self)
    }
}
impl CommitProducer {
    fn visit_input_producers_mut_in_state(
        &self,
        state: &mut CommitState,
        visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
    ) {
        for writer in &mut state.writer_producers {
            visit("writer", &mut **writer);
        }
        for (key, seed) in &mut state.seed_producers {
            visit(&format!("seed {key}"), &mut **seed);
        }
    }
}

impl CommitProducer {
    /// Open the store on the pull its whole seed has arrived, and answer whether it is open.
    /// Until then it is undecided — no tick 0, so no frontier — and a writer reads nothing to
    /// build an attempt against, which is why nothing is attempted before it opens either.
    fn open_store(&self, state: &mut CommitState) -> bool {
        if state.engine.is_none() {
            let mut seed = state.seed.clone();
            let mut resolved = 0;
            for (key, producer) in &mut state.seed_producers {
                if let Ok(value) = seed_value(&producer.get(producer.tiling().universal_guard())) {
                    seed.insert(key.clone(), value);
                    resolved += 1;
                }
            }
            if resolved == state.seed_producers.len() {
                let engine = CommitEngine::new(seed);
                state.engine = Some(engine);
                // The engine holds the seed from here, so the concrete part is not kept twice.
                state.seed.clear();
                // The seed is read once, at the store's opening, so it is released there.
                for (_, producer) in &mut state.seed_producers {
                    producer.release(producer.tiling().universal_guard());
                }
            }
        }
        state.engine.is_some()
    }

    /// Pull writer `k`, and answer the proposals it holds that the store has neither attempted
    /// nor taken, with the step of each and the source position of its item.
    fn new_proposals(&self, state: &mut CommitState, k: usize) -> Vec<(u64, Position, Proposal)> {
        let guard = state.writer_producers[k].tiling().universal_guard();
        let tile = state.writer_producers[k].get(guard);
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = tile
        else {
            return Vec::new();
        };
        // A writer is terminal once its proposal stream is — every transaction has been
        // emitted and (by the retry/advance protocol) committed. Monotonic: writers don't
        // un-finish, so latch with `|=` rather than `=` (a transient non-`True` pull after
        // terminality must not un-set it — the store's terminality gates output convergence).
        state.writer_terminal[k] |= matches!(domain_predicate, Predicate::True);
        // The proposal-stream codomain is a record `{snap, reads, writes, pos}` —
        // `proposal_stream_tiling` declares it so and the writer renders it to match, so a
        // non-`Record` value on a collection proposal tile is impossible.
        let Tile::Record { fields, absent } = *codomain else {
            unreachable!(
                "the proposal stream's codomain is a {{snap, reads, writes, pos}} record \
                 (proposal_stream_tiling); got a non-Record codomain"
            );
        };
        crate::interpreter::tile_operators::assert_no_absent_cells(&absent);
        let snaps = record_field(&fields, F_SNAP);
        let reads = record_field(&fields, F_READS);
        let writes = record_field(&fields, &F_WRITES.runtime_key());
        let positions = record_field(&fields, F_POS);
        // The proposal tile is an offset window: its domain carries the absolute step values
        // (the writer compacts its released prefix), so read the step from the domain column
        // and index the codomain by column position `j`. `consumed[k]` is the absolute count of
        // steps already attempted — a step value, not a column position.
        (0..domain.len())
            .filter_map(|j| {
                // The proposal-stream domain extent is `Base(UInt)` (proposal_stream_tiling), so
                // a step is always a UInt.
                let Value::UInt(step) = domain.index_at(j) else {
                    unreachable!(
                        "proposal step is a UInt (the proposal-stream domain extent is \
                         Base(UInt))"
                    );
                };
                if step < state.consumed[k] {
                    return None; // attempted on an earlier pull (below the live edge)
                }
                // `snap` is a position of the commit clock, a `Scalar(UInt)` column to match it.
                let snapshot = Position::new(snaps.index_at(j));
                debug_assert!(
                    matches!(snapshot.value(), Value::UInt(_)),
                    "a proposal's snapshot is a commit-clock position, which is a UInt; got \
                     {snapshot}"
                );
                Some((
                    step,
                    Position::new(positions.index_at(j)),
                    Proposal {
                        snapshot,
                        reads: value_to_map(&reads.index_at(j)),
                        writes: value_to_map(&writes.index_at(j)),
                    },
                ))
            })
            .collect()
    }

    /// Release writer `k`'s proposal stream through the step the store has taken.
    fn release_steps(&self, state: &mut CommitState, k: usize, step: u64) {
        state.writer_producers[k].release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(step)),
        )));
    }

    /// Check a commit of writer `k`'s that wrote `written`.
    #[cfg(debug_assertions)]
    fn debug_assert_committed(&self, state: &CommitState, k: usize, written: &[Value]) {
        debug_assert!(
            written
                .iter()
                .all(|w| self.writer_write_keys[k].contains(w)),
            "a committed write stays inside its writer's declared footprint: writer {k} wrote \
             {written:?}, declaring {:?}",
            self.writer_write_keys[k]
        );
        debug_assert!(
            written.iter().all(|w| !state.reported_closed.contains(w)),
            "no commit writes a key the store has reported closed: writer {k} wrote \
             {written:?}, closed {:?}",
            state.reported_closed
        );
    }

    /// The store as the engine holds it, terminal once every writer is, with the keys every
    /// writer of which is terminal closed.
    fn render_store(&self, state: &mut CommitState) -> Tile {
        let tiling = self.tiling().clone();
        let mut store = self.open_engine(state).render_full_store_tile(&tiling);
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
            writer_takes,
            ..
        } = &mut store
        {
            *writer_takes = state
                .settled
                .iter()
                .zip(&state.again)
                .map(|(settled, again)| WriterTakes {
                    settled: settled.clone(),
                    again: again.iter().cloned().collect(),
                })
                .collect();

            if state.writer_terminal.iter().all(|&t| t) {
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
                    .zip(&state.writer_terminal)
                    .all(|(keys, &t)| t || !keys.contains(k));
                if done && !closed.contains(k) {
                    closed.push(k.clone());
                }
            }
            #[cfg(debug_assertions)]
            state.reported_closed.extend(closed.iter().cloned());
            *closed_keys = closed;
        }
        debug_assert!(
            store.check_from(self.tiling()),
            "rendered store tile does not match the full-store tiling"
        );
        store
    }

    /// Pull writer `k` and take each decision it brings into the writer's queue, keyed by the
    /// source position the proposal carries. The take releases the proposal's step to the
    /// writer, which acks its attempt, so the drive moves on to its next item while the store
    /// holds the decision. Every decision retains its read set for validation, including an empty write set.
    fn take(&self, state: &mut CommitState, k: usize) {
        for (step, item, proposal) in self.new_proposals(state, k) {
            #[cfg(debug_assertions)]
            debug_assert!(
                state.takes_published,
                "writer {k} decides under a store taking ahead only against a published tile \
                 that states `writer_takes`, so it hands every decision to the store: the store \
                 published none before it opened, when no writer has a frontier to decide at"
            );
            debug_assert!(
                self.open_engine(state)
                    .decided
                    .as_ref()
                    .is_some_and(|frontier| &proposal.snapshot <= frontier),
                "a dispatched proposal reads a published snapshot, never a future frontier"
            );
            state.consumed[k] = step + 1;
            self.release_steps(state, k, step);
            let earlier = state.queued[k].insert(item.clone(), proposal);
            debug_assert!(
                earlier.is_none(),
                "the store holds one decision per item of a writer: writer {k} decided {item} \
                 while the store held a decision for it"
            );
        }
    }

    /// Attempt ready decisions, rotating among writers after each attempt. Only positions of
    /// the same writer are compared. A stale decision is re-evaluated against the current store.
    fn commit_ready(&self, state: &mut CommitState) {
        let n = state.writer_producers.len();
        while let Some(k) = (0..n)
            .map(|off| (state.drain_start + off) % n)
            .find(|&k| !state.queued[k].is_empty())
        {
            state.drain_start = (k + 1) % n;
            let item = state.queued[k].first_key_value().unwrap().0.clone();
            let proposal = state.queued[k]
                .remove(&item)
                .expect("the selected writer holds a decision");
            #[cfg(debug_assertions)]
            let written: Vec<Value> = proposal.writes.keys().cloned().collect();
            let outcome = self.open_engine(state).attempt(proposal);
            #[cfg(debug_assertions)]
            if let CommitOutcome::Committed { .. } = outcome {
                self.debug_assert_committed(state, k, &written);
            }
            match matches!(outcome, CommitOutcome::Committed { .. }) {
                true => {
                    state.again[k].remove(&item);
                    state.settled[k] = state.settled[k].union(&Predicate::point(item.into_value()));
                }
                false => self.drive_again(state, k, &item),
            }
        }
    }

    /// Record that writer `k` must decide `item` again at a new frontier. Its previous
    /// decision was made against a frontier another writer has committed past. The store
    /// names `item` among the writer's [`again`](WriterTakes::again) and publishes its state,
    /// which the drive and the writer read through the recurrence.
    ///
    /// Transaction control queues the retry after publishing this statement.
    fn drive_again(&self, state: &mut CommitState, k: usize, item: &Position) {
        state.again[k].insert(item.clone());
    }

    /// Publish the store as the engine holds it, and have the operators inside its cycle read
    /// again: a writer pulled in the same step reads what the step committed.
    fn publish_commits(&self, state: &mut CommitState) {
        let tile = self.render_store(state);
        let cycle = state
            .breaker
            .cycle
            .clone()
            .expect("a transaction store steps itself only as its cyclic fan-out's input");
        cycle.publish(&tile);
        #[cfg(debug_assertions)]
        {
            state.takes_published = true;
        }
        self.read_cycle_inputs(state, &cycle);
    }

    /// Commit what the store holds once every input has finished: take what
    /// each writer still proposes, and attempt every ready decision, until a pull of every writer brings
    /// nothing. That last pull finds each writer terminal: its drive is done once the store has
    /// let go of all its items.
    fn settle_ready(&self, state: &mut CommitState) {
        assert!(
            state.queued.iter().all(BTreeMap::is_empty)
                && state.again.iter().all(BTreeSet::is_empty),
            "a transaction store finishes after its dispatched attempts settle"
        );
        if self.open_store(state) {
            let tile = self.render_store(state);
            if let Some(cycle) = &state.breaker.cycle {
                cycle.publish(&tile);
            }
            state.breaker.snapshot = Some(tile);
        }
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
/// `levels_above` is how many collection levels stand above the induction store's stores, so it is
/// how many components of a path name a row. An induction store with none is one store over the
/// whole extent, and the whole tile is its one seed, at the empty path. An induction store with
/// rows has a seed that is a morphism of the enclosing position, compiled against the
/// enclosing positions, so its tile is keyed by those rows and every row has one whether or not
/// its inner loop runs a position.
///
/// A seed a pull does not carry is absent rather than reported: the row it would open
/// opens on a later pull instead, which is the same thing a row the drive has not reached
/// does.
fn decode_row_seeds(tile: &Tile, levels_above: usize) -> Vec<(Path, Value)> {
    if levels_above == 0 {
        return seed_value(tile)
            .map(|value| (Path::default(), value))
            .into_iter()
            .collect();
    }
    decode_source_paths(tile, levels_above)
        .into_iter()
        .filter_map(|(row, value)| {
            // A seed holding a collection still arriving is part of a value, not one: the
            // row opens once it is whole, as it does once a missing seed arrives.
            if !is_whole_value(&value) {
                return None;
            }
            Some((row, materialized_row(value)))
        })
        .collect()
}

/// A nested store's output tiling: one [`Tile::Store`] per row of `enclosing`, under the
/// levels `standing` leaves above it.
///
/// The standing levels stand above the induction store: a nest three deep is this same induction
/// store replicated per row of the loop around it, not an induction store that counts its own
/// depth. `pair_domain` is the `(enclosing, inner)` domain the driver sequences positions in; the
/// store splits it, keeping the enclosing component as the collection level above it.
pub fn nested_engines_tiling(
    standing: &Tiling,
    depth: usize,
    pair_domain: &Extent,
    values: HashMap<SmolStr, Tiling>,
) -> Tiling {
    let (enclosing, inner) = split_pair_domain(pair_domain).unwrap_or_else(|| {
        panic!("a nested store sequences its positions as pairs, got {pair_domain}")
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
/// There is exactly one writer, visiting each iteration position once in order: no proposals, no
/// conflicts, no retries. The store is the *consuming* half of the recurrence — it reads the body's
/// decision record `{writes, __to_<defer>*}` ([`decision_at_index`] decodes each write's `` `fired
/// ``/`` `idle `` tag) and [`step`](CommitEngine::step)s the engine, appending a change of the
/// writes that fire and **carrying** where none does (no change; each value inherits). Its cycle
/// partner [`InductionDriver`] produces the body's `(prev…, item)` input from the changelog this
/// store emits, read back through a `FanOut::new_cyclic` — so the accumulator crosses between them
/// as a tile, like every other operator-to-operator value.
///
/// A plain (unconditional) `mut` loop writes at every position (a dense changelog); a
/// conditional write is sparse in position space (a position where it is idle appends
/// nothing to its changelog) while the frontier still tracks the whole extent.
pub struct InductionStore {
    /// The writer body `` λ (prev…, item) → {writes(, __to_<defer>…)} ``,
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
    tap_fields: Vec<SmolStr>,
    /// Per accumulator key, the stream giving each row's value **before** any of its
    /// positions.
    ///
    /// A carry at a row's first position folds to this, so a store cannot open without it.
    /// An induction store with no rows above it has one store and so one seed, keyed by the empty
    /// path; a nested one restarts per row, and its driver reads the same stream to
    /// snapshot the body. The store needs it too, because a fold resolves there: at a row's
    /// position that writes nothing, a store without it would carry the previous row's final
    /// where the driver's snapshot holds this row's seed.
    seed_ops: Vec<(Value, std::sync::Arc<dyn TileOperator>)>,
    base: OperatorBase,
}

impl InductionStore {
    /// Assemble an induction store over `output_tiling` — a collection level per row above
    /// its stores, which [`full_store_tiling`] and [`nested_engines_tiling`] build.
    ///
    /// `seed_ops` gives each accumulator's value before any position, keyed by the row it
    /// opens; `write_keys` follows the commit store's writer convention, the accumulators
    /// followed by tap keys. `resumed_after` is where a predecessor store stopped, which
    /// only an induction store with no rows above it has.
    pub fn new(
        seed_ops: Vec<(Value, std::sync::Arc<dyn TileOperator>)>,
        write_keys: Vec<Value>,
        tap_fields: Vec<SmolStr>,
        output_tiling: Tiling,
        resumed_after: Option<Position>,
    ) -> Self {
        assert!(
            resumed_after.is_none() || !output_tiling.is_data_function(),
            "an induction store with rows above it does not resume: the store around it is what \
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
    pub fn body_input_setter(&self) -> impl FnOnce(std::sync::Arc<dyn TileOperator>) + use<> {
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // Forward body progress to this store's consumer. The body's input is the driver,
        // which forwards the loop source's arrivals, so a downstream reader is notified of an
        // async source's incremental delivery and reads the store again.
        let consumer = shared_consumer(consumer);

        let body_op = self.body_input.get().expect(
            "InductionStore: the decision body is unwired at subscribe — either \
                 `body_input_setter` was never called, or this store is being subscribed \
                 twice (the first subscribe takes the slot)",
        );
        // The body is the store's input as a pipeline breaker: the entry in front of it queues
        // what a pipeline beneath pushes for the store's pipeline once a planner places it, and
        // stops every push before then.
        let (body_producer, placement) = subscribe_behind_entry(&body_op, cx);
        // A seed stays subscribed rather than being drained here: it is ordinary dataflow, so a
        // seed computed from a loop settles over as many pulls as that loop takes, and the
        // pull it settles on is the one that opens the store. Draining at subscribe
        // instead bounds a seed by how many positions its input can deliver before the
        // runtime has started. The store reads a seed by pull at a step. Each seed is
        // subscribed behind an entry a planner places in the pipeline of the loop's scope, which
        // takes no push of it and records what it has decided.
        let mut seed_placements = Vec::new();
        let seed_producers = self
            .seed_ops
            .iter()
            .map(|(key, op)| {
                let (seed, placement) = subscribe_seed(op, cx);
                seed_placements.push(placement);
                (key.clone(), seed)
            })
            .collect();
        Box::new(InductionStoreProducer {
            base: ProducerBase::new(
                InductionStoreProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(consumer.clone(), placement),
            seed_placements,
            resumed_after: self.resumed_after.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            state: std::sync::Mutex::new(InductionState {
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
                body_producer,
                breaker: BreakerState::default(),
                #[cfg(debug_assertions)]
                stepped_through: None,
            }),
            run: None,
        })
    }
}

/// An induction store with accumulator state and dispatcher-run control.
pub struct InductionStoreProducer {
    base: ProducerBase,
    /// Per seed stream, the placement of the entry it is subscribed behind, which a planner sets
    /// to the pipeline of the loop's scope.
    seed_placements: Vec<crate::interpreter::dispatcher::Placement>,
    /// The last position a predecessor store reached, which this one's store is decided
    /// through from the moment it opens. Only an induction store with no rows above it resumes —
    /// a nested one's rows belong to the store around it — so this is `None` wherever the
    /// engine tree has levels, and every row opens undecided.
    resumed_after: Option<Position>,
    write_keys: Vec<Value>,
    tap_fields: Vec<SmolStr>,
    state: std::sync::Mutex<InductionState>,
    pub(crate) run: Option<crate::interpreter::dispatcher::loop_scope::InductionRun>,
}
struct InductionState {
    /// Per accumulator key, the per-row seed stream. An induction store with no rows above it has
    /// one row, the empty path, so its seed arrives there.
    seed_producers: Vec<(Value, Box<dyn TileProducer>)>,
    /// What the body says is complete, one predicate per level of its decision stream,
    /// outermost first: the row levels above the stores, then the positions within one. The
    /// drive is what knows, from its source; the store carries it to the read. An induction store
    /// with no rows above it has the one entry — its positions.
    complete_rows: Vec<Predicate>,
    /// One engine per store, nested one level per collection level above it. An induction store
    /// with no rows above it is [`Engines::Store`]; a nested one is [`Engines::Rows`],
    /// each row holding its own seed and changelog rather than a share of one flat log.
    engines: Engines,
    body_producer: Box<dyn TileProducer>,
    /// What the store keeps to run as a pipeline breaker.
    breaker: BreakerState,
    /// The highest path this induction store has stepped, for the check that rows open in
    /// ascending path order and never reopen. Survives [`Engines::remove_covered`], which
    /// moves [`decided_path`](InductionStoreProducer::decided_path) back when it drops the rows it names.
    #[cfg(debug_assertions)]
    stepped_through: Option<Path>,
}

impl InductionStoreProducer {
    /// The store at `row`, opened at `seed` if this is the pull that reaches it.
    ///
    /// Every store opens here, whatever its depth: `resumed_after` is a position of the one
    /// store at the empty path, and a store under a row does not resume, so it is `None`
    /// wherever `row` names one.
    fn open_at<'a>(
        &self,
        state: &'a mut InductionState,
        row: &Path,
        seed: &HashMap<Value, Value>,
    ) -> &'a mut CommitEngine {
        debug_assert!(
            row.is_empty() || self.resumed_after.is_none(),
            "an induction store with rows above it does not resume, so its rows open undecided; \
             row {row:?} would open at {:?}",
            self.resumed_after
        );
        let resumed_after = self.resumed_after.clone();
        state.engines.store_at(row, &mut || {
            CommitEngine::seeded_at(resumed_after.clone(), seed.clone())
        })
    }

    /// The region of the body's decisions this store has consumed, as the guard that
    /// names it.
    ///
    /// A **prefix of the path**, because that is what a sequential drive delivers and so
    /// what has been consumed: the enclosing positions before the head entirely, and within the
    /// head row everything up to its last decided position. Saying it as a `Codomain`
    /// instead would claim that prefix in *every* row, including rows that have delivered
    /// nothing — and a release is a promise never to ask again.
    fn consumed_guard(&self, decided: &Path) -> TileGuard {
        domain_prefix_over(decided.to_vec(), &path_levels(self.tiling()))
    }

    /// Release the seed streams through `decided`, whose rows are open and so read no seed
    /// again.
    ///
    /// A nested store's seed streams are keyed by the enclosing positions, so the region is
    /// the rows through `decided`'s, each opened and reading its seed no more. The streams
    /// are shared with the drive's reseeds, and a `FanOut` passes on only what every slot
    /// has released, so a store holding them would pin the seed stream for the whole run.
    /// An induction store with no rows above it reads one seed, whole, and releases it when the
    /// body goes terminal.
    fn release_seeds_through(&self, state: &mut InductionState, decided: &Path) {
        let Some((row, _)) = decided.split_position().filter(|(row, _)| !row.is_empty()) else {
            return;
        };
        for (_, producer) in &mut state.seed_producers {
            let levels = path_levels(producer.tiling());
            producer.release(domain_prefix_over(row.to_vec(), &levels));
        }
    }

    /// The path this induction store has decided through: the last row it opened at each level,
    /// down to that store's watermark. `None` before anything is decided.
    ///
    /// The drive is sequential, so the last row of a level that has decided a position is
    /// the one still running and every row before it is complete — which is what makes one
    /// path the whole cursor. A row opened after it decided nothing, its inner loop having
    /// no position, so it names no position to stand at.
    fn decided_path(&self, state: &InductionState) -> Option<Path> {
        fn walk(at: &Engines) -> Option<Vec<Value>> {
            match at {
                Engines::Store(engine) => {
                    Some(vec![engine.as_ref()?.decided_watermark()?.value().clone()])
                }
                Engines::Rows(rows) => rows.iter().rev().find_map(|(row, below)| {
                    let mut path = vec![row.clone()];
                    path.extend(walk(below)?);
                    Some(path)
                }),
            }
        }
        walk(&state.engines).map(Path::from)
    }

    /// Publish a flat store's seed before its source delivers the first loop position.
    /// A carried seed must remain available to the next handover while the source is idle.
    pub(crate) fn initialize_seed(&mut self) -> bool {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;
        if !matches!(state.engines, Engines::Store(None)) {
            return false;
        }
        let row = Path::default();
        let Some(seed) = self.row_seeds(state).remove(&row) else {
            return false;
        };
        self.open_at(state, &row, &seed);
        let tile = self.render_store(state);
        if let Some(cycle) = &state.breaker.cycle {
            cycle.publish(&tile);
        }
        state.breaker.snapshot = Some(tile);
        true
    }

    /// Each row's value before any of its positions, read from the per-key seed streams.
    ///
    /// A seed stream is keyed the way the body it was compiled against is. An induction store with
    /// no rows above it takes the position alone, so its seed is one value and it seeds
    /// the empty path. A nested store's body takes the `(enclosing, position)` pair, so
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
    fn row_seeds(&self, state: &mut InductionState) -> HashMap<Path, HashMap<Value, Value>> {
        let levels_above = self.tiling().levels();
        let keys = state.seed_producers.len();
        let mut seeds: HashMap<Path, HashMap<Value, Value>> = HashMap::new();
        for (key, producer) in &mut state.seed_producers {
            let tile = producer.get(producer.tiling().universal_guard());
            for (row, value) in decode_row_seeds(&tile, levels_above) {
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

    /// The delta a decision applies: the writes and the taps that fire.
    ///
    /// An idle write or tap is omitted, so its per-position read skips that position; a
    /// position that fires nothing appends nothing at all, and each accumulator holds from
    /// the seed or its latest earlier change.
    fn write_set(&self, writes: Vec<Option<Value>>) -> Option<HashMap<Value, Value>> {
        debug_assert_eq!(
            writes.len(),
            self.write_keys.len(),
            "the decision's write set aligns with the store's write keys"
        );
        let delta: HashMap<Value, Value> = self
            .write_keys
            .iter()
            .cloned()
            .zip(writes)
            .filter_map(|(key, value)| value.map(|v| (key, v)))
            .collect();
        (!delta.is_empty()).then_some(delta)
    }

    /// One step of the store: read the seeds and the body, open the rows and decide the
    /// positions the body has decided, release what the store has consumed, and render the
    /// store. A dispatcher consume makes as many steps as its morsel requires.
    fn step(&self, state: &mut InductionState) -> Tile {
        // Read the seeds before the body. A store opens the moment both its row and its
        // seed are known, and for the store at the empty path, an induction store with no rows
        // above it, the row is known from the start, so it opens here. It has to: the driver reads the
        // accumulator's value before the first position out of this store, and a store
        // that is not open carries none. A nested store's rows open below, at a row's first
        // decision or once the body calls it complete, so none of its seeds lands at the
        // empty path.
        // An open store of its own has read its seed, and nothing more of it is wanted.
        let row_seeds = match &state.engines {
            Engines::Store(Some(_)) => HashMap::new(),
            _ => self.row_seeds(state),
        };
        if let Some(seed) = row_seeds.get(&Path::default()) {
            let seed = seed.clone();
            self.open_at(state, &Path::default(), &seed);
            // The seed is read once, at the store's opening, so it is released there.
            for (_, producer) in &mut state.seed_producers {
                producer.release(producer.tiling().universal_guard());
            }
        }
        let body_tile = state
            .body_producer
            .get(state.body_producer.tiling().universal_guard());
        // **Every enclosing position opens**, a row whose inner loop runs no position included:
        // its store holds its seed and nothing else, which is the value the row's loop ends
        // at. Such a row has no decision to open it, so it opens once the body calls it
        // complete. The drive is sequential, so every row the body calls complete precedes
        // the one still running, and opening them before this pull's decisions keeps the
        // rows opening in ascending order.
        if let Some(rows) = self.tiling().levels().checked_sub(1) {
            let complete = body_tile.completion_at(CurryLevel::new(rows));
            let mut ready: Vec<&Path> = row_seeds
                .keys()
                .filter(|row| {
                    !row.is_empty()
                        && state.engines.get(row).is_none()
                        && complete.contains_path(row)
                })
                .collect();
            ready.sort();
            let ready: Vec<(Path, HashMap<Value, Value>)> = ready
                .into_iter()
                .map(|row| (row.clone(), row_seeds[row].clone()))
                .collect();
            for (row, seed) in ready {
                self.open_at(state, &row, &seed);
            }
        }
        // Consume the body's decisions **in ascending position order**, starting past
        // the last position decided and stopping at the first the body has not
        // decided. The next position need not be the next integer: a restricted loop
        // source skips the extent positions its filter excluded, and the store
        // decides only the positions it iterates. The decision gates commit (append
        // the change) vs carry (`step(_, None)` — the value inherits from the seed
        // or the latest earlier change). The driver emits one position per pull, so
        // this normally steps once; consuming a run costs nothing extra and keeps
        // the store's rule independent of that rate.
        let started_at = self.decided_path(state);
        // A decision names the store it belongs to and the position within it, as the path
        // down the levels the recurrence is indexed by. An induction store with no rows above it
        // has paths of one component, which is the whole of that statement at depth zero:
        // one store, at the empty path.
        let decisions = match body_tile.deepest_values() {
            values @ (Tile::Scalar(_) | Tile::Record { .. }) => decision_column(values),
            _ => return self.render_store(state),
        };
        for (path, idx) in decided_paths(&body_tile) {
            let Some((rows, inner)) = path.split_position() else {
                unreachable!("a decision's path names a store and a position in it")
            };
            let (row, inner) = (Path::from(rows.to_vec()), Position::new(inner.clone()));
            if state
                .engines
                .get(&row)
                .and_then(CommitEngine::decided_watermark)
                .is_some_and(|d| inner <= *d)
            {
                continue;
            }
            // Carry writes lead, taps follow (the layout `build_induction_store_single`
            // sets). A position applies the writes and the taps that fire on its route; an
            // idle one is omitted from the delta, so its per-position read (`store_delta_at`)
            // skips this position. A position that fires nothing carries every accumulator.
            let Some(writes) =
                decision_at_index(&decisions, idx, &self.write_keys, &self.tap_fields)
            else {
                break;
            };
            // A row with no seed yet is left for a later pull rather than opened at
            // nothing: the carry at its first position folds to the seed, so opening
            // without one answers a value the row never held. An open row needs no seed,
            // and the seeds of the positions it has decided are released below.
            let seed = match state.engines.get(&row) {
                Some(_) => HashMap::new(),
                None => match row_seeds.get(&row) {
                    Some(seed) => seed.clone(),
                    None => break,
                },
            };
            #[cfg(debug_assertions)]
            {
                debug_assert!(
                    state
                        .stepped_through
                        .as_ref()
                        .is_none_or(|high| path > *high),
                    "an induction store steps its decisions in ascending path order and never \
                     reopens a row: stepping {path:?} at or below {:?}, the highest path already \
                     stepped",
                    state.stepped_through
                );
                state.stepped_through = Some(path.clone());
            }
            let write_set = self.write_set(writes);
            let engine = self.open_at(state, &row, &seed);
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
        // A consuming nested store also releases its body by whole rows (below).
        let by_rows = matches!(state.engines, Engines::Rows(_));
        if let Some(decided) = self.decided_path(state)
            && Some(&decided) != started_at.as_ref()
        {
            state.body_producer.release(self.consumed_guard(&decided));
            self.release_seeds_through(state, &decided);
        }
        // The body says what is complete at every level of its decision stream, and the
        // store publishes each level on its own so a read can answer a row as a whole. Every
        // level is read: a standing level's rows are not the induction store's, the loop around a
        // standing level waits on that level's own last row, and the innermost level is the
        // positions a store will gain no more of.
        //
        // The outermost level saying `True` is what closes the store's domain (`terminal`),
        // so a settled read resolves: a level's predicate means complete at every depth
        // beneath it. Each row's watermark in `frontier` stays where it is, spanning a
        // trailing run of carries, so `store_frontier` does not undercount to the latest
        // change position when the tail is all carry. The driver closes its body-input domain
        // once a complete source has been fully emitted, and that rides the body chain down to
        // here.
        for level in 0..state.complete_rows.len() {
            let Tile::DataFunction {
                domain_predicate, ..
            } = body_tile.values_at(CurryLevel::new(level))
            else {
                continue;
            };
            state.complete_rows[level] = state.complete_rows[level].union(domain_predicate);
        }
        // A row whose keys the level beneath states complete in full is complete: the body states
        // a row's last position, and the level beneath it whole, before the level above learns
        // the row has ended, and a release of the row whole then leaves the store no step that
        // would read that.
        for level in (0..state.complete_rows.len().saturating_sub(1)).rev() {
            let whole = rows_whole_beneath(&state.complete_rows[level + 1]);
            state.complete_rows[level] = state.complete_rows[level].union(&whole);
        }
        // Reading a terminal body stream as "the whole extent is decided" rests on the loop
        // above having consumed all of it. That loop stops at the first position it cannot
        // decode as a decision, so a terminal stream with an undecodable row and decisions
        // past it would close the frontier early and drop them without a sound. The check
        // reads paths, since an inner position repeats across rows; `decided_paths` is in
        // drive order, so the first past the cursor is the lowest. It re-reads every decision,
        // and runs on each step while the body is terminal and not yet released whole, which is
        // one step once every decision is stepped.
        //
        // A terminal body whose every decision is stepped offers nothing more, so the store
        // releases it whole. Its release through the decided path alone never names a position
        // the loop's source filtered out, and a dispatcher's finish checks that the body has
        // released every morsel the store consumed.
        if body_tile.is_terminal() && !state.body_producer.obsolete_guard().is_universal() {
            let through = self.decided_path(state);
            let undecided = decided_paths(&body_tile)
                .into_iter()
                .map(|(path, _)| path)
                .find(|path| through.as_ref().is_none_or(|d| path > d));
            debug_assert!(
                undecided.is_none(),
                "induction store: the body's decision stream is terminal but still decides \
                 {undecided:?}, past the watermark {through:?}"
            );
            if undecided.is_none() {
                state
                    .body_producer
                    .release(state.body_producer.tiling().universal_guard());
            }
        }
        // A consuming nested store releases whole each row the body calls complete, a row of no
        // position among them, once it holds no decision the store has not stepped. A loop's
        // scope closes a row by stepping the store until its body has released the row
        // (`src/interpreter/design-dispatcher.md`, "A loop in rounds"), and the release through
        // the decided path names the row's positions only, not the keys past them.
        if by_rows {
            // A loop's scope queues this store rows of the level directly above its positions,
            // and a scope around that one rows of a level above, so the release covers every
            // level above the positions.
            let through = self.decided_path(state);
            let unstepped: Vec<Path> = decided_paths(&body_tile)
                .into_iter()
                .map(|(path, _)| path)
                .filter(|path| through.as_ref().is_none_or(|decided| path > decided))
                .collect();
            let rows: Vec<TileGuard> = (0..state.complete_rows.len() - 1)
                .filter_map(|level| {
                    let complete = &state.complete_rows[level];
                    debug_assert!(
                        unstepped
                            .iter()
                            .all(|path| !complete.contains_path(&path[..=level])),
                        "induction store: the body calls rows complete that still decide \
                         positions past the watermark {through:?}: {unstepped:?}"
                    );
                    let rows = unstepped.iter().fold(complete.clone(), |rows, path| {
                        match Projection::of_path(&path[..=level]) {
                            Projection::Keys { keys, .. } => rows.minus(&keys),
                            other => unreachable!("a path's projection names its keys: {other:?}"),
                        }
                    });
                    (!rows.is_false()).then(|| {
                        CurryLevel::new(level)
                            .wrap_guard(TileGuard::Function(FunctionGuard::Domain(rows)))
                    })
                })
                .collect();
            if !rows.is_empty() {
                state.body_producer.release(TileGuard::flatten_or(rows));
            }
        }
        // The body states complete positions that hold no decision: positions the loop's source
        // filtered out, and keys a live source calls complete and never delivers. Nothing is
        // left to decide there, so the store releases them as it releases a decided position,
        // whether or not a later position is decided; a position that still holds a decision
        // the store has not stepped stays held. A store with rows above it releases by rows
        // instead, while consuming (above), and its drive states read-past positions only where
        // it has none.
        if matches!(state.engines, Engines::Store(_)) {
            let level = state.complete_rows.len() - 1;
            let through = self.decided_path(state);
            let empty = decided_paths(&body_tile)
                .into_iter()
                .map(|(path, _)| path)
                .filter(|path| through.as_ref().is_none_or(|decided| path > decided))
                .fold(
                    state.complete_rows[level].clone(),
                    |empty, path| match Projection::of_path(&path) {
                        Projection::Keys { keys, .. } => empty.minus(&keys),
                        other => unreachable!("a path's projection names its keys: {other:?}"),
                    },
                );
            if !empty.is_false() {
                state.body_producer.release(
                    CurryLevel::new(level)
                        .wrap_guard(TileGuard::Function(FunctionGuard::Domain(empty))),
                );
            }
        }
        // A nested store's rows open as they are decided and release their seeds as they
        // go (`release_seeds_through`); the rest go once the body is done, since a row that
        // ran no position answers from the enclosing position's default instead. The induction
        // store's own store released its seed when it opened.
        if body_tile.is_terminal() && matches!(state.engines, Engines::Rows(_)) {
            for (_, producer) in &mut state.seed_producers {
                producer.release(producer.tiling().universal_guard());
            }
        }
        // A finite input's last consumed prefix closes its release to the whole extent.
        // That release settles every decision even when the last tile states only the prefix.
        if state.body_producer.obsolete_guard().is_universal() {
            state.complete_rows.fill(Predicate::True);
        }
        self.render_store(state)
    }

    /// This induction store's engines as a tile, each store `terminal` once the recurrence is final
    /// (the accumulator can no longer change, so a downstream `StoreFinalRead` resolves).
    ///
    /// A store waiting for its seed contributes nothing: an undecided frontier, no change,
    /// and no value before any position. That is what it holds, and it is what the driver
    /// reads to know not to emit yet.
    fn render_store(&self, state: &InductionState) -> Tile {
        let store = render_engines(&state.engines, self.tiling(), &state.complete_rows);
        debug_assert!(
            store.check_from(self.tiling()),
            "rendered induction store tile does not match the induction store's tiling"
        );
        store
    }
}

impl TileProducer for InductionStoreProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        visit("body", &*state.body_producer);
        for (key, seed) in &state.seed_producers {
            visit(&format!("seed {key}"), &**seed);
        }
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let state = self
            .state
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        visit("body", &mut *state.body_producer);
        for (key, seed) in &mut state.seed_producers {
            visit(&format!("seed {key}"), &mut **seed);
        }
    }

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(state.engines.held_values())
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if state.breaker.snapshot.is_none() {
            return render_engines(
                &Engines::unopened(self.tiling()),
                self.tiling(),
                &state.complete_rows,
            );
        }
        let mut tile = state.breaker.offer();
        if matches!(state.engines, Engines::Rows(_)) && !self.obsolete_guard().is_empty() {
            tile.remove_guarded(self.obsolete_guard().clone());
        }
        tile
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn read_cycle_again(&mut self) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let cycle = state
            .breaker
            .cycle
            .clone()
            .expect("an induction store's round reads its cyclic fan-out's cycle again");
        self.read_cycle_inputs(state, &cycle);
    }

    fn enter_cycle(&mut self, cycle: Cycle) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.breaker.enter_cycle(cycle);
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // Changelog GC (mirrors [`CommitProducer::release_impl`]). The store sits behind a
        // `FanOut`, so this guard is the **meet** of what every slot has released — the
        // drive, the dense and tap reads, a settled read — and so the region safe to
        // reclaim. `gc_released_prefix` keeps the carry source a position can still fold
        // back to, including the one the drive folds at the frontier, so the GC never
        // strands the recurrence and a never-terminating loop's changelog stays at
        // O(keys) plus the slowest reader's lag.
        //
        // A release names a region of the induction store, one arm per level ([`domain_prefix`]),
        // so the prefix each store may reclaim is its own: the positions of that store the
        // guard covers. Asked of the store's own decided positions rather than of the
        // predicate, because a qualified predicate answers about a **path** and a
        // watermark is a value — which is why [`Predicate::max_released_position`] declines
        // one. An induction store with no rows above it is the same walk over one store at the
        // empty path, where the guard is unqualified and every decided position it covers is a
        // prefix.
        let mut at: Vec<Value> = Vec::new();
        state.engines.for_each_store_mut(&mut |rows, engine| {
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
        state.engines.remove_covered(&obsolete_guard);
    }

    fn as_induction_store(&self) -> Option<&InductionStoreProducer> {
        Some(self)
    }

    fn as_induction_store_mut(&mut self) -> Option<&mut InductionStoreProducer> {
        Some(self)
    }
}
impl InductionStoreProducer {
    fn visit_input_producers_mut_in_state(
        &self,
        state: &mut InductionState,
        visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
    ) {
        visit("body", &mut *state.body_producer);
        for (key, seed) in &mut state.seed_producers {
            visit(&format!("seed {key}"), &mut **seed);
        }
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
/// A surface `await_final(x)` does not come through here: it is a [`StoreFinalRead`],
/// sampling the key once its writers have drained.
pub struct StoreValueStream {
    base: OperatorBase,
    store_op: std::sync::Arc<dyn TileOperator>,
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
        store_op: std::sync::Arc<dyn TileOperator>,
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let consumer = shared_consumer(consumer);

        // The stream is keyed by the store's commit ticks, so a region of ticks the store
        // decided names the stream's keys as it is.
        let store_producer = subscribe_forwarding_keeping_keys(&self.store_op, &consumer, cx);
        Box::new(StoreValueStreamProducer {
            base: ProducerBase::new(
                StoreValueStreamProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            carry_forward: self.carry_forward,
            release_cursor: std::sync::Mutex::new(PrefixReleaseCursor::default()),
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
    release_cursor: std::sync::Mutex<PrefixReleaseCursor>,
}

impl TileProducer for StoreValueStreamProducer {
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("store", &*self.store_producer);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("store", &mut *self.store_producer);
    }

    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        // Read the published store without advancing its writers.
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
            if self.release_cursor.lock().unwrap().is_released(tick) {
                continue;
            }
            if let Some(v) = v {
                ticks.push(tick.value().clone());
                values.push(v);
            }
        }
        let mut out = read_tile(
            ColumnValue::from_values(ticks, &Extent::Base(BaseType::UInt)),
            values,
            &self.value_extent,
            domain_predicate.clone(),
        );
        out.restrict_to(&projection_guard.projection_for(self), self.tiling());
        out
    }
    fn release_impl(&self, obsolete_guard: TileGuard) {
        // Advance the emit cursor past every released commit tick (so we don't
        // re-emit a merged prefix — a re-fold that unions this tap at a later
        // frontier would otherwise duplicate a position through the `Memo` merge)
        // AND forward that prefix upstream to the store: a consumer that merged
        // commits `≤ max_tick` no longer needs them, so this read slot releases
        // them. The store reclaims a version only once *every* slot (this reader,
        // the writers) has released it — the cyclic `FanOut` intersects — so
        // forwarding here is safe and is what lets a long-lived collection log shed
        // its merged prefix. A terminal (`True`) release covers the whole
        // changelog.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard {
            let forward = match self.release_cursor.lock().unwrap().advance_from(pred) {
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
/// closes, sampled through [`store_current`]. So it is neither a reduction nor a
/// projection of the history, and needs no seed operand, because the store holds its
/// seed beside its changelog.
///
/// **Under rows** — an inner loop's store, one per enclosing position — it is one such read
/// per row, `K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ V`: each row's value once the induction store calls that row complete,
/// which is its seed where the row's inner loop ran no position.
pub struct StoreFinalRead {
    /// Output tiling [`Tiling::from_extent`] of `V` under the rows it reads one value for: a
    /// terminal read is one value per row, not a stream, and a collection-valued key's value
    /// is handed out as a level, the way every other store read hands it out ([`read_tiling`]).
    base: OperatorBase,
    /// The commit store (a [`Tile::Store`] fan slot).
    store_op: std::sync::Arc<dyn TileOperator>,
    /// The key whose settled value this reads.
    key: Value,
    value_extent: Extent,
    /// How many collection levels stand above the store, the rows it reads one value for.
    levels_above: usize,
}

impl StoreFinalRead {
    pub fn new(
        store_op: std::sync::Arc<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
    ) -> Self {
        Self::per_row_at(store_op, key, value_extent, 0)
    }

    /// One read per row of the `levels_above` levels standing above the store.
    pub fn per_row_at(
        store_op: std::sync::Arc<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
        levels_above: usize,
    ) -> Self {
        let tiling = with_values_at(
            store_op.tiling(),
            CurryLevel::new(levels_above),
            Tiling::from_extent(&value_extent),
        );
        Self {
            base: OperatorBase::new(tiling),
            store_op,
            key,
            value_extent,
            levels_above,
        }
    }
}

impl TileOperator for StoreFinalRead {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("store_op", &*self.store_op));
    }
    fn subscribe(
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // A final read requires completion of this key, even when other store keys remain live.
        let consumer = shared_consumer(consumer);

        let forward = forwarding_consumer_keeping_keys(&consumer);
        let forward: Box<dyn Consumer> = if self.levels_above == 0 {
            Box::new(FinalKeyConsumer {
                key: self.key.clone(),
                downstream: crate::interpreter::widening(forward),
            })
        } else {
            crate::interpreter::notifications::through_values(
                CurryLevel::new(self.levels_above),
                self.tiling(),
                forward,
            )
        };
        let store_producer = self.store_op.clone().clone().subscribe(
            self.store_op.tiling().universal_guard(),
            forward,
            cx,
        );
        Box::new(StoreFinalReadProducer {
            read_frontier: Default::default(),
            base: ProducerBase::new(
                StoreFinalReadProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            levels_above: self.levels_above,
        })
    }
}

struct FinalKeyConsumer {
    key: Value,
    downstream: Box<dyn Consumer>,
}

impl Consumer for FinalKeyConsumer {
    fn notify(
        &mut self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        landing.requiring_final_key(&self.key, |landing| self.downstream.notify(region, landing));
    }
}

struct StoreFinalReadProducer {
    read_frontier: crate::interpreter::tile_operators::DroppedRows,
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    key: Value,
    value_extent: Extent,
    levels_above: usize,
}

impl TileProducer for StoreFinalReadProducer {
    fn restates(&self) -> Restates {
        Restates::Above(CurryLevel::new(self.levels_above))
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("store", &*self.store_producer);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("store", &mut *self.store_producer);
    }

    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn input_level(&self, _: &str, _: CurryLevel) -> Option<CurryLevel> {
        None
    }
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        if self.obsolete_guard().is_universal() {
            return self.tiling().empty_tile();
        }
        // A reader can pull some rows, as one that takes rows as they arrive does, so the answer
        // keeps the rows the pull names.
        if self.levels_above > 0 {
            let mut tile = self.per_row();
            tile.restrict_to(&projection_guard.projection_for(self), self.tiling());
            return tile;
        }
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // Release through the frontier. This read wants the key's value as the store
        // stands, and `gc_released_prefix` keeps each key's carry source where nothing above
        // the boundary supersedes it, so the fold below is never stranded. Without this
        // release the `FanOut`'s meet cannot advance past this slot until the read retires,
        // which holds every version of every key for the length of the loop.
        if let Some(frontier) = store_frontier(&store) {
            let levels = path_levels(self.store_producer.tiling());
            self.read_frontier
                .remember(domain_prefix_over(vec![frontier.into_value()], &levels));
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
        let mut tile = stored_value_tile(value.into_iter().collect(), &self.value_extent);
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.restrict_to(&projection_guard.projection_for(self), self.tiling());
        tile
    }
    fn release_impl(&self, obsolete_guard: TileGuard) {
        self.read_frontier.release_to(&*self.store_producer);
        // Under rows the output's levels are the store's, so a release of rows names the
        // same rows of the store, whose stores those rows' readers are then done with.
        // Beneath the rows the output holds a value where the store holds a store, so only a
        // release of a row's whole value reaches its store ([`through_shared_levels`]).
        if self.levels_above > 0 {
            let input = self.store_producer.tiling().clone();
            self.store_producer
                .release(crate::interpreter::tiling::through_shared_levels(
                    obsolete_guard,
                    self.levels_above,
                    &input,
                ));
            return;
        }
        // A universal release from the one consumer of a scalar retires this read, and
        // releasing the store slot with it is safe: every other reader of the store
        // holds its own guard through the fan, which the fan intersects, so the store
        // reclaims a version only once all of them have released it too.
        if obsolete_guard.is_universal() {
            self.store_producer
                .release(self.store_producer.tiling().universal_guard());
        }
    }
}

impl StoreFinalReadProducer {
    /// Each row's value once the induction store calls the row complete: the row's store as it
    /// stands, its seed where its inner loop ran no position. A row still running is left
    /// out, as a scalar read leaves out a store still running, and the induction store's statement
    /// of which rows are complete is the output's.
    fn per_row(&self) -> Tile {
        let tile = self
            .store_producer
            .get(self.store_producer.tiling().universal_guard());
        let rows = CurryLevel::new(self.levels_above - 1);
        let complete = tile.completion_at(rows);
        let paths = tile.paths_at(rows);
        let mut out = tile;
        let Tile::DataFunction {
            codomain: stores, ..
        } = out.values_at_mut(rows)
        else {
            unreachable!("an induction store with rows holds a collection of stores")
        };
        let n = paths.len();
        let values: Vec<Option<Value>> = (0..n)
            .map(|k| store_value_now(&store_row(stores, k, n), &self.key))
            .collect();
        // A row is answered once complete. One whose key has no value yet — a
        // collection-valued key its seed omits, before its first write — has none to give.
        let whole = (0..n)
            .map(|k| complete.contains_path(&paths[k]) && values[k].is_some())
            .collect::<Vec<bool>>();
        let answered: Vec<Value> = values
            .into_iter()
            .enumerate()
            .filter_map(|(k, v)| v.filter(|_| whole[k]))
            .collect();
        let answered_rows = (0..n)
            .filter(|&k| whole[k])
            .map(|k| Predicate::exactly(&paths[k]))
            .fold(Predicate::False, |all, one| all.union(&one));
        // The level keeps the rows answered, and the answers take their stores' place.
        let level = out.values_at_mut(rows);
        level.retain_keys(&whole);
        let Tile::DataFunction { codomain, .. } = level else {
            unreachable!("retaining keys leaves a collection a collection")
        };
        // The values state their levels whole without knowing which rows they stand under, so
        // they are qualified by the rows answered: a row still running holds no value yet.
        let mut values = stored_value_tile(answered, &self.value_extent);
        values.map_level_predicates(&mut |depth, pred| pred.qualified_by(&answered_rows, depth));
        **codomain = values;
        out
    }
}

/// A **dense** induction-store read: `key`'s value at every position the store decided,
/// folded from its [`Tile::Store`] changelog into `Fun(D, V)`.
///
/// The positions are the store's own domain rather than an enumeration of the loop extent,
/// so a restricted source's read spans exactly the positions the recurrence ran at, in
/// ascending order — which a co-iterated read (`for r in …: cnt += 1; with begin(): store :=
/// store + cnt`) needs to align with its source through `zip_arms_at`. The fold reads the
/// changelog rather than the frontier, so a carry position takes the latest earlier write and
/// a leading carry takes the seed.
///
/// Under rows the read carries the same levels the store does, and produces one history per
/// row, each folded against that row's own store. A loop's trailing read is
/// [`StoreFinalRead`], per row under rows, which samples the settled store and does not come
/// through here.
///
/// This and [`StoreValueStream`] are the same changelog projection over different clocks:
/// loop positions here, commit ticks there. Both share the changelog fold, where a carry
/// holds and a tap is an event ([`fold_changelog_key_ascending`]).
pub struct StoreDenseRead {
    /// Output tiling [`read_tiling`] over `D`.
    base: OperatorBase,
    /// The induction store (a [`Tile::Store`] fan slot).
    store_op: std::sync::Arc<dyn TileOperator>,
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
    /// flat store, its enclosing positions for a nested one, and those rows under the levels
    /// they in turn stand beneath for an induction store inside a deeper nest.
    enclosing: Vec<Extent>,
    /// The level of histories this read rebuilds: the store's own rows. Stated here, where
    /// the levels above the store are counted, because the read's tiling carries the
    /// position level beneath them too — so this is not its innermost level.
    level: Option<CurryLevel>,
}

impl StoreDenseRead {
    pub fn new(
        store_op: std::sync::Arc<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
        carry_forward: bool,
    ) -> Self {
        // A nested store is a store per enclosing position, so its read is one history per
        // row — the shape the enclosing body consumes it at, produced here rather than
        // regrouped afterwards. Recovering the rows from a flat pair-keyed read is not
        // possible: which rows are complete is not a fact about pairs.
        //
        // However many levels stand above the store, the read carries the same ones: a
        // flat store has none, a nested one its enclosing positions, and one beneath a
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // Forward store progress to the consumer: a newly decided position is both a position
        // to emit and the value to emit there, so it is the only news this read has.
        let consumer = shared_consumer(consumer);

        let store_producer = subscribe_forwarding_keeping_keys(&self.store_op, &consumer, cx);
        Box::new(StoreDenseReadProducer {
            base: ProducerBase::new(
                StoreDenseReadProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            ),
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            carry_forward: self.carry_forward,
            domain: self.domain.clone(),
            enclosing: self.enclosing.clone(),
            level: self.level,
            release_cursor: std::sync::Mutex::new(PrefixReleaseCursor::default()),
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
    release_cursor: std::sync::Mutex<PrefixReleaseCursor>,
}

impl StoreDenseReadProducer {
    /// A **nested** induction store's read: one inner history per enclosing position.
    ///
    /// Each row is folded against its own store — its own changelog and its own seed — so
    /// a position that writes nothing resolves to the value that row began with rather
    /// than to the previous row's last write. The enclosing level's `domain_predicate`
    /// comes straight from the store, which knows it because the drive is sequential: a
    /// row can gain no further position once the next row has one.
    fn read_per_row(&self, store: &Tile) -> Tile {
        // Standing levels stand above the induction store and are kept as they are; only the level
        // holding the stores becomes a level of histories. Beneath a standing level the
        // stores are one collection whose groups belong to different enclosing positions, and
        // folding across a group boundary would carry one row's last write into the
        // next — so each group is read on its own and the level put back together
        // (`group_at` / `regroup_beneath`).
        let level = self
            .level
            .unwrap_or_else(|| unreachable!("a per-row read has the store's own rows"));
        // The empty level carries what the store says about that level. An induction store that
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

    /// One induction store's worth: a history per enclosing position, from that row's own store.
    fn read_one_level(&self, store: &Tile) -> Tile {
        let Tile::DataFunction {
            domain: rows,
            codomain,
            domain_predicate,
            ..
        } = store
        else {
            unreachable!(
                "a nested store's read is entered only where the constructor found a \
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
            starts,
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
                    Predicate::qualified(
                        rows,
                        Predicate::at_or_below_in(frontier.value().clone(), &self.domain),
                    )
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
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("store", &*self.store_producer);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("store", &mut *self.store_producer);
    }

    impl_producer_base!();

    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
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
        // carry folds to the store's seed: no external default, and never `None`. The read
        // states complete only what the store's guard (`Tile::to_guard`) names, so the
        // consumer re-pulls until the store is terminal.
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // The store is read whole, since a position's value folds the changelog below it, and
        // the answer is cut to the pull's positions.
        if !self.enclosing.is_empty() {
            let mut out = self.read_per_row(&store);
            out.restrict_to(&projection, self.tiling());
            return out;
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
        // domain must be position-ordered, because a co-iterated read aligns with its
        // source by domain value through `zip_arms_at`.
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
        // A pull at a region of positions is answered there, less what the read released,
        // as every pull is (`Tile::within`).
        let pulled = match Projection::of(&projection_guard) {
            Ok(Projection::Keys { level, keys }) if level == CurryLevel::OUTERMOST => Some(keys),
            _ => None,
        };
        let mut kept: Vec<Position> = Vec::with_capacity(sorted.len());
        let mut values: Vec<Value> = Vec::with_capacity(sorted.len());
        for (p, v) in sorted.iter().zip(folded) {
            if self.release_cursor.lock().unwrap().is_released(p)
                || pulled
                    .as_ref()
                    .is_some_and(|keys| !keys.contains(p.value()))
            {
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
        // The read is decided where the store is: at every position its rounds have run, the
        // positions a round wrote no tap value at and those its source never delivered included
        // (`Tile::to_guard`), and everywhere once it is terminal. A consumer may take that prefix,
        // and a `Memo` may cache it, without waiting for the loop to end, and it releases what the
        // store pushed of it.
        let domain_predicate = match store.to_guard() {
            TileGuard::Function(FunctionGuard::Domain(decided)) => decided,
            other => unreachable!("a flat store's guard names its positions: {other:?}"),
        };
        // A pull at a region states completeness there alone: a position outside it is not read.
        let domain_predicate = match &pulled {
            Some(keys) => domain_predicate.intersect(keys),
            None => domain_predicate,
        };
        let mut out = read_tile(positions, values, &self.value_extent, domain_predicate);
        out.restrict_to(&projection, self.tiling());
        out
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
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
        // its own to compute. Under rows the guard names rows, which the induction store has too
        // — a row released whole leaves its engine tree and its render together
        // ([`Engines::remove_covered`]), so the arm means there what it means here.
        if self.enclosing.is_empty()
            && let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
        {
            // With no rows the released positions come off the render through this
            // cursor; under rows `remove_guarded` takes the whole region at once.
            self.release_cursor.lock().unwrap().advance_from(pred);
        }
        self.store_producer.release(obsolete_guard);
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
    snapshot_at: Option<Position>,
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
    /// The **outer row** this position sits under, for a nested writer: one component per
    /// level above it, outermost first. Levels rather than components of the position,
    /// which is what keeps a position a plain value of its own domain.
    outer_row: Option<Path>,
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
        let mut path: Vec<Value> = self.outer_row.as_ref().map_or(Vec::new(), |p| p.to_vec());
        path.push(self.position.value().clone());
        path
    }
}

/// The inner rows of a driver window that sit under one outer row: the rows of positions,
/// and the enclosing row they are under.
struct DriverGroup {
    /// The outer row's path, one component per level above the positions; `None` for a
    /// window whose positions have no rows above them.
    outer_row: Option<Path>,
    /// The rows of positions under it, ascending. Empty once a release has named them all
    /// while the outer row is still live.
    inner_rows: Vec<DriverRow>,
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
    /// The enclosing position and parameter a **nested** writer's body takes, and `None` for
    /// a top-level one. See [`body_input_tiling`].
    nested: Option<NestedBody>,
    read_extents: Vec<Extent>,
    /// The item slot's tiling, which is the source's own ([`source_item_tiling`]). Held
    /// so an empty window can still render the slot: with no rows there is no slice to
    /// take the shape from.
    item: Tiling,
    /// For a transaction drive, the extent of its source's positions, which each row carries
    /// its item's position in ([`F_ITEM_POSITION`]); `None` for an induction drive, whose
    /// row's position is its item's.
    item_positions: Option<Extent>,
    /// How many rows have ever been pushed — the transaction driver's next attempt
    /// position, its attempts being a contiguous `UInt` domain of its own. Held
    /// across compaction, so a window emptied by a release still knows where it is.
    /// The induction driver takes its positions from its source instead and never
    /// reads this.
    attempts: u64,
    /// The last row and position pushed, for the ascending check. A domain need carry no
    /// successor, so the window records what it has rather than what comes next, and it
    /// records the **row** beside it: a nested store restarts its positions at each
    /// enclosing position, so the check is per row and the window's own contents cannot say
    /// which row that is — compaction empties them.
    highest_pushed: Option<(Option<Path>, Position)>,
    /// The live inner rows, grouped under the outer row each sits under, in ascending order. A
    /// group stays until a release names its outer row whole, which is later than the release
    /// of its last position: its key is in what the window renders, and the drive has called
    /// it complete, so a window that kept only the inner rows would drop a key it still owes.
    /// A window with no rows above its positions has the one group of inner rows under no
    /// outer row.
    groups: Vec<DriverGroup>,
    /// Highest absolute position a consumer has released. The body fans this
    /// input through a `Memo` that pulls it several times per round, so an
    /// already-released position must not re-emit — that would duplicate a
    /// domain position in the `Memo`'s append-merge.
    release_cursor: std::sync::Mutex<PrefixReleaseCursor>,
}

impl DriverWindow {
    /// The values the window holds: each live row's snapshot, item and enclosing
    /// parameter.
    fn held_values(&self) -> usize {
        self.inner_rows()
            .map(|r| {
                r.snapshot.len()
                    + r.item.cell_count()
                    + r.enclosing.as_ref().map_or(0, Tile::cell_count)
            })
            .sum()
    }

    /// How many collection levels stand above the positions, and 0 for a drive whose rows
    /// are its positions. The paths such a drive indexes by are one longer — the row
    /// levels, then the position within the innermost.
    fn levels_above(&self) -> usize {
        self.nested.as_ref().map_or(0, |n| n.rows.len())
    }

    /// The live inner rows, in ascending order.
    fn inner_rows(&self) -> impl DoubleEndedIterator<Item = &DriverRow> {
        self.groups.iter().flat_map(|g| g.inner_rows.iter())
    }

    /// How many inner rows are live.
    fn inner_row_count(&self) -> usize {
        self.groups.iter().map(|g| g.inner_rows.len()).sum()
    }

    fn new(
        domain: Extent,
        nested: Option<NestedBody>,
        read_extents: Vec<Extent>,
        item: Tiling,
        item_positions: Option<Extent>,
    ) -> Self {
        Self {
            domain,
            nested,
            read_extents,
            item,
            item_positions,
            attempts: 0,
            highest_pushed: None,
            groups: Vec::new(),
            release_cursor: std::sync::Mutex::new(PrefixReleaseCursor::default()),
        }
    }

    /// The next attempt position of a driver whose positions are its own contiguous
    /// count — the transaction driver's.
    fn next_attempt(&self) -> Position {
        Position::new(Value::UInt(self.attempts))
    }

    /// Append an inner row at absolute position `position`, under `outer_row`.
    fn push(
        &mut self,
        snapshot: Vec<Value>,
        item: Tile,
        enclosing: Option<Tile>,
        outer_row: Option<Path>,
        item_position: Position,
        position: Position,
    ) -> &mut DriverRow {
        debug_assert_eq!(
            snapshot.len(),
            self.read_extents.len(),
            "a body-input row carries one snapshot value per read key"
        );
        // Positions ascend **within an outer row**: a nested store restarts its positions at
        // each enclosing position, and the outer row is the level above rather than a
        // component of the position, so the two runs are independent.
        debug_assert!(
            self.highest_pushed
                .as_ref()
                .is_none_or(|(r, h)| *r != outer_row || position > *h),
            "body-input positions ascend within an outer row: pushing {position} at or below \
             the highest already pushed ({:?})",
            self.highest_pushed
        );
        self.highest_pushed = Some((outer_row.clone(), position.clone()));
        if self.groups.last().is_none_or(|g| g.outer_row != outer_row) {
            self.groups.push(DriverGroup {
                outer_row: outer_row.clone(),
                inner_rows: Vec::new(),
            });
        }
        debug_assert_eq!(
            enclosing.is_some(),
            self.nested.is_some(),
            "a nested writer's body takes its enclosing parameter at every row, and a \
             top-level one at none"
        );
        debug_assert_eq!(
            outer_row.is_some(),
            self.nested.is_some(),
            "a nested writer's inner rows each name the outer row they belong to"
        );
        let group = self.groups.last_mut().expect("a group was just ensured");
        group.inner_rows.push(DriverRow {
            snapshot_at: None,
            snapshot,
            item,
            enclosing,
            outer_row,
            item_position,
            position,
        });
        self.attempts += 1;
        group.inner_rows.last_mut().expect("the pushed row")
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
            g => {
                self.groups.retain(|group| {
                    group
                        .outer_row
                        .as_ref()
                        .is_none_or(|outer_row| !g.covers_path(outer_row))
                });
                for group in &mut self.groups {
                    group.inner_rows.retain(|r| !g.covers_path(&r.path()));
                }
            }
        }
    }

    /// The newest live row with its absolute position, or `None` when the window
    /// is empty.
    fn newest(&self) -> Option<(&Position, &DriverRow)> {
        self.inner_rows().next_back().map(|r| (&r.position, r))
    }

    /// Drop the released attempt prefix of a window with no enclosing rows.
    fn acknowledge(&mut self, pred: &Predicate) {
        let extent = self.release_cursor.lock().unwrap().advance_from(pred);
        // Only a window with no rows above its positions acknowledges, so its inner rows are
        // the one group's.
        debug_assert!(
            self.nested.is_none(),
            "a release is acknowledged by a window with no rows above its positions"
        );
        let Some(group) = self.groups.first_mut() else {
            return;
        };
        let drop_through = match extent {
            ReleasedExtent::Nothing => return,
            ReleasedExtent::All => group.inner_rows.len(),
            // Positions ascend, so the released ones are a prefix of the window.
            ReleasedExtent::Through(ref w) => {
                group.inner_rows.partition_point(|r| r.position <= *w)
            }
        };
        group.inner_rows.drain(..drop_through);
    }

    /// Every position the drive has emitted, as the prefix through the last one pushed.
    ///
    /// Beneath an enclosing position the positions restart, so the prefix is a path's: every
    /// position under each enclosing position before the last one's, at every level, and the
    /// positions up to the last one under that row itself. Reading the position column
    /// alone would say the same of a row the drive has not reached — over a nest of two,
    /// `(0,0) (0,1) (1,0)` holds positions `0, 1, 0`, and the keys alone claim position
    /// `1` under enclosing position `1` as well.
    fn emitted_prefix(&self) -> Predicate {
        let Some((row, position)) = &self.highest_pushed else {
            return Predicate::False;
        };
        let rows: &[Value] = row.as_ref().map_or(&[], |r| r.as_ref());
        self.path_prefix(rows, position.value(), true)
    }

    /// Every path ordered before the position `position` under the enclosing positions `rows`,
    /// and that path itself when `inclusive`, stated at the position level: every position
    /// under each enclosing position before the path's, at every level, then the positions under
    /// the path's own row up to its own.
    fn path_prefix(&self, rows: &[Value], position: &Value, inclusive: bool) -> Predicate {
        let own = match inclusive {
            true => Predicate::at_or_below_in(position.clone(), &self.domain),
            false => Predicate::below_in(position.clone(), &self.domain),
        };
        (0..rows.len())
            .map(|level| {
                let row_domain = &self
                    .nested
                    .as_ref()
                    .expect("a window with rows above its positions is nested")
                    .rows[level];
                let earlier = Predicate::qualified(
                    Predicate::exactly(&rows[..level]),
                    Predicate::below_in(rows[level].clone(), row_domain),
                );
                earlier.descend(rows.len() - level)
            })
            .chain(std::iter::once(Predicate::qualified(
                Predicate::exactly(rows),
                own,
            )))
            .reduce(|a, b| a.union(&b))
            .unwrap_or(Predicate::False)
    }

    /// The window as the body's input tile, terminal once `done`, with the rows the drive
    /// knows are complete — one predicate per row level above the positions, outermost
    /// first, and none for a body whose rows are its positions — and the positions it has read
    /// past without emitting, `read_past`.
    ///
    /// [`reclaim`](Self::reclaim) has already dropped what a release named, so every
    /// retained row is live: a re-pull within a round re-emits only what the body has not
    /// merged, and an already-released position cannot come back to duplicate a domain
    /// position in the body's `Memo`.
    fn render(&self, done: bool, complete_rows: &[Predicate], read_past: &Predicate) -> Tile {
        // Column `i` is read key `i`'s snapshot, and the item's is the rows' own slices
        // run together. Same index that names the field, so the layout stays the tiling's.
        // Each row's item is a collection stated over its own paths, taken from the source
        // one position at a time, so its statements are qualified by that position's path as
        // the column stacks them ([`Predicate::beneath`]).
        let items = column_of_rows(
            self.inner_rows().map(|r| {
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
            .inner_rows()
            .map(|r| Predicate::exactly(&r.path()))
            .fold(Predicate::False, |all, one| all.union(&one));
        let fields = body_input_fields(&self.read_extents, items, |i, ext| {
            // A snapshot value comes from the store, which holds one value per key per
            // tick, so it is opened into the level the body reads it as. The column states
            // its values whole without knowing which rows it stands under, so it is qualified
            // by the rows it does.
            let mut column = stored_value_tile(
                self.inner_rows().map(|r| r.snapshot[i].clone()).collect(),
                ext,
            );
            column.map_level_predicates(&mut |depth, pred| pred.qualified_by(&held_rows, depth));
            column
        });
        let mut fields = fields;
        if let Some(extent) = &self.item_positions {
            fields.insert(
                SmolStr::new_static(F_ATTEMPT_SNAPSHOT),
                Tile::Scalar(ColumnValue::from_values(
                    self.inner_rows()
                        .map(|row| {
                            row.snapshot_at
                                .as_ref()
                                .expect("a transaction attempt carries its snapshot")
                                .value()
                                .clone()
                        })
                        .collect(),
                    &Extent::Base(BaseType::UInt),
                )),
            );

            fields.insert(
                SmolStr::new_static(F_ITEM_POSITION),
                Tile::Scalar(ColumnValue::from_values(
                    self.inner_rows()
                        .map(|r| r.item_position.value().clone())
                        .collect(),
                    extent,
                )),
            );
        }
        let slots = Tile::record(fields);
        let codomain = match &self.nested {
            None => slots,
            Some(n) => Tile::record(HashMap::from([
                (
                    tuple_field(0),
                    column_of_rows(
                        self.inner_rows().map(|r| {
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
            .inner_rows()
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
            self.emitted_prefix().union(read_past)
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
        // sequential — order-dependent logic is what an induction store exists for, so there
        // is nothing to reorder. A level's key begins a new run wherever the path down to it
        // differs from the previous row's, so a nest of any depth is one walk.
        let depth = nested.rows.len();
        let mut keys: Vec<Vec<Value>> = vec![Vec::new(); depth];
        // `starts[d]` indexes `keys[d]`, one entry per key of the level above it; the top
        // level stands at the one row every tile has.
        let mut starts: Vec<Vec<usize>> = vec![Vec::new(); depth];
        starts[0].push(0);
        let mut position_starts: Vec<usize> = Vec::new();
        let mut prev: Option<&Path> = None;
        // A group stands until a release names its outer row whole, so an outer row whose
        // inner rows are all released is a key with no position under it.
        let mut at = 0;
        for group in &self.groups {
            let path = group
                .outer_row
                .as_ref()
                .expect("a nested inner row names the outer row it sits under");
            for d in 0..depth {
                if prev.is_some_and(|q| q[..=d] == path[..=d]) {
                    continue;
                }
                match starts.get_mut(d + 1) {
                    Some(below) => below.push(keys[d + 1].len()),
                    None => position_starts.push(at),
                }
                keys[d].push(path[d].clone());
            }
            at += group.inner_rows.len();
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
            position_starts,
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
                std::mem::take(&mut starts[d]),
                ColumnValue::from_values(std::mem::take(&mut keys[d]), &nested.rows[d]),
                Box::new(tile),
                level_complete,
                BitSet::new(),
            );
        }
        tile
    }
}

/// Driver subscriptions and control handles. The source entry records arrivals in source keys;
/// store progress forwards to the driver's consumer so its published snapshot can be read again.
struct DriverInputs {
    consumer: SharedConsumer,
    /// The source entry, placed in an induction scope's request pipeline or a transaction
    /// store's writer pipeline.
    placement: crate::interpreter::dispatcher::Placement,
    /// Where the entry in front of the source records a decided push while unplaced.
    decides: crate::interpreter::dispatcher::CompletionTarget,
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// Set by every notification the source sends, for a driver that pulls the source
    /// only when it has news ([`InductionDriverProducer`], [`TransactDriverProducer`]).
    source_news: crate::interpreter::tile_operators::Arrivals,
}

/// `op` subscribed behind an entry no planner places: an input its producer reads only by pull,
/// as a store reads its seed at a step, so a push from a pipeline beneath it stops there. Nothing
/// is notified through it.
fn subscribe_pulled(
    op: &std::sync::Arc<dyn TileOperator>,
    cx: &mut SubscribeContext,
) -> Box<dyn TileProducer> {
    subscribe_behind_entry(op, cx).0
}

/// `op` subscribed whole behind an unplaced entry
/// ([`Entry::unplaced`](crate::interpreter::dispatcher::Entry::unplaced)), and the entry's
/// placement, which a planner sets to place it in a pipeline.
fn subscribe_behind_entry(
    op: &std::sync::Arc<dyn TileOperator>,
    cx: &mut SubscribeContext,
) -> (
    Box<dyn TileProducer>,
    crate::interpreter::dispatcher::Placement,
) {
    let (producer, placement, _) = subscribe_deciding(op, None, None, cx);
    (producer, placement)
}

/// [`subscribe_behind_entry`], answering beside the placement the entry's decided target
/// ([`CompletionTarget`](crate::interpreter::dispatcher::CompletionTarget)).
fn subscribe_deciding(
    op: &std::sync::Arc<dyn TileOperator>,
    arrivals: Option<&crate::interpreter::tile_operators::Arrivals>,
    item_level: Option<CurryLevel>,
    cx: &mut SubscribeContext,
) -> (
    Box<dyn TileProducer>,
    crate::interpreter::dispatcher::Placement,
    crate::interpreter::dispatcher::CompletionTarget,
) {
    let (entry, placement) = crate::interpreter::dispatcher::Entry::unplaced(op.tiling().clone());
    let decides = entry.complete_target();
    let entry: Box<dyn Consumer> = match item_level {
        Some(level) => {
            crate::interpreter::notifications::through_values(level, op.tiling(), Box::new(entry))
        }
        None => Box::new(entry),
    };
    let consumer = match arrivals {
        Some(arrivals) => arrivals.consumer(entry),
        None => entry,
    };
    let producer = op
        .clone()
        .clone()
        .subscribe(op.tiling().universal_guard(), consumer, cx);
    (producer, placement, decides)
}

fn subscribe_driver_inputs(
    store_op: &std::sync::Arc<dyn TileOperator>,
    source_op: &std::sync::Arc<dyn TileOperator>,
    item_level: CurryLevel,
    consumer: Box<dyn Consumer>,
    cx: &mut SubscribeContext,
) -> DriverInputs {
    let consumer = shared_consumer(consumer);
    let source_news = crate::interpreter::tile_operators::Arrivals::new();
    source_news.record(&Projection::Everything);
    // The source entry receives pushes in source keys. The planner places it in the induction
    // scope's request pipeline or transaction store's writer pipeline; otherwise it stops pushes
    // and the source is read by pull.
    let (source_producer, placement, decides) =
        subscribe_deciding(source_op, Some(&source_news), Some(item_level), cx);
    // The store's progress changes what the drive renders — the next position it may
    // emit, and which rows it calls complete — so its notifications reach the drive's consumer.
    let store_producer = subscribe_forwarding(store_op, &consumer, cx);
    DriverInputs {
        consumer,

        placement,
        decides,
        store_producer,
        source_producer,
        source_news,
    }
}

/// What a **nested** drive carries and a top-level one does not.
///
/// Two facts, and nothing else: a nested body takes the enclosing parameter beside its
/// slots, and a nested accumulator restarts at each enclosing position. Everything else about
/// the drive is the same operation at a deeper path.
pub struct NestedDrive<T> {
    /// The enclosing positions and parameter the body input carries.
    pub body: NestedBody,
    /// `Fun((outer, inner), (ᴘ, Pos))` — each position's enclosing parameter, which the
    /// body reads and which the reseeds are compiled over.
    pub pairs: T,
    /// Per read key, `Fun((outer, inner), V)` — where that accumulator restarts at an
    /// enclosing position boundary.
    pub reseeds: Vec<T>,
}

/// A nested drive's inputs for one pull, keyed by the paths they answer at.
struct NestedAt {
    /// Each position's enclosing parameter, which the body takes beside its slots.
    pairs: HashMap<Path, Tile>,
    /// Per read key, where that accumulator restarts at an enclosing position boundary.
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
/// - **It reseeds at each enclosing position.** A nested accumulator restarts where the
///   enclosing one had got to — `h(p, 0) = body(seed(p), item(p, 0))`, carrying within an
///   enclosing position as usual. At an enclosing-position boundary the body's snapshot is
///   that position's reseed, read from `reseeds`; everywhere else it is read from the store,
///   which carries as a flat store does. A boundary is a position whose enclosing components
///   differ from the last one emitted. At depth zero that is the first position, where the
///   store already holds its seed, so the reseed and the store's value are the same.
/// - **It passes the enclosing parameter through.** The body takes `((ᴘ, Pos), slots)`
///   where a top-level one takes `slots`, because parameter elimination gave it that and
///   rewriting it would leave each inner level's own type stale. `pairs` carries it.
///
/// Over `for x in [1,2,3]: for y in [1,2]: total += x*y` each enclosing position's seed
/// equals the previous position's final, since the enclosing writer writes back exactly that.
/// An enclosing body that writes the accumulator between two runs of the inner loop makes
/// them differ.
pub struct InductionDriver {
    base: OperatorBase,
    /// The store read back through the cyclic `FanOut`.
    store_op: std::sync::Arc<dyn TileOperator>,
    /// The iteration source — the items of each row's extent, curried one level per row
    /// above the positions.
    source_op: std::sync::Arc<dyn TileOperator>,
    /// `None` for a drive whose body takes the position alone.
    nested: Option<NestedDrive<std::sync::Arc<dyn TileOperator>>>,
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
        store_op: std::sync::Arc<dyn TileOperator>,
        source_op: std::sync::Arc<dyn TileOperator>,
        nested: Option<NestedDrive<std::sync::Arc<dyn TileOperator>>>,
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
                None,
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

    /// A nested drive's own inputs, with the enclosing positions read off `pair_domain`.
    ///
    /// `standing` are the levels the induction store sits under and leaves standing; `pair_domain`
    /// is the `(enclosing, inner)` domain the writer sequences its positions in, whose
    /// enclosing component is the level of the induction store's rows.
    pub fn nested_parts(
        pairs_op: std::sync::Arc<dyn TileOperator>,
        reseed_ops: Vec<std::sync::Arc<dyn TileOperator>>,
        standing: Vec<Extent>,
        enclosing_extent: Extent,
        pair_domain: &Extent,
    ) -> (NestedDrive<std::sync::Arc<dyn TileOperator>>, Extent) {
        let (rows, inner) = split_pair_domain(pair_domain).unwrap_or_else(|| {
            panic!("a nested store sequences its positions as pairs, got {pair_domain}")
        });
        let nested = NestedDrive {
            body: NestedBody {
                rows: [standing.as_slice(), std::slice::from_ref(&rows)].concat(),
                param: enclosing_extent,
            },
            // Cached until they notify: these are read once per position, and the laps of
            // every enclosing level multiply. Unlike the source, nothing reads their
            // release as a position, so a `Memo` costs the drive nothing it owes.
            pairs: std::sync::Arc::new(Memo::new(pairs_op)) as std::sync::Arc<dyn TileOperator>,
            reseeds: reseed_ops
                .into_iter()
                .map(|seed| {
                    std::sync::Arc::new(Memo::new(seed)) as std::sync::Arc<dyn TileOperator>
                })
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let inputs = subscribe_driver_inputs(
            &self.store_op,
            &self.source_op,
            CurryLevel::new(self.nested.as_ref().map_or(1, |n| n.body.rows.len() + 1)),
            consumer,
            cx,
        );
        let consumer = inputs.consumer;
        let nested = self.nested.as_ref().map(|n| NestedDrive {
            body: n.body.clone(),
            pairs: subscribe_pulled(&n.pairs, cx),
            reseeds: n
                .reseeds
                .iter()
                .map(|op| subscribe_pulled(op, cx))
                .collect(),
        });
        let rendered = self.tiling().empty_tile();
        crate::interpreter::tile_operators::share_breaker(InductionDriverProducer {
            base: ProducerBase::new(
                InductionDriverProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(consumer.clone(), inputs.placement),
            decides: inputs.decides,
            read_keys: self.read_keys.clone(),
            state: std::sync::Mutex::new(InductionDriverState {
                store_producer: inputs.store_producer,
                source_producer: inputs.source_producer,
                source_news: inputs.source_news,
                source: DecodedSource::default(),
                nested,
                window: DriverWindow::new(
                    self.positions.clone(),
                    self.nested.as_ref().map(|n| n.body.clone()),
                    self.read_extents.clone(),
                    self.item.clone(),
                    None,
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
                source_absent: Predicate::False,
                reseeded: None,
                rendered,
            }),
        })
    }
}

/// A position of a drive with no rows above it, as the path that names it.
fn one_component(position: Position) -> Path {
    Path::from(vec![position.into_value()])
}

/// What the driver last read off its source: the undelivered items by path, and every path
/// the source held then.
///
/// The driver reads the source when it has news and answers every other pull from this, so
/// a pull that emits one position costs that position rather than the rows still to come.
/// Both maps shed what the driver passes: the induction driver's emitted position leaves
/// `items`, and a release leaves both.
#[derive(Default)]
struct DecodedSource {
    /// The items the source delivers, in drive order ([`decode_source_paths`]).
    items: BTreeMap<Path, Tile>,
    /// Every path of the positions level the source held, rows it marks deleted included.
    held: BTreeSet<Path>,
    /// Whether the source said it will add nothing more.
    terminal: bool,
}

impl DecodedSource {
    /// What `src` holds, with `levels_above` collection levels standing above its positions.
    fn read(src: &Tile, levels_above: usize) -> Self {
        Self {
            items: decode_source_paths(src, levels_above + 1)
                .into_iter()
                .collect(),
            held: src
                .paths_at(CurryLevel::new(levels_above))
                .into_iter()
                .map(Path::from)
                .collect(),
            terminal: src.is_terminal(),
        }
    }

    /// The smallest delivered path above `after`.
    fn next_delivered(&self, after: Option<&Path>) -> Option<&Path> {
        let from = after.map_or(Unbounded, Excluded);
        self.items
            .range::<Path, _>((from, Unbounded))
            .next()
            .map(|(p, _)| p)
    }

    /// Forget every path at or below `through`.
    fn forget_through(&mut self, through: &Path) {
        while let Some(entry) = self.items.first_entry()
            && entry.key() <= through
        {
            entry.remove();
        }
        while self.held.first().is_some_and(|p| p <= through) {
            self.held.pop_first();
        }
    }
}

struct InductionDriverProducer {
    base: ProducerBase,
    /// Where the entry in front of the source records a decided push while unplaced.
    decides: crate::interpreter::dispatcher::CompletionTarget,
    read_keys: Vec<Value>,
    state: std::sync::Mutex<InductionDriverState>,
}
struct InductionDriverState {
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// Whether the source has notified since it was last read.
    source_news: crate::interpreter::tile_operators::Arrivals,
    /// The source as of its last read.
    source: DecodedSource,
    /// `None` for a drive whose body takes the position alone.
    nested: Option<NestedDrive<Box<dyn TileProducer>>>,
    /// The emitted rows and the body-input tile they render. This is the
    /// producer's own output, not recurrence state: a row is never read back to
    /// compute a later one.
    window: DriverWindow,
    /// The path of the highest position emitted, or `None` before the first. This is the
    /// item cursor, and it is not recoverable from the window, which a release compacts
    /// emitted rows away from.
    emitted_through: Option<Path>,
    /// Highest source path released back upstream. The driver never re-reads a position it
    /// has emitted and never reads a filtered one, so every emitted position, and every
    /// filtered one it has read past , is reclaimable; a co-iterated
    /// reader keeps its own positions live through the source's cross-producer release
    /// intersection.
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
    /// Positions of a flat source proven absent, independent of the emission cursor.
    source_absent: Predicate,
    /// The last row this drive reseeded and the snapshot it reseeded it at, until the
    /// store's frontier enters that row, for the check that the reseed is the store's seed
    /// there. Checked once per row, so it costs a seed read per row.
    reseeded: Option<(Path, Vec<Value>)>,
    /// What the last consume rendered.
    rendered: Tile,
}

impl InductionDriverProducer {
    /// The window rendered, less every region released so far.
    ///
    /// [`DriverWindow::reclaim`] drops the rows a release covers whole, which is all a
    /// release naming positions asks. A release can also name part of a row's value — the
    /// items of a nest whose elements are collections are collections, and a `Memo` in
    /// front of this driver releases whatever it has cached — and a row it only partly
    /// covers stays in the window, so its released part is stripped here.
    fn render(
        &self,
        state: &InductionDriverState,
        done: bool,
        complete_rows: &[Predicate],
        read_past: &Predicate,
    ) -> Tile {
        let mut tile = state.window.render(done, complete_rows, read_past);
        tile.remove_guarded(self.obsolete_guard());
        tile
    }

    /// Reclaim the prefix this drive has consumed, in the store's changelog and in the
    /// source, and close the source once the drive is over.
    ///
    /// Both releases name a **path prefix** ([`domain_prefix`]) — the rows before the one
    /// being run entirely, and within that row everything up to the frontier — which is
    /// what a sequential drive has consumed at any depth. A drive with no rows above it
    /// has paths of one component, where that prefix is the watermark it always was.
    fn reclaim_consumed(
        &self,
        state: &mut InductionDriverState,
        frontier: Option<&Path>,
        read_through: Option<Path>,
        done: bool,
    ) {
        // The drive only ever folds at the *frontier*, and the store's GC preserves the
        // carry source a live position reads inside a released prefix — so releasing
        // through the frontier never strands the fold, and without it the store's
        // `FanOut`-intersected release watermark could never advance past this cycle
        // slot and the changelog would grow with the loop.
        if let Some(frontier) = frontier {
            let levels = path_levels(state.store_producer.tiling());
            state
                .store_producer
                .release(domain_prefix_over(frontier.to_vec(), &levels));
        }
        // The source prefix this drive has consumed: what it has emitted, and the filtered
        // rows it has read past. It only ever reads the position it is about to emit and
        // never re-reads an earlier one.
        if let Some(through) = state.emitted_through.clone().max(read_through)
            && !state
                .source_released_through
                .as_ref()
                .is_some_and(|r| *r >= through)
        {
            let levels = path_levels(state.source_producer.tiling());
            state
                .source_producer
                .release(domain_prefix_over(through.to_vec(), &levels));
            // The enclosing parameter and the reseeds are read at positions past the cursor
            // only, so their consumed prefix goes too, and a memo over each answers every pull
            // from its whole cache, so without this each pull decodes the run so far. The
            // parameter is keyed by pairs. A reseed is keyed by the row and read only at the
            // row's first position, which the cursor has passed once it is anywhere in the
            // row, so the rows through the cursor's go.
            if let Some(nested) = state.nested.as_mut() {
                let levels = path_levels(nested.pairs.tiling());
                nested
                    .pairs
                    .release(domain_prefix_over(pair_keyed(&through), &levels));
                if let Some((row, _)) = through.split_position() {
                    for reseed in &mut nested.reseeds {
                        let levels = path_levels(reseed.tiling());
                        reseed.release(domain_prefix_over(row.to_vec(), &levels));
                    }
                }
            }
            state.source.forget_through(&through);
            state.source_released_through = Some(through);
        }
        if done && !state.source_fully_released {
            state
                .source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
            if let Some(nested) = state.nested.as_mut() {
                for input in std::iter::once(&mut nested.pairs).chain(&mut nested.reseeds) {
                    input.release(input.tiling().universal_guard());
                }
            }
            state.source_fully_released = true;
        }
    }
}

impl TileProducer for InductionDriverProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        visit("store", &*state.store_producer);
        visit("source", &*state.source_producer);
        if let Some(nested) = &state.nested {
            visit("pairs", &*nested.pairs);
            for reseed in &nested.reseeds {
                visit("reseed", &**reseed);
            }
        }
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let state = self
            .state
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        visit("store", &mut *state.store_producer);
        visit("source", &mut *state.source_producer);
        if let Some(nested) = &mut state.nested {
            visit("pairs", &mut *nested.pairs);
            for reseed in &mut nested.reseeds {
                visit("reseed", &mut **reseed);
            }
        }
    }

    /// The drive reads its source again at its next step; it reads its other inputs at every one.
    fn read_again(&mut self, input: &str) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if input == "source" {
            state.source_news.record(&Projection::Everything);
        }
    }

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(state.window.held_values())
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    /// A loop run in rounds asks it for one position's path, at the level of the position.
    fn restates(&self) -> Restates {
        Restates::Every
    }

    /// A step reads its source, the store and the nested inputs whole, whatever a round asks.
    fn input_level(&self, _role: &str, _level: CurryLevel) -> Option<CurryLevel> {
        None
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    fn get_impl(&self, guard: TileGuard) -> Tile {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let mut tile = state.rendered.clone();
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.restrict_to(&guard.projection_for(self), self.tiling());
        tile
    }

    fn next_position(&self) -> Option<Option<Vec<Value>>> {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let next = state
            .source
            .next_delivered(state.emitted_through.as_ref())
            .map(|path| path.to_vec());
        Some(next)
    }

    fn completes_through(&self) -> Option<crate::interpreter::dispatcher::CompletionTarget> {
        Some(self.decides.clone())
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // Retention only: this driver's cursor is the store's frontier, so a
        // release says nothing about progress — it only reclaims rows the body
        // has consumed and the store has decided.
        state.window.reclaim(&obsolete_guard);
    }
}

/// The rows `beneath`, a statement of the level beneath them, calls complete in full: the
/// enclosing paths of its arms that admit every key under them.
fn rows_whole_beneath(beneath: &Predicate) -> Predicate {
    let arms: Vec<&Predicate> = match beneath {
        Predicate::Or(arms) => arms.iter().collect(),
        one => vec![one],
    };
    Predicate::union_all(
        arms.into_iter()
            .filter_map(|arm| match arm {
                Predicate::Qualified { enclosing, here } if here.is_true() => {
                    Some((**enclosing).clone())
                }
                _ => None,
            })
            .collect(),
    )
}

/// The drive of a loop run in rounds is the pipeline breaker a round starts: a package names
/// the position the round runs, the next its source delivers, and a consume emits it where the
/// store has decided the position before it. See `src/interpreter/design-dispatcher.md`, "A loop in
/// rounds".
impl Breaker for InductionDriverProducer {
    /// The source's tiling, which the entry in front of the source and the drive's release of the
    /// source are of. A package names one position's path, or nothing.
    fn input_tiling(&self, _: InputId) -> Tiling {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.source_producer.tiling().clone()
    }

    /// What the drive has released of its source: every position it has emitted or read past.
    fn input_released(&self, _: InputId) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.source_producer.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    /// One step at `guard`, emitting a position only inside the region it names: a drive with
    /// rows above it is asked for a path of every level.
    fn consume_impl(&self, _: InputId, guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let asked = guard.projection_for(self);
        // A consume at no position is a loop's scope asking the drive to read its source: the
        // source of a loop nested in another is read through pipelines of the scope around it,
        // which take their packages by the dispatcher and notify no one.
        if asked == Projection::Nothing {
            state.source_news.record(&Projection::Everything);
        }
        state.rendered = self.step(state, &asked);
    }
}

impl BreakingProducer for InductionDriverProducer {
    /// The region the last step's rendering states.
    fn complete(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.rendered.to_guard()
    }
}

impl InductionDriverProducer {
    /// One step of the drive: read the source where it has news, the store and the nested
    /// inputs, emit the next position where `asked` names it and the store has decided the one
    /// before, release what the store has consumed, and render the body's input.
    fn step(&self, state: &mut InductionDriverState, asked: &Projection) -> Tile {
        // The driver is over once it has universally released the source: pulling it
        // again would break that release's promise, and every position has already
        // been emitted, so the live window is the whole remaining answer. The driver
        // owns the source, so the obligation is its to keep.
        if state.source_fully_released {
            return self.render(state, true, &[], &Predicate::False);
        }
        let levels_above = state.window.levels_above();
        // Everything the drive indexes is keyed by the **path** that reaches it: the
        // curried source names it as levels already, and the pair-keyed streams have their
        // pair exploded to match. Two spellings of one position would match neither.
        //
        // How many levels stand above the positions is the drive's own statement
        // ([`NestedBody::rows`]), not a count of the source's levels: an item that is itself a
        // collection — a nest whose elements are collections — carries its own levels
        // beneath the positions, and counting those names a path one level too deep.
        //
        // The source is read when it has notified, and not otherwise: a tile only grows
        // between its notifications and the drive's own releases, so the last read still
        // answers. Without this each pull decodes every row not yet emitted, and a loop
        // over `n` rows costs `n²`.
        if state.source_news.take() != Projection::Nothing {
            let src = state
                .source_producer
                .get(state.source_producer.tiling().universal_guard());
            state.source = DecodedSource::read(&src, levels_above);
            if levels_above == 0 {
                let Tile::DataFunction { domain, .. } = &src else {
                    unreachable!("a drive's source is a collection")
                };
                state.source_absent = state.source_absent.union(
                    &src.level_statement()
                        .minus(&Predicate::from_column_value(domain)),
                );
            }
            // The rows of one level the source will gain no more items beneath — one of the
            // two halves of a row being answerable as a whole, `rows_folded_at` below being
            // the other. Read at the level itself: a standing level's rows are not the level
            // beneath's, and each level's completion is its own statement.
            for level in 0..state.source_producer.tiling().levels() {
                let at = src.values_at(CurryLevel::new(level));
                if let Tile::DataFunction { .. } = at {
                    let complete = at.level_statement();
                    match state.source_complete.get_mut(level) {
                        Some(known) => *known = known.union(&complete),
                        None => state.source_complete.push(complete),
                    }
                }
            }
            // A whole child domain closes its enclosing row even when the source states
            // that completion only at the deeper level.
            for level in (0..state.source_complete.len().saturating_sub(1)).rev() {
                state.source_complete[level] = state.source_complete[level]
                    .union(&rows_whole_beneath(&state.source_complete[level + 1]));
            }
            state.source.terminal |= state
                .source_complete
                .first()
                .is_some_and(Predicate::is_true);
            // Invariant: no path at or below the cursor arrives after the drive has passed
            // it. The source may deliver in any order. The drive holds this by emitting a
            // position only once the source calls every path before it complete (`waits`
            // below), and nothing is added beneath a complete path. A path at or below the
            // cursor is still legitimate *here*: the release is what removes the consumed
            // prefix, and the source is free to honour it a pull late. The domain need not
            // be contiguous — a restricted source (`for l in [x for x in xs if p(x)]`)
            // delivers a subset of its extent's positions and the recurrence runs over
            // exactly those.
            debug_assert!(
                state.source.items.keys().all(|p| {
                    state.emitted_through.as_ref().is_none_or(|e| p > e)
                        || state
                            .source_released_through
                            .as_ref()
                            .is_some_and(|r| p <= r)
                }),
                "induction source delivered a position at or below the emitted cursor {:?} \
                 that was never released: {:?}",
                state.emitted_through,
                state.source.items.keys().collect::<Vec<_>>()
            );
        }
        let source_complete = state.source.terminal;
        // The enclosing parameter and the reseeds, keyed by the same paths. A reseed
        // restarts an accumulator, so it stands beside the store reads in the same
        // snapshot column and is read the way the store holds one: as a value per key.
        let nested_at = state.nested.as_mut().map(|n| {
            let read = |p: &mut Box<dyn TileProducer>| {
                let tile = p.get(p.tiling().universal_guard());
                decode_pairs_pathed(&tile, levels_above - 1)
            };
            NestedAt {
                pairs: read(&mut n.pairs).into_iter().collect(),
                // A reseed is a morphism of the enclosing position, so it is keyed by the
                // row the position stands in rather than by the position.
                reseeds: n
                    .reseeds
                    .iter_mut()
                    .map(|p| {
                        let tile = p.get(p.tiling().universal_guard());
                        decode_source_paths(&tile, levels_above)
                            .into_iter()
                            // A reseed holding a collection still arriving is part of a
                            // value, not one, so it is absent until it is whole, as the
                            // store's seed is: the position waits with the ones whose
                            // reseed has not arrived.
                            .filter(|(_, seed)| is_whole_value(seed))
                            .map(|(path, seed)| (path, materialized_row(seed)))
                            .collect()
                    })
                    .collect(),
            }
        });
        let store = state
            .store_producer
            .get(state.store_producer.tiling().universal_guard());
        // An induction store is a collection of stores; the drive is sequential, so the one it is
        // adding to is the last, and at depth zero it is the only one. Its frontier is the
        // whole induction store's watermark — positions are sequenced across rows even though the
        // state is not. The drive's cursor is a path, so the frontier it compares against
        // must be one too: a row's own watermark says nothing about which row it belongs
        // to.
        let frontier = frontier_path(&store);
        let store = current_row_store(&store);
        // The store opens a row at its seed stream's value and the drive restarts the row's
        // accumulator at its reseed stream's, which is one stream behind a `FanOut`. The two
        // are visible together once the store's frontier is inside the row the drive
        // reseeded.
        if let Some((row, reseed)) = state.reseeded.take() {
            match frontier.as_ref().and_then(Path::split_position) {
                Some((rows, _)) if rows == &row[..] => {
                    let seeds: Vec<Option<Value>> = self
                        .read_keys
                        .iter()
                        .map(|k| store_seed_value(&store, k))
                        .collect();
                    assert!(
                        seeds
                            .iter()
                            .zip(&reseed)
                            .all(|(s, r)| s.as_ref() == Some(r)),
                        "a drive's reseed at a row is the store's seed for that row: row \
                         {row:?} reseeded at {reseed:?}, the store seeded it at {seeds:?}"
                    );
                }
                Some((rows, _)) if Path::from(rows.to_vec()) > row => {}
                _ => state.reseeded = Some((row, reseed)),
            }
        }

        let known_complete = &state.source_complete;
        let source_complete_at = |level: CurryLevel| {
            known_complete
                .get(level.index())
                .cloned()
                .unwrap_or(Predicate::False)
        };
        debug_assert!(
            frontier.as_ref() <= state.emitted_through.as_ref(),
            "the store decided through {frontier:?} but the driver has only emitted \
             through {:?} — a decision cannot precede the input it decides",
            state.emitted_through
        );
        // What the source calls complete, stated at the position level: each level's
        // statement read at the paths beneath it, completeness being downward-closed.
        let settled = (0..=levels_above)
            .map(|level| source_complete_at(CurryLevel::new(level)).descend(levels_above - level))
            .fold(Predicate::False, |all, level| all.union(&level));
        // A position is emitted only inside the region `asked` names, keys of the positions' own
        // level read on the position's path. An inline query asks for everything; a loop run in rounds
        // asks for one position per round, and a round at a row of a nested loop emits none.
        if frontier == state.emitted_through
            && let Some(pos) = state
                .source
                .next_delivered(state.emitted_through.as_ref())
                .cloned()
            && match asked {
                Projection::Everything => true,
                Projection::Nothing => false,
                Projection::Keys { level, keys } => {
                    level.index() + 1 == pos.len() && keys.contains_path(&pos)
                }
            }
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
            let boundary = state.emitted_through.as_ref().is_none_or(|e| {
                e.split_position().map(|(rows, _)| rows)
                    != pos.split_position().map(|(rows, _)| rows)
            });
            // Passing a path is final: the drive never looks back, so a path arriving below
            // the cursor would be dropped. A source need not deliver in the drive's order. A
            // product or a concatenation with a streamed part delivers a later position before
            // an earlier one. So a position goes only once no path before it can still arrive,
            // which is the source calling every such path complete, at the position level or
            // at a row level above it (completeness is downward-closed). The drive waits on
            // the paths before this one and on nothing after it.
            let waits = {
                let (rows, at) = pos
                    .split_position()
                    .unwrap_or_else(|| unreachable!("a delivered path names a position"));
                !settled.subsumes(&state.window.path_prefix(rows, at, false))
            };
            let snapshot: Option<Vec<Value>> = self
                .read_keys
                .iter()
                .enumerate()
                .map(|(i, k)| match nested_at.as_ref().filter(|_| boundary) {
                    Some(n) => {
                        let (row, _) = pos
                            .split_position()
                            .unwrap_or_else(|| unreachable!("a delivered path names a position"));
                        n.reseeds[i].get(&Path::from(row.to_vec())).cloned()
                    }
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
            if !waits
                && let (Some(snapshot), Some(item), Some(enclosing)) =
                    (snapshot, state.source.items.get(&pos), enclosing)
            {
                let (rows, at) = pos
                    .split_position()
                    .unwrap_or_else(|| unreachable!("a delivered path names a position"));
                let inner = Position::new(at.clone());
                let row = state.nested.is_some().then(|| Path::from(rows.to_vec()));
                if boundary && let Some(row) = &row {
                    state.reseeded = Some((row.clone(), snapshot.clone()));
                }
                state
                    .window
                    .push(snapshot, item.clone(), enclosing, row, inner.clone(), inner);
                state.source.items.remove(&pos);
                state.emitted_through = Some(pos);
            }
        }

        // A row's accumulator is final once the row has stopped gaining items **and** the
        // store has folded every one of them. Those come apart: a literal source is
        // complete over every row on the pull that delivers it, while the fold reaches one
        // position per pull, so publishing the source's predicate alone answers rows whose
        // positions are still being decided — and the reader that takes a row's final value
        // stops there, with the fold part-done.
        //
        // A row is folded once no position under it is left to decide. The drive is sequential
        // and positions run in order, so everything at or below the store's frontier is decided.
        // What is left is the positions the source has delivered and this drive has not
        // emitted, and an emitted position past the frontier: an emitted position is released
        // back to the source, so the source no longer shows it while the store may not yet have
        // decided it. A row with no position under it, including every row while the source
        // holds none, is folded as soon as it arrives: left unfolded, the loop around it would
        // wait on it forever. Each level answers for its own rows, so a nest never waits on a
        // last row that only the level above can call whole. Reading the frontier here is not
        // circular: the frontier advances from the body's decisions, which never consult this
        // predicate.
        //
        // A row stays complete once stated: `source_complete_at` only accumulates, and a source
        // puts no position under a row it has called complete. A source that did would withdraw
        // the completion, which the check in `tile_operators/mod.rs` reports ("withdrew
        // completion").
        let undecided = undecided_positions(
            state.source.items.keys(),
            state.emitted_through.as_ref(),
            frontier.as_ref(),
        );
        let complete_rows: Vec<Predicate> = (0..levels_above)
            .map(|level| {
                source_complete_at(CurryLevel::new(level))
                    .intersect(&rows_folded_at(level, &undecided))
            })
            .collect();

        // Every position of a complete source has been emitted: the body input is final,
        // and that terminality propagates through the body's decision stream to close the
        // induction store's frontier. A complete source holds every path it will ever deliver, so
        // "no delivered path above the cursor" means "there is no next" — the question a
        // restricted source needs asked, since the position one past the cursor may simply
        // not be in its domain.
        //
        // Not "and the store has decided them all", though the store owes a decision on
        // whatever was emitted this pull. The store is this drive's caller — it pulls the
        // body, which pulls this — so a position emitted here is decided before that same
        // store pull renders, and waiting for the frontier to show it would cost a lap per
        // loop. The store asserts the other side of that (a terminal decision stream it
        // has not fully consumed), which is where a body that failed to decide is caught.
        //
        let pending = state
            .source
            .next_delivered(state.emitted_through.as_ref())
            .cloned();
        let done = source_complete && pending.is_none();
        // Before the lowest pending item, every decided key was emitted or holds no item.
        // Known-absent keys beyond that prefix are also finished; they emit no item and
        // need not wait for an intervening item to run.
        let read_past = match levels_above {
            0 => {
                let complete = source_complete_at(CurryLevel::OUTERMOST);
                match &pending {
                    Some(next) => complete.intersect(&Predicate::below_in(
                        next[0].clone(),
                        &state
                            .source_producer
                            .tiling()
                            .domain_extent()
                            .expect("a drive's source is a collection"),
                    )),
                    None => complete,
                }
            }
            _ => Predicate::False,
        };
        let read_past = read_past.union(&state.source_absent);
        // The filtered rows this drive has read past, at every depth: the highest path the
        // source holds, deleted rows included, below the next one to run, where the source
        // calls it complete along with every path before it (the source states
        // the rule for a drive with no rows above it).
        let read_through = state
            .source
            .held
            .range::<Path, _>((Unbounded, pending.as_ref().map_or(Unbounded, Excluded)))
            .rfind(|p| {
                let (rows, at) = p
                    .split_position()
                    .unwrap_or_else(|| unreachable!("a source path names a position"));
                settled.subsumes(&state.window.path_prefix(rows, at, true))
            })
            .cloned();
        self.reclaim_consumed(state, frontier.as_ref(), read_through, done);
        // A row the drive calls complete has every position emitted and decided, so the drive reads
        // no more of it and releases it from its source whole. A
        // loop's scope closes a row of a nested loop by a round at the row
        // (`src/interpreter/design-dispatcher.md`, "A loop in rounds").
        let rows: Vec<TileGuard> = complete_rows
            .iter()
            .enumerate()
            .filter(|(_, rows)| !rows.is_false())
            .map(|(level, rows)| {
                CurryLevel::new(level)
                    .wrap_guard(TileGuard::Function(FunctionGuard::Domain(rows.clone())))
            })
            .collect();
        if !rows.is_empty() {
            let rows = TileGuard::flatten_or(rows);
            if !guard_minus(&rows, &state.source_producer.obsolete_guard()).is_empty() {
                state.source_producer.release(rows);
            }
        }
        if !state.source_absent.is_false() {
            state
                .source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    state.source_absent.clone(),
                )));
        }
        self.render(state, done, &complete_rows, &read_past)
    }
}

/// The transaction body's input, produced from the store read back through the
/// cycle: `DataFunction(UInt → {_0: snap_{k₀}, …, _{r-1}: snap_{k_{r-1}}, _r:
/// item})` — the [`InductionDriver`]'s sibling, differing only in how the item
/// advances.
///
/// An induction position is decided by the store's frontier; a transaction's is
/// not, because a commit is what *moves* the frontier. Its item is acknowledged by the
/// **commit-ack**, delivered as a release — but a release from
/// the body alone would be wrong, because a body releases a row the moment it
/// consumes it, long before the attempt commits. The driver therefore sits behind
/// a `FanOut` with two slots, the body and [`TransactWriter`], and reads the
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
    /// The released prefix boundary inherited from a retired drive, or `None` for a fresh drive.
    /// The new drive includes this prefix in its released region so those source keys are not attempted again.
    resumed_after: Option<Position>,
    /// The store read back through the cyclic `FanOut`.
    store_op: std::sync::Arc<dyn TileOperator>,
    /// The transaction source — one item per transaction to attempt.
    source_op: std::sync::Arc<dyn TileOperator>,
    /// Runtime keys the body reads a snapshot of, in body-parameter order.
    read_keys: Vec<Value>,
    read_extents: Vec<Extent>,
    /// The item slot's tiling, taken from the source ([`source_item_tiling`]).
    item: Tiling,
    /// The extent of the source's positions, which each body-input row carries its item's in
    /// ([`F_ITEM_POSITION`]).
    item_positions: Extent,
    /// The index of this drive's writer among its store's writers, which names what the store
    /// says to it ([`WriterTakes`]).
    writer: usize,
}

impl TransactDriver {
    /// A driver whose rows each carry their item's source position ([`F_ITEM_POSITION`]).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        store_op: std::sync::Arc<dyn TileOperator>,
        source_op: std::sync::Arc<dyn TileOperator>,
        read_keys: Vec<Value>,
        read_extents: Vec<Extent>,
        item_extent: Extent,
        resumed_after: Option<Position>,
        writer: usize,
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
        let Tiling::DataFunction {
            domain: item_positions,
            ..
        } = source_op.tiling()
        else {
            unreachable!("a transaction source is a collection of items")
        };
        let item_positions = item_positions.clone();
        Self {
            base: OperatorBase::new(body_input_tiling(
                &Extent::Base(BaseType::UInt),
                None,
                &read_extents,
                item.clone(),
                Some(&item_positions),
            )),
            store_op,
            source_op,
            read_keys,
            read_extents,
            item,
            item_positions,
            resumed_after,
            writer,
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let inputs = subscribe_driver_inputs(
            &self.store_op,
            &self.source_op,
            CurryLevel::new(1),
            consumer,
            cx,
        );
        if let Some(through) = &self.resumed_after {
            inputs
                .source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below_in(through.value().clone(), &self.item_positions),
                )));
        }
        crate::interpreter::tile_operators::share_breaker(TransactDriverProducer {
            decides: inputs.decides,
            base: ProducerBase::new(
                TransactDriverProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(inputs.consumer, inputs.placement.clone()),
            source_entry: inputs.placement,
            read_keys: self.read_keys.clone(),
            writer: self.writer,
            state: std::sync::Mutex::new(TransactionDriverState {
                rendered: self.tiling().empty_tile(),
                store_producer: inputs.store_producer,
                source_producer: inputs.source_producer,
                source_news: inputs.source_news,
                source: DecodedSource::default(),
                // A transaction driver's body-input domain is its own attempt counter, not
                // its source's positions: a retried item takes a fresh attempt position.
                window: DriverWindow::new(
                    Extent::Base(BaseType::UInt),
                    None,
                    self.read_extents.clone(),
                    self.item.clone(),
                    Some(self.item_positions.clone()),
                ),
                latest_emit: None,
                source_released: self
                    .resumed_after
                    .as_ref()
                    .map_or(Predicate::False, |position| {
                        Predicate::at_or_below_in(position.value().clone(), &self.item_positions)
                    }),
                taken: BTreeMap::new(),
            }),
        })
    }
}

struct TransactDriverProducer {
    decides: crate::interpreter::dispatcher::CompletionTarget,
    base: ProducerBase,
    /// The entry before the source, placed in the transaction store's writer pipeline.
    source_entry: crate::interpreter::dispatcher::Placement,
    read_keys: Vec<Value>,
    /// The index of this drive's writer among its store's writers ([`TransactDriver::writer`]).
    writer: usize,
    state: std::sync::Mutex<TransactionDriverState>,
}
struct TransactionDriverState {
    rendered: Tile,
    store_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// Whether a notification or consuming delivery requires decoding the source again.
    source_news: crate::interpreter::tile_operators::Arrivals,
    /// The source as of its last read, with a position a path of one component.
    source: DecodedSource,
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
    /// The exact source region released by acknowledgements or decided-absent rows.
    source_released: Predicate,
    /// Once the store says it takes decisions ahead of their commits, by stating
    /// [`WriterTakes`] for its writers, each item an ack has finished that the store has not
    /// called settled, by source position.
    ///
    /// Under such a store an ack is its take of the attempt's decision, which may need making
    /// again, so the drive keeps the item to emit it again when the store names it among the
    /// writer's [`again`](WriterTakes::again). The ack released the item from the source, so the
    /// drive keeps a copy of its own.
    taken: BTreeMap<Position, Tile>,
}

/// The most rows this driver's live window may hold: the attempt the writer has
/// decided, plus at most one newer row emitted since it decided.
///
/// This bound *is* the O(1) claim the writer's supersession release exists for,
/// and it holds only because of it. Rows are added at most one per pull and only
/// for one source item; they leave on the release intersection. The writer contributes
/// two releases — everything below the position it decides (supersession) and
/// `≤ attempt` when the item finishes (the ack) — and it is the first that caps
/// the window. Drop it and the window instead holds one row per retry between
/// acks: O(retries) rows retained and, because the body re-renders the whole
/// window each pull, O(retries²) body rows evaluated.
const MAX_LIVE_ATTEMPTS: usize = 2;

impl TransactDriverProducer {
    /// Release `region`. Product arrivals need not form a
    /// prefix, so completing one item releases no position other than that item.
    fn release_source_region(&self, state: &mut TransactionDriverState, region: Predicate) {
        if region.minus(&state.source_released).is_false() {
            return;
        }
        state.source_released = state.source_released.union(&region);
        state
            .source_producer
            .release(TileGuard::Function(FunctionGuard::Domain(region)));
    }

    /// The two standing facts about the live window, checked on both sides of the
    /// only two things that move it: an emit and the release that acknowledges its item.
    ///
    /// It is **all one item**: rows are emitted only for the lowest unfinished
    /// source position currently offered, and an acknowledgement removes that item and its rows. That is what lets the writer decide the newest position and treat
    /// every older live one as superseded — if the window ever spanned two items,
    /// that rule would abandon a real attempt.
    ///
    /// And it is **bounded** by [`MAX_LIVE_ATTEMPTS`], which no test asserts
    /// directly because this does: `sustained_contention_conserves_pool` runs a
    /// stuck item through many retries in a debug build, so an unbounded window
    /// trips here rather than passing quietly with the right answer.
    fn debug_assert_window_invariants(&self, state: &TransactionDriverState) {
        debug_assert!(
            state
                .window
                .inner_rows()
                .zip(state.window.inner_rows().skip(1))
                .all(|(a, b)| a.item_position == b.item_position),
            "the driver's live window spans more than one item: {:?}",
            state
                .window
                .inner_rows()
                .map(|r| r.item_position.clone())
                .collect::<Vec<_>>(),
        );
        debug_assert!(
            state.window.inner_row_count() <= MAX_LIVE_ATTEMPTS,
            "the driver's live window holds {} attempts (bound {MAX_LIVE_ATTEMPTS}) — a \
             superseded row is not being reclaimed, so a contended item costs O(retries) \
             rows retained and O(retries²) body rows evaluated",
            state.window.inner_row_count()
        );
    }
}

impl TransactDriverProducer {
    fn advance(&self, state: &mut TransactionDriverState) -> Tile {
        // Read the source after a notification or consuming delivery. Between those arrivals
        // and the drive's own releases its tile does not grow, so the last decode still answers.
        // A release removes what the driver has finished with. The drive
        // releases each finished item's exact key (`release_impl`), which is why
        // an item is named by its domain position rather than by a column index. Without the
        // cache each pull decodes and sorts every item not yet released.
        // A source released whole is not pulled again: the release promised it nothing more.
        if state.source_news.take() != Projection::Nothing
            && !state.source_producer.obsolete_guard().is_universal()
        {
            let src = state
                .source_producer
                .get(state.source_producer.tiling().universal_guard());
            state.source = DecodedSource::read(&src, 0);
            // A level whose keys follow the level beneath is complete once that level is
            // (`src/interpreter/design-operators.md`, "Keys that follow the level beneath").
            let source_complete = match &src {
                Tile::DataFunction { .. } => src.level_statement(),
                _ => Predicate::False,
            };
            // A source may honour a release a pull late, so a read can still show what the
            // drive has already released.
            state
                .source
                .items
                .retain(|path, _| !state.source_released.contains(&path[0]));
            state
                .source
                .held
                .retain(|path| !state.source_released.contains(&path[0]));
            // Every decided position with no delivered item is finished without an attempt.
            let pending = state
                .source
                .items
                .keys()
                .fold(Predicate::False, |pending, path| {
                    pending.union(&Predicate::point(path[0].clone()))
                });
            // A terminal tile decides the entire key universe. Until this drive is exhausted,
            // release only its held absent keys: releasing the complement of pending items would
            // become universal on the last ack, before a pull observes exhaustion. Registration
            // during reload distinguishes that early stop from a source released whole.
            let complete = if state.source.terminal {
                state
                    .source
                    .held
                    .iter()
                    .fold(Predicate::False, |held, path| {
                        held.union(&Predicate::point(path[0].clone()))
                    })
            } else {
                source_complete
            };
            self.release_source_region(state, complete.minus(&pending));
        }
        // The source is *complete* only when its tile is terminal. A batch source
        // (a list) is terminal on the first pull; a live source (an HTTP request
        // stream) never is, so a momentarily drained one must not read as done.
        let source_complete = state.source.terminal;
        // Positioned, so an item is named by where it sits in the source's own
        // domain rather than by where it sits in the columns still on offer. The
        // smallest currently delivered item is attempted next. Its acknowledgement removes it
        // without excluding a smaller position that another product dimension may deliver later.
        let next_item = state.source.next_delivered(None).cloned();
        let store = state
            .store_producer
            .get(state.store_producer.tiling().universal_guard());
        // The snapshot the attempt is built against: the store's decided
        // frontier. A read key with no value yet (an *append* onto an empty
        // collection store) folds to nothing — the empty-store bootstrap.
        let frontier = store_frontier(&store);
        let olds: Vec<Option<Value>> = self
            .read_keys
            .iter()
            .map(|k| store_current(&store, k).map(|(_, v)| v))
            .collect();
        // Release the store below the decided frontier: this driver reads only the frontier
        // and each key's latest value at or below it, which the store's reclaim keeps, so the
        // changelog behind the frontier is dead to it. The release names the last change
        // strictly below the frontier, so the frontier's own change survives. Without it this
        // slot holds the `FanOut`'s meet where the store began, and every pull of the loop
        // re-reads a changelog as long as the loop has run.
        if let Some(f) = &frontier {
            release_store_below(&mut *state.store_producer, &store, f);
        }

        // What the store says of the decisions it took from this drive's writer, where it takes
        // them ahead of their commits: the drive keeps what it acks from then on, lets go of
        // what the store calls settled, and emits again what the store names to decide again.
        let takes = match &store {
            Tile::Store { writer_takes, .. } => writer_takes.get(self.writer).cloned(),
            _ => None,
        };
        let again = takes.and_then(|takes| {
            // Reloads occur at a drained boundary, where no store holds a decision it took and has
            // not settled (`Breaker::holds_unsettled_decisions`, asserted in `drive_live`). The
            // retired source release therefore names settled items.
            state
                .taken
                .retain(|item, _| !takes.settled.contains(item.value()));
            // The store names an item to decide again only in the tile it publishes before the
            // pull that decides it, and the decision commits or stands before the store publishes
            // again (`CommitProducer::commit_ready`). A second pull of this drive within
            // that pull finds the item's row in the window, and the emit is suppressed as a
            // repeat of `(item, frontier)`.
            debug_assert!(
                takes.again.len() <= 1,
                "the store names at most one item of a writer to decide again: {:?}",
                takes.again
            );
            takes.again.into_iter().next()
        });
        debug_assert!(
            again
                .as_ref()
                .is_none_or(|item| state.taken.contains_key(item)),
            "the store names to decide again an item this drive took: {again:?}"
        );
        // A taken item to decide again comes before the next item.
        let emit = match &again {
            Some(item) => Some(one_component(item.clone())),
            None => next_item.clone(),
        };
        if let Some(path) = &emit
            && let Some(frontier) = frontier
            && let pos = Position::new(path[0].clone())
            && state.latest_emit.as_ref() != Some(&(pos.clone(), frontier.clone()))
        {
            let item = match &again {
                Some(_) => {
                    debug_assert_eq!(
                        state.window.inner_row_count(),
                        0,
                        "a drive emits an item again once its writer has decided every row it \
                         emitted, which a pull of the writer does"
                    );
                    state.taken[&pos].clone()
                }
                _ => state.source.items[path].clone(),
            };
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
            let attempt = state.window.next_attempt();
            state
                .window
                .push(snap_in, item, None, None, pos.clone(), attempt)
                .snapshot_at = Some(frontier.clone());
            state.latest_emit = Some((pos, frontier));
        }
        self.debug_assert_window_invariants(state);
        // Every item has been acked and no more can arrive.
        let exhausted = source_complete && next_item.is_none();
        // Terminal once every item has finished. This is the writer's completeness signal
        // too: it owns no source of its own, so "all transactions attempted" is exactly this
        // tile closing. A live window that is momentarily empty over an incomplete source
        // stays non-terminal — the drained-but-live case. An item the store holds a decision
        // for has not finished, since it may need deciding again.
        let done = exhausted && again.is_none() && state.taken.is_empty();
        // An exhausted drive reads nothing more of its source: the source can deliver no more,
        // and an item the store holds a decision for is this drive's own copy. It releases the
        // source whole, as an induction drive does, rather than through the last item acked,
        // which names positions and not the source.
        if exhausted && !state.source_producer.obsolete_guard().is_universal() {
            state
                .source_producer
                .release(state.source_producer.tiling().universal_guard());
        }
        let mut tile = state.window.render(done, &[], &Predicate::False);
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }
}

impl Breaker for TransactDriverProducer {
    fn input_tiling(&self, _: InputId) -> Tiling {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.source_producer.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.source_producer.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    fn consume_impl(&self, _: InputId, _: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.rendered = self.advance(state);
    }
}

impl BreakingProducer for TransactDriverProducer {
    fn complete(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.rendered.to_guard()
    }

    fn final_guard(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        self.complete_in_state(state)
    }
}
impl TransactDriverProducer {
    fn complete_in_state(&self, state: &TransactionDriverState) -> TileGuard {
        state.rendered.to_guard()
    }
}

impl TileProducer for TransactDriverProducer {
    impl_producer_base!();

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn next_position(&self) -> Option<Option<Vec<Value>>> {
        Some(None)
    }

    fn completes_through(&self) -> Option<crate::interpreter::dispatcher::CompletionTarget> {
        Some(self.decides.clone())
    }

    fn input_entry(&self, input: &str) -> Option<crate::interpreter::dispatcher::Placement> {
        (input == "source").then(|| self.source_entry.clone())
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        visit("store", &*state.store_producer);
        visit("source", &*state.source_producer);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let state = self
            .state
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        visit("store", &mut *state.store_producer);
        visit("source", &mut *state.source_producer);
    }

    /// The drive reads its source again at its next pull; it reads its store at every one.
    fn read_again(&mut self, input: &str) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        if input == "source" {
            state.source_news.record(&Projection::Everything);
        }
    }

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(state.window.held_values())
    }

    fn get_impl(&self, guard: TileGuard) -> Tile {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let mut tile = state.rendered.clone();
        tile.restrict_to(&guard.projection(&self.name()), self.tiling());
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // A release names the drive's rows; what it has decided holds no key.
        let obsolete_guard = &obsolete_guard;
        // The commit-ack — but only because this producer sits behind a `FanOut`
        // whose slots are the body and the writer, so what arrives here is
        // their **intersection**. The body releases a row as soon as it has
        // *consumed* it, which is not an ack; the writer releases it when the
        // attempt has *finished* (committed, or denied without proposing). The
        // intersection acknowledges the item. Superseded retries for the same item share an attempt prefix
        // and give the same answer, so the rule is idempotent under any order.
        //
        // The window holds rows, so it acts on the rows the release names whole. What the
        // release names of a row's values is withheld from the output (`get_impl`).
        let pred = &obsolete_guard.whole_keys();
        // Only the **newest** live row's release is the item's finish. An older one
        // is a superseded retry, which the writer releases as soon as a newer
        // attempt replaces it — reclaiming that row must not acknowledge
        // an item still in flight, which is the same mistake as taking the body's
        // consume-release for an ack. The window is all one item, so the newest row
        // is the last, and superseded rows are exactly the prefix compacted below.
        if let Some((pos, row)) = state.window.newest()
            && pred.contains(pos.value())
        {
            let finished = row.item_position.clone();
            state.taken.insert(finished.clone(), row.item.clone());
            let path = one_component(finished.clone());
            state.source.items.remove(&path);
            state.source.held.remove(&path);
            self.release_source_region(state, Predicate::point(finished.into_value()));
        }
        state.window.acknowledge(pred);
        self.debug_assert_window_invariants(state);
    }
}

/// The body-input tiling both writers' drivers produce: `domain → {_0…_{r-1}: read, _r:
/// item}`, where `domain` is the loop's positions for an induction drive and the attempt
/// counter for a transactional one. A nested drive stands the rows above its positions over
/// that, one level each, and wraps the slots with the enclosing parameter
/// ([`wrap_enclosing_tiling`]).
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
    item_positions: Option<&Extent>,
) -> Tiling {
    let mut fields = body_input_fields(read_extents, item, |_, ext| Tiling::from_extent(ext));
    if let Some(extent) = item_positions {
        fields.insert(
            SmolStr::new_static(F_ATTEMPT_SNAPSHOT),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        fields.insert(
            SmolStr::new_static(F_ITEM_POSITION),
            Tiling::Scalar(extent.clone()),
        );
    }
    let slots = Tiling::Record(fields);
    let per_position = Tiling::data_function(
        domain.clone(),
        wrap_enclosing_tiling(nested.map(|n| &n.param), slots),
    );
    match nested {
        None => per_position,
        // A nested store's body runs over a **path** — the rows above it, then the
        // position within the last — and the path is one level per component rather than
        // one encoded key.
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
    /// The last is the enclosing positions, one row of the induction store each; anything
    /// before it **stands above** — levels the induction store sits under and leaves standing,
    /// which a nest deeper than two has. Depth lives in this list's length and nowhere in the code that walks it.
    pub rows: Vec<Extent>,
    /// The enclosing parameter `(ᴘ, Pos)` the body takes beside its slots.
    pub param: Extent,
}

/// A **nested** writer's body takes `((ᴘ, Pos), slots)` where a top-level one takes
/// `slots`: everything it reads from the enclosing position arrives as a slot, but the
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
) -> HashMap<SmolStr, T> {
    let mut fields: HashMap<SmolStr, T> = HashMap::with_capacity(read_extents.len() + 1);
    for (i, ext) in read_extents.iter().enumerate() {
        fields.insert(tuple_field(i), read(i, ext));
    }
    fields.insert(tuple_field(read_extents.len()), item);
    fields
}

/// The source position of the item driver row `pos` was built for, read off its
/// [`F_ITEM_POSITION`] field.
fn item_position_at(driver_tile: &Tile, pos: &Position) -> Value {
    driver_field_at(driver_tile, pos, F_ITEM_POSITION)
}

fn driver_field_at(driver_tile: &Tile, pos: &Position, field: &str) -> Value {
    let Tile::DataFunction {
        domain, codomain, ..
    } = driver_tile
    else {
        panic!("a transaction driver renders a collection of rows, got {driver_tile:?}")
    };
    let row = (0..domain.len())
        .find(|&i| &domain.index_at(i) == pos.value())
        .unwrap_or_else(|| panic!("the attempt {pos} is a row of its driver"));
    let Tile::Record { fields, .. } = codomain.as_ref() else {
        panic!("a transaction driver's row is a record of its slots")
    };
    let Some(Tile::Scalar(positions)) = fields.get(field) else {
        panic!("a transaction driver's row carries {field}")
    };
    positions.index_at(row)
}

/// The field of a transaction driver's row holding the source position of its item, beside the
/// body's slots ([`TransactDriver::new`]). The writer keys its proposals and its taps by it, which
/// is how a consuming store learns the item a proposal is for. It is not a tuple field, so no
/// projection of the body's parameter reaches it.
pub(crate) const F_ITEM_POSITION: &str = "item_position";
const F_ATTEMPT_SNAPSHOT: &str = "attempt_snapshot";

/// The `` `fired `` tag of a write's or a tap's `` {`fired{𝑉} | `idle} ``, matched by name
/// so a variant materialized in any arm order reads the same.
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

/// Release a store's changelog at or below `through` on this consumer's slot of the store.
///
/// The commit store reclaims a version once every slot behind its `FanOut` has released it.
fn release_store_through(store: &mut dyn TileProducer, through: &Position) {
    store.release(TileGuard::Function(FunctionGuard::Domain(
        Predicate::at_or_below(through.value().clone()),
    )));
}

/// Release a store's changelog through its last change strictly below `bound`, which leaves
/// the change at `bound` itself for the fold to find. A store with no change below `bound`
/// releases nothing.
fn release_store_below(store: &mut dyn TileProducer, tile: &Tile, bound: &Position) {
    if let Some(below) = last_position_below(tile.store_change_positions(), bound) {
        release_store_through(store, &below);
    }
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

/// Extract a writer body's *decision* at position `pos` of its input.
///
/// The body returns a **decision record** `{writes: {𝑘: …}, __to_<defer>*}`
/// ([`crate::ccl::ccl_utils::writer_decision`]), each write and each tap holding
/// `` {`fired{𝑉} | `idle} ``: one record per position, as one column of records or a record
/// of columns.
///
/// Returns one entry per `write_keys` key, carry keys then taps: the value the decision
/// writes there where it fires, and `None` where it is `` `idle ``. A carry key's entry is the
/// written value, and a tap's is its whole `` `fired `` value, which the store holds tag and
/// all: the IR reads a tap through ``variant_project(`fired)``, so the stream's restriction to
/// fired positions happens there, on a value whose type says what it is. `None` where the
/// body has not decided `pos`.
fn body_decision_at(
    tile: &Tile,
    pos: &Position,
    write_keys: &[Value],
    tap_fields: &[SmolStr],
) -> Option<Vec<Option<Value>>> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = tile
    else {
        return None;
    };
    let row = (0..domain.len()).find(|&i| &domain.index_at(i) == pos.value())?;
    decision_at_index(&decision_column(codomain), row, write_keys, tap_fields)
}

/// The decisions a body tile holds at its deepest level, as one column of records: a body
/// whose decision holds only scalars renders them as one, which this borrows, and one
/// assembled field by field as a record of columns, which this pivots.
fn decision_column(values: &Tile) -> std::borrow::Cow<'_, ColumnValue> {
    match values {
        Tile::Scalar(column) => std::borrow::Cow::Borrowed(column),
        record @ Tile::Record { .. } => std::borrow::Cow::Owned(
            crate::interpreter::tile_operators::scalar_tile_to_column_value(record.clone()),
        ),
        other => panic!("a writer body's decisions are records, got {other:?}"),
    }
}

/// [`body_decision_at`] once the row is known. The induction store finds the row by walking
/// the decision stream's levels ([`decided_paths`]) rather than by looking a position up:
/// an inner position repeats across enclosing positions, so only the path identifies a
/// decision.
fn decision_at_index(
    decisions: &ColumnValue,
    row: usize,
    write_keys: &[Value],
    tap_fields: &[SmolStr],
) -> Option<Vec<Option<Value>>> {
    let Value::Record(decision) = decisions.index_at(row) else {
        return None;
    };
    // The write set is keyed by the variable written, so it is read back by name, in
    // `write_keys` order — the order the caller aligns with. A store key is the variable's
    // name as a tag over the data key it holds (`store_key`), so the name is the tag; the
    // write set never keys by the data key, because a keyed write commits the whole
    // collection at `` `reg(unit) ``. `write_keys` is carry keys ++ tap keys (the layout
    // `build_induction_store_single` and `build_commit_store` both set).
    assert!(
        write_keys.len() >= tap_fields.len(),
        "write keys are the carry keys followed by one per tap: {} keys, {} taps",
        write_keys.len(),
        tap_fields.len(),
    );
    let n_carry = write_keys.len() - tap_fields.len();
    let mut writes = Vec::with_capacity(write_keys.len());
    match decision.get(&F_WRITES.runtime_key())? {
        Value::Record(writes_rec) => {
            debug_assert_eq!(
                writes_rec.len(),
                n_carry,
                "a decision states every carry key of the store consuming it",
            );
            for key in &write_keys[..n_carry] {
                let Value::Union {
                    tag: crate::ccl::FieldKey::Name(name),
                    ..
                } = key
                else {
                    return None;
                };
                let Value::Union { tag, inner } = writes_rec.get(&name.runtime_key())?.clone()
                else {
                    return None;
                };
                writes.push(is_fired_tag(&tag).then_some(*inner));
            }
        }
        // A writer that only reads writes nothing: its write set is `unit`.
        Value::Unit => debug_assert_eq!(n_carry, 0, "a `unit` write set states no key"),
        _ => return None,
    }
    for tap in tap_fields {
        let value = decision.get(tap)?.clone();
        let Value::Union { tag, .. } = &value else {
            return None;
        };
        writes.push(is_fired_tag(tag).then_some(value));
    }
    Some(writes)
}

/// A complete transaction writer over a multi-key [`CommitOperator`], fused into
/// one operator (the store read, the body application, and the proposal build)
/// so it has a *single* consumer — the `CommitProducer` — and emits a
/// **stable, append-only** proposal stream (positions never shift), exactly like
/// the hand-written `TokenWriter`. Fusing is load-bearing: a writer split across
/// fanned operators desyncs, because the `FanOut` compacts released positions
/// per-slot and the proposal positions would re-index out from under the
/// `CommitProducer`'s cursor.
///
/// Each consume: take the newest live position from the [`TransactDriver`] — which built
/// that row from `(item, frontier)`, one row per pair — pull the body for its decision,
/// and append the proposal `{snap: frontier, reads: {key ↦ old}, writes: {key ↦ new}}`.
/// Releasing the driver row acks the attempt's finish, so the driver advances to the next
/// item. Retries (a fresh attempt at a new frontier) append as new positions.
pub struct TransactWriter {
    base: OperatorBase,
    store_op: std::sync::Arc<dyn TileOperator>,
    body_op: std::sync::Arc<dyn TileOperator>,
    /// A second slot of the [`TransactDriver`] the body reads. The writer pulls
    /// it to learn which attempt is in flight, and **releases** it to ack the
    /// attempt's finish — the half of the driver's release intersection that a
    /// body's consume-release cannot supply.
    driver_op: std::sync::Arc<dyn TileOperator>,
    /// Runtime keys the body reads a snapshot of, in body-parameter order
    /// (snapshot position `i` ↦ `read_keys[i]`).
    read_keys: Vec<Value>,
    /// Runtime keys the body writes, aligned with the decision's `writes` tuple
    /// followed by the `tap_fields` taps (`write_keys[j]` ↦ the `j`-th committed
    /// value). A reply (`resps << e`) rides the writer body as a `__to_<defer>`
    /// decision field (a *tap*); op-conversion folds each tap into the committed
    /// write set as a write-only key, so the reply is committed atomically with
    /// the transaction.
    write_keys: Vec<Value>,
    /// Decision-record field names of the reply taps, in `write_keys` tail order.
    /// Their values are appended to each committed write set (a tap commits iff
    /// its transaction does, so a denied request replies nothing). Each commits as the pair
    /// `(item position, value)`, the position read off the driver's row
    /// ([`F_ITEM_POSITION`]), which `RekeySorted` re-keys the tap's stream by, so a reply is
    /// keyed by the item it answers.
    tap_fields: Vec<SmolStr>,
    /// The extent of the transaction source's positions, which each proposal carries its
    /// item's in.
    item_positions: Extent,
}

impl TransactWriter {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        store_op: std::sync::Arc<dyn TileOperator>,
        body_op: std::sync::Arc<dyn TileOperator>,
        driver_op: std::sync::Arc<dyn TileOperator>,
        read_keys: Vec<Value>,
        write_keys: Vec<Value>,
        tap_fields: Vec<SmolStr>,
        key_extent: Extent,
        value_extent: Extent,
        item_positions: Extent,
    ) -> Self {
        Self {
            base: OperatorBase::new(proposal_stream_tiling(
                &key_extent,
                &value_extent,
                &item_positions,
            )),
            store_op,
            body_op,
            driver_op,
            read_keys,
            write_keys,
            tap_fields,
            item_positions,
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
        self: std::sync::Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        // The driver's source entry schedules this writer's requests. Its notifications
        // reach readers through the driver slot below. The store and body are read inside
        // the scheduled writer pipeline; forwarding the cyclic store would loop.
        let consumer = shared_consumer(consumer);
        let sg = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.clone().subscribe(sg, Box::new(|| {}), cx);
        let body_tiling = self.body_op.tiling().clone();
        let (entry, body_entry) =
            crate::interpreter::dispatcher::Entry::unplaced(body_tiling.clone());
        let body_consumer = shared_consumer(Box::new(entry));
        let body_producer = self.body_op.clone().subscribe(
            body_tiling.universal_guard(),
            forwarding_consumer_keeping_keys(&body_consumer),
            cx,
        );
        // Forward the driver's notification to this writer's consumer: the driver
        // owns the transaction source, so a request arriving on a live source
        // reaches this writer, and through it the commit cycle, along this edge.
        let driver_producer = self.driver_op.clone().subscribe(
            self.driver_op.tiling().universal_guard(),
            crate::interpreter::notifications::through_values(
                CurryLevel::new(1),
                self.driver_op.tiling(),
                forwarding_consumer_keeping_keys(&body_consumer),
            ),
            cx,
        );
        crate::interpreter::tile_operators::share_breaker(TransactWriterProducer {
            base: ProducerBase::new(
                TransactWriterProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(consumer, body_entry),
            read_keys: self.read_keys.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            item_positions: self.item_positions.clone(),
            state: std::sync::Mutex::new(TransactionWriterState {
                store_producer,
                body_producer,
                driver_producer,
                last_decided_pos: None,
                driver_terminal: false,
                committed_base: 0,
                emitted: Vec::new(),
            }),
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
/// The item's source position rides along as the driver's row stated it
/// ([`F_ITEM_POSITION`]): the writer copies it into the proposal for a store that keys its
/// takes by it. The driver owns the transaction source and acknowledges its items. The writer
/// names an attempt by the driver position it came from, which is the identity the driver
/// itself uses.
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
    /// The source position of the attempt's item, as the driver's row states it.
    item: Position,
}

struct TransactWriterProducer {
    base: ProducerBase,
    read_keys: Vec<Value>,
    write_keys: Vec<Value>,
    /// Reply-tap decision fields, appended to each write set (see
    /// [`TransactWriter::tap_fields`]).
    tap_fields: Vec<SmolStr>,
    /// The extent of the transaction source's positions ([`TransactWriter::item_positions`]).
    item_positions: Extent,
    state: std::sync::Mutex<TransactionWriterState>,
}
struct TransactionWriterState {
    store_producer: Box<dyn TileProducer>,
    body_producer: Box<dyn TileProducer>,
    /// The driver slot this writer acks on (see [`TransactWriter::driver_op`]).
    driver_producer: Box<dyn TileProducer>,
    /// How far the drive has decided its source, as its last pull stated it
    /// ([`decided_tile`]), which this writer forwards.
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
    committed_base: u64,
    /// Proposals not yet released — append-only within the live window. The
    /// entry at vector index `i` is absolute position `committed_base + i`.
    emitted: Vec<InFlightProposal>,
}

impl TransactWriterProducer {
    fn render(&self, state: &TransactionWriterState) -> Tile {
        let n = state.emitted.len();
        let reads: Vec<Value> = state
            .emitted
            .iter()
            .map(|p| map_to_value(&p.reads))
            .collect();
        let writes: Vec<Value> = state
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
        let terminal = state.driver_terminal && state.emitted.is_empty();
        Tile::data_function(
            // Absolute positions: the live window is `[committed_base, …)`; the
            // released prefix has been compacted away. Positions never renumber.
            ColumnValue::from_uints(
                (state.committed_base..state.committed_base + uint_of_row(n)).collect(),
            ),
            Box::new(Tile::record(HashMap::from([
                (
                    SmolStr::from(F_SNAP),
                    Tile::Scalar(ColumnValue::from_values(
                        state
                            .emitted
                            .iter()
                            .map(|p| p.snapshot.value().clone())
                            .collect(),
                        &Extent::Base(BaseType::UInt),
                    )),
                ),
                (
                    SmolStr::from(F_READS),
                    Tile::Scalar(ColumnValue::Variants(reads)),
                ),
                (
                    F_WRITES.runtime_key(),
                    Tile::Scalar(ColumnValue::Variants(writes)),
                ),
                (
                    SmolStr::from(F_POS),
                    Tile::Scalar(ColumnValue::from_values(
                        state
                            .emitted
                            .iter()
                            .map(|p| p.item.value().clone())
                            .collect(),
                        &self.item_positions,
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

    /// Ack every attempt at or below `pos` — issued when an attempt finishes: a
    /// deny (no proposal to commit) or a commit-ack on the proposal it produced.
    ///
    /// It releases both driver slots this writer controls: its **own**, which
    /// is the half of the driver's release intersection meaning "finished" (the
    /// body's half only means "consumed"), and the body's decision prefix, which
    /// bounds the body sub-operator's caches. Positions are absolute, so the
    /// windows slide forward without renumbering.
    fn ack_through(&self, state: &mut TransactionWriterState, pos: &Position) {
        let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            pos.value().clone(),
        )));
        state.driver_producer.release(guard.clone());
        state.body_producer.release(guard);
    }

    /// The write set a decision at driver position `pos` proposes: each carry key and each
    /// tap it fires, a tap paired with the item it answers. A decision that fires nothing, a
    /// deny or a read that replies nothing, proposes an empty write set.
    fn proposal_writes(
        &self,
        writes: Vec<Option<Value>>,
        driver_tile: &Tile,
        pos: &Position,
    ) -> HashMap<Value, Value> {
        // `write_keys` and the decision's writes are two views of the same store keys,
        // aligned by position: carry keys, then tap keys (the layout `build_commit_store`
        // sets). A length mismatch is a `transact_phase`/inference bug that `zip` would
        // otherwise paper over by silently dropping the tail.
        debug_assert_eq!(
            self.write_keys.len(),
            writes.len(),
            "commit operator: decision write-set arity ({}) disagrees with write_keys ({}) — \
             zip would silently drop the tail",
            writes.len(),
            self.write_keys.len()
        );
        let n_carry = self.write_keys.len() - self.tap_fields.len();
        let item_position =
            (!self.tap_fields.is_empty()).then(|| item_position_at(driver_tile, pos));
        self.write_keys
            .iter()
            .cloned()
            .zip(writes)
            .enumerate()
            .filter_map(|(i, (key, value))| {
                let value = value?;
                if i < n_carry {
                    return Some((key, value));
                }
                let at = item_position
                    .clone()
                    .expect("a writer with a tap reads item positions");
                let pair = Value::Record(HashMap::from([
                    (tuple_field(0), at),
                    (tuple_field(1), value),
                ]));
                Some((key, pair))
            })
            .collect()
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
    fn drop_superseded(&self, state: &mut TransactionWriterState, attempt: &Position) {
        debug_assert!(
            state.emitted.iter().all(|p| p.attempt < *attempt),
            "drop_superseded: live window holds a proposal at or past the position being \
             decided ({attempt}) — {:?}; a superseded proposal is one from a strictly \
             earlier attempt",
            state
                .emitted
                .iter()
                .map(|p| p.attempt.clone())
                .collect::<Vec<_>>()
        );
        let drop = state.emitted.len();
        if drop > 0 {
            state.emitted.clear();
            state.committed_base += uint_of_row(drop);
        }
    }
}

impl TransactWriterProducer {
    fn debug_assert_position_invariant(&self, state: &mut TransactionWriterState) {
        // The proposal stream is append-only and consumer-indexed
        // (`CommitProducer` reads it by position), so a live window's entries stay
        // in emission order: each proposal is decided from a strictly later driver
        // position than the one before. A window that ever went backwards would
        // mean a position had shifted under the consumer's cursor. Driver positions
        // are the ordering because they are what the writer names an attempt by —
        // source positions identify items but do not order attempts.
        debug_assert!(
            state
                .emitted
                .windows(2)
                .all(|w| w[0].attempt < w[1].attempt),
            "the live proposal window is out of attempt order: {:?}",
            state
                .emitted
                .iter()
                .map(|p| p.attempt.clone())
                .collect::<Vec<_>>()
        );
    }
}

impl Breaker for TransactWriterProducer {
    fn input_tiling(&self, _: InputId) -> Tiling {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.body_producer.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        state.body_producer.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }

    fn consume_impl(&self, _: InputId, _: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        let store_tile = state
            .store_producer
            .get(state.store_producer.tiling().universal_guard());
        // The snapshot the proposal is built against: the store's decided frontier
        // (watermark). Each read key reads its value there; a key with no value
        // yet (an *append* onto an empty collection store) reads nothing — it is
        // omitted from the read set, the empty-store bootstrap that lets the first
        // `<<` commit (a collection store starts with no element).
        let snapshot = store_frontier(&store_tile);
        // Read each key's current value *and* the tick it was decided at — the
        // tick bounds this writer's store-slot release below.
        let olds_at: Vec<Option<(Position, Value)>> = self
            .read_keys
            .iter()
            .map(|k| store_current(&store_tile, k))
            .collect();
        // Store-slot GC release. The store reclaims a committed version only
        // once *every* consumer slot has released it (the cyclic `FanOut`
        // intersects the release guards; `gc_released_prefix` then drops the
        // released prefix, keeping the carry source a live position reads — the
        // carry-forward value a scalar read still needs). Two writer shapes
        // release here:
        //
        //  - **Empty read set** (a collection-append / overwrite writer, e.g.
        //    `<<` or `latest = msg`): it reads no tick's value, only the frontier,
        //    so it releases the whole decided prefix.
        //  - **Non-empty read set** (a carry drawdown, e.g. `pool = pool - r`):
        //    it releases strictly below the oldest tick it read this pull, so it
        //    never releases a version a proposal in its own window read, and
        //    because GC reclaims only the intersection of every slot's release,
        //    one writer's release never strands another writer's or a reader's
        //    reads. A proposal a consuming store has taken is no longer in this
        //    window, and the store protects its reads itself: its reclaim stops
        //    below the oldest held proposal's snapshot
        //    (`CommitProducer::release_impl`). Without this release a reading
        //    writer released nothing and pinned the commit log for its lifetime.
        if self.read_keys.is_empty() {
            if let Some(through) = &snapshot {
                release_store_through(&mut *state.store_producer, through);
            }
        } else if let Some(oldest_read) = olds_at
            .iter()
            .filter_map(|o| o.as_ref().map(|(t, _)| t))
            .min()
        {
            release_store_below(&mut *state.store_producer, &store_tile, oldest_read);
        }
        // The decisions for every live attempt. Which one to act on is settled
        // below, off the driver: the driver emits a row once per `(item, frontier)`,
        // so a position appearing here is a distinct attempt, and re-pulling at an
        // unchanged pair adds none.
        let body_tile = state
            .body_producer
            .get(state.body_producer.tiling().universal_guard());
        // The attempt to decide is the newest live position on this writer's own
        // driver slot — the row the driver emitted for `(current, frontier)` this
        // pull, or the one still in flight from an earlier one. Reading it here
        // rather than counting positions independently keeps the writer and the
        // driver from inventing two numberings that could drift.
        let driver_tile = state
            .driver_producer
            .get(state.driver_producer.tiling().universal_guard());
        state.driver_terminal = driver_tile.is_terminal();
        let newest = newest_body_position(&driver_tile);
        // The body can run while another writer commits. Its proposal must retain the
        // frontier captured by this attempt, never the frontier at proposal consumption.
        let snapshot = newest.as_ref().map(|position| {
            Position::new(driver_field_at(&driver_tile, position, F_ATTEMPT_SNAPSHOT))
        });
        let olds: Vec<Option<Value>> = self
            .read_keys
            .iter()
            .map(|key| {
                snapshot
                    .as_ref()
                    .and_then(|at| store_value_at(&store_tile, at, key))
            })
            .collect();

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
                .is_none_or(|n| state.last_decided_pos.as_ref().is_none_or(|d| n >= d)),
            "the driver's newest position {newest:?} went backwards past the decided watermark {:?}",
            state.last_decided_pos
        );
        // Reclaim what supersession abandons, on this writer's driver slot. Every
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
            state
                .driver_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::at_or_below(through.into_value()),
                )));
        }
        // Decide a position once. A *new* newest position is a fresh attempt (a
        // new item, or a retry of this one at a moved frontier); an unchanged one
        // is either already decided — the driver suppresses re-emitting at an
        // unchanged `(item, frontier)` — or a not-ready decision to re-read.
        if let Some(pos) = newest
            && Some(&pos) != state.last_decided_pos.as_ref()
            && let Some(frontier) = snapshot
        {
            let item = Position::new(item_position_at(&driver_tile, &pos));
            // Every decision proposes, a deny and a grant that writes nothing included: a
            // transaction takes a tick whatever it writes, so the engine, and not this
            // writer's pull timing, places the snapshot it read
            // (`src/ccl/design/mutability.md`, "Every transaction takes a tick"). The operator
            // decides whether it commits — its ack releases the driver row, which is what
            // advances the driver past this item — or is stale, leaving the item to be
            // re-attempted at the moved frontier, where the body may decide otherwise.
            let writes =
                match body_decision_at(&body_tile, &pos, &self.write_keys, &self.tap_fields) {
                    Some(writes) => Some(self.proposal_writes(writes, &driver_tile, &pos)),
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
                        None
                    }
                };
            if let Some(writes) = writes {
                // The read set omits never-written keys (append → empty read).
                let reads: HashMap<Value, Value> = self
                    .read_keys
                    .iter()
                    .zip(&olds)
                    .filter_map(|(k, o)| o.clone().map(|v| (k.clone(), v)))
                    .collect();
                // Re-proposing this item at a new frontier supersedes its prior stale
                // proposal(s), whichever way they decided; drop them so the window stays
                // O(1).
                self.drop_superseded(state, &pos);
                state.last_decided_pos = Some(pos.clone());
                // The body-input row stays live until the commit-ack: it is the attempt in
                // flight, and releasing it now would tell the driver this item is finished
                // before it has committed.
                state.emitted.push(InFlightProposal {
                    snapshot: frontier,
                    reads,
                    writes,
                    attempt: pos,
                    item,
                });
            }
        }
        self.debug_assert_position_invariant(state);
        if state.driver_terminal && state.emitted.is_empty() {
            state
                .body_producer
                .release(state.body_producer.tiling().universal_guard());
            state
                .driver_producer
                .release(state.driver_producer.tiling().universal_guard());
        }
    }
}

impl BreakingProducer for TransactWriterProducer {
    fn complete(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        self.render(state).to_guard()
    }

    fn final_guard(&self) -> TileGuard {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        self.complete_in_state(state)
    }
}
impl TransactWriterProducer {
    fn complete_in_state(&self, state: &TransactionWriterState) -> TileGuard {
        self.render(state).to_guard()
    }
}

impl TileProducer for TransactWriterProducer {
    impl_producer_base!();

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        visit("store", &*state.store_producer);
        visit("body", &*state.body_producer);
        visit("driver", &*state.driver_producer);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let state = self
            .state
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner);

        visit("store", &mut *state.store_producer);
        visit("body", &mut *state.body_producer);
        visit("driver", &mut *state.driver_producer);
    }

    fn state_info(&self) -> ProducerStateInfo {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        ProducerStateInfo::holding(
            state
                .emitted
                .iter()
                .map(|p| p.reads.len() + p.writes.len())
                .sum(),
        )
    }

    fn get_impl(&self, guard: TileGuard) -> Tile {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // A release naming part of a proposal rather than the proposal leaves it in the
        // window (`release_impl`), so what it names is withheld here.
        let mut tile = self.render(state);
        tile.restrict_to(&guard.projection(&self.name()), self.tiling());
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let mut state_guard = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let state = &mut *state_guard;

        // commit-ack: advance past the item each released proposal was for, then
        // compact the released prefix out of the live window. Idempotent.
        self.debug_assert_position_invariant(state);
        //
        // The window holds rows, so it acts on the rows the release names whole. What the
        // release names of a row's values is withheld from the output (`get_impl`). What the
        // drive has decided holds no key to release.
        let pred = &&obsolete_guard.whole_keys();
        // The entry at vector index `i` is absolute position `committed_base + i`
        // (positions are stable; the consumer releases by that absolute value).
        // A committed proposal finishes its item, so ack the driver row it was
        // decided from — the driver acknowledges and removes the source item.
        let ack = state
            .emitted
            .iter()
            .enumerate()
            .filter(|(i, _)| pred.contains(&Value::UInt(state.committed_base + uint_of_row(*i))))
            .map(|(_, p)| p.attempt.clone())
            .max();
        if let Some(pos) = ack {
            self.ack_through(state, &pos);
        }
        // Drop the released leading prefix and advance the window base. Releases
        // are prefixes (`at_or_below(step)`, accumulated across commits), so the
        // released positions form a run from `committed_base` up. Dropping frees
        // the proposal records (their read/write maps) without renumbering the
        // live suffix — `CommitProducer` reads remaining positions by value.
        let mut drop = 0;
        while drop < state.emitted.len()
            && pred.contains(&Value::UInt(state.committed_base + uint_of_row(drop)))
        {
            drop += 1;
        }
        if drop > 0 {
            state.emitted.drain(0..drop);
            state.committed_base += uint_of_row(drop);
        }
    }
}

/// The positions a nested drive has yet to see decided: the `delivered` ones above the
/// `emitted_through` cursor, and the emitted position itself while the store's `frontier` has
/// not reached it.
///
/// A delivered path at or below the cursor is not undecided: the source may honour the drive's
/// release a pull late, so its decode can still show a position the drive has emitted. The
/// drive emits only when the frontier is at its last emitted position, so the emitted position
/// is the only one that can be past the frontier. `delivered` is in path order.
fn undecided_positions<'a>(
    delivered: impl Iterator<Item = &'a Path>,
    emitted_through: Option<&'a Path>,
    frontier: Option<&Path>,
) -> Vec<&'a Path> {
    delivered
        .filter(|p| emitted_through.is_none_or(|e| *p > e))
        .chain(emitted_through.filter(|e| frontier.is_none_or(|f| *e > f)))
        .collect()
}

/// The rows at `level` with no undecided position under them: every row of the level less the
/// row each undecided position lies in, named by its full prefix of enclosing rows. A row no
/// position names is in the predicate, including every row when `undecided` is empty.
fn rows_folded_at(level: usize, undecided: &[&Path]) -> Predicate {
    let mut rows_of_undecided: Vec<&[Value]> = undecided
        .iter()
        .map(|p| {
            let (rows, _) = p
                .split_position()
                .unwrap_or_else(|| unreachable!("a source path names a position"));
            &rows[..=level]
        })
        .collect();
    // `undecided` lists the delivered paths in order, so their rows are grouped and one `minus`
    // answers for all the positions under a row. The emitted position follows them; a repeat
    // there is an idempotent `minus`.
    rows_of_undecided.dedup();
    rows_of_undecided
        .into_iter()
        .fold(Predicate::True, |folded, rows| {
            folded.minus(&Predicate::exactly(rows))
        })
}

impl InductionStoreProducer {
    fn inputs_in_state(&self) -> usize {
        1
    }
}
impl InductionStoreProducer {
    fn read_cycle_inputs(&self, state: &mut InductionState, cycle: &Cycle) {
        let fan = cycle.fan();
        self.read_inputs_again(state, &|producer| {
            producer.recurrence_of().map(|through| through == fan)
        });
    }
}
impl InductionStoreProducer {
    fn read_inputs_again(
        &self,
        state: &mut InductionState,
        target: &dyn Fn(&dyn TileProducer) -> Option<bool>,
    ) {
        self.visit_input_producers_mut_in_state(state, &mut |_, input| {
            read_again_toward(input, target);
        });
    }
}
impl CommitProducer {
    fn read_cycle_inputs(&self, state: &mut CommitState, cycle: &Cycle) {
        let fan = cycle.fan();
        self.read_inputs_again(state, &|producer| {
            producer.recurrence_of().map(|through| through == fan)
        });
    }
}
impl CommitProducer {
    fn read_inputs_again(
        &self,
        state: &mut CommitState,
        target: &dyn Fn(&dyn TileProducer) -> Option<bool>,
    ) {
        self.visit_input_producers_mut_in_state(state, &mut |_, input| {
            read_again_toward(input, target);
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
    // The consumer helpers own shared-cell construction for the operators here; the
    // fixtures below build their own recording cells, hence the direct imports.
    use crate::ccl::{FieldKey, TagMap, V_FIRED, V_IDLE};
    use crate::interpreter::tile_operators::{Constant, FanOut, Memo};
    use crate::interpreter::tiling::{one_row_decided, row_frontier};
    use crate::interpreter::validate_tile;
    use rstest::rstest;
    use std::sync::Arc;
    use std::sync::RwLock;

    struct DispatchedStore {
        _ctx: crate::ccl::context::GlobalContext,
        program: crate::ccl::context::CompiledProgram,
        fan: Arc<FanOut>,
    }

    impl std::ops::Deref for DispatchedStore {
        type Target = Arc<FanOut>;
        fn deref(&self) -> &Self::Target {
            &self.fan
        }
    }

    impl DispatchedStore {
        fn new(source: &str) -> Self {
            Self::with(source, |_| {})
        }

        fn with(source: &str, setup: impl FnOnce(&mut crate::ccl::context::GlobalContext)) -> Self {
            use crate::ccl::{
                context::{GlobalContext, compile_program},
                load::LoadedProgram,
            };
            let mut ctx = GlobalContext::default();
            setup(&mut ctx);
            ctx.register_test_sink("out");
            let program = compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
                .unwrap_or_else(|errors| panic!("{source}: {errors:?}"));
            let operators = ctx.take_operator_map();
            let mut stores = operators
                .operators()
                .into_iter()
                .filter(|fan| fan.store().is_some());
            let fan = stores.next().expect("the fixture declares a store");
            assert!(stores.next().is_none(), "the fixture declares one store");
            Self {
                _ctx: ctx,
                program,
                fan,
            }
        }

        fn run(&mut self) {
            crate::interpreter::dispatcher::run_program(&mut self.program, 1)
                .expect("the fixture dispatches");
        }

        fn poll(&mut self) {
            struct Pause;
            impl crate::interpreter::dispatcher::RunObserver for Pause {
                fn drained(&mut self, _: bool) -> std::ops::ControlFlow<()> {
                    std::ops::ControlFlow::Break(())
                }
            }
            let mut targets = crate::interpreter::dispatcher::Targets::default();
            targets.add_sinks(&self.program);
            targets.run(1, &mut Pause).expect("the fixture dispatches");
        }

        fn snapshot(&mut self) -> Tile {
            let reader = self.fan.slot();
            let producer = reader.clone().subscribe(
                reader.tiling().universal_guard(),
                Box::new(|| {}),
                &mut SubscribeContext::new(),
            );
            self.run();
            producer.get(producer.tiling().universal_guard())
        }
    }

    fn consume_input(fan: &Arc<FanOut>, input: usize, guard: TileGuard) {
        let cell = fan.store().expect("the store is subscribed");
        let mut store = cell.write();
        store
            .as_breaking_mut()
            .unwrap()
            .consume_in_pipeline(InputId(input), guard);
    }

    /// Consume the breaker `reader` shares at the whole of its input, as the pipeline feeding it
    /// does, then read it: a breaker read inside a run answers from what it has consumed.
    fn consume_and_read(reader: &mut Box<dyn TileProducer>) -> Tile {
        consume_shared(&mut **reader, &mut |_| {});
        reader.get(reader.tiling().universal_guard())
    }

    /// Consume a nested drive `reader` shares as its pipelines do: first the memo over its
    /// enclosing parameter and over each reseed, each a breaker of a pipeline of its own, then
    /// the drive. Read it after.
    fn consume_nested_drive_and_read(reader: &mut Box<dyn TileProducer>) -> Tile {
        consume_shared(&mut **reader, &mut |drive| {
            drive.visit_input_producers_mut(&mut |role, input| {
                if role == "pairs" || role == "reseed" {
                    consume_shared(input, &mut |_| {});
                }
            });
        });
        reader.get(reader.tiling().universal_guard())
    }

    /// Consume the breaker `reader` shares at the whole of its input, after `first` has run on
    /// the breaker.
    fn consume_shared(reader: &mut dyn TileProducer, first: &mut dyn FnMut(&mut dyn TileProducer)) {
        let mut reached = false;
        reader.visit_input_producers_mut(&mut |role, breaker| {
            assert_eq!(role, "breaker", "the reader shares a breaker");
            first(&mut *breaker);
            let breaker = breaker
                .as_breaking_mut()
                .expect("a shared breaker breaks a pipeline");
            let whole = breaker.input_tiling(InputId::ONLY).universal_guard();
            breaker.consume_in_pipeline(InputId::ONLY, whole);
            reached = true;
        });
        assert!(reached, "the reader shares a breaker");
    }

    /// The drive an induction store's body reads.
    fn drive_of(fan: &Arc<FanOut>) -> crate::interpreter::dispatcher::BreakerHandle {
        let cell = fan.store().expect("the store is subscribed");
        crate::interpreter::tile_operators::test_helpers::drive_of(&**cell.read())
    }

    /// Step an induction store through `positions` as its loop's scope does: open the store with
    /// a consume at no position, then at each position consume the drive, which emits it into the
    /// body once the store has decided the position before, and then the store.
    fn step_induction(fan: &Arc<FanOut>, positions: std::ops::Range<u64>) {
        let none = fan
            .store()
            .expect("the store is subscribed")
            .write()
            .as_breaking_mut()
            .unwrap()
            .input_tiling(InputId::ONLY)
            .empty_guard();
        consume_input(fan, 0, none);
        let drive = drive_of(fan);
        for position in positions {
            let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(
                position,
            ))));
            drive
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .consume_in_pipeline(InputId::ONLY, guard.clone());
            consume_input(fan, 0, guard);
        }
    }

    mod induction_run_lifecycle {
        use super::*;
        use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        use crate::interpreter::dispatcher::{Ended, RunObserver, Targets};
        use crate::interpreter::operator_conversion::OperatorMap;
        use crate::interpreter::tile_operators::StoreCell;
        use crate::interpreter::{TestDataSource, TestSink};
        use indoc::indoc;
        use std::ops::ControlFlow;
        use std::sync::Arc;

        struct Fixture {
            _ctx: GlobalContext,
            _operators: OperatorMap,
            program: CompiledProgram,
            feed: crate::ccl::SourceDefinition<TestDataSource>,
            sink: Arc<TestSink>,
            store: StoreCell,
        }

        impl Fixture {
            fn new() -> Self {
                let mut ctx = GlobalContext::default();
                let feed = TestDataSource::new(
                    "source1",
                    crate::ccl::Type::Base(BaseType::Int),
                    Extent::Base(BaseType::Int),
                );
                ctx.register_source(feed.clone());
                let sink = ctx.register_test_sink("out");
                let source = indoc! {"
                    out = test_sink()
                    total := 0
                    for x in source1():
                        total += x
                    out << total
                "};
                let program =
                    compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
                        .expect("the induction loop compiles");
                let operators = ctx.take_operator_map();
                let mut stores: Vec<_> = operators
                    .operators()
                    .into_iter()
                    .filter_map(|fan| fan.store())
                    .collect();
                assert_eq!(stores.len(), 1);
                Self {
                    _ctx: ctx,
                    _operators: operators,
                    program,
                    feed,
                    sink,
                    store: stores.remove(0),
                }
            }

            fn first_delivery(&self) {
                let mut feed = self
                    .feed
                    .write()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                feed.add_data(&[
                    (Value::UInt(0), Value::Int(1)),
                    (Value::UInt(1), Value::Int(2)),
                ]);
                feed.set_yield_predicate(Predicate::at_or_below(Value::UInt(1)));
            }

            fn targets(&self) -> Targets {
                let mut targets = Targets::default();
                targets.add_sinks(&self.program);
                targets
            }

            fn assert_run_cleared(&self) {
                let mut store = self.store.write();
                let store = store.as_induction_store_mut().expect("an induction store");
                assert!(
                    store.run.is_none(),
                    "the completed execution plan leaves no scheduling state on its producer"
                );
                assert_eq!(
                    store.state.get_mut().unwrap().breaker.last_finishes,
                    0,
                    "planned induction runs retain no finish count between execution plans"
                );
                assert!(
                    store
                        .seed_placements
                        .iter()
                        .all(|placement| placement.get().is_none()),
                    "a finished run leaves no seed entry assigned to an old pipeline"
                );
                fn check_targets(producer: &dyn TileProducer) {
                    if producer.recurrence_of().is_some() {
                        return;
                    }
                    if let Some(target) = producer.completes_through() {
                        assert!(
                            target
                                .read()
                                .unwrap_or_else(std::sync::PoisonError::into_inner)
                                .is_none(),
                            "source completeness retains no target in the discarded dispatcher"
                        );
                    }
                    producer.visit_input_producers(&mut |_, input| check_targets(input));
                }
                store.visit_input_producers(&mut |_, input| check_targets(input));
            }
        }

        fn progress(store: &StoreCell) -> (Tile, TileGuard) {
            let mut store = store.write();
            let store = store.as_induction_store_mut().expect("an induction store");
            (
                store
                    .state
                    .get_mut()
                    .unwrap()
                    .breaker
                    .snapshot
                    .clone()
                    .expect("the loop has stepped"),
                store.input_released(InputId::ONLY),
            )
        }

        struct AtBoundary {
            store: StoreCell,
            observed: Option<(Tile, TileGuard)>,
            panic: bool,
        }

        impl RunObserver for AtBoundary {
            fn drained(&mut self, _: bool) -> ControlFlow<()> {
                assert!(
                    self.store
                        .write()
                        .as_induction_store_mut()
                        .expect("an induction store")
                        .run
                        .is_some(),
                    "round control belongs to the active execution plan"
                );
                self.observed = Some(progress(&self.store));
                assert!(!self.panic, "intentional induction boundary failure");
                ControlFlow::Break(())
            }
        }

        #[rstest]
        fn scheduling_state_ends_with_the_run_and_progress_survives_replanning(
            #[values(1, usize::MAX)] rows: usize,
        ) {
            let fixture = Fixture::new();
            fixture.first_delivery();
            let mut observer = AtBoundary {
                store: fixture.store.clone(),
                observed: None,
                panic: false,
            };
            assert!(matches!(
                fixture.targets().run(rows, &mut observer).unwrap(),
                Ended::Paused(_)
            ));
            fixture.assert_run_cleared();
            assert_eq!(progress(&fixture.store), observer.observed.unwrap());
            assert_eq!(store_frontier(&progress(&fixture.store).0), Some(pos(1)));

            let mut extra_ctx = GlobalContext::default();
            let extra_sink = extra_ctx.register_test_sink("extra");
            let extra = compile_program(
                &mut extra_ctx,
                &LoadedProgram::test(indoc! {"
                extra = test_sink()
                extra << 7
            "}),
                Box::new(|| {}),
            )
            .expect("the preceding root compiles");
            let _extra_operators = extra_ctx.take_operator_map();
            let mut targets = Targets::default();
            targets.add_sinks(&extra);
            targets.add_sinks(&fixture.program);
            {
                let mut feed = fixture
                    .feed
                    .write()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                feed.add_data(&[(Value::UInt(2), Value::Int(3))]);
                feed.set_yield_predicate(Predicate::True);
            }
            let mut observer = AtBoundary {
                store: fixture.store.clone(),
                observed: None,
                panic: false,
            };
            assert!(matches!(
                targets.run(rows, &mut observer).unwrap(),
                Ended::Done(_)
            ));
            fixture.assert_run_cleared();
            assert!(progress(&fixture.store).0.is_terminal());
            let written = fixture.sink.value().unwrap();
            assert_eq!(written.as_function().len(), 1);
            assert_eq!(written.as_function()[0].output, Value::Int(6));
            assert_eq!(
                extra_sink.value().unwrap().as_function()[0].output,
                Value::Int(7)
            );
        }

        #[test]
        fn scheduling_state_is_cleared_when_execution_unwinds() {
            let fixture = Fixture::new();
            fixture.first_delivery();
            let mut observer = AtBoundary {
                store: fixture.store.clone(),
                observed: None,
                panic: true,
            };
            let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                fixture.targets().run(1, &mut observer)
            }));
            let failure = match failed {
                Err(failure) => failure,
                Ok(_) => panic!("the boundary observer panics"),
            };
            assert_eq!(
                failure
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| failure.downcast_ref::<&str>().copied()),
                Some("intentional induction boundary failure")
            );
            fixture.assert_run_cleared();
            assert_eq!(progress(&fixture.store), observer.observed.unwrap());
        }
    }

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
    fn pos(n: u64) -> Position {
        Position::new(Value::UInt(n))
    }

    /// A store key: the variable's name tagged over the data key it holds
    /// ([`store_key`](crate::interpreter::operator_conversion::store_key)), which is the
    /// shape `body_decision_at` reads the write set's names back from.
    fn acct(name: &str) -> Value {
        store_key(&Label::new(name))
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
    /// is what lets a nest three deep reuse the induction store a nest two deep uses.
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

    /// **A store whose keys hold different value types** renders each changelog at its own
    /// key's type: a `String` key's values are a string column and an `Int` key's an int
    /// column, seed and changelog alike, where one shared codomain could only name their
    /// union. A tick writing one key appears in that key's changelog alone.
    #[test]
    fn a_store_renders_each_key_at_its_own_value_type() {
        let mut e = CommitEngine::new(HashMap::from([
            (acct("name"), Value::String("a".into())),
            (acct("count"), int(0)),
        ]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: HashMap::new(),
                writes: HashMap::from([(acct("count"), int(1))]),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        let tiling = full_store_tiling(
            commit_clock_domain(),
            HashMap::from([
                (
                    "name".into(),
                    Tiling::Scalar(Extent::Base(BaseType::String)),
                ),
                ("count".into(), Tiling::Scalar(value_extent())),
            ]),
        );
        let tile = e.render_full_store_tile(&tiling);
        assert!(validate_tile(&tile));
        let (name_ticks, name_values) = tile.store_changelog("name").expect("a key");
        let (count_ticks, count_values) = tile.store_changelog("count").expect("a key");
        assert!(name_ticks.is_empty(), "nothing wrote `name` after its seed");
        assert_eq!(*name_values, Tile::Scalar(ColumnValue::Strings(Vec::new())));
        assert_eq!(*count_ticks, ColumnValue::from_uints(vec![1]));
        assert_eq!(*count_values, Tile::Scalar(ColumnValue::Ints(vec![1])));
        let Tile::Store { seed, .. } = &tile else {
            panic!("a render is a store: {tile:?}")
        };
        let Tile::Record { fields: seeds, .. } = seed.as_ref() else {
            panic!("a store's seed is a record per key: {seed:?}")
        };
        assert_eq!(
            seeds["name"],
            Tile::Scalar(ColumnValue::Strings(vec!["a".into()]))
        );
        assert_eq!(seeds["count"], Tile::Scalar(ColumnValue::Ints(vec![0])));
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
            tile.store_change_positions().len(),
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

    /// A store's parts state what is final under each store's own row. Two rows decided to
    /// different watermarks restart their positions, so position 1 is final under the row
    /// decided through 2 and not under the row decided through 0. The frontier's watermarks
    /// still move, so it calls nothing final until the store is terminal.
    #[test]
    fn a_store_states_its_parts_complete_under_each_row() {
        let (mut ahead, mut behind) = (CommitEngine::unopened(), CommitEngine::unopened());
        for p in 0..=2 {
            ahead.step(pos(p), Some(balances(&[("acc", p as i64)])));
        }
        behind.step(pos(0), Some(balances(&[("acc", 10)])));
        let tiling = store_tiling(&["acc"]);
        let rows = [
            (vec![Value::UInt(0)], &ahead),
            (vec![Value::UInt(1)], &behind),
        ];
        let statement = |tile: &Tile| {
            let Tile::Store {
                state,
                decided,
                frontier,
                ..
            } = tile
            else {
                panic!("renders a store")
            };
            let Tile::Record { fields: logs, .. } = &**state else {
                panic!("a store's state is a record of changelogs")
            };
            let of = |t: &Tile| match t {
                Tile::DataFunction {
                    domain_predicate, ..
                } => domain_predicate.clone(),
                other => panic!("a store's parts are collections, got {other:?}"),
            };
            (of(&logs["acc"]), of(decided), of(frontier))
        };

        let (changelog, decided, frontier) = statement(&super::store_tile(&rows, &tiling, false));
        for pred in [&changelog, &decided] {
            assert!(pred.contains_path(&[Value::UInt(0), Value::UInt(2)]));
            assert!(pred.contains_path(&[Value::UInt(1), Value::UInt(0)]));
            assert!(
                !pred.contains_path(&[Value::UInt(1), Value::UInt(1)]),
                "the row decided through 0 has not decided position 1: {pred:?}"
            );
        }
        assert_eq!(frontier, Predicate::False);

        let (changelog, decided, frontier) = statement(&super::store_tile(&rows, &tiling, true));
        assert_eq!(
            (changelog, decided, frontier),
            (Predicate::True, Predicate::True, Predicate::True),
            "a terminal store decides nothing more anywhere"
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
                ColumnValue::uints_from_rows(0..items.len()),
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
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(FixedSourceProducer {
                base: ProducerBase::unowned(FixedSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
            })
        }
    }

    /// A live loop source whose rows a filter has removed: every row of `items` is marked
    /// deleted, the source calls them complete, and the tile is not terminal. It records
    /// every release it receives.
    struct FilteredLiveSource {
        tiling: Tiling,
        tile: Tile,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }

    impl FilteredLiveSource {
        fn new(items: &[i64]) -> Self {
            let tiling =
                Tiling::data_function(Extent::Base(BaseType::UInt), Tiling::Scalar(value_extent()));
            let tile = Tile::data_function(
                ColumnValue::uints_from_rows(0..items.len()),
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    items.iter().map(|n| int(*n)).collect(),
                    &value_extent(),
                ))),
                Predicate::at_or_below(Value::uint_from_row(items.len() - 1)),
                (0..items.len()).collect(),
            );
            Self {
                tiling,
                tile,
                released: Arc::default(),
            }
        }
    }

    impl TileOperator for FilteredLiveSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(RecordingSourceProducer {
                base: ProducerBase::unowned(RecordingSourceProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                released: self.released.clone(),
            })
        }
    }

    struct RecordingSourceProducer {
        base: ProducerBase,
        tile: Tile,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }

    impl TileProducer for RecordingSourceProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        // A `Restrict` keeps a filtered row's key, marked deleted, in every tile it
        // emits, so this offers the tile as built.
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }
        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .push(obsolete_guard);
        }
    }

    /// The induction driver releases the rows a filter removed once it reads past them, as
    /// the transaction driver does: no decision is emitted for one, so no store release ever
    /// reaches it. Over a live source filtered to nothing, it releases both rows.
    #[test]
    fn induction_driver_releases_filtered_rows_it_reads_past() {
        let acc = acct("acc");
        let store = InductionStore::new(
            vec![(acc.clone(), Arc::new(Constant::new(int(0), value_extent())))],
            vec![acc.clone()],
            Vec::new(),
            full_store_tiling(Extent::Base(BaseType::UInt), store_values(&["acc"])),
            None,
        );
        let set_body = store.body_input_setter();
        let fan = Arc::new(FanOut::new_cyclic(Arc::new(store)));
        let source = FilteredLiveSource::new(&[10, 20]);
        let released = source.released.clone();
        let driver = InductionDriver::new(
            fan.slot(),
            Arc::new(source),
            None,
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            Extent::Base(BaseType::UInt),
            None,
        );
        set_body(Arc::new(AddIfBody::new(Arc::new(driver), i64::MIN, "acc")));
        let op = fan.slot();
        let guard = op.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let _producer = op.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        step_induction(&fan, 0..2);
        let both = |g: &TileGuard| (0..2).all(|p| g.covers_path(&[Value::UInt(p)]));
        assert!(
            released
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .iter()
                .any(both),
            "the driver releases both filtered rows: {:?}",
            released
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
        );
    }

    /// The decision extent for a single-key writer, `{writes: {acc: {`fired{value} | `idle}}}`.
    ///
    /// The write set is keyed by the variable written, so these fixtures name the key the same
    /// way the CCL side does, and the tags by name, so the order they are listed in is
    /// immaterial.
    fn decision_extent(key: &str) -> Extent {
        let write = Extent::Union(TagMap::from_arms(vec![
            (FieldKey::Name(V_FIRED), value_extent()),
            (FieldKey::Name(V_IDLE), Extent::Base(BaseType::Unit)),
        ]));
        Extent::Record(HashMap::from([(
            F_WRITES.runtime_key(),
            Extent::Record(HashMap::from([(SmolStr::from(key), write)])),
        )]))
    }

    /// A decision value writing `write` to `key`, or nothing where `write` is `None`.
    fn decision_value(key: &str, write: Option<Value>) -> Value {
        let write = match write {
            Some(v) => Value::Union {
                tag: FieldKey::Name(V_FIRED),
                inner: Box::new(v),
            },
            None => Value::Union {
                tag: FieldKey::Name(V_IDLE),
                inner: Box::new(Value::Unit),
            },
        };
        Value::Record(HashMap::from([(
            F_WRITES.runtime_key(),
            Value::Record(HashMap::from([(SmolStr::from(key), write)])),
        )]))
    }

    /// A single-key decision body: over its `(read, item)` input (a driver's tile), writes
    /// `read + item` where `item > threshold`, and nothing elsewhere.
    ///
    /// Serves both drivers, because the body shape is the same on both sides: for
    /// induction it models `for i in xs: if guard(i): acc += i`, a position that writes
    /// nothing being a carry the accumulator holds through; for a transaction it is a
    /// drawdown of a negative item against the read snapshot, with `i64::MIN`
    /// making every attempt a grant so contention is the only thing under test.
    struct AddIfBody {
        input: Arc<dyn TileOperator>,
        tiling: Tiling,
        /// The accumulator this body writes. The write set is keyed by the
        /// variable written, so a fixture has to name its key the same way the
        /// writer that consumes the decision does.
        key: String,
        /// The guard threshold: a write iff `item > threshold` (`i64::MIN` ⇒ an
        /// unconditional loop, a write everywhere).
        threshold: i64,
    }

    impl AddIfBody {
        fn new(input: Arc<dyn TileOperator>, threshold: i64, key: &str) -> Self {
            // The decision record, one column of records.
            let tiling = Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(decision_extent(key)),
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
            self: Arc<Self>,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            let input = self.input.clone().clone().subscribe(
                self.input.tiling().universal_guard(),
                consumer,
                cx,
            );
            Box::new(AddIfBodyProducer {
                key: self.key.clone(),
                base: ProducerBase::unowned(AddIfBodyProducer::alloc_id(), &self.tiling),
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
        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }
        fn visit_input_producers_mut(
            &mut self,
            visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
        ) {
            visit("input", &mut *self.input);
        }

        impl_producer_base!();
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
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
            let Tile::Record { fields, .. } = *codomain else {
                panic!("AddIfBody input codomain is a Record {{_0: prev, _1: item}}");
            };
            let prev = record_field(&fields, &tuple_field(0));
            let item = record_field(&fields, &tuple_field(1));
            // Per row: `item > threshold` → a write of `prev + item`, else nothing (a carry).
            let mut rows = Vec::with_capacity(domain.len());
            for j in 0..domain.len() {
                let (Value::Int(p), Value::Int(i)) = (prev.index_at(j), item.index_at(j)) else {
                    panic!("AddIfBody prev/item are Ints");
                };
                rows.push(decision_value(
                    &self.key,
                    (i > self.threshold).then(|| int(p + i)),
                ));
            }
            Tile::data_function(
                domain,
                Box::new(Tile::Scalar(ColumnValue::from_values(
                    rows,
                    &decision_extent(&self.key),
                ))),
                // A per-position decision map: the decision stream is final
                // exactly when its input is, as a compiled body's operator chain
                // propagates it. The store reads this to close its frontier.
                domain_predicate,
                BitSet::new(),
            )
        }

        fn release_impl(&self, obsolete_guard: TileGuard) {
            // Forward the store's decision release to the driver, which compacts
            // its emitted window and releases the loop source in turn.
            self.input.release(obsolete_guard);
        }
    }

    /// Wire a single-accumulator induction cycle: store → body → driver → cyclic
    /// fan → store. Returns the fan (its slots are the store's readers) and
    /// the accumulator key.
    fn induction_cycle(items: &[i64], threshold: i64, init: i64) -> (DispatchedStore, Value) {
        let condition = if threshold == i64::MIN {
            "1 == 1".to_string()
        } else {
            format!("i > {threshold}")
        };
        let source = indoc::formatdoc! {r#"
            out = test_sink()
            acc := {init}
            for i in {items:?}:
                if {condition}:
                    acc += i
            out << acc
        "#};
        (DispatchedStore::new(&source), acct("acc"))
    }

    fn snapshot_after_run(
        fixture: &mut DispatchedStore,
        producer: &mut Box<dyn TileProducer>,
    ) -> Tile {
        fixture.run();
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(tile.is_terminal(), "the dispatched fixture finishes");
        tile
    }

    /// Convergence bound for the test cycles here — far above any test's
    /// iteration count, so exceeding it means the cycle stalled.
    const MAX_CYCLE_PULLS: usize = 64;

    /// Drive an `InductionStore` for a single-accumulator loop end-to-end through
    /// the tile protocol and return the converged store tile.
    fn drive_induction(items: &[i64], threshold: i64, init: i64) -> Tile {
        let (mut fan, _acc) = induction_cycle(items, threshold, init);
        let op = fan.slot();
        let guard = op.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = op.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        snapshot_after_run(&mut fan, &mut producer)
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
            tile.store_change_positions(),
            vec![pos(2), pos(3)],
            "the two firing positions (items 3, 4); the rest carry, and the init is the \
             store's seed rather than a change"
        );
    }

    /// A plain (unconditional) `mut` loop writes at every position: `acc := 10; for i in [1,2,3]:
    /// acc += i` → 16, a dense changelog.
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
            tile.store_change_positions(),
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
        let (mut fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 10); // unconditional
        let op = fan.slot();
        let guard = op.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = op.clone().subscribe(guard, Box::new(|| {}), &mut cx);

        let full = snapshot_after_run(&mut fan, &mut producer);
        assert_eq!(
            full.store_change_positions().len(),
            3,
            "full dense changelog: one write per position"
        );

        let store = fan.store().expect("the fixture subscribed its store");
        let before = store.read().state_info().values;
        // A reader consumed loop positions ≤ 1.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(1)),
        )));

        let bounded = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(validate_tile(&bounded));
        assert_eq!(
            store_current(&bounded, &acc).map(|(_, v)| v),
            Some(int(16)),
            "the accumulator still reads its correct final value after GC"
        );
        assert_eq!(
            store.read().state_info().values,
            3,
            "the engine retains its seed, final change and final decided position"
        );
        assert!(
            store.read().state_info().values < before,
            "release reclaims engine state without a stepping read"
        );
    }

    /// Build an `InductionStore` behind a fan and read `acc` densely over the loop
    /// extent via `StoreDenseRead`; return the dense `Fun(D, V)` values in order.
    fn dense_read(items: &[i64], threshold: i64, init: i64) -> Vec<i64> {
        let (mut fan, acc) = induction_cycle(items, threshold, init);
        let reader = Arc::new(StoreDenseRead::new(fan.slot(), acc, value_extent(), true));
        let guard = reader.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = reader.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        // The cycle advances one position per pull, so the dense read converges
        // over several pulls rather than one.
        let tile = snapshot_after_run(&mut fan, &mut producer);
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
    /// the per-tick oracle at every query tick ([`store_value_at`] for a carry,
    /// [`store_delta_at`] for a tap) — the invariant the O(N) rewrite of both changelog readers
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
        let queries: Vec<u64> = (0..=4).collect();
        for carry in [true, false] {
            let batched =
                fold_changelog_key_ascending(&store, queries.iter().copied().map(pos), &acc, carry);
            let per_tick: Vec<Option<Value>> = queries
                .iter()
                .map(|t| {
                    if carry {
                        store_value_at(&store, &pos(*t), &acc)
                    } else {
                        store_delta_at(&store, &pos(*t), &acc)
                    }
                })
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
        let (mut fan, acc) = induction_cycle(&[5, 1, 1, 9], 3, 0);
        let reader = Arc::new(StoreDenseRead::new(fan.slot(), acc, value_extent(), true));
        let guard = reader.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = reader.clone().subscribe(guard, Box::new(|| {}), &mut cx);

        fan.run();
        let read_values = |p: &mut Box<dyn TileProducer>| -> Vec<(u64, i64)> {
            // The cycle advances one position per pull, so the first full read
            // converges over several pulls; a later re-read is already terminal
            // and returns immediately.
            let tile = p.read_in_pipeline(p.tiling().universal_guard());
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
        for (p, v) in [(1u64, 5i64), (2, 5), (3, 14)] {
            assert!(
                after.contains(&(p, v)),
                "position {p} must still read {v} after releasing position 0; got {after:?}"
            );
        }
    }

    /// Records the domain-release watermarks a producer receives — lets a test
    /// observe what `StoreDenseRead` forwards to the store *without* a second
    /// FanOut slot (which would perturb GC via the release intersection).
    /// A guard naming a row whole takes that row's store out of the tree, and leaves a
    /// row it names only part of alone. This is what keeps the render and the engines
    /// saying the same thing: the render walks the tree, so a row dropped here is a row
    /// the next render cannot rebuild.
    #[test]
    fn remove_covered_drops_the_rows_the_guard_names_whole() {
        let mut engines = Engines::Rows(Vec::new());
        let mut seed = || CommitEngine::new(balances(&[("n", 0)]));
        for row in 0..3u64 {
            engines.store_at(&[Value::UInt(row)], &mut seed);
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
        let (mut fan, acc) = induction_cycle(&[5, 1, 1, 9], 3, 0);
        let reader = Arc::new(StoreDenseRead::new(fan.slot(), acc, value_extent(), true));
        let guard = reader.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = reader.clone().subscribe(guard, Box::new(|| {}), &mut cx);

        // The cycle advances one position per pull, so drive the fold to convergence.
        let tile = snapshot_after_run(&mut fan, &mut producer);
        assert_eq!(dense_values(&tile), vec![5, 5, 5, 14]);

        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(0)),
        )));
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert_eq!(
            dense_values(&tile),
            vec![5, 5, 14],
            "positions 1 and 2 carry the write at the released position 0"
        );

        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(2)),
        )));
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
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

    /// A transaction that writes nothing, a deny or a read-only grant, takes a tick like any
    /// other: the tick is decided and every key's value carries across it.
    #[test]
    fn an_empty_write_set_takes_a_tick() {
        let mut e = CommitEngine::new(balances(&[("alice", 100)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: HashMap::new(),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        assert_eq!(e.decided_watermark(), Some(&pos(1)));
        assert_eq!(e.read_as_of(&pos(1), &acct("alice")), Some(int(100)));
    }

    /// A deny read what it decided on, so a commit to that key after its snapshot makes it
    /// stale, and it retries as a grant does: at the moved frontier it may decide otherwise.
    #[test]
    fn a_deny_whose_read_moved_is_stale() {
        let mut e = CommitEngine::new(balances(&[("alice", 100)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 30)]),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        assert_eq!(
            e.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("alice", 100)]),
                writes: HashMap::new(),
            }),
            CommitOutcome::Stale
        );
        assert_eq!(e.decided_watermark(), Some(&pos(1)));
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
        for i in 1..=3i64 {
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
                CommitOutcome::Committed { ts: pos(i as u64) }
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
    /// of allocate-on-validate, where the tick sequence has no gaps because nothing
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
        let key = |i: usize| store_key(&Label::new(format!("k{i}")));
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

    /// The full multi-key store renders as `Position ⇀ {key: value}`: one
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
        store_seed_value(tile, &store_key(&Label::new(key)))
    }

    /// A store key's changelog as `(tick, value)` pairs.
    fn changelog_of(tile: &Tile, key: &str) -> Vec<(u64, Value)> {
        let (ticks, values) = tile.store_changelog(key).expect("a key of this store");
        (0..ticks.len())
            .map(|i| match ticks.index_at(i) {
                Value::UInt(t) => (t, changelog_value(values, i)),
                other => panic!("a change tick is a UInt; got {other:?}"),
            })
            .collect()
    }

    // --- The engine as a live tile operator ---------------------------------

    /// Balances are ints; they type a proposal's read and write sets, which ride one cell per
    /// attempt.
    fn value_extent() -> Extent {
        Extent::Base(BaseType::Int)
    }

    /// A store's per-key value tilings over `accounts`: one key each, holding a balance.
    fn store_values(accounts: &[&str]) -> HashMap<SmolStr, Tiling> {
        accounts
            .iter()
            .map(|a| ((*a).into(), Tiling::Scalar(value_extent())))
            .collect()
    }

    /// The whole store tiling over `accounts`, which a render needs to name its keys.
    fn store_tiling(accounts: &[&str]) -> Tiling {
        full_store_tiling(commit_clock_domain(), store_values(accounts))
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
                let key = store_key(&Label::from_runtime_key(name));
                Some((key.clone(), store_seed_value(tile, &key)?))
            })
            .collect();
        let entries = std::iter::once((commit_clock_start(), seed))
            .chain(tile.store_change_positions().into_iter().map(|tick| {
                let delta = tile
                    .store_keys()
                    .filter_map(|name| {
                        let key = store_key(&Label::from_runtime_key(name));
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

    /// The conflict scenario, run through a dispatched store: the store consumes the writer's
    /// map-encoded proposals into the engine and publishes the full store tile.
    #[test]
    fn live_producer_conflict() {
        let tile = DispatchedStore::new(indoc::indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for cost in [70]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            for cost in [50]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            out << await_final(pool)
        "#})
        .snapshot();
        assert!(validate_tile(&tile));
        assert!(tile.is_terminal());
        let (frontier, value) = store_at(&tile, &acct("pool")).expect("pool is decided");
        assert_eq!(frontier, pos(2), "the grant and deny each take a tick");
        assert!(
            [30, 50].contains(&value),
            "the stale draw retries and denies"
        );
    }

    /// Sequential (non-conflicting) writers drive a dense store through the operator.
    #[test]
    fn live_producer_sequential() {
        let tile = DispatchedStore::new(indoc::indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for value in [30, 20]:
                with begin():
                    pool := value
            out << await_final(pool)
        "#})
        .snapshot();
        assert!(validate_tile(&tile));
        assert!(tile.is_terminal());
        assert_eq!(seed_of(&tile, "pool"), Some(int(100)));
        assert_eq!(
            changelog_of(&tile, "pool"),
            vec![(1, int(30)), (2, int(20))]
        );
        assert_eq!(store_at(&tile, &acct("pool")), Some((pos(2), 20)));
    }

    // --- The body↔store cycle -----------------------------------------------

    /// A test writer body that models a single-writer counter loop on one store
    /// `key`: each pull it folds the store to read `key`'s value and proposes
    /// `value + 1`, reporting the frontier it observed as its snapshot. Appends
    /// one proposal per pull, up to `n` steps. It reads the store through its
    /// `store_op` input — which, in the cycle, is a slot of the commit
    /// operator's own output.
    /// A single writer reads the store and proposes increments through the
    /// commit operator, reading its own committed output back via a cyclic
    /// `FanOut`. Each pull advances the cycle one step (the first pull
    /// bootstraps: the body sees the empty cached store and proposes nothing).
    #[test]
    fn single_writer_cycle() {
        let latest = DispatchedStore::new(indoc::indoc! {r#"
            out = test_sink()
            n: Mut(Int, Txn) := 0
            for i in [1, 2, 3]:
                with begin():
                    n := n + 1
            out << await_final(n)
        "#})
        .snapshot();
        assert_eq!(store_at(&latest, &acct("n")), Some((pos(3), 3)));
    }

    /// A resumed drive skips the source prefix settled before the reload boundary.
    #[test]
    fn a_resumed_drive_starts_after_its_settled_prefix() {
        let tiling = store_tiling(&["pool"]);
        let mut store =
            CommitEngine::new(balances(&[("pool", 100)])).render_full_store_tile(&tiling);
        if let Tile::Store { writer_takes, .. } = &mut store {
            *writer_takes = vec![WriterTakes {
                settled: Predicate::False,
                again: Vec::new(),
            }];
        }
        let drive = Arc::new(TransactDriver::new(
            Arc::new(ItemSource {
                tiling,
                tile: store,
            }),
            Arc::new(ItemSource::new(&[1, 2])),
            vec![acct("pool")],
            vec![value_extent()],
            value_extent(),
            Some(Position::new(Value::UInt(0))),
            0,
        ));
        let mut cx = SubscribeContext::new();
        let guard = drive.tiling().universal_guard();
        let mut producer = drive
            .clone()
            .subscribe(guard.clone(), Box::new(|| {}), &mut cx);
        producer.visit_input_producers_mut(&mut |_, input| {
            let breaker = input
                .as_breaking_mut()
                .expect("the canonical transaction driver");
            let whole = breaker.input_tiling(InputId::ONLY).universal_guard();
            breaker.consume_in_pipeline(InputId::ONLY, whole);
        });
        let rows = producer.read_in_pipeline(guard);
        assert_eq!(item_position_at(&rows, &pos(0)), Value::UInt(1));
    }

    /// Six writers each draw 1 from a pool of 100, each reading and writing the one key `pool`.
    /// Every draw commits exactly once: the pool ends at 94. A lone driver's window under
    /// repeated retries is `a_repeatedly_retried_item_keeps_the_drive_window_flat`.
    #[test]
    fn contending_writers_each_commit_their_draw_once() {
        use crate::ccl::{
            context::{GlobalContext, compile_program},
            load::LoadedProgram,
        };
        let source = indoc::indoc! {"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1]:
                with begin():
                    pool := pool - r
            for r in [1]:
                with begin():
                    pool := pool - r
            for r in [1]:
                with begin():
                    pool := pool - r
            for r in [1]:
                with begin():
                    pool := pool - r
            for r in [1]:
                with begin():
                    pool := pool - r
            for r in [1]:
                with begin():
                    pool := pool - r
            out << await_final(pool)
        "};
        let mut ctx = GlobalContext::default();
        let sink = ctx.register_test_sink("out");
        let mut program =
            compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        crate::interpreter::dispatcher::run_program(&mut program, 1)
            .expect("contending writers dispatch");
        let Ok(Value::Function(bindings)) = sink.value() else {
            panic!("a completed pool: {:?}", sink.value())
        };
        let [binding] = &bindings[..] else {
            panic!("the sink holds one value: {bindings:?}")
        };
        assert_eq!(binding.output, Value::Int(94), "{source}");
    }

    #[test]
    fn a_repeatedly_retried_item_keeps_the_drive_window_flat() {
        use crate::interpreter::tile_operators::test_helpers::NotifyingOp;
        let tiling = store_tiling(&["pool"]);
        let mut engine = CommitEngine::new(balances(&[("pool", 100)]));
        let (store, _, snapshot, _) =
            NotifyingOp::scripted(engine.render_full_store_tile(&tiling), tiling.clone());
        let driver = Arc::new(TransactDriver::new(
            Arc::new(store),
            Arc::new(ItemSource::new(&[-1])),
            vec![acct("pool")],
            vec![value_extent()],
            value_extent(),
            None,
            0,
        ));
        let mut driver = driver.clone().subscribe(
            driver.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        for retry in 0..=8u64 {
            if retry > 0 {
                assert!(matches!(
                    engine.attempt(Proposal {
                        snapshot: pos(retry - 1),
                        reads: balances(&[("pool", 101 - retry as i64)]),
                        writes: balances(&[("pool", 100 - retry as i64)])
                    }),
                    CommitOutcome::Committed { .. }
                ));
            }
            let mut tile = engine.render_full_store_tile(&tiling);
            if let Tile::Store { writer_takes, .. } = &mut tile {
                *writer_takes = vec![WriterTakes {
                    settled: Predicate::False,
                    again: if retry == 0 { vec![] } else { vec![pos(0)] },
                }];
            }
            *snapshot
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner) = tile;
            driver.visit_input_producers_mut(&mut |_, producer| {
                let breaker = producer
                    .as_breaking_mut()
                    .expect("the canonical transaction driver");
                let whole = breaker.input_tiling(InputId::ONLY).universal_guard();
                breaker.consume_in_pipeline(InputId::ONLY, whole);
            });
            let rows = driver.read_in_pipeline(driver.tiling().universal_guard());
            let Tile::DataFunction { domain, .. } = &rows else {
                panic!("attempt rows")
            };
            assert!(domain.len() <= MAX_LIVE_ATTEMPTS, "retry {retry}: {rows:?}");
            assert_eq!(newest_body_position(&rows), Some(pos(retry)));
            driver.release(TileGuard::Function(FunctionGuard::Domain(
                Predicate::at_or_below(Value::UInt(retry)),
            )));
        }
    }

    #[test]
    fn current_values_allow_history_reclamation_after_a_lagging_reader_releases() {
        use crate::ccl::{BaseType as CclBase, Type};
        use crate::interpreter::TestDataSource;
        let source = TestDataSource::new("source1", Type::Base(CclBase::Int), value_extent());
        let mut fixture = DispatchedStore::with(
            indoc::indoc! {r#"
            out = test_sink()
            acc := 0
            for i in source1():
                acc += i
            out << acc
        "#},
            |ctx| ctx.register_source(source.clone()),
        );
        let history = fixture.slot();
        let mut history = history.clone().subscribe(
            history.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .add_data(&[
                (Value::UInt(0), int(1)),
                (Value::UInt(1), int(2)),
                (Value::UInt(2), int(3)),
            ]);
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(2)));
        fixture.poll();
        let tile = history.read_in_pipeline(history.tiling().universal_guard());
        assert_eq!(
            tile.store_change_positions().len(),
            3,
            "the historical reader retains every change"
        );
        let store = fixture.store().unwrap();
        let before = store.read().state_info().values;
        history.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(1)),
        )));
        assert!(
            store.read().state_info().values < before,
            "a history reader's release permits reclamation"
        );
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_yield_predicate(Predicate::True);
        fixture.run();
        assert_eq!(
            store_value_now(
                &history.read_in_pipeline(history.tiling().universal_guard()),
                &acct("acc")
            ),
            Some(int(6))
        );
    }

    #[rstest]
    #[case(indoc::indoc! {r#"
        out = test_sink()
        acc := 0
        for i in [1, 2, 3]:
            acc += i
        out << acc
    "#})]
    #[case(indoc::indoc! {r#"
        out = test_sink()
        acc: Mut(Int, Txn) := 0
        for i in [1, 2, 3]:
            with begin():
                acc += i
        out << await_final(acc)
    "#})]
    fn store_reads_do_not_advance_execution(#[case] source: &str) {
        let mut fixture = DispatchedStore::new(source);
        let reader = fixture.slot();
        let reader = reader.clone().subscribe(
            reader.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        for _ in 0..3 {
            assert!(store_frontier(&reader.get(reader.tiling().universal_guard())).is_none());
        }
        fixture.run();
        for _ in 0..3 {
            let tile = reader.get(reader.tiling().universal_guard());
            assert!(tile.is_terminal());
            assert_eq!(store_value_now(&tile, &acct("acc")), Some(int(6)));
        }
    }

    /// Two concurrent writers draw from a shared pool of 100: A wants 70, B wants
    /// 50. They read the same snapshot and both propose grants; the operator
    /// commits A and finds B stale (no tick). B retries, now sees pool = 30 < 50,
    /// and proposes a deny, which takes the second tick. The pool never goes negative: it
    /// ends at 30.
    #[test]
    fn token_pool_two_writers() {
        let latest = DispatchedStore::new(indoc::indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for cost in [70]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            for cost in [50]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            out << await_final(pool)
        "#})
        .snapshot();
        assert!(latest.is_terminal());
        let (frontier, pool) = store_at(&latest, &acct("pool")).expect("pool decided");
        assert_eq!(frontier, pos(2), "a grant and a deny, a tick each");
        assert!(
            (0..=100).contains(&pool),
            "the token pool cannot be oversold"
        );
        assert!([30, 50].contains(&pool));
    }

    /// A stale deny retries against the advanced snapshot and can then grant.
    #[test]
    fn a_stale_deny_retries_and_grants() {
        let mut engine = CommitEngine::new(balances(&[("pool", 20)]));
        assert_eq!(
            engine.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("pool", 20)]),
                writes: balances(&[("pool", 80)]),
            }),
            CommitOutcome::Committed { ts: pos(1) }
        );
        assert_eq!(
            engine.attempt(Proposal {
                snapshot: pos(0),
                reads: balances(&[("pool", 20)]),
                writes: HashMap::new(),
            }),
            CommitOutcome::Stale
        );
        assert_eq!(
            engine.attempt(Proposal {
                snapshot: pos(1),
                reads: balances(&[("pool", 80)]),
                writes: balances(&[("pool", 30)]),
            }),
            CommitOutcome::Committed { ts: pos(2) }
        );
        assert_eq!(engine.decided_watermark(), Some(&pos(2)));
        assert_eq!(engine.read_as_of(&pos(2), &acct("pool")), Some(int(30)));
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
        let latest = DispatchedStore::new(indoc::indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for cost in [70, 40]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            for cost in [50, 30]:
                with begin():
                    if pool >= cost:
                        pool := pool - cost
            out << await_final(pool)
        "#})
        .snapshot();
        assert!(latest.is_terminal());
        let (frontier, pool) = store_at(&latest, &acct("pool")).expect("pool decided");
        assert!(
            (0..=100).contains(&pool),
            "the token pool cannot be oversold"
        );
        assert_eq!(
            frontier,
            pos(4),
            "every request takes a tick, grant or deny"
        );
    }

    // --- Prefix-reactive read (`read as of t`) ------------------------------

    /// A reader that resolves to `key`'s value as of `t` once the watermark
    /// covers `t`, and is empty (non-terminal) until then. Folding `state_as_of`
    /// at `t` walks past ticks that wrote *other* keys (decided-absent for this
    /// key) — the multi-key store is where that fold does real work. Reads the
    /// store through a slot of the commit operator's output; pulling it also
    /// drives the cycle.
    struct StoreReadAsOf {
        tiling: Tiling,
        store_op: Arc<dyn TileOperator>,
        key: Value,
        t: u64,
    }

    impl StoreReadAsOf {
        fn new(store_op: Arc<dyn TileOperator>, key: Value, t: u64) -> Self {
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
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            let store_guard = self.store_op.tiling().universal_guard();
            let store_producer =
                self.store_op
                    .clone()
                    .clone()
                    .subscribe(store_guard, Box::new(|| {}), cx);
            Box::new(StoreReadAsOfProducer {
                base: ProducerBase::unowned(StoreReadAsOfProducer::alloc_id(), &self.tiling),
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
        t: u64,
    }

    impl TileProducer for StoreReadAsOfProducer {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
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
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// A read as of timestamp 2 against a counter that climbs to 3: it stays
    /// empty until the watermark reaches 2, then resolves to the value at tick 2
    /// without waiting for the writer to finish.
    #[test]
    fn read_as_of_resolves_at_watermark() {
        use crate::interpreter::TestDataSource;
        let source = TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        let mut fixture = DispatchedStore::with(
            indoc::indoc! {r#"
            out = test_sink()
            n: Mut(Int, Txn) := 0
            for x in source1():
                with begin():
                    n := n + 1
            out << await_final(n)
        "#},
            |ctx| ctx.register_source(source.clone()),
        );
        let reader = Arc::new(StoreReadAsOf::new(fixture.slot(), acct("n"), 2));
        let mut producer = reader.clone().subscribe(
            reader.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        assert!(
            producer
                .read_in_pipeline(producer.tiling().universal_guard())
                .is_empty()
        );
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .add_data(&[(Value::UInt(0), int(1)), (Value::UInt(1), int(2))]);
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(1)));
        fixture.poll();
        let latest = producer.read_in_pipeline(producer.tiling().universal_guard());
        let Tile::Scalar(cv) = latest else {
            panic!("a scalar as-of read")
        };
        assert_eq!(cv.as_single(), Some(int(2)));
        assert!(
            !fixture.fan.cached_tile().unwrap().is_terminal(),
            "the writer remains live"
        );
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
    fn run_bank_transactions(
        init: HashMap<Value, Value>,
        a: Vec<(Value, Value, i64)>,
        b: Vec<(Value, Value, i64)>,
    ) -> HashMap<SmolStr, i64> {
        use crate::ccl::{
            context::{GlobalContext, compile_program},
            load::LoadedProgram,
        };
        let mut source = indoc::indoc! {r#"
            out = test_sink()
        "#}
        .to_string();
        let mut accounts: Vec<_> = init.iter().collect();
        accounts.sort_by_key(|(key, _)| key.to_string());
        for (key, value) in &accounts {
            let name = store_key_name(key).expect("a named account");
            source.push_str(&indoc::formatdoc! {r#"
                {name}: Mut(Int, Txn) := {value}
            "#});
        }
        for (writer, transfers) in [a, b].into_iter().enumerate() {
            let [(from, to, amount)] = transfers.as_slice() else {
                panic!("one transfer per writer")
            };
            let from = store_key_name(from).unwrap();
            let to = store_key_name(to).unwrap();
            source.push_str(&indoc::formatdoc! {r#"
                for amount{writer} in [{amount}]:
                    with begin():
                        {from} := {from} - amount{writer}
                        {to} := {to} + amount{writer}
            "#});
        }
        let fields = accounts
            .iter()
            .map(|(key, _)| {
                let name = store_key_name(key).unwrap();
                format!("{name}=await_final({name})")
            })
            .collect::<Vec<_>>()
            .join(", ");
        source.push_str(&indoc::formatdoc! {r#"
            out << ({fields})
        "#});
        let mut ctx = GlobalContext::default();
        let sink = ctx.register_test_sink("out");
        let mut program =
            compile_program(&mut ctx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
        crate::interpreter::dispatcher::run_program(&mut program, 1)
            .expect("bank transactions dispatch");
        let Value::Function(bindings) = sink.value().expect("a completed bank snapshot") else {
            panic!("the sink is keyed")
        };
        assert_eq!(bindings.len(), 1);
        let Value::Record(fields) = &bindings[0].output else {
            panic!("all accounts form a record")
        };
        fields
            .iter()
            .map(|(name, value)| {
                let Value::Int(value) = value else {
                    panic!("an account holds an integer")
                };
                (name.clone(), *value)
            })
            .collect()
    }

    /// Both disjoint multi-key transfers commit and conserve the balance.
    #[test]
    fn bank_transfer_disjoint_commit() {
        let accounts = run_bank_transactions(
            balances(&[("alice", 100), ("bob", 100), ("carol", 100), ("dave", 100)]),
            vec![(acct("alice"), acct("bob"), 30)],
            vec![(acct("carol"), acct("dave"), 40)],
        );
        assert_eq!(accounts["alice"], 70);
        assert_eq!(accounts["bob"], 130);
        assert_eq!(accounts["carol"], 60);
        assert_eq!(accounts["dave"], 140);
        assert_eq!(accounts.values().sum::<i64>(), 400);
    }

    /// Overlapping transfers retry against the committed balance and conserve it.
    #[test]
    fn bank_transfer_overlap_conflict_and_retry() {
        let accounts = run_bank_transactions(
            balances(&[("alice", 100), ("bob", 100), ("carol", 100)]),
            vec![(acct("alice"), acct("bob"), 30)],
            vec![(acct("alice"), acct("carol"), 50)],
        );
        assert_eq!(accounts["alice"], 20);
        assert_eq!(accounts["bob"], 130);
        assert_eq!(accounts["carol"], 150);
        assert_eq!(accounts.values().sum::<i64>(), 300);
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
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(FixedSourceProducer {
                base: ProducerBase::unowned(FixedSourceProducer::alloc_id(), &self.tiling),
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
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            honoring_release(&self.tile, &self.obsolete_guard())
        }
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// `StoreValueStream` projects the store's history to `key`'s commit-value
    /// stream (`Txn ⇀ Value`), observable as it commits — no terminal gate — with
    /// terminality flowing through from the store. This checks the projection
    /// (both values visible while still committing) and that `ExtractFinal`
    /// composes over it once terminal — the mechanism a surface `await_final` read
    /// compiles to, exercised here at the operator level.
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
        let stream = Arc::new(StoreValueStream::new(
            Arc::new(FixedSource {
                tiling: store_tiling.clone(),
                tile: store_tile.clone(),
            }),
            acc.clone(),
            value_ext.clone(),
            true, // carry: hold the committed value forward
        ));
        let g = stream.tiling().universal_guard();
        let mut p =
            stream
                .clone()
                .clone()
                .subscribe(g, Box::new(|| {}), &mut SubscribeContext::new());
        let t = p.read_in_pipeline(p.tiling().universal_guard());
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
            Arc::new(FixedSource {
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
        let extract = Arc::new(crate::interpreter::tile_operators::ExtractFinal::new(
            Arc::new(stream),
            Arc::new(*default),
        ));
        let g = extract.tiling().universal_guard();
        let mut p = extract
            .clone()
            .subscribe(g, Box::new(|| {}), &mut SubscribeContext::new());
        let t = consume_and_read(&mut p);
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

    /// A collection-valued final read keeps projected completeness bounded and released keys absent.
    #[test]
    fn a_final_collection_read_projects_and_releases_its_keys() {
        let value_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let value = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10, 20, 30]))),
            Predicate::True,
            BitSet::new(),
        );
        let value_extent = value_tiling.extent();
        let key = acct("xs");
        let engine = CommitEngine::new(HashMap::from([(
            key.clone(),
            seed_value(&value).unwrap_or_else(|_| panic!("a closed collection is a value")),
        )]));
        let store_tiling = full_store_tiling(
            commit_clock_domain(),
            HashMap::from([("xs".into(), Tiling::Scalar(value_extent.clone()))]),
        );
        let mut tile = engine.render_full_store_tile(&store_tiling);
        let Tile::Store { terminal, .. } = &mut tile else {
            unreachable!()
        };
        *terminal = true;
        let read = Arc::new(StoreFinalRead::new(
            Arc::new(FixedSource {
                tiling: store_tiling,
                tile,
            }),
            key,
            value_extent,
        ));
        let mut cx = Default::default();
        let mut producer = read.clone().clone().subscribe(
            read.tiling().universal_guard(),
            Box::new(|| {}),
            &mut cx,
        );
        for key in [1, 2] {
            let projection = Projection::admitting(Predicate::point(Value::UInt(key)));
            let guard = projection.guard(producer.tiling());
            let mut expected = value.clone();
            expected.restrict_to(&projection, producer.tiling());
            assert_eq!(producer.read_in_pipeline(guard.clone()), expected);
            producer.release(guard.clone());
            assert!(producer.read_in_pipeline(guard).is_empty());
        }
    }

    /// A settled read reclaims the history below the frontier of the store it read, on the
    /// release its consumer delivers after the read.
    ///
    /// It reads the key's value as the store stands, so it needs the latest write and
    /// nothing before it. The store's release watermark is the `FanOut` intersection over
    /// its readers, so a reader that holds its slot until it retires keeps every version
    /// of every key for the length of the run — measured at 180 retained entries over a
    /// 90-position loop against 4 with this release.
    #[test]
    fn a_settled_read_releases_the_history_below_the_frontier() {
        let mut cx = SubscribeContext::new();
        let live = store_tile(
            &["alice"],
            &[("alice", 100)],
            &[(1, &[("alice", 70)]), (2, &[("alice", 40)])],
            Predicate::at_or_below(Value::UInt(2)),
        );
        let recorder = Arc::new(RwLock::new(Vec::new()));
        let read = Arc::new(StoreFinalRead::new(
            Arc::new(RecordingSource {
                tiling: store_tiling(&["alice"]),
                tile: live,
                released: recorder.clone(),
            }),
            acct("alice"),
            value_extent(),
        ));
        let g = read.tiling().universal_guard();
        let mut producer = read.clone().subscribe(g, Box::new(|| {}), &mut cx);
        let read = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(
            recorder
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_empty(),
            "the read holds the history until its consumer releases"
        );
        producer.release(read.to_guard());
        assert_eq!(
            recorder
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .as_slice(),
            [TileGuard::Function(FunctionGuard::Domain(
                Predicate::at_or_below(Value::UInt(2))
            ))],
            "the release after the read releases through the frontier the read folded at"
        );
    }

    /// A [`FixedSource`] that records what its consumer released.
    struct RecordingSource {
        tiling: Tiling,
        tile: Tile,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }
    struct RecordingProducer {
        base: ProducerBase,
        tile: Tile,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }
    impl TileOperator for RecordingSource {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(RecordingProducer {
                base: ProducerBase::unowned(RecordingProducer::alloc_id(), &self.tiling),
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
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }
        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .push(obsolete_guard);
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

        fn field<T>(t: T) -> HashMap<SmolStr, T> {
            HashMap::from([("units".into(), t)])
        }
        // A column of record values, and a record of columns over the fields.
        let units = ColumnValue::from_ints(vec![2, 1]);
        let boxed = seed(Tile::Scalar(ColumnValue::Records(field(units.clone()))));
        let struct_of_arrays = seed(Tile::record(field(Tile::Scalar(units))));

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
        let expected = vec![("btc".into(), 2), ("eth".into(), 1)];
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
        entries: &[(u64, &[(&str, i64)])],
        frontier: Predicate,
    ) -> Tile {
        let mut written: HashMap<&str, Vec<(u64, i64)>> =
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
                    // As `CommitEngine` renders one: complete where the store has decided.
                    frontier.clone(),
                    BitSet::new(),
                );
                (account.into(), tile)
            })
            .collect();
        let seed_record = accounts
            .iter()
            .map(|a| {
                let column = match seed.iter().find(|(k, _)| k == a) {
                    Some((_, v)) => ColumnValue::from_ints(vec![*v]),
                    None => ColumnValue::from_ints(vec![]),
                };
                ((*a).into(), Tile::Scalar(column))
            })
            .collect();
        let tile = Tile::Store {
            state: Box::new(Tile::record(state)),
            seed: Box::new(Tile::record(seed_record)),
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
            writer_takes: Vec::new(),
        };
        assert!(validate_tile(&tile), "store_tile built an invalid tile");
        tile
    }

    /// A three-tick store: the seed holds both accounts, tick 1 writes only
    /// `alice`, tick 2 writes only `bob`. Completion through the watermark `w`.
    fn skew_store(w: u64) -> Tile {
        store_tile(
            &["alice", "bob"],
            &[("alice", 100), ("bob", 50)],
            &[(1, &[("alice", 70)]), (2, &[("bob", 40)])],
            Predicate::at_or_below(Value::UInt(w)),
        )
    }

    /// A flat induction store over untagged positions pushes its positions as it decides them; a
    /// store with rows above its positions, and one over a concatenation's tagged positions at
    /// the top or inside a record, holds nothing short of terminal.
    #[test]
    fn only_a_flat_store_over_untagged_positions_pushes_what_it_decides() {
        let store = |domain: Extent| Tiling::Store {
            domain,
            codomain: Box::new(Tiling::Record(HashMap::new())),
        };
        let tagged = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::UInt),
            Extent::Base(BaseType::UInt),
        ]));
        let record = Extent::Record(
            [
                (SmolStr::new("_0"), Extent::Base(BaseType::UInt)),
                (SmolStr::new("_1"), tagged.clone()),
            ]
            .into_iter()
            .collect(),
        );
        assert!(pushes_complete_positions(&store(Extent::Base(
            BaseType::UInt
        ))));
        assert!(!pushes_complete_positions(&store(tagged)));
        assert!(!pushes_complete_positions(&store(record)));
        let nested = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            store(Extent::Base(BaseType::UInt)),
        );
        assert!(!pushes_complete_positions(&nested));
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
        assert_eq!(done.store_change_positions(), vec![pos(3)]);
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
    fn decode_source_positioned_skips_deleted_rows() {
        // A `Restrict` marks a row deleted and keeps its key, so the decode is what drops
        // it: the recurrence runs over the positions the source still has.
        let mut deleted = BitSet::new();
        deleted.insert(1);
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10, 20, 30]))),
            Predicate::True,
            deleted,
        );
        assert_eq!(
            decode_source_positioned(&tile),
            vec![
                (pos(0), Tile::Scalar(ColumnValue::from_ints(vec![10]))),
                (pos(2), Tile::Scalar(ColumnValue::from_ints(vec![30]))),
            ],
        );
    }

    #[test]
    fn decode_source_positioned_pairs_by_domain_and_sorts() {
        // An async source's domain arrives unordered (it enumerates a set of
        // arrived keys), and the codomain aligns to the domain *column*, not to
        // position. Decoding must pair each item with its actual domain position
        // and sort — otherwise the position-driven driver reads the wrong item at
        // each position.
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
        let log = |ticks: Vec<u64>, values: Vec<i64>| Tile::DataFunction {
            row_starts: vec![0],
            domain: ColumnValue::from_uints(ticks),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_ints(values))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
            keys_follow_beneath: false,
        };
        let store = |state: Tile| Tile::Store {
            state: Box::new(state),
            seed: Box::new(Tile::record(HashMap::new())),
            decided: Box::new(one_row_decided(ColumnValue::from_uints(vec![]))),
            frontier: Box::new(one_row_decided(ColumnValue::from_uints(vec![]))),
            terminal: false,
            closed_keys: Vec::new(),
            writer_takes: Vec::new(),
        };
        let one_key = |log: Tile| store(Tile::record(HashMap::from([("a".into(), log)])));
        // Non-ascending change ticks.
        assert!(!validate_tile(&one_key(log(vec![2, 1], vec![1, 2]))));
        // More values than ticks to hold them.
        assert!(!validate_tile(&one_key(log(vec![0], vec![1, 2]))));
        // A state that is not a record of changelogs.
        assert!(!validate_tile(&store(Tile::Scalar(
            ColumnValue::from_ints(vec![1])
        ))));
        // A position decided above the frontier, and one decided with no frontier at all.
        let decided_through = |decided: Vec<u64>, frontier: Vec<u64>| Tile::Store {
            state: Box::new(Tile::record(HashMap::new())),
            seed: Box::new(Tile::record(HashMap::new())),
            decided: Box::new(one_row_decided(ColumnValue::from_uints(decided))),
            frontier: Box::new(one_row_decided(ColumnValue::from_uints(frontier))),
            terminal: false,
            closed_keys: Vec::new(),
            writer_takes: Vec::new(),
        };
        assert!(validate_tile(&decided_through(vec![0, 1], vec![1])));
        assert!(!validate_tile(&decided_through(vec![0, 2], vec![1])));
        assert!(!validate_tile(&decided_through(vec![0], vec![])));
    }
    /// Two memo'd readers of one cyclic store both end at the final state, in whichever
    /// order they are pulled.
    ///
    /// Two memo readers of a dispatched cycle observe the same final snapshot regardless of
    /// which reader queries it first.
    #[rstest]
    #[case::laggard_first(true)]
    #[case::leader_first(false)]
    fn both_memo_readers_of_one_cycle_reach_the_final_state(#[case] laggard_first: bool) {
        let (mut fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 0); // unconditional
        let mut cx = SubscribeContext::new();
        let subscribe = |cx: &mut SubscribeContext| {
            let reader = StoreDenseRead::new(fan.slot(), acc.clone(), value_extent(), true);
            let memo = Arc::new(Memo::new(Arc::new(reader)));
            let guard = memo.tiling().universal_guard();
            memo.clone().subscribe(guard, Box::new(|| {}), cx)
        };
        let mut lagging = subscribe(&mut cx);
        let mut leading = subscribe(&mut cx);

        // Both readers pull each lap, in the order under test, until the one pulled
        // second closes the cycle.
        fan.run();
        let mut closing = consume_and_read(&mut leading);
        for _ in 0..MAX_CYCLE_PULLS {
            if closing.is_terminal() {
                break;
            }

            if laggard_first {
                let _ = consume_and_read(&mut lagging);
                closing = consume_and_read(&mut leading);
            } else {
                closing = consume_and_read(&mut leading);
                let _ = consume_and_read(&mut lagging);
            }
        }
        assert!(closing.is_terminal(), "the closing reader converged");

        // The sibling now gets only what the runtime would deliver — no further pull of
        // the other reader to drive the cycle on its behalf.
        let mut lagged = consume_and_read(&mut lagging);
        for _ in 0..MAX_CYCLE_PULLS {
            if lagged.is_terminal() {
                break;
            }

            lagged = consume_and_read(&mut lagging);
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
        let (mut fan, acc) = induction_cycle(&[1, 2, 3], i64::MIN, 0); // unconditional
        let reader = StoreDenseRead::new(fan.slot(), acc, value_extent(), true);
        let memo = Arc::new(Memo::new(Arc::new(reader)));
        let guard = memo.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = memo.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        fan.run();
        let tile = consume_and_read(&mut producer);
        assert!(tile.is_terminal(), "the dispatched fixture finishes");
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
        tile: Arc<RwLock<Tile>>,
    }
    struct SharedSourceProducer {
        base: ProducerBase,
        tile: Arc<RwLock<Tile>>,
    }
    impl TileOperator for SharedSource {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(SharedSourceProducer {
                base: ProducerBase::unowned(SharedSourceProducer::alloc_id(), &self.tiling),
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
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            honoring_release(
                &self
                    .tile
                    .read()
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
                &self.obsolete_guard(),
            )
        }
        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    fn position_path(components: &[u64]) -> Path {
        Path::from(
            components
                .iter()
                .map(|c| Value::UInt(*c))
                .collect::<Vec<_>>(),
        )
    }

    fn row_folded(folded: &Predicate, row: &[u64]) -> bool {
        folded.contains_path(&row.iter().map(|c| Value::UInt(*c)).collect::<Vec<_>>())
    }

    /// An emitted position the store has not decided keeps its row unfolded, and one the
    /// frontier has reached does not: with no frontier, or one before it, the position is
    /// undecided.
    #[test]
    fn an_emitted_position_is_undecided_until_the_frontier_reaches_it() {
        let emitted = position_path(&[0, 3]);
        for (frontier, undecided) in [
            (None, true),
            (Some(position_path(&[0, 2])), true),
            (Some(position_path(&[0, 3])), false),
            (Some(position_path(&[1, 0])), false),
        ] {
            let positions =
                undecided_positions(std::iter::empty(), Some(&emitted), frontier.as_ref());
            assert_eq!(
                positions.len(),
                usize::from(undecided),
                "frontier {frontier:?}"
            );
            assert_eq!(
                row_folded(&rows_folded_at(0, &positions), &[0]),
                !undecided,
                "frontier {frontier:?}"
            );
        }
    }

    /// A delivered path at or below the cursor is a position the drive already emitted that the
    /// source has not yet dropped, so it keeps no row unfolded.
    #[test]
    fn a_stale_delivered_path_at_or_below_the_cursor_is_not_undecided() {
        let emitted = position_path(&[0, 2]);
        let frontier = position_path(&[0, 2]);
        let delivered = [
            position_path(&[0, 1]),
            position_path(&[0, 2]),
            position_path(&[1, 0]),
        ];
        let positions = undecided_positions(delivered.iter(), Some(&emitted), Some(&frontier));
        assert_eq!(positions, [&position_path(&[1, 0])]);
        let folded = rows_folded_at(0, &positions);
        assert!(row_folded(&folded, &[0]) && !row_folded(&folded, &[1]));
    }

    /// A row with no position under it is folded, at every level, and with no position at
    /// all every row is.
    #[test]
    fn a_row_with_no_position_under_it_is_folded() {
        let delivered = [position_path(&[1, 4, 0])];
        let positions = undecided_positions(delivered.iter(), None, None);
        let level0 = rows_folded_at(0, &positions);
        assert!(row_folded(&level0, &[0]) && !row_folded(&level0, &[1]));
        let level1 = rows_folded_at(1, &positions);
        assert!(
            row_folded(&level1, &[1, 3]),
            "a sibling row at the level below"
        );
        assert!(
            row_folded(&level1, &[0, 4]),
            "the same key under another enclosing row"
        );
        assert!(!row_folded(&level1, &[1, 4]));
        let none = undecided_positions(std::iter::empty(), None, None);
        assert!(row_folded(&rows_folded_at(0, &none), &[7]));
        assert!(row_folded(&rows_folded_at(1, &none), &[7, 7]));
    }

    /// A source that delivered row 1 before row 0 leaves row 1 unfolded and has no say about
    /// row 0, which the source's own completeness decides.
    #[test]
    fn an_out_of_order_delivery_leaves_only_the_delivered_row_unfolded() {
        let delivered = [position_path(&[1, 0]), position_path(&[1, 1])];
        let positions = undecided_positions(delivered.iter(), None, None);
        let folded = rows_folded_at(0, &positions);
        assert!(row_folded(&folded, &[0]) && !row_folded(&folded, &[1]));
    }

    /// The rows under a frontier inside row R: the rows before R and rows holding no
    /// position are folded; R is folded only when nothing under it is delivered or emitted
    /// past the frontier.
    #[test]
    fn a_frontier_inside_a_row_folds_the_rows_before_it() {
        let frontier = position_path(&[1, 2]);
        let emitted = position_path(&[1, 2]);
        let delivered = [position_path(&[1, 3])];
        let positions = undecided_positions(delivered.iter(), Some(&emitted), Some(&frontier));
        let folded = rows_folded_at(0, &positions);
        assert!(row_folded(&folded, &[0]) && row_folded(&folded, &[2]));
        assert!(
            !row_folded(&folded, &[1]),
            "position (1, 3) is still to run"
        );
        let positions = undecided_positions(std::iter::empty(), Some(&emitted), Some(&frontier));
        assert!(row_folded(&rows_folded_at(0, &positions), &[1]));
    }

    /// Folding a row never shrinks as the frontier advances over a fixed delivery: a row
    /// folded at one frontier is folded at every later one.
    #[test]
    fn a_row_folded_stays_folded_as_the_frontier_advances() {
        let delivered = [position_path(&[2, 0])];
        let emitted = position_path(&[1, 1]);
        let frontiers = [
            None,
            Some(position_path(&[0, 5])),
            Some(position_path(&[1, 1])),
        ];
        let mut folded_before: Vec<Vec<u64>> = Vec::new();
        for frontier in &frontiers {
            let positions =
                undecided_positions(delivered.iter(), Some(&emitted), frontier.as_ref());
            let folded = rows_folded_at(0, &positions);
            for row in &folded_before {
                assert!(
                    row_folded(&folded, row),
                    "row {row:?} was folded at an earlier frontier"
                );
            }
            folded_before = (0..3u64)
                .map(|r| vec![r])
                .filter(|row| row_folded(&folded, row))
                .collect();
        }
        assert_eq!(folded_before, vec![vec![0], vec![1]]);
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
        let pair = |r: u64, p: u64| {
            Value::Record(HashMap::from([
                (tuple_field(0), Value::UInt(r)),
                (tuple_field(1), Value::UInt(p)),
            ]))
        };
        // The curried source: rows 0 and 1, one position each, no row complete yet.
        let source_of = |row0: Vec<u64>, items0: Vec<i64>| {
            let n0 = row0.len();
            let mut positions = row0;
            positions.push(0);
            let mut items = items0;
            items.push(10);
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::grouped(
                    vec![0, n0],
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
        let source = Arc::new(RwLock::new(source_of(vec![0], vec![1])));
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
        let render =
            |e: &Engines| render_engines(e, &store_tiling, &[Predicate::False, Predicate::False]);
        let store = Arc::new(RwLock::new(render(&engines)));
        let (nested, inner) = InductionDriver::nested_parts(
            Arc::new(SharedSource {
                tiling: pairs_tiling.clone(),
                tile: Arc::new(RwLock::new(pairs_tile(vec![100, 100, 200]))),
            }),
            // One reseed per enclosing position.
            vec![Arc::new(SharedSource {
                tiling: Tiling::data_function(uint.clone(), Tiling::Scalar(value_extent())),
                tile: Arc::new(RwLock::new(Tile::data_function(
                    ColumnValue::from_uints(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::from_ints(vec![0, 0]))),
                    Predicate::True,
                    BitSet::new(),
                ))),
            })],
            Vec::new(),
            value_extent(),
            &pair_extent,
        );
        let driver = Arc::new(InductionDriver::new(
            Arc::new(SharedSource {
                tiling: store_tiling.clone(),
                tile: store.clone(),
            }),
            Arc::new(SharedSource {
                tiling: source_tiling,
                tile: source.clone(),
            }),
            Some(nested),
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            inner,
            None,
        ));
        let g = driver.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = driver.clone().subscribe(g, Box::new(|| {}), &mut cx);
        let emitted = |t: &Tile| -> Vec<Vec<Value>> {
            decided_paths(t)
                .into_iter()
                .map(|(p, _)| p.to_vec())
                .collect()
        };
        let first = consume_nested_drive_and_read(&mut producer);
        assert_eq!(emitted(&first), vec![vec![Value::UInt(0), Value::UInt(0)]]);
        // The store decides (0, 0).
        engines
            .store_at(&[Value::UInt(0)], &mut || {
                CommitEngine::seeded_at(None, HashMap::from([(acc.clone(), int(0))]))
            })
            .step(pos(0), Some(HashMap::from([(acc.clone(), int(1))])));
        *store
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = render(&engines);

        let second = consume_nested_drive_and_read(&mut producer);
        let paths = emitted(&second);
        assert!(
            !paths.contains(&vec![Value::UInt(1), Value::UInt(0)]),
            "the drive entered row 1 while the source had not called row 0 complete: {paths:?}"
        );
    }

    /// A reseed holding a collection still arriving is not yet a value, so the position
    /// entering its row waits for it, as a row whose seed has not arrived does, rather than
    /// handing the body part of a collection.
    #[test]
    fn a_nested_drive_waits_for_a_reseed_still_arriving() {
        let acc = acct("acc");
        let uint = Extent::Base(BaseType::UInt);
        let pair_extent = Extent::Record(HashMap::from([
            (tuple_field(0), uint.clone()),
            (tuple_field(1), uint.clone()),
        ]));
        let pair = |r: u64, p: u64| {
            Value::Record(HashMap::from([
                (tuple_field(0), Value::UInt(r)),
                (tuple_field(1), Value::UInt(p)),
            ]))
        };
        // One row, one position, the row complete.
        let source = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::from_ints(vec![10]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let source_tiling = Tiling::data_function(
            uint.clone(),
            Tiling::data_function(uint.clone(), Tiling::Scalar(value_extent())),
        );
        let pairs_tiling =
            Tiling::data_function(pair_extent.clone(), Tiling::Scalar(value_extent()));
        let pairs = Tile::data_function(
            ColumnValue::from_values(vec![pair(0, 0)], &pair_extent),
            Box::new(Tile::Scalar(ColumnValue::from_ints(vec![100]))),
            Predicate::True,
            BitSet::new(),
        );
        // Row 0's reseed is a collection whose keys are still open: no level calls it
        // complete, the row's own included, since completeness closes downward.
        let reseed_tiling = Tiling::data_function(
            uint.clone(),
            Tiling::data_function(uint.clone(), Tiling::Scalar(value_extent())),
        );
        let reseed = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::from_ints(vec![1]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let store_tiling = nested_store_tiling(uint.clone(), uint.clone(), store_values(&["acc"]));
        let engines = Engines::unopened(&store_tiling);
        let store = render_engines(
            &engines,
            &store_tiling,
            &[Predicate::False, Predicate::False],
        );
        let (nested, inner) = InductionDriver::nested_parts(
            Arc::new(SharedSource {
                tiling: pairs_tiling,
                tile: Arc::new(RwLock::new(pairs)),
            }),
            vec![Arc::new(SharedSource {
                tiling: reseed_tiling,
                tile: Arc::new(RwLock::new(reseed)),
            })],
            Vec::new(),
            value_extent(),
            &pair_extent,
        );
        let driver = Arc::new(InductionDriver::new(
            Arc::new(SharedSource {
                tiling: store_tiling.clone(),
                tile: Arc::new(RwLock::new(store)),
            }),
            Arc::new(SharedSource {
                tiling: source_tiling,
                tile: Arc::new(RwLock::new(source)),
            }),
            Some(nested),
            vec![acc],
            vec![value_extent()],
            value_extent(),
            inner,
            None,
        ));
        let g = driver.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = driver.clone().subscribe(g, Box::new(|| {}), &mut cx);
        let first = consume_nested_drive_and_read(&mut producer);
        assert!(
            decided_paths(&first).is_empty(),
            "the drive ran a position whose reseed is part of a collection: {first:?}"
        );
    }

    /// A seed stand-in counting its pulls and recording what it was released.
    struct CountingSeed {
        tiling: Tiling,
        value: Value,
        gets: Arc<RwLock<usize>>,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }
    struct CountingSeedProducer {
        base: ProducerBase,
        value: Value,
        gets: Arc<RwLock<usize>>,
        released: Arc<RwLock<Vec<TileGuard>>>,
    }
    impl TileOperator for CountingSeed {
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            self: Arc<Self>,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(CountingSeedProducer {
                base: ProducerBase::unowned(CountingSeedProducer::alloc_id(), &self.tiling),
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
        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            *self
                .gets
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner) += 1;
            if self.obsolete_guard().is_universal() {
                return self.tiling().empty_tile();
            }
            Tile::Scalar(ColumnValue::single(self.value.clone()))
        }
        fn release_impl(&self, obsolete_guard: TileGuard) {
            self.released
                .write()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .push(obsolete_guard);
        }
    }

    type Counters = (Arc<RwLock<usize>>, Arc<RwLock<Vec<TileGuard>>>);

    fn counting_seed(init: i64) -> (CountingSeed, Counters) {
        let gets = Arc::new(RwLock::new(0));
        let released = Arc::new(RwLock::new(Vec::new()));
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
            vec![(acc.clone(), Arc::new(seed))],
            vec![acc.clone()],
            Vec::new(),
            full_store_tiling(
                Extent::uint_range(uint_of_row(items.len())),
                store_values(&["acc"]),
            ),
            None,
        );
        let set_body = store.body_input_setter();
        let fan = Arc::new(FanOut::new_cyclic(Arc::new(store)));
        let driver = InductionDriver::new(
            fan.slot(),
            Arc::new(ItemSource::new(&items)),
            None,
            vec![acc.clone()],
            vec![value_extent()],
            value_extent(),
            Extent::uint_range(uint_of_row(items.len())),
            None,
        );
        set_body(Arc::new(AddIfBody::new(Arc::new(driver), i64::MIN, "acc")));
        let op = fan.slot();
        let guard = op.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let producer = op.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        step_induction(&fan, 0..items.len() as u64);
        let gets_at_open = *gets
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for _ in 0..4 {
            assert!(
                producer
                    .get(producer.tiling().universal_guard())
                    .is_terminal()
            );
        }
        assert_eq!(
            *gets
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            gets_at_open,
            "snapshot reads never read the seed again"
        );
        assert!(
            !released
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_empty(),
            "the seed is released after opening"
        );
    }

    /// A commit store releases its seed stream once it has opened on it.
    #[test]
    fn an_open_commit_store_releases_its_seed() {
        let acc = acct("acc");
        let (seed, (gets, released)) = counting_seed(7);
        let op = CommitOperator::with_seed_ops(
            vec![(acc.clone(), Arc::new(seed))],
            store_values(&["acc"]),
            Vec::new(),
        );
        let fan = Arc::new(FanOut::new_cyclic(Arc::new(op)));
        let reader = fan.slot();
        let mut producer = reader.clone().subscribe(
            reader.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        consume_input(&fan, 0, seed_input_tiling().universal_guard());
        let last = producer.read_in_pipeline(producer.tiling().universal_guard());
        assert!(last.is_terminal(), "a store with no writers is terminal");
        assert_eq!(store_value_now(&last, &acc), Some(int(7)));
        assert!(
            *gets
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                > 0
        );
        assert!(
            !released
                .read()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_empty(),
            "the seed is released after opening"
        );
    }

    /// A reclaim takes the prefix of decided positions the meet covers and stops at the
    /// first it does not: a reader that released positions 0 and 2 still reads 1.
    #[test]
    fn a_reclaim_stops_at_the_first_position_still_read() {
        let (mut fan, _acc) = induction_cycle(&[1, 2, 3, 4], i64::MIN, 0);
        let reader = fan.slot();
        let guard = reader.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = reader.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        let tile = snapshot_after_run(&mut fan, &mut producer);
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

        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
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
        let stream = Arc::new(StoreValueStream::new(
            Arc::new(FixedSource {
                tiling: store_tiling,
                tile,
            }),
            acc,
            Extent::Base(BaseType::Int),
            true,
        ));
        let g = stream.tiling().universal_guard();
        let mut p =
            stream
                .clone()
                .clone()
                .subscribe(g, Box::new(|| {}), &mut SubscribeContext::new());
        let tile = p.read_in_pipeline(p.tiling().universal_guard());
        // Ticks 0 and 1 were reclaimed, so the stream starts at tick 2, where the carry
        // still folds to the write made there.
        let Tile::DataFunction {
            domain, codomain, ..
        } = &tile
        else {
            panic!("a value stream is a collection over the commit clock, got {tile:?}")
        };
        assert_eq!(*domain, ColumnValue::from_uints(vec![2]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::from_ints(vec![50])));
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
        let seed = Tile::record(HashMap::from([
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
        // A seed is keyed by the enclosing position it seeds.
        let seeds = |complete: Predicate| {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::grouped(
                    vec![0, 1],
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
        let row = |r: u64| Path::from(vec![Value::UInt(r)]);
        assert_eq!(rows(&seeds(Predicate::True)), vec![row(0), row(1)]);
        let first = Predicate::from_column_value(&ColumnValue::from_uints(vec![0]));
        assert_eq!(rows(&seeds(first)), vec![row(0)]);
        assert_eq!(rows(&seeds(Predicate::False)), Vec::<Path>::new());
    }
}

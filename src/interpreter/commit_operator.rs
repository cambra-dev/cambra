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
//!   store back (the operator's own output) before proposing — the `Recurse`
//!   feedback idiom. The store the writer reads carries a watermark, and the
//!   writer reports the timestamp it observed as its proposal's snapshot.
//!
//! Both the **engine** and the **operator** are multi-key. The store is
//! `CommitTimestamp ⇀ (Key ⇀ Value)`, held as per-tick write sets with a per-key
//! latest-write index; the in-engine read is `read_as_of(t, key)` (folding the
//! delta history), and the whole-store render is
//! [`CommitEngine::render_full_store_tile`]. Disjoint write sets never conflict;
//! decided-absence is where a tick that wrote other keys is absent for this key,
//! though decided — its value holding from the latest earlier change. A writer's
//! proposal carries its read and write sets as *maps*: each rides a tile cell as
//! a [`map_to_value`] `Value::Function` in a `ColumnValue::Variants` column
//! (heterogeneous key sets per cell, no `CurriedFunction`), so the proposal
//! stream is `step → {snap, reads, writes}` with `reads`/`writes` map-valued. The
//! operator's output is the full store as a [`Tile::Store`] changelog in that
//! same delta encoding, which the writers *fold* per key ([`store_current`] /
//! [`store_value_at`]) when they read it back through the cycle — the step
//! function, never mistaken for a directly-indexed `SealedFunction`.
//!
//! # Concurrency is logical
//!
//! The interpreter is single-threaded dataflow. "Concurrent writers" means
//! multiple input domains the operator interleaves — the order in which
//! [`CommitEngine::attempt`] is called. There is no parallelism; serialization
//! semantics are validated deterministically.

use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
};

use intervalsets::Bounding;

use crate::ccl::F_WRITES;
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, FunctionGuard, Predicate, Scheduler, SharedConsumer,
    Tile, TileGuard, Tiling, Value, WakeupQueue,
    tile_operators::{CyclicSequencingProducer, ProducerBase, TileOperator, TileProducer},
    tuple_field,
};
use crate::pretty_graph::VizOptions;
use crate::pretty_tree::InspectNode;

use crate::interpreter::tile_operators::impl_producer_base;

/// A commit timestamp — a position on the runtime's monotonic commit clock.
///
/// Tick `0` is reserved for the store's initial value; allocated commit
/// attempts start at `1`.
pub type CommitTs = usize;

/// A writer-input slot, filled after construction via
/// [`CommitOperator::writer_input_setter`] (the cycle requires late wiring).
type WriterSlot = Rc<RefCell<Option<Box<dyn TileOperator>>>>;

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
    pub snapshot: CommitTs,
    /// Keys observed at `snapshot`, with the values seen (the read set).
    pub reads: HashMap<Value, Value>,
    /// Keys to update, with their new values (the write set).
    pub writes: HashMap<Value, Value>,
}

/// The outcome of a commit attempt under **allocate-on-commit**: a valid
/// proposal consumes the next tick and writes; a stale one consumes nothing and
/// the writer retries by re-reading and re-proposing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitOutcome {
    Committed { ts: CommitTs },
    Stale,
}

/// The pure serialization engine: no tiles, directly unit-testable.
///
/// **Allocate-on-commit**: a tick is consumed only by a successful commit, so
/// the timestamp domain is dense and a stale proposal leaves no trace. Validates
/// the read set with backward validation, and tracks the committed values, the
/// watermark, and the per-key latest-write index.
pub struct CommitEngine {
    /// `tick → write set`. Dense in the *timestamp* domain under
    /// allocate-on-commit: every allocated tick is a successful commit, so ticks
    /// `0..=watermark` all have an entry, tick `0` being the initial state.
    /// A *per-key* view is sparse: a tick whose write set omits a key is
    /// decided-absent for that key — that is where the decided-positions
    /// machinery does real work.
    committed: BTreeMap<CommitTs, HashMap<Value, Value>>,
    /// Per key, the largest tick that wrote it (`0` = only the initial state). A
    /// read of `key` at `snapshot` is still current iff `latest_write[key] ≤
    /// snapshot`.
    latest_write: HashMap<Value, CommitTs>,
    /// The next clock tick to allocate. Only successful commits allocate, so
    /// `next_ts - 1` is the highest committed tick — the watermark.
    next_ts: CommitTs,
}

impl CommitEngine {
    /// Create an engine whose initial state is `init` at tick `0`.
    pub fn new(init: HashMap<Value, Value>) -> Self {
        let latest_write = init.keys().map(|k| (k.clone(), 0)).collect();
        Self {
            committed: BTreeMap::from([(0, init)]),
            latest_write,
            next_ts: 1,
        }
    }

    /// Create an engine whose initial state is `init` at tick `at`, for a
    /// position-driven store whose first iteration position is not `0`.
    ///
    /// A store built to replace one in a running program enrols with its source
    /// at the source's current frontier, so its first position is wherever the
    /// replaced version had reached. The drive maps iteration position `p` to
    /// tick `p + 1` and reads the previous accumulator as of tick `p`, so the
    /// seed has to sit at the tick the first position reads rather than at `0`.
    /// Re-basing the ticks instead would break the correspondence the dense read
    /// relies on.
    pub fn seeded_at(at: CommitTs, init: HashMap<Value, Value>) -> Self {
        let latest_write = init.keys().map(|k| (k.clone(), at)).collect();
        Self {
            committed: BTreeMap::from([(at, init)]),
            latest_write,
            next_ts: at + 1,
        }
    }

    /// An empty engine for a **position-driven induction store**: no tick-0 init
    /// seed (the accumulator's init is the reader's fold default, supplied by
    /// `get_prev_seq`), driven by [`step`](Self::step) rather than
    /// [`attempt`](Self::attempt). Undecided until the first `step`.
    ///
    /// Test-only: production `InductionStore`/commit engines seed tick 0 via
    /// [`CommitEngine::new`]. This unseeded form models the pre-first-`step`
    /// state directly for the `step`/carry unit tests.
    #[cfg(test)]
    pub fn for_induction() -> Self {
        Self {
            committed: BTreeMap::new(),
            latest_write: HashMap::new(),
            next_ts: 0,
        }
    }

    /// The watermark frontier: all ticks `≤ watermark()` are decided. `None`
    /// before anything is decided (an induction engine before its first
    /// [`step`](Self::step); a commit engine always has its tick-0 init).
    pub fn decided_watermark(&self) -> Option<CommitTs> {
        self.next_ts.checked_sub(1)
    }

    /// The watermark frontier: all ticks `≤ watermark()` are decided.
    pub fn watermark(&self) -> CommitTs {
        self.next_ts - 1
    }

    /// Position-driven induction step (the sequential, no-conflict dual of
    /// [`attempt`](Self::attempt)): advance the decided frontier to `position`
    /// **unconditionally** — every iteration position is decided — and record a
    /// write at tick = `position` iff `writes` is `Some`. A `None` is a **carry**:
    /// no change, the accumulator holds from the latest earlier write. Because the
    /// tick *is* the position (not allocate-on-commit), the changelog is sparse in
    /// position space while the frontier tracks the whole extent — so a store with
    /// a trailing run of carries still reports the right decided region. There is
    /// no conflict/retry: a single writer visits each position once in order.
    pub fn step(&mut self, position: CommitTs, writes: Option<HashMap<Value, Value>>) {
        debug_assert!(
            self.decided_watermark().is_none_or(|w| position > w),
            "induction positions advance strictly monotonically (got {position}, watermark {:?})",
            self.decided_watermark()
        );
        self.next_ts = position + 1;
        if let Some(w) = writes {
            for k in w.keys() {
                self.latest_write.insert(k.clone(), position);
            }
            self.committed.insert(position, w);
        }
    }

    /// Validate and (if valid) commit one proposal. Allocate-on-commit: a valid
    /// proposal consumes the next tick and applies its write set; a stale one
    /// consumes no tick and returns [`CommitOutcome::Stale`], leaving the writer
    /// to retry.
    pub fn attempt(&mut self, p: Proposal) -> CommitOutcome {
        debug_assert!(
            p.snapshot <= self.watermark(),
            "proposal snapshot {} is beyond the watermark {}",
            p.snapshot,
            self.watermark()
        );
        debug_assert!(
            p.reads
                .iter()
                .all(|(k, v)| self.read_as_of(p.snapshot, k).as_ref() == Some(v)),
            "a proposal read does not match the store at its snapshot"
        );

        // Backward validation: no key the writer read may have been overwritten
        // by a commit after the snapshot. Disjoint write sets never conflict.
        let stale = p
            .reads
            .keys()
            .any(|k| self.latest_write.get(k).copied().unwrap_or(0) > p.snapshot);
        if stale {
            return CommitOutcome::Stale;
        }
        let c = self.next_ts;
        self.next_ts += 1;
        for k in p.writes.keys() {
            self.latest_write.insert(k.clone(), c);
        }
        self.committed.insert(c, p.writes);
        CommitOutcome::Committed { ts: c }
    }

    /// The value of `key` as of timestamp `t` — the latest write to `key` at a
    /// tick `≤ t`, folding past ticks that wrote other keys — or `None` if `t` is
    /// beyond the watermark or `key` was never written.
    pub fn read_as_of(&self, t: CommitTs, key: &Value) -> Option<Value> {
        if t > self.watermark() {
            return None;
        }
        self.committed
            .range(..=t)
            .rev()
            .find_map(|(_, ws)| ws.get(key).cloned())
    }

    /// Read-side commit-log GC: reclaim committed versions at ticks `≤ through`
    /// that every store consumer has released, **except each key's latest write**
    /// — that entry is the carry-forward source a current-value fold (a writer
    /// reading the store, a scalar read) still needs.
    ///
    /// One rule covers both store kinds. A **collection** key's latest write is
    /// the newest append (`> through` once a consumer has merged a prefix), so
    /// every released entry `≤ through` is dropped — the merged log prefix is
    /// reclaimed. A **scalar** key's latest write is kept; a superseded scalar
    /// entry below `through` is dropped. Soundness rests on the caller: pass only
    /// a prefix that *every* consumer has released (the `FanOut`-intersected
    /// watermark), so dropping it cannot strand a live read (tile monotonicity —
    /// only `release` shrinks).
    pub fn gc_released_prefix(&mut self, through: CommitTs) {
        let latest = &self.latest_write;
        let mut emptied: Vec<CommitTs> = Vec::new();
        for (tick, delta) in self.committed.range_mut(..=through) {
            delta.retain(|k, _| latest.get(k).copied() == Some(*tick));
            if delta.is_empty() {
                emptied.push(*tick);
            }
        }
        for t in &emptied {
            self.committed.remove(t);
        }
    }

    /// Render the full store as a [`Tile::Store`] changelog `CommitTimestamp ⇀
    /// (Key ⇀ Value)`: each committed tick as a change carrying its *write-set
    /// delta*, encoded via [`map_to_value`] into the `deltas` `Variants` column,
    /// with `frontier` the watermark. A consumer reads state by *folding* the
    /// changelog per key ([`store_value_at`] / [`store_snapshot_at`], latest delta
    /// containing the key `≤ t`); a tick whose delta omits a key is decided-absent
    /// for it, its value holding from the latest earlier change. This is the
    /// multi-key operator's output — the writers read it back through the cycle,
    /// and it is the step function, not a `SealedFunction`, so the fold cannot be
    /// mistaken for direct indexing.
    pub fn render_full_store_tile(&self) -> Tile {
        let ticks: Vec<usize> = self.committed.keys().copied().collect();
        let deltas: Vec<Value> = self.committed.values().map(map_to_value).collect();
        // The decided frontier is the watermark; an induction engine that has not
        // stepped yet is undecided (`False`). The frontier is `LessThanEq(w)` even
        // when the latest position(s) carried no write, so a trailing run of
        // carries stays decided — the changelog is sparse but the frontier is not.
        let frontier = match self.decided_watermark() {
            Some(w) => Predicate::LessThanEq(Value::UInt(w)),
            None => Predicate::False,
        };
        Tile::Store {
            changes: ColumnValue::from_uints(ticks),
            deltas: ColumnValue::Variants(deltas),
            frontier,
            // A rendered store is *live* by default; a producer that knows its
            // writers are finished flips `terminal` (keeping the numeric frontier).
            terminal: false,
        }
    }
}

/// Why draining a computed-init producer yielded no value — distinguishes a
/// genuinely empty init from one that never settled, so the caller can report
/// the right diagnosis (the two are otherwise indistinguishable from a bare
/// `None`).
enum InitDrainFailure {
    /// The producer yielded a scalar tile, but it was always empty: the init has
    /// no value to seed (e.g. a read of an empty collection).
    Empty,
    /// The producer never yielded a non-empty scalar within the pull bound. For
    /// an *acyclic* init that should resolve on the first pull, this means the
    /// producer isn't converging (or isn't scalar-shaped) — a structural bug.
    Diverged,
}

/// Drain a scalar-valued producer to its single value — the tick-0 store value
/// for a computed init. The producer is acyclic (it never reads the store), so a
/// non-empty scalar appears on the first pull; the [`MAX_INIT_PULLS`] bound is a
/// belt-and-braces guard against a producer that never yields. On failure,
/// distinguishes a genuinely [`InitDrainFailure::Empty`] init (a scalar tile was
/// produced but stayed empty) from a [`InitDrainFailure::Diverged`] one (no
/// scalar tile settled within the bound).
fn read_initial_scalar(producer: &mut dyn TileProducer) -> Result<Value, InitDrainFailure> {
    use crate::interpreter::tile_operators::scalar_tile_to_column_value;
    let guard = producer.tiling().universal_guard();
    let mut saw_empty_scalar = false;
    for _ in 0..MAX_INIT_PULLS {
        // A compound (tuple/record) accumulator's init is struct-of-arrays
        // (`Tile::Record`); box it into a single scalar record value so it seeds
        // like any scalar. A plain scalar init passes straight through.
        let cv = match producer.get(guard.clone()) {
            Tile::Scalar(cv) => cv,
            tile @ Tile::Record(_) => scalar_tile_to_column_value(tile),
            _ => continue,
        };
        if !cv.is_empty() {
            return Ok(cv.index_at(0));
        }
        saw_empty_scalar = true;
    }
    // A scalar that stayed empty across the bound is a genuinely empty init; a
    // producer that never even yielded a scalar never settled.
    Err(if saw_empty_scalar {
        InitDrainFailure::Empty
    } else {
        InitDrainFailure::Diverged
    })
}

/// Pull bound for [`read_initial_scalar`]: an acyclic scalar init resolves on the
/// first pull, so a small margin is ample; exceeding it means the input isn't
/// converging (the doc's "a couple of pulls" claim).
const MAX_INIT_PULLS: usize = 8;

/// The watermark of a store tile's `frontier` predicate (the decode behind
/// [`store_frontier`]). A store always carries its watermark as `LessThanEq(w)`
/// — terminality is a separate flag, never a `True` frontier that would discard
/// `w` — so the watermark reads directly and counts trailing carries. `None` for
/// an undecided/empty changelog.
fn frontier_from_domain(domain: &ColumnValue, domain_predicate: &Predicate) -> Option<CommitTs> {
    if domain.is_empty() {
        return None;
    }
    match domain_predicate {
        Predicate::LessThanEq(Value::UInt(f)) => Some(*f),
        _ => None,
    }
}

// ── Step-function reads over a `Tile::Store` changelog ────────────────────────
//
// A `Tile::Store` *is* its changelog: `changes[i]` committed the write-set delta
// `deltas[i]` (a `map_to_value` cell), ticks strictly ascending, `frontier`
// the decided watermark. These four functions are the sanctioned way to read a
// store's value — a plain index into `changes` is meaningless, because a tick
// absent from the changelog is *decided-absent* (its value holds from the latest
// earlier change), not unknown. They fold with right-continuous step
// interpolation, and are the single tile-level store read: the writers
// (`store_current`) and the value-stream projection both route through them, the
// tile-side counterpart of the engine's own `read_as_of` fold over its BTreeMap.

/// The decided frontier tick of a store tile, from its `frontier` predicate and
/// `changes`. `None` if `tile` is not a [`Tile::Store`], is empty, or is
/// undecided. Mirrors [`frontier_from_domain`]: `LessThanEq(w)` reads the
/// watermark directly; the terminal `True` flip takes the final (largest) change
/// tick.
pub fn store_frontier(tile: &Tile) -> Option<CommitTs> {
    let Tile::Store {
        changes, frontier, ..
    } = tile
    else {
        return None;
    };
    frontier_from_domain(changes, frontier)
}

/// `key`'s value as of commit time `t`: the latest change at a tick `≤ t` whose
/// delta wrote `key`, folding past ticks that wrote only other keys. `None` if
/// `tile` is not a store or `key` was never written at or below `t`. The
/// tile-level analog of [`CommitEngine::read_as_of`] (which folds the engine's
/// `BTreeMap`); this folds the rendered changelog a consumer holds.
pub fn store_value_at(tile: &Tile, t: CommitTs, key: &Value) -> Option<Value> {
    let Tile::Store {
        changes, deltas, ..
    } = tile
    else {
        return None;
    };
    // Scan newest-first: the first change `≤ t` that names `key` is its value as
    // of `t` (ticks ascending, so once `tick ≤ t` every earlier index is too).
    for i in (0..changes.len()).rev() {
        let Value::UInt(tick) = changes.index_at(i) else {
            continue;
        };
        if tick > t {
            continue;
        }
        if let Some(v) = value_to_map(&deltas.index_at(i)).get(key) {
            return Some(v.clone());
        }
    }
    None
}

/// `key`'s value written **at exactly** tick `t` — the delta at tick `t` if it
/// names `key`, else `None`. Unlike [`store_value_at`] (which carries the latest
/// write ≤ `t` forward), this reads only the change *at* `t`: the per-position
/// event a reply tap is, so a position that did not fire the tap yields `None`
/// (and the dense read omits it).
pub fn store_delta_at(tile: &Tile, t: CommitTs, key: &Value) -> Option<Value> {
    let Tile::Store {
        changes, deltas, ..
    } = tile
    else {
        return None;
    };
    for i in 0..changes.len() {
        if changes.index_at(i) == Value::UInt(t) {
            return value_to_map(&deltas.index_at(i)).get(key).cloned();
        }
    }
    None
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
/// (commit clock vs loop position, `+1` offset), but the per-tick fold is this.
pub fn fold_changelog_key(
    tile: &Tile,
    t: CommitTs,
    key: &Value,
    carry_forward: bool,
) -> Option<Value> {
    if carry_forward {
        store_value_at(tile, t, key)
    } else {
        store_delta_at(tile, t, key)
    }
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
    query_ticks: impl IntoIterator<Item = CommitTs>,
    key: &Value,
    carry_forward: bool,
) -> Vec<Option<Value>> {
    let queries: Vec<CommitTs> = query_ticks.into_iter().collect();
    let Tile::Store {
        changes, deltas, ..
    } = tile
    else {
        return vec![None; queries.len()];
    };
    let n = changes.len();
    let mut idx = 0usize; // next unprocessed change index (monotonic)
    let mut carry: Option<Value> = None; // running latest write ≤ the current query
    let mut out = Vec::with_capacity(queries.len());
    for t in queries {
        let mut exact: Option<Value> = None;
        while idx < n {
            let Value::UInt(tick) = changes.index_at(idx) else {
                idx += 1;
                continue;
            };
            if tick > t {
                break;
            }
            if let Some(v) = value_to_map(&deltas.index_at(idx)).get(key) {
                carry = Some(v.clone());
                if tick == t {
                    exact = Some(v.clone());
                }
            }
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
/// `SealedFunction` reads (the source of the read-skew divergence) cannot.
pub fn store_snapshot_at(tile: &Tile, t: CommitTs) -> HashMap<Value, Value> {
    let Tile::Store {
        changes, deltas, ..
    } = tile
    else {
        return HashMap::new();
    };
    let mut acc = HashMap::new();
    for i in 0..changes.len() {
        let Value::UInt(tick) = changes.index_at(i) else {
            continue;
        };
        if tick > t {
            break;
        }
        acc.extend(value_to_map(&deltas.index_at(i)));
    }
    acc
}

/// `key`'s current value — its latest change at or below the decided frontier —
/// with the frontier tick. `None` if the store is undecided/empty or `key` was
/// never written. Unlike an `ExtractFinal` over a `SealedFunction`, this is
/// defined *without the stream ever terminating*: it reads the decided frontier,
/// which a live store advances on every commit. This is the read the writers
/// perform on the store they read back through the cycle.
pub fn store_current(tile: &Tile, key: &Value) -> Option<(CommitTs, Value)> {
    let f = store_frontier(tile)?;
    store_value_at(tile, f, key).map(|v| (f, v))
}

/// The largest commit tick a release predicate covers (a prefix-style release of
/// the commit-time domain). `None` for predicates with no concrete upper bound
/// (`True`, `False`, non-`UInt`) — `True` is the terminal release, after which
/// the consumer pulls no more, so there is nothing to advance the cursor past.
fn max_released_tick(pred: &Predicate) -> Option<usize> {
    match pred {
        Predicate::LessThanEq(Value::UInt(k)) => Some(*k),
        Predicate::Intervals(iset) => iset
            .intervals()
            .iter()
            .filter_map(|iv| match iv.rval() {
                Some(&Value::UInt(k)) => Some(k),
                _ => None,
            })
            .max(),
        Predicate::Or(arms) => arms.iter().filter_map(max_released_tick).max(),
        // A union's arms are tag-keyed, so they are walked by value rather than
        // sharing the `Or` arm's positional vector.
        Predicate::Union(arms) => arms.values().filter_map(max_released_tick).max(),
        _ => None,
    }
}

/// A compacting prefix watermark over a monotone `UInt` domain.
///
/// Several commit-store readers/producers emit an append-only stream and, as a
/// consumer releases a prefix, must stop re-emitting positions at or below the
/// released edge (a re-emit would duplicate a domain position through a `Memo`
/// merge, or re-latch a frozen `AsOf` snapshot). Each one otherwise hand-rolls
/// the same `Option<usize>` watermark plus the monotone-max fold and the
/// "≤ watermark" test; this centralizes that state and those two operations.
/// The callers keep whatever *extra* work rides their release (forwarding the
/// release upstream, compacting a `latched` set) — only the watermark itself
/// lives here.
#[derive(Default)]
struct PrefixReleaseCursor {
    /// Highest released position; `None` before any release.
    through: Option<usize>,
}

impl PrefixReleaseCursor {
    /// Advance the watermark to at least `pos` (monotone: never retreats).
    fn advance_to(&mut self, pos: usize) {
        self.through = Some(self.through.map_or(pos, |r| r.max(pos)));
    }

    /// Mark the entire domain released — the terminal (`True`) release, after
    /// which no position may re-emit.
    fn release_all(&mut self) {
        self.through = Some(usize::MAX);
    }

    /// Whether `pos` is at or below the released watermark.
    fn is_released(&self, pos: usize) -> bool {
        self.through.is_some_and(|r| pos <= r)
    }

    /// The raw watermark (highest released position), for a caller doing
    /// base-relative arithmetic against it.
    fn through(&self) -> Option<usize> {
        self.through
    }

    /// Advance the watermark from a released domain predicate, centralizing the
    /// one decision every commit-store reader shares. A fully-decided (`True`)
    /// release covers the whole domain — `release_all`, since no finite tick
    /// bounds it and a bare `max_released_tick` of `None` there would be misread
    /// as "release nothing". A bounded release advances to its max released tick.
    /// Anything else releases no prefix. Returns the extent so the caller can do
    /// its own release-driven work (forward the release upstream, compact a
    /// latched set) without re-deriving this classification — the gap that let one
    /// reader silently drop the terminal case while the other handled it.
    fn advance_from(&mut self, pred: &Predicate) -> ReleasedExtent {
        if pred.as_bool() == Some(true) {
            self.release_all();
            ReleasedExtent::All
        } else if let Some(w) = max_released_tick(pred) {
            self.advance_to(w);
            ReleasedExtent::Through(w)
        } else {
            ReleasedExtent::Nothing
        }
    }
}

/// The prefix a domain-predicate release covers, as classified by
/// [`PrefixReleaseCursor::advance_from`]: nothing, a bounded prefix `≤ tick`, or
/// the whole (terminal) domain.
enum ReleasedExtent {
    Nothing,
    Through(usize),
    All,
}

/// Encode a `Key ⇀ Value` map (a read set, write set, or store delta) as a
/// `Value::Function` — a collection of `key ↦ value` bindings. This is how a map
/// rides in a single tile cell: a column of these is a `ColumnValue::Variants`
/// (row-wise, heterogeneous), so per-tick write sets and per-proposal read/write
/// sets can have *different* key sets without a fixed `Record` extent or a
/// `CurriedFunction` CSR layout. The multi-key operator and the E4 proposal
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
/// [`map_extent`] (`Key ⇀ Value`). That holds for store deltas (rendered by
/// [`CommitEngine::render_full_store_tile`]) and for proposal read/write sets
/// (inference's `emit_transact_writer` types the proposal codomain's
/// `reads`/`writes` fields as map-valued, and the writer renders them via
/// [`map_to_value`]). A non-`Function` value would be a `Variants` cell holding
/// something other than its declared map extent — impossible by construction.
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
/// carried in a `Variants` column. Used for both store deltas (the full-store
/// codomain) and a proposal's read/write sets.
fn map_extent(key_extent: &Extent, value_extent: &Extent) -> Extent {
    Extent::Function {
        domain: Box::new(key_extent.clone()),
        codomain: Box::new(value_extent.clone()),
    }
}

/// The full multi-key store tiling: a [`Tiling::Store`] step function
/// `CommitTimestamp ⇀ (Key ⇀ Value)`, each change tick carrying a `Key ⇀ Value`
/// delta cell. The codomain is a `Scalar` of the map extent because a whole
/// delta rides one cell as a `Value::Function`. The `Store` tiling (not
/// `SealedFunction`) is what marks the output as a changelog to be folded, not a
/// function to be indexed.
pub fn full_store_tiling(key_extent: &Extent, value_extent: &Extent) -> Tiling {
    Tiling::Store {
        domain: Extent::Base(BaseType::UInt),
        codomain: Box::new(Tiling::Scalar(map_extent(key_extent, value_extent))),
    }
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
    Tiling::SealedFunction {
        domain: Extent::Base(BaseType::UInt),
        codomain: Box::new(Tiling::Record(HashMap::from([
            (
                F_SNAP.to_string(),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
            (F_READS.to_string(), Tiling::Scalar(map.clone())),
            (F_WRITES.to_string(), Tiling::Scalar(map)),
        ]))),
    }
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
    /// `init_ops` at subscribe.
    init: HashMap<Value, Value>,
    /// Per scalar key, an acyclic operator producing its tick-0 value (it never
    /// reads the store), read once at subscribe. A literal init is just the
    /// trivial init operator; a collection key has no entry (its log starts
    /// empty). This is the op-conversion seeding path.
    init_ops: Vec<(Value, Box<dyn TileOperator>)>,
    output_tiling: Tiling,
    writer_inputs: Vec<WriterSlot>,
}

impl CommitOperator {
    /// Create a commit operator whose store starts at `init` (the tick-0 state),
    /// with keys in `key_extent` and values in `value_extent`.
    pub fn new(
        init: HashMap<Value, Value>,
        key_extent: Extent,
        value_extent: Extent,
        n_writers: usize,
    ) -> Self {
        let output_tiling = full_store_tiling(&key_extent, &value_extent);
        Self {
            init,
            init_ops: Vec::new(),
            output_tiling,
            writer_inputs: (0..n_writers)
                .map(|_| Rc::new(RefCell::new(None)))
                .collect(),
        }
    }

    /// Create a commit operator whose scalar keys' tick-0 values are produced by
    /// `init_ops` (each a scalar-valued, acyclic operator — it never reads the
    /// store), read once at subscribe. This is the op-conversion path for
    /// `Mut(V, Txn)` keys; a literal init is just the trivial init
    /// operator, and a collection key contributes no entry (its log starts
    /// empty). ([`Self::new`] is the concrete-map constructor used by
    /// engine-level tests.)
    pub fn with_init_ops(
        init_ops: Vec<(Value, Box<dyn TileOperator>)>,
        key_extent: Extent,
        value_extent: Extent,
        n_writers: usize,
    ) -> Self {
        let output_tiling = full_store_tiling(&key_extent, &value_extent);
        Self {
            init: HashMap::new(),
            init_ops,
            output_tiling,
            writer_inputs: (0..n_writers)
                .map(|_| Rc::new(RefCell::new(None)))
                .collect(),
        }
    }

    /// Wire writer `k`'s input. Call after the operator is boxed, so the writer
    /// can be built around a branch of the operator's store output (the cycle).
    pub fn writer_input_setter(&self, k: usize) -> impl FnOnce(Box<dyn TileOperator>) + use<> {
        let slot = self.writer_inputs[k].clone();
        move |op| {
            *slot.borrow_mut() = Some(op);
        }
    }
}

impl TileOperator for CommitOperator {
    fn tiling(&self) -> &Tiling {
        &self.output_tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Wake this operator's consumer whenever any writer's (live) source
        // delivers a new item: the arrival drives a commit, and that commit must
        // propagate to a downstream reader of a store key or `to_<defer>` tap (a
        // live cross-endpoint read — a read-only transaction's reply). This is the
        // same both-inputs-wake wiring `AsOf` uses; without it the sink reading a
        // tap off a live commit store would never be notified and would hang.
        // The store always has its initial value, so kick once immediately to
        // start the drain loop.
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        consumer.borrow_mut().notify();
        // Resolve the tick-0 store state: the concrete seed plus each scalar key's
        // init op (read once here; acyclic, so a single drain to a scalar value is
        // sound). Collection keys contribute no entry — their log starts empty.
        let mut init = self.init.clone();
        for (key, mut op) in std::mem::take(&mut self.init_ops) {
            let g = op.tiling().universal_guard();
            let mut producer = op.subscribe(g, Box::new(|| {}), scheduler);
            let value = read_initial_scalar(&mut *producer).unwrap_or_else(|e| match e {
                InitDrainFailure::Empty => panic!(
                    "CommitOperator: computed init op for key {key:?} produced an empty scalar \
                     (no value to seed the tick-0 store)"
                ),
                InitDrainFailure::Diverged => panic!(
                    "CommitOperator: computed init op for key {key:?} never settled to a scalar \
                     within {MAX_INIT_PULLS} pulls (an acyclic init should resolve on the first \
                     pull)"
                ),
            });
            init.insert(key, value);
        }
        let writer_producers = self
            .writer_inputs
            .iter()
            .enumerate()
            .map(|(k, slot)| {
                let mut input = slot.borrow_mut().take().unwrap_or_else(|| {
                    panic!("CommitOperator: writer {k} not wired (call writer_input_setter)")
                });
                let guard = input.tiling().universal_guard();
                input.subscribe(guard, Box::new(consumer.clone()), scheduler)
            })
            .collect::<Vec<_>>();
        let n = writer_producers.len();
        Box::new(CommitProducer {
            base: ProducerBase::new(CommitProducer::alloc_id(), &self.output_tiling),
            writer_producers,
            consumed: vec![0; n],
            writer_terminal: vec![false; n],
            engine: CommitEngine::new(init),
            output_tiling: self.output_tiling.clone(),
            drain_start: 0,
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
    engine: CommitEngine,
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

impl TileProducer for CommitProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        self.debug_assert_position_invariant();
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
            let Tile::SealedFunction {
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
            // non-`Record` codomain on a `SealedFunction` proposal tile is
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
                // `snap` is typed `Scalar(UInt)` by emit_transact_writer.
                let Value::UInt(snapshot) = snaps.index_at(j) else {
                    unreachable!(
                        "proposal snap is a UInt (the snap field is typed Scalar(UInt) by \
                         emit_transact_writer)"
                    );
                };
                let outcome = self.engine.attempt(Proposal {
                    snapshot,
                    reads: value_to_map(&reads.index_at(j)),
                    writes: value_to_map(&writes.index_at(j)),
                });
                self.consumed[k] = step + 1;
                if let CommitOutcome::Committed { .. } = outcome {
                    // Acknowledge the commit by releasing this step (and any
                    // earlier stale ones) back to the writer — its signal to
                    // advance and to compact its proposal window. A stale
                    // proposal is left unreleased.
                    self.writer_producers[k].release(TileGuard::Function(FunctionGuard::Domain(
                        Predicate::LessThanEq(Value::UInt(step)),
                    )));
                }
            }
        }
        // Rotate the drain start for the next pull (round-robin fairness). Guard
        // `n == 0`: a store with no writers never drains, and `% 0` would panic.
        if n > 0 {
            self.drain_start = (self.drain_start + 1) % n;
        }
        let mut store = self.engine.render_full_store_tile();
        // Signal terminality once every writer is done: the store is then fully
        // decided (no more commits), so the watermark `LessThanEq(w)` becomes
        // `True`. A downstream `read`/output gates on this to know the cycle has
        // converged (the harness re-pulls a non-terminal output to drive it).
        // A store with **no** writers is trivially terminal (no commit can ever
        // happen) — `all()` over the empty writer set is `true`, which is what we
        // want, so there is no `is_empty()` guard.
        if self.writer_terminal.iter().all(|&t| t)
            && let Tile::Store { terminal, .. } = &mut store
        {
            // Close the frontier (no more commits), keeping its numeric watermark.
            *terminal = true;
        }
        debug_assert!(
            store.check_from(&self.output_tiling),
            "rendered store tile does not match the full-store tiling"
        );
        store
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Read-side commit-log GC. The store sits behind a cyclic `FanOut`, so
        // this guard is the **intersection** of what every consumer (the writers
        // *and* the readers) has released — exactly the prefix safe to reclaim
        // (tile monotonicity: only `release` shrinks). Drop those committed
        // versions, keeping each key's latest write. A live `AsOf` reader
        // *does* release the prefix below its latched frontier (`AsOfProducer::
        // get_impl`), so a store with a writing endpoint still sheds its
        // superseded history through this branch — the intersection just also
        // waits on that reader's own released prefix.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(through) = max_released_tick(pred)
        {
            self.engine.gc_released_prefix(through);
        }
    }
}

/// Extract a source stream's codomain elements (the items to transact over) in
/// the codomain's **column order**.
///
/// This is correct for the **commit writer** precisely because transactions are
/// *unordered* — each item becomes a commit proposal the [`CommitOperator`]
/// serializes by frontier/conflict, and any serialization is a valid commit order
/// (see the unordered-mutability design commitment). So an async source whose
/// domain arrives out of position order (a `HashMap` enumeration) may be processed
/// in arrival order without affecting the result.
///
/// The **induction** drive must NOT use this: its recurrence `xₙ = f(xₙ₋₁, itemₙ)`
/// is position-ordered, so it reads by absolute domain position via
/// [`decode_source_positioned`], which sorts. The two look alike but carry opposite
/// ordering requirements — do not swap one for the other.
fn decode_source_items(tile: &Tile) -> Vec<Value> {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        return Vec::new();
    };
    match codomain.as_ref() {
        Tile::Scalar(cv) => (0..domain.len()).map(|i| cv.index_at(i)).collect(),
        // A cross-domain co-iterated source `zip((item, acc(r), …))`: each position
        // is a `Record` of the scalar columns. The writer body reads the loop item
        // off `._0` and each threaded induction accumulator off its own field —
        // the shape `build_writer` lays out for a commit decision that reads an
        // accumulator at its request position.
        Tile::Record(_) => (0..domain.len())
            .map(|i| source_value_at(codomain, i))
            .collect(),
        _ => Vec::new(),
    }
}

/// Decode an iteration source tile into `(absolute domain position, item)` pairs,
/// **sorted by position** — the ordered counterpart of [`decode_source_items`].
///
/// The induction drive's recurrence is position-ordered, so it cannot use column
/// order: an **async** source's domain arrives *unordered* (it enumerates a set of
/// arrived keys) and *compacts* as its consumed prefix is released, so column order
/// is not position order. Pairing each item with its actual `UInt` domain position
/// and sorting makes the drive read `x₀, x₁, …` in order regardless of arrival. A
/// finite list is the special case (its domain is already `[0, 1, …]`). Contrast
/// [`decode_source_items`], which the *transaction* writer uses because commit
/// order is unordered.
fn decode_source_positioned(tile: &Tile) -> Vec<(usize, Value)> {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        return Vec::new();
    };
    if !matches!(codomain.as_ref(), Tile::Scalar(_) | Tile::Record(_)) {
        return Vec::new();
    }
    let mut pairs: Vec<(usize, Value)> = (0..domain.len())
        .filter_map(|i| match domain.index_at(i) {
            Value::UInt(pos) => Some((pos, source_value_at(codomain, i))),
            _ => None,
        })
        .collect();
    pairs.sort_by_key(|(pos, _)| *pos);
    pairs
}

/// The `Value` at position `i` of a source codomain tile — a scalar column or a
/// (possibly nested) `Record` of scalar columns.
fn source_value_at(codomain: &Tile, i: usize) -> Value {
    match codomain {
        Tile::Scalar(cv) => cv.index_at(i),
        Tile::Record(fields) => Value::Record(
            fields
                .iter()
                .map(|(k, t)| (k.clone(), source_value_at(t, i)))
                .collect(),
        ),
        other => panic!("cross-domain writer source column is not scalar/record: {other:?}"),
    }
}

/// A **position-driven induction store** (a `mut` loop accumulator, plain or with
/// a conditional write `if p: total += x`) built on the same [`CommitEngine`] +
/// [`Tile::Store`] changelog machinery as the concurrent [`CommitOperator`], but
/// driven by *iteration position* rather than by concurrent proposals.
///
/// There is exactly one writer, visiting each iteration position once in order:
/// no proposals, no conflicts, no retries. The accumulator recurrence — position
/// `i` reads `xᵢ₋₁` and decides `xᵢ` — is driven **sequentially inside the
/// producer**: the driver holds the engine, folds the previous accumulator out of
/// it ([`CommitEngine::read_as_of`], defaulting below the earliest change to the
/// key's init), feeds the body `(prev…, item)` through a [`BodyInputBuffer`], reads
/// the body's `` {`commit{writes} | `abort} `` decision ([`body_decision_at`] decodes
/// the union tag), and [`step`](CommitEngine::step)s the engine — a `.Commit`
/// position appends a change, an `` `abort `` (a failed guard) is a **carry** (no
/// change; the value inherits).
///
/// The key structural difference from the retired dense `Recurse` realization:
/// the accumulator lives in the engine, not on a cyclic tile, so there is **no
/// cyclic `FanOut`** — the previous value is always available before the body
/// needs it, and a conditional write's carry positions simply produce no change
/// rather than having to synthesize a same-value "write" on a complement leg.
/// A plain (unconditional) `mut` loop is the degenerate `` `commit ``-everywhere
/// case (a dense changelog); a conditional write is sparse in position space
/// (`` `abort `` positions append nothing) while the frontier still tracks the whole extent.
/// The current value of each of a store's carried keys, kept up to date by the
/// store's producer.
///
/// A store is where a program's mutable variables live, so this is the state a
/// replacement version inherits. It is a shared cell rather than something read
/// out of the producer because the producer is owned deep inside the operator
/// graph the replacement is about to drop, and its type is not recoverable from
/// the `dyn TileProducer` that holds it.
pub type StoreState = Rc<RefCell<HashMap<Value, Value>>>;

pub struct InductionStore {
    /// Per accumulator key, its runtime key and the acyclic operator producing
    /// its tick-0 fold default (the accumulator's init; read once at subscribe,
    /// like [`CommitOperator::with_init_ops`]). Written in `write_keys` order.
    init_ops: Vec<(Value, Box<dyn TileOperator>)>,
    /// The writer body `` λ (prev…, item) → {`commit{writes(, to_<defer>…)} | `abort} ``,
    /// compiled around a [`BodyInputSource`] over `buffer`.
    body_op: Box<dyn TileOperator>,
    /// The iteration source `Fun(D, item)` — the loop extent's items in order.
    source_op: Box<dyn TileOperator>,
    /// The body-input buffer the driver pushes `(prev…, item)` rows onto.
    buffer: BodyInputBuffer,
    /// Accumulator keys the body reads a snapshot of, in body-parameter order
    /// (for an induction store these are exactly the accumulators it writes).
    read_keys: Vec<Value>,
    /// Keys written, in decision-`writes` order: the carry keys, then
    /// any reply-tap (`to_<defer>`) keys.
    write_keys: Vec<Value>,
    /// Reply-tap decision fields, appended to each write set (see
    /// [`body_decision_at`]). Empty for a store with no feed.
    tap_fields: Vec<String>,
    output_tiling: Tiling,
    /// The carried keys' current values, for a replacement version to resume
    /// from. See [`StoreState`].
    state: StoreState,
}

impl InductionStore {
    /// Assemble an induction store. `init_ops`/`read_keys`/`write_keys` follow the
    /// same conventions as the commit store's writer, with `read_keys ==` the
    /// accumulator keys and `write_keys` the accumulators followed by tap keys.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        init_ops: Vec<(Value, Box<dyn TileOperator>)>,
        body_op: Box<dyn TileOperator>,
        source_op: Box<dyn TileOperator>,
        buffer: BodyInputBuffer,
        read_keys: Vec<Value>,
        write_keys: Vec<Value>,
        tap_fields: Vec<String>,
        key_extent: Extent,
        value_extent: Extent,
    ) -> Self {
        let output_tiling = full_store_tiling(&key_extent, &value_extent);
        Self {
            init_ops,
            body_op,
            source_op,
            buffer,
            read_keys,
            write_keys,
            tap_fields,
            output_tiling,
            state: StoreState::default(),
        }
    }

    /// The carried keys' current values, tracking this store as it runs.
    pub fn state(&self) -> StoreState {
        self.state.clone()
    }
}

impl TileOperator for InductionStore {
    fn tiling(&self) -> &Tiling {
        &self.output_tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward source/body progress to this store's consumer: an async loop
        // source (a data source arriving over scheduler notifications) delivers
        // its elements incrementally, and each arrival must wake a downstream
        // reader so it re-pulls and the drive loop processes the new positions.
        // Without this the store stalls at whatever prefix arrived by the first
        // pull (a batch/list source is complete on the first pull, so it never
        // needed the wiring — but an async source does). Kick once to start.
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        consumer.borrow_mut().notify();
        // Resolve each accumulator's tick-0 fold default. The init op is acyclic
        // (it never reads the store), so a single drain to a scalar is sound —
        // the same seeding path as `CommitOperator::with_init_ops`.
        let mut inits: HashMap<Value, Value> = HashMap::with_capacity(self.init_ops.len());
        for (key, mut op) in std::mem::take(&mut self.init_ops) {
            let g = op.tiling().universal_guard();
            let mut producer = op.subscribe(g, Box::new(|| {}), scheduler);
            let value = read_initial_scalar(&mut *producer).unwrap_or_else(|e| match e {
                InitDrainFailure::Empty => panic!(
                    "InductionStore: init op for accumulator {key:?} produced an empty scalar \
                     (no value to seed the accumulator)"
                ),
                InitDrainFailure::Diverged => panic!(
                    "InductionStore: init op for accumulator {key:?} never settled to a scalar \
                     within {MAX_INIT_PULLS} pulls (an acyclic init resolves on the first pull)"
                ),
            });
            inits.insert(key, value);
        }
        let source_producer = {
            let g = self.source_op.tiling().universal_guard();
            self.source_op
                .subscribe(g, Box::new(consumer.clone()), scheduler)
        };
        let body_producer = {
            let g = self.body_op.tiling().universal_guard();
            self.body_op
                .subscribe(g, Box::new(consumer.clone()), scheduler)
        };
        Box::new(InductionStoreProducer {
            base: ProducerBase::new(InductionStoreProducer::alloc_id(), &self.output_tiling),
            // Seed tick 0 with the accumulators' inits, so the changelog is
            // self-describing: `read_as_of`/`store_value_at` fold to the init below
            // the first *iteration* change (a leading carry) without an external
            // default. Iterations therefore occupy ticks 1.., a `+ 1` offset the
            // drive loop and the dense read both apply.
            engine: CommitEngine::new(inits.clone()),
            inits,
            state: self.state.clone(),
            body_producer,
            source_producer,
            buffer: self.buffer.clone(),
            read_keys: self.read_keys.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            output_tiling: self.output_tiling.clone(),
            processed: None,
            source_complete: false,
            released_through: None,
            source_fully_released: false,
        })
    }
}

struct InductionStoreProducer {
    base: ProducerBase,
    engine: CommitEngine,
    /// The accumulators' seed values, retained so the engine can be re-seeded at
    /// the first iteration position once it is known. See
    /// [`processed`](Self::processed).
    inits: HashMap<Value, Value>,
    /// The shared cell this producer keeps current, for a replacement version to
    /// resume from. See [`StoreState`].
    state: StoreState,
    body_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    buffer: BodyInputBuffer,
    read_keys: Vec<Value>,
    write_keys: Vec<Value>,
    tap_fields: Vec<String>,
    /// The full-store output tiling — for a debug-time shape check on the rendered
    /// store tile.
    output_tiling: Tiling,
    /// Iteration positions already fed to the body and stepped into the engine.
    /// Monotonic; the drive resumes here each pull as the source grows.
    ///
    /// `None` until the first pull that carries a position, then the base of the
    /// arrived run. It is not fixed at `0` because the source a store iterates
    /// need not begin there: a store built to replace one in a running program
    /// enrols with the source at its current frontier, so the first window it
    /// sees starts wherever the replaced version had reached. Starting at `0`
    /// against such a window finds no position to drive and the store emits
    /// nothing.
    processed: Option<usize>,
    /// Whether the iteration source is complete (its most recent pull was terminal). A
    /// batch source (a list — the usual loop extent) is complete on the first pull.
    source_complete: bool,
    /// Highest source position released back upstream (the reclaimed prefix). The
    /// drive drives positions strictly forward and never re-reads a position
    /// `< processed`, so that prefix is obsolete and released incrementally
    /// (bounding source retention on a long async loop, the same reclamation the
    /// dense `Recurse` path performed). A co-iterated reader still holding earlier
    /// positions keeps them live via the source's cross-producer release
    /// intersection. `None` until the first release.
    released_through: Option<usize>,
    /// Whether the whole source has been released (`True`) after the loop reached
    /// its terminal end-state — the finite loop's `get_released_predicate() == True`
    /// invariant; issued once.
    ///
    /// It also *ends the drive*: the release is only issued when the source is
    /// complete and every arrived position has been decided, so there is nothing
    /// left to read — a source honoring the release answers empty, and one that
    /// re-answers would have the drive re-fold positions it already decided.
    /// Later pulls serve the accumulated store, which is already the whole answer
    /// (the same promise the dense `Recurse` path kept once its recurrence
    /// converged).
    source_fully_released: bool,
}

impl InductionStoreProducer {
    /// The engine's accumulated store as a tile, marked `terminal` once the
    /// recurrence is final (the accumulator can no longer change, so a downstream
    /// `ExtractLast` / `final_or_default` resolves).
    fn render_store(&self, recurrence_final: bool) -> Tile {
        let mut store = self.engine.render_full_store_tile();
        if recurrence_final && let Tile::Store { terminal, .. } = &mut store {
            *terminal = true;
        }
        debug_assert!(
            store.check_from(&self.output_tiling),
            "rendered induction store tile does not match the full-store tiling"
        );
        store
    }
}

impl TileProducer for InductionStoreProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // The drive is over once the source has been universally released: pulling
        // it again would break that release's promise, and every position is already
        // decided, so the accumulated store is the whole answer.
        if self.source_fully_released {
            return self.render_store(true);
        }
        let src = self
            .source_producer
            .get(self.source_producer.tiling().universal_guard());
        self.source_complete = src.is_terminal();
        // Pair each item with its absolute domain position and sort. An async
        // source's domain arrives unordered, so we drive by position, not by the
        // codomain's column order (see [`decode_source_positioned`]).
        let by_pos: HashMap<usize, Value> = decode_source_positioned(&src).into_iter().collect();
        // Invariant: an induction source domain has **no interior hole** — a
        // finite list `[0, N)` or an async `DataSource`'s UInt domain only ever
        // gaps at the *trailing* end (positions not yet arrived). The drive relies
        // on this (it stops at the first missing `processed` and resumes when it
        // arrives); a permanent interior hole would stall forever. The arrived set
        // is *not* a prefix from 0: `get_impl` releases the consumed prefix below,
        // so a later pull sees a shifted window (e.g. `{5, 6, 7}`). Assert the
        // sorted positions form a contiguous run from their retained base instead.
        debug_assert!(
            !self.source_complete || {
                let mut ks: Vec<usize> = by_pos.keys().copied().collect();
                ks.sort_unstable();
                ks.windows(2).all(|w| w[1] == w[0] + 1)
            },
            "induction source domain has an interior gap: {:?}",
            {
                let mut ks: Vec<usize> = by_pos.keys().copied().collect();
                ks.sort_unstable();
                ks
            }
        );
        // Drive each not-yet-processed position **in contiguous order**. Tick 0 is
        // the seeded init, so iteration `pos` occupies tick `pos + 1`: it reads the
        // previous accumulator as of tick `pos` (the init at `pos == 0`, else the
        // latest change ≤ that tick — a leading carry inherits the seed), feeds the
        // body, and steps tick `pos + 1`. The engine must be stepped through `pos`
        // before we fold, hence the sequential push-body-step loop. The body's
        // decision gates commit (append the change) vs carry (`step(_, None)` — the
        // value inherits from tick 0 / the latest earlier change). Stop at the first
        // gap (position `processed` not yet arrived): the recurrence is sequential,
        // so a later position cannot be decided before its predecessor.
        // The base of the arrived run on the first pull that has one; afterwards
        // the drive's own monotonic cursor.
        let mut next = match self.processed {
            Some(next) => next,
            None => match by_pos.keys().copied().min() {
                // The seed belongs at the tick this first position reads, not at
                // tick 0. See [`CommitEngine::seeded_at`].
                Some(base) => {
                    if base > 0 {
                        self.engine = CommitEngine::seeded_at(base, self.inits.clone());
                    }
                    base
                }
                // Nothing has arrived. Fall through with the cursor unset so the
                // terminality check below still runs: an empty source is complete
                // on its first pull, and returning early here leaves a loop over
                // one waiting for a notification that never comes.
                None => 0,
            },
        };
        while let Some(item) = by_pos.get(&next) {
            let pos = next;
            let snap_in: Vec<Value> = self
                .read_keys
                .iter()
                .map(|k| {
                    self.engine
                        .read_as_of(pos, k)
                        .expect("tick 0 seeds every accumulator, so a prev read always resolves")
                })
                .collect();
            self.buffer.borrow_mut().rows.push((snap_in, item.clone()));
            let body_tile = self
                .body_producer
                .get(self.body_producer.tiling().universal_guard());
            let Some((commit, writes, tap_fired)) =
                body_decision_at(&body_tile, pos, &self.tap_fields)
            else {
                // The decision for a freshly-pushed row of a self-contained
                // induction body is always ready on the pull. A `None` means the
                // body has not converged at this position — for the loop shapes
                // that reach here (no cross-loop broadcast in the body) this does
                // not happen, so stop the drive and re-render; the harness re-pulls
                // a non-terminal store to make progress.
                break;
            };
            let write_set: Option<HashMap<Value, Value>> = if commit {
                debug_assert_eq!(
                    writes.len(),
                    self.write_keys.len(),
                    "the decision's write set aligns with the store's write keys"
                );
                // Carry writes lead, taps follow (the layout `build_induction_
                // store_single` sets). A committing position applies every carry
                // write but only the taps that *fired* on its route — a non-fired
                // conditional feed is omitted from the delta, so its per-position
                // read (`store_delta_at`) skips this position. `commit` is true
                // whenever a tap fires (the letrec phase folds feed-fire paths into
                // the commit gate), so a fired tap always rides an appended change.
                // Layout invariant (as on the transaction side): `write_keys` =
                // carry keys ++ tap keys, so the subtraction never underflows —
                // a break would wrap `n_reg` to a huge value in release and
                // mis-index `tap_fired`.
                debug_assert!(
                    self.write_keys.len() >= self.tap_fields.len(),
                    "induction store: tap fields ({}) exceed write keys ({})",
                    self.tap_fields.len(),
                    self.write_keys.len()
                );
                let n_reg = self.write_keys.len() - self.tap_fields.len();
                Some(
                    self.write_keys
                        .iter()
                        .cloned()
                        .zip(writes)
                        .enumerate()
                        .filter(|(i, _)| *i < n_reg || tap_fired[*i - n_reg])
                        .map(|(_, kv)| kv)
                        .collect(),
                )
            } else {
                // Carry: no change is appended, so a tap (fired or not) contributes
                // nothing at this position — an *ungated* tap (one whose fire path
                // is the commit itself, so it carries no `__fire` gate) reads
                // `tap_fired = true` by default, but a carry position records it
                // nowhere, which is correct: the letrec phase folds every feed-fire
                // path into `commit`, so a position that genuinely fires a tap
                // commits (and takes the branch above) rather than carrying here.
                None // the accumulator holds from tick 0 / the latest change
            };
            self.engine.step(pos + 1, write_set);
            next = pos + 1;
            self.processed = Some(next);
        }
        // Incrementally reclaim the processed prefix of the source. The drive only
        // ever pulls position `processed` forward and never re-reads a position
        // `< processed`, so `[0, processed)` is obsolete to *this* producer;
        // releasing it bounds source retention on a long async loop (matching the
        // dense `Recurse` path). The source drops a row only once every producer
        // releases it (cross-producer intersection), so a co-iterated reader still
        // folding earlier positions keeps them live.
        let unused = self
            .processed
            .is_none_or(|p| p == 0 || self.released_through.is_some_and(|r| r + 1 >= p));
        if !unused {
            let through = next - 1;
            self.source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::LessThanEq(Value::UInt(through)),
                )));
            self.released_through = Some(through);
        }
        // Publish the accumulators' current values for a replacement version to
        // resume from. `read_keys` is exactly the carried accumulators — a reply
        // tap is a per-position event with nothing to carry — and the watermark
        // is the latest decided tick, so this is each variable's value now.
        if self.processed.is_some() {
            let watermark = self.engine.watermark();
            let mut state = self.state.borrow_mut();
            for key in &self.read_keys {
                if let Some(value) = self.engine.read_as_of(watermark, key) {
                    state.insert(key.clone(), value);
                }
            }
        }
        // Signal terminality once the source is complete and every arrived position
        // has been decided: the accumulator is final, so the frontier *closes*
        // (`terminal`) and a downstream `ExtractFinal`/`final_or_default` resolves.
        // The frontier keeps its `LessThanEq(w)` watermark, which spans the whole
        // extent including a trailing run of carries — so `len`/`store_frontier`
        // no longer undercount to the latest change tick when the tail is all carry.
        // A terminal source has a gapless domain, so having driven every contiguous
        // position (`by_pos` no longer holds `processed`) means the whole extent is
        // decided — robust to the incremental prefix release above shrinking
        // `by_pos`.
        let done = self.source_complete && !by_pos.contains_key(&next);
        // Final reclamation: once terminal, release the *whole* source (`True`) so a
        // finite loop reaches the `get_released_predicate() == True` end-state (the
        // incremental prefix release above stops one short of a `True` predicate).
        if done && !self.source_fully_released {
            self.source_producer
                .release(TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
            self.source_fully_released = true;
        }
        self.render_store(done)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Keep-latest changelog GC (mirrors [`CommitProducer::release_impl`]). The
        // store sits behind a `FanOut`, so this guard is the **intersection** of
        // what every reader (dense accumulator reads, reply-tap reads) has released
        // — the tick prefix safe to reclaim. `gc_released_prefix` drops the
        // superseded entries in that prefix but **keeps each key's latest write**,
        // which is exactly what the drive's own recurrence needs (`read_as_of(
        // processed)` folds to the latest ≤ processed), so the GC never strands the
        // recurrence — bounding a never-terminating streaming loop's changelog to
        // O(keys) + the slowest reader's lag. (A scalar-final `ExtractFinal` reader
        // holds the whole stream until terminal, so it releases nothing early — but
        // that read is inherently non-terminating over an endless source anyway.)
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(through) = max_released_tick(pred)
        {
            self.engine.gc_released_prefix(through);
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
/// finish. Its `domain_predicate` mirrors the store's (`LessThanEq(watermark)`
/// while committing, `True` once terminal), so terminality flows through.
///
/// This backs the **in-block reply tap** (`out << e` inside a block —
/// `carry_forward: false`, one entry per commit tick), the **read-your-writes
/// mutable variable carry** (`carry_forward: true`, the latest write ≤ each tick), and the
/// **terminal read**: a surface `await_final(x)` reduces this stream with
/// [`ExtractFinal`](crate::interpreter::tile_operators::ExtractFinal), which resolves
/// once the store flips `terminal` below. A read fed *out* of a block does not reduce
/// it — it folds the store as-of via [`AsOf`] instead, sampling an arbitrary commit
/// position. One stream, two reducers, selected by the term the program wrote.
pub struct StoreValueStream {
    tiling: Tiling,
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
        Self {
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(value_extent.clone())),
            },
            store_op,
            key,
            value_extent,
            carry_forward,
        }
    }
}

impl TileOperator for StoreValueStream {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward store progress to this stream's consumer: a new commit on the
        // store (e.g. a live cross-endpoint read-only transaction committing its
        // reply tap) must wake the downstream sink so it re-pulls and sees the new
        // value. Without this, a tap/key reader off a live commit store is only
        // woken once (the kick) and never again. The store starts at its tick-0
        // value, so kick once to start the drain loop.
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        consumer.borrow_mut().notify();
        let g = self.store_op.tiling().universal_guard();
        let store_producer = self
            .store_op
            .subscribe(g, Box::new(consumer.clone()), scheduler);
        Box::new(StoreValueStreamProducer {
            base: ProducerBase::new(StoreValueStreamProducer::alloc_id(), &self.tiling),
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
        // terminality flows through the store's `terminal` flag below.
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // Fold the changelog directly. Terminality flows to this stream: a closed
        // store (`terminal`) yields a `True` output domain predicate so a
        // downstream terminal read resolves; a live store carries its `LessThanEq`
        // watermark through.
        let Tile::Store {
            changes,
            frontier,
            terminal,
            ..
        } = &store
        else {
            return self.tiling().empty_tile();
        };
        let domain_predicate = if *terminal {
            Predicate::True
        } else {
            frontier.clone()
        };
        // Fold the changelog to `key`'s value under the carry policy
        // ([`fold_changelog_key_ascending`], shared with the induction
        // `StoreDenseRead`): a carry holds the latest write ≤ the tick; a
        // reply tap emits only the tick that wrote it (carrying it forward would
        // smear one writer's reply across another's commit ticks on the shared
        // clock). One O(changes) ascending pass folds every tick — the released
        // prefix is still walked so the carry is built correctly, then dropped at
        // emit time (the accumulating consumer has already merged it).
        let all_ticks: Vec<usize> = (0..changes.len())
            .filter_map(|i| match changes.index_at(i) {
                Value::UInt(tick) => Some(tick),
                _ => None,
            })
            .collect();
        let folded = fold_changelog_key_ascending(
            &store,
            all_ticks.iter().copied(),
            &self.key,
            self.carry_forward,
        );
        let mut ticks: Vec<usize> = Vec::with_capacity(all_ticks.len());
        let mut values: Vec<Value> = Vec::with_capacity(all_ticks.len());
        for (tick, v) in all_ticks.iter().zip(folded) {
            if self.release_cursor.is_released(*tick) {
                continue;
            }
            if let Some(v) = v {
                ticks.push(*tick);
                values.push(v);
            }
        }
        Tile::SealedFunction {
            domain: ColumnValue::from_uints(ticks),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                values,
                &self.value_extent,
            ))),
            domain_predicate: domain_predicate.clone(),
            deleted: bit_set::BitSet::new(),
        }
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
                    Some(Predicate::LessThanEq(Value::UInt(max_tick)))
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

/// The **terminal read** of a transactional mutable variable: `key`'s value at the
/// position its own writers finish, or the store's seed if no commit wrote it.
///
/// A Txn read samples the key's carried value; this one's position is where the key
/// closes. It takes the same sample [`AsOf`] does, through the same
/// [`store_current`] — the difference is what fixes the position: a trigger arrival
/// there, the store's own closure here. So it is neither a reduction nor a
/// projection of the history, and needs no seed operand, because tick 0 of the
/// changelog holds the seed.
pub struct StoreFinalRead {
    /// Output tiling `Scalar(V)` — a terminal read is one value, not a stream.
    tiling: Tiling,
    /// The commit store (a [`Tile::Store`] fan branch).
    store_op: Box<dyn TileOperator>,
    /// The key whose settled value this reads.
    key: Value,
    value_extent: Extent,
}

impl StoreFinalRead {
    pub fn new(store_op: Box<dyn TileOperator>, key: Value, value_extent: Extent) -> Self {
        Self {
            tiling: Tiling::Scalar(value_extent.clone()),
            store_op,
            key,
            value_extent,
        }
    }
}

impl TileOperator for StoreFinalRead {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("store", self.store_op.inspect(opts))
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Forward store progress downstream, as [`StoreValueStream`] does: the key is
        // not settled until the store says so, and the consumer has to be woken to
        // re-pull when that happens. Kick once to start the drain loop.
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        consumer.borrow_mut().notify();
        let g = self.store_op.tiling().universal_guard();
        let store_producer = self
            .store_op
            .subscribe(g, Box::new(consumer.clone()), scheduler);
        Box::new(StoreFinalReadProducer {
            base: ProducerBase::new(StoreFinalReadProducer::alloc_id(), &self.tiling),
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
        if !store.is_terminal() {
            // A writer may still commit, so the key has no settled value to report.
            // An empty scalar is non-terminal, so the consumer pulls again.
            return self.tiling().empty_tile();
        }
        // `store_current` bounds the sample at the decided frontier; a key no commit
        // wrote folds to tick 0's seed.
        let value = store_current(&store, &self.key).map(|(_, v)| v);
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

/// A **dense** induction-accumulator read: `key`'s value at *every* position of
/// the loop extent `D`, folded from the [`Tile::Store`] changelog —
/// `Fun(D, V)` where position `p ↦ store_value_at(store, p, key)` (carry-forward,
/// defaulting to `init` below the first change).
///
/// This is the induction counterpart of [`StoreValueStream`] (a commit
/// carry's per-tick stream). The difference is the domain: a carry stream
/// is indexed by *commit tick* (sparse change events), but an induction
/// accumulator co-iterated into another store (e.g. `for r in …: cnt += 1; with
/// begin(): store := store + cnt`) must present a *dense* function over the loop
/// extent so it aligns (via `fan_in`) with the co-iterated `iter`. Because
/// [`store_value_at`] folds by scanning changes `≤ p` — **independent of the
/// store's frontier** — this reads every position correctly even across a
/// trailing run of carries, so it needs neither the frontier watermark nor the
/// extent recorded on the tile: the positions come from the `trigger`
/// (`IterateExtent`-style enumeration of `D`), the values from the fold.
///
/// A scalar-final read (`total` after the loop) is `ExtractFinal` over this dense
/// stream; a co-iterated read is the stream itself — one reader serves both.
///
/// The per-tick fold — a carry holds, a tap is a delta event — is the shared
/// [`fold_changelog_key`]; this reader and [`StoreValueStream`] are the same
/// changelog projection differing only on *which* ticks they fold (loop positions
/// at `p + 1` here, commit ticks there) and how they emit (full re-emit here for
/// `fan_in`/`ExtractFinal`; delta-once there for `Memo`-accumulating consumers).
pub struct StoreDenseRead {
    /// Output tiling `SealedFunction { domain: D, codomain: Scalar(V) }`.
    tiling: Tiling,
    /// Enumerates the loop extent `D` (its positions drive the output domain, so
    /// it aligns with any co-iterated source over the same `D`).
    trigger: Box<dyn TileOperator>,
    /// The induction store (a [`Tile::Store`] fan branch).
    store_op: Box<dyn TileOperator>,
    /// The key to project.
    key: Value,
    value_extent: Extent,
    /// Whether the key carries its value forward across positions that do not
    /// write it. An **accumulator** (`true`) folds the latest write ≤ each
    /// position (`store_value_at`), so every trigger position has a value. A
    /// **reply tap** (`false`) is a per-position event: it appears only at the
    /// position whose changelog delta actually wrote it (`store_delta_at`), so the
    /// dense read emits the fired subset of positions.
    carry_forward: bool,
}

impl StoreDenseRead {
    pub fn new(
        trigger: Box<dyn TileOperator>,
        store_op: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
        carry_forward: bool,
    ) -> Self {
        let Tiling::SealedFunction { domain, .. } = trigger.tiling() else {
            panic!(
                "StoreDenseRead trigger must be a SealedFunction (the loop extent), got {}",
                trigger.tiling()
            );
        };
        debug_assert!(
            matches!(store_op.tiling(), Tiling::Store { .. }),
            "StoreDenseRead source must be a Store, got {}",
            store_op.tiling()
        );
        let tiling = Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(value_extent.clone())),
        };
        Self {
            tiling,
            trigger,
            store_op,
            key,
            value_extent,
            carry_forward,
        }
    }
}

impl TileOperator for StoreDenseRead {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Wake the consumer on store progress (a new decided position) and on
        // trigger progress. Route both through a shared notifier, and kick once.
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        consumer.borrow_mut().notify();
        let trigger_producer = {
            let g = self.trigger.tiling().universal_guard();
            self.trigger
                .subscribe(g, Box::new(consumer.clone()), scheduler)
        };
        let store_producer = {
            let g = self.store_op.tiling().universal_guard();
            self.store_op
                .subscribe(g, Box::new(consumer.clone()), scheduler)
        };
        Box::new(StoreDenseReadProducer {
            base: ProducerBase::new(StoreDenseReadProducer::alloc_id(), &self.tiling),
            trigger_producer,
            store_producer,
            key: self.key.clone(),
            value_extent: self.value_extent.clone(),
            carry_forward: self.carry_forward,
            key_write_ticks: Vec::new(),
        })
    }
}

struct StoreDenseReadProducer {
    base: ProducerBase,
    trigger_producer: Box<dyn TileProducer>,
    store_producer: Box<dyn TileProducer>,
    carry_forward: bool,
    key: Value,
    value_extent: Extent,
    /// Ascending ticks at which `key` was written, cached from the previous fold. A
    /// carry read's [`Self::release_impl`] uses it to find the carry source of the
    /// earliest still-needed position — the store prefix it can safely release.
    key_write_ticks: Vec<usize>,
}

impl TileProducer for StoreDenseReadProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // The loop-extent positions (the output domain) — the same positions a
        // co-iterated `iter` presents, so the two `fan_in` cleanly.
        let trigger = self
            .trigger_producer
            .get(self.trigger_producer.tiling().universal_guard());
        let Tile::SealedFunction {
            domain: positions,
            domain_predicate: trigger_pred,
            ..
        } = trigger
        else {
            return self.tiling().empty_tile();
        };
        // Sample the induction store once (consumer-driven; no producer-side
        // drive-to-fixpoint), then fold `key` at each position. The induction writer
        // drives its whole loop per pull (every arrived position steps the engine in
        // one `get_impl`), so a batch source converges in this single sample; an
        // async source's later arrivals re-pull us through the store's
        // source-forwarding consumer. Iterations occupy ticks 1.. (tick 0 is the
        // seeded init), so loop position `p` reads tick `p + 1` — the accumulator
        // *after* iteration `p`. `store_value_at` scans changes ≤ that tick, so a
        // carry position inherits the latest earlier write, and a leading carry folds
        // to the tick-0 init — no external default needed, and never `None` (tick 0
        // is seeded). The `store.is_terminal()` gate below keeps this read
        // non-terminal until the store is fully decided, so the consumer re-pulls.
        let sg = self.store_producer.tiling().universal_guard();
        let store = self.store_producer.get(sg);
        // Sort the trigger's positions ascending before folding. An async source's
        // iteration domain arrives in arbitrary (set) order, but the dense read's
        // output domain must be position-ordered: a scalar-final read is
        // `ExtractFinal` over this stream — the *final column* — which is the final
        // accumulator only if the highest loop position is last. (A co-iterated
        // read aligns by domain *value* via `fan_in`, so ordering is immaterial
        // there; sorting is correct for both.)
        let mut sorted: Vec<usize> = (0..positions.len())
            .map(|i| match positions.index_at(i) {
                Value::UInt(p) => p,
                _ => unreachable!("induction loop-extent positions are UInt"),
            })
            .collect();
        sorted.sort_unstable();
        // Fold `key` at every position's tick `p + 1` in one ascending pass (the
        // shared [`fold_changelog_key_ascending`]): an accumulator carries the
        // latest write ≤ that tick (every position resolves — tick 0 seeds it); a
        // reply tap yields a value only where that tick actually wrote it, so a
        // non-firing position is omitted (the feed's per-position stream over
        // exactly the fired positions). One O(changes + positions) pass, not an
        // O(changes)-per-position re-scan.
        let folded = fold_changelog_key_ascending(
            &store,
            sorted.iter().map(|p| p + 1),
            &self.key,
            self.carry_forward,
        );
        debug_assert!(
            !self.carry_forward || folded.iter().all(Option::is_some),
            "tick 0 seeds every accumulator, so the carry fold always resolves"
        );
        let mut kept: Vec<usize> = Vec::with_capacity(sorted.len());
        let mut values: Vec<Value> = Vec::with_capacity(sorted.len());
        for (p, v) in sorted.iter().zip(folded) {
            if let Some(v) = v {
                kept.push(*p);
                values.push(v);
            }
        }
        let positions = ColumnValue::from_uints(kept);
        // Cache the (ascending) ticks that wrote `key`, so a carry read's release
        // can find the carry source of the first still-needed position. Only a
        // carry read back-references earlier ticks; a tap needs no such cache.
        if self.carry_forward
            && let Tile::Store {
                changes, deltas, ..
            } = &store
        {
            self.key_write_ticks = (0..changes.len())
                .filter_map(|i| match changes.index_at(i) {
                    Value::UInt(t) if value_to_map(&deltas.index_at(i)).contains_key(&self.key) => {
                        Some(t)
                    }
                    _ => None,
                })
                .collect();
        }
        // The dense read is decided over `D` once the store is terminal (every
        // position folded to its final value); until then it tracks the trigger's
        // own completion but stays non-terminal so the consumer re-pulls.
        let domain_predicate = if store.is_terminal() {
            trigger_pred
        } else {
            Predicate::False
        };
        Tile::SealedFunction {
            domain: positions,
            codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                values,
                &self.value_extent,
            ))),
            domain_predicate,
            deleted: bit_set::BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A downstream release of loop positions `≤ max_pos` is a promise never to
        // request them again, so we forward whatever the store no longer needs — a
        // decision derived purely from the release, not from who the consumer is.
        //
        // The **trigger** (the iteration source) is always released `≤ max_pos`: a
        // consumed async `DataSource` / finite list is reclaimed.
        //
        // The **store** release depends on the read mode, because it decides which
        // ticks a *future* fold can still reach:
        // - A **tap** read (`carry_forward: false`) reads only tick `p + 1`'s delta
        //   at position `p` — no back-reference — so positions `≤ max_pos` make ticks
        //   `≤ max_pos + 1` dead.
        // - A **carry** read (`carry_forward: true`) reads the latest write `≤` each
        //   position's tick. The earliest still-needed position is `max_pos + 1`
        //   (reading tick `max_pos + 2`); its **carry source** is the latest write to
        //   `key` at a tick `≤ max_pos + 2`, and the carry source only moves forward
        //   for later positions. So every tick *strictly below* that carry source is
        //   dead for all future positions — and nothing above it is released, so the
        //   engine's keep-latest GC never drops a live carry source. This bounds the
        //   changelog for *any* carry consumer (scalar-final or co-iterated) without
        //   the producer knowing which it is.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard {
            if let Some(max_pos) = max_released_tick(pred) {
                let store_release_upto = if self.carry_forward {
                    let need_tick = max_pos + 2;
                    // Carry source = latest write to `key` at tick ≤ need_tick;
                    // release strictly below it (the seed at tick 0 bounds this).
                    self.key_write_ticks
                        .iter()
                        .rev()
                        .find(|&&t| t <= need_tick)
                        .and_then(|&carry_source| carry_source.checked_sub(1))
                } else {
                    Some(max_pos + 1)
                };
                if let Some(upto) = store_release_upto {
                    self.store_producer
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::LessThanEq(Value::UInt(upto)),
                        )));
                }
            }
            self.trigger_producer.release(obsolete_guard);
        }
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
/// (which the immutability invariant forbids). It is the dual of the commit
/// `Recurse`: `Recurse` latches a private accumulator per *source* step; `AsOf`
/// latches the store's current value per *trigger* step.
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
    /// A single mutable variable → scalar codomain `Fun(B, Scalar(V))` — the bare or
    /// computed single-variable as-of read.
    Scalar { key: Value, value_extent: Extent },
    /// A whole-snapshot record → `Fun(B, Record{field: Scalar(V)})` — the
    /// multi-variable as-of read. Every field is folded from a single source render
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
    /// The codomain tiling (`Scalar(V)` or `Record{field: Scalar(V)}`).
    fn codomain_tiling(&self) -> Tiling {
        match self {
            AsOfOutput::Scalar { value_extent, .. } => Tiling::Scalar(value_extent.clone()),
            AsOfOutput::Record { fields } => Tiling::Record(
                fields
                    .iter()
                    .map(|f| (f.field.clone(), Tiling::Scalar(f.value_extent.clone())))
                    .collect(),
            ),
        }
    }
}

pub struct AsOf {
    /// Output tiling: `SealedFunction { domain: B, codomain }` where `codomain`
    /// is `Scalar(V)` (single mutable variable) or `Record{field: Scalar(V)}` (snapshot).
    tiling: Tiling,
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
    /// `Fun(B, Scalar(value_extent))`.
    pub fn new(
        trigger: Box<dyn TileOperator>,
        source: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
    ) -> Self {
        Self::build(trigger, source, AsOfOutput::Scalar { key, value_extent })
    }

    /// The multi-variable **snapshot** read: sample every `field`'s mutable variable at
    /// one commit snapshot → output `Fun(B, Record{field: Scalar(V)})`, from which
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
        let Tiling::SealedFunction { domain: b_ext, .. } = trigger.tiling() else {
            panic!(
                "AsOf trigger must be a SealedFunction, got {}",
                trigger.tiling()
            );
        };
        debug_assert!(
            matches!(source.tiling(), Tiling::Store { .. }),
            "AsOf source must be a commit Store, got {}",
            source.tiling()
        );
        let tiling = Tiling::SealedFunction {
            domain: b_ext.clone(),
            codomain: Box::new(output.codomain_tiling()),
        };
        Self {
            tiling,
            trigger,
            source,
            output,
        }
    }
}

impl TileOperator for AsOf {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("trigger", self.trigger.inspect(opts))
            .child("source", self.source.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Both inputs wake the consumer: a new *trigger* position needs a fresh
        // latch, and *source* progress (a new commit) is what lets an
        // already-seen trigger position finally latch a value — and, crucially,
        // re-pulls until the cyclic store converges (the source's first pull may
        // only propose; later pulls commit and render).
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        let tg = self.trigger.tiling().universal_guard();
        let trigger = self
            .trigger
            .subscribe(tg, Box::new(consumer.clone()), scheduler);
        let sg = self.source.tiling().universal_guard();
        let source = self
            .source
            .subscribe(sg, Box::new(consumer.clone()), scheduler);
        let b_extent = match &self.tiling {
            Tiling::SealedFunction { domain, .. } => domain.clone(),
            _ => unreachable!("AsOf tiling is SealedFunction"),
        };
        Box::new(AsOfProducer {
            base: ProducerBase::new(AsOfProducer::alloc_id(), &self.tiling),
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
        matches!(b, Value::UInt(u) if self.release_cursor.is_released(*u))
    }

    /// Build the output tile from the currently-latched `(b ↦ snapshot)` pairs,
    /// under `domain_predicate`. The latched set is already compacted of released
    /// positions, so it emits exactly the live response window. The codomain is a
    /// `Scalar` column (single mutable variable) or a `Record` of per-field `Scalar`
    /// columns (snapshot), each column indexed by the emitted domain position.
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
            AsOfOutput::Scalar { value_extent, .. } => Tile::Scalar(ColumnValue::from_values(
                cols.into_iter().next().unwrap_or_default(),
                value_extent,
            )),
            AsOfOutput::Record { fields } => Tile::Record(
                fields
                    .iter()
                    .zip(cols)
                    .map(|(f, col)| {
                        (
                            f.field.clone(),
                            Tile::Scalar(ColumnValue::from_values(col, &f.value_extent)),
                        )
                    })
                    .collect(),
            ),
        };
        Tile::SealedFunction {
            domain: ColumnValue::from_values(bs, &self.b_extent),
            codomain: Box::new(codomain),
            // Terminality rides with the trigger: when no more requests will
            // arrive (trigger terminal) the response set is complete.
            domain_predicate,
            deleted: bit_set::BitSet::new(),
        }
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
        // every scalar mutable variable is seeded at tick 0 (`init_ops`), so `store_current`
        // always has a decided value once the store has committed its seeds — no
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
            Tile::SealedFunction {
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
        if let (Tile::SealedFunction { domain, .. }, Some(snap)) = (&trigger_tile, &snapshot) {
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
        // `CommitProducer` GCs the `FanOut`-intersected prefix (keep-latest). We
        // keep the frontier tick itself so the fold still finds each key's value.
        if let Some(f) = frontier
            && f > 0
        {
            self.source
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::LessThanEq(Value::UInt(f - 1)),
                )));
        }
        // Terminality gate. With the producer-side drive-to-fixpoint retired, this
        // reader samples one watermark per pull and relies on being re-pulled (via the
        // writer's wakeup fanning through the cyclic `FanOut`) to converge. So it must stay
        // **non-terminal** until the store itself is terminal, or it could report "done"
        // while the store is still committing and freeze a store no other consumer drives.
        //
        // The unlatched-position half covers the one way a terminal store can still owe a
        // value: the snapshot above is all-or-nothing, so a key with no decided value
        // withholds it. Every present position latches on the pull that finds a snapshot,
        // which is why this is otherwise false by the time the gate reads it.
        let has_unlatched_position = matches!(&trigger_tile, Tile::SealedFunction { domain, .. }
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
                        let drop = matches!(b, Value::UInt(u) if *u <= w);
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

/// Shared body-input feed for the fused [`TransactWriter`]: a sliding window of
/// `(store snapshot, item)` rows the writer appends to and feeds its body
/// through [`BodyInputSource`]. The body still consumes a `Tile` via `get`; this
/// is just how the writer constructs that input incrementally (analogous to how
/// `Recurse` feeds its body).
///
/// `base` is the absolute position of `rows[0]`: rows the writer has already
/// consumed (read the body decision for) are compacted away, so the body-input
/// stays bounded on a long-lived store. Positions are absolute and stable —
/// [`BodyInputSource`] emits them as the domain and [`body_decision_at`] looks a
/// row up by value, not by column position.
#[derive(Default)]
pub struct WriterBuffer {
    /// Absolute position of `rows[0]` — the count of consumed rows dropped.
    pub base: usize,
    /// The live `(snapshot, item)` rows; `rows[i]` is absolute position `base + i`.
    pub rows: Vec<(Vec<Value>, Value)>,
}

pub type BodyInputBuffer = Rc<RefCell<WriterBuffer>>;

/// The writer body's input: serves the buffer as
/// `SealedFunction(UInt → {_0: snap_{k₀}, …, _{r-1}: snap_{k_{r-1}}, _r: item})`
/// — the flat `(snapshot…, item)` tuple the body's `let kᵢ = p.i … let item =
/// p.r` shape expects (read keys followed by the iteration item). Idempotent: a
/// pull returns the current buffer, so it is safe to read repeatedly within a
/// round.
pub struct BodyInputSource {
    tiling: Tiling,
    buffer: BodyInputBuffer,
    read_extents: Vec<Extent>,
    item_extent: Extent,
}

impl BodyInputSource {
    pub fn new(buffer: BodyInputBuffer, read_extents: Vec<Extent>, item_extent: Extent) -> Self {
        let tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Record(body_input_fields(
                &read_extents,
                &item_extent,
                Tiling::Scalar,
            ))),
        };
        Self {
            tiling,
            buffer,
            read_extents,
            item_extent,
        }
    }
}

/// The body-input codomain fields `{_0..._{r-1}: read, _r: item}`, built over
/// either tilings (`f = Tiling::Scalar`) or tiles. `r = read_extents.len()`.
fn body_input_fields<T>(
    read_extents: &[Extent],
    item_extent: &Extent,
    f: impl Fn(Extent) -> T,
) -> HashMap<String, T> {
    let mut fields: HashMap<String, T> = HashMap::with_capacity(read_extents.len() + 1);
    for (i, ext) in read_extents.iter().enumerate() {
        fields.insert(tuple_field(i), f(ext.clone()));
    }
    fields.insert(tuple_field(read_extents.len()), f(item_extent.clone()));
    fields
}

impl TileOperator for BodyInputSource {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        _consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(BodyInputSourceProducer {
            base: ProducerBase::new(BodyInputSourceProducer::alloc_id(), &self.tiling),
            buffer: self.buffer.clone(),
            read_extents: self.read_extents.clone(),
            item_extent: self.item_extent.clone(),
            release_cursor: PrefixReleaseCursor::default(),
        })
    }
}

struct BodyInputSourceProducer {
    base: ProducerBase,
    buffer: BodyInputBuffer,
    read_extents: Vec<Extent>,
    item_extent: Extent,
    /// Highest absolute buffer position a consumer has released. The body op fans
    /// this source through a `FanOut`/`Memo` that pulls it repeatedly within one
    /// round (once per fanned use — the `{commit, writes}` decision reads it in
    /// several places); re-emitting an already-released position would make the
    /// `Memo`'s append-merge duplicate that domain position (an invalid tile).
    /// Emitting only positions past this cursor makes the source delta-producing,
    /// exactly as the induction body's `fan_in` input is — so repeated pulls
    /// after a release contribute nothing.
    release_cursor: PrefixReleaseCursor,
}

impl TileProducer for BodyInputSourceProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let buf = self.buffer.borrow();
        // Emit only unreleased rows (absolute position `base + i > released`).
        let start = match self.release_cursor.through() {
            Some(r) if r >= buf.base => (r + 1 - buf.base).min(buf.rows.len()),
            _ => 0,
        };
        let live = &buf.rows[start..];
        // `_i` (i < r) is read-key i's snapshot column; `_r` is the item column.
        let mut fields: HashMap<String, Tile> = HashMap::with_capacity(self.read_extents.len() + 1);
        for (i, ext) in self.read_extents.iter().enumerate() {
            fields.insert(
                tuple_field(i),
                Tile::Scalar(ColumnValue::from_values(
                    live.iter().map(|(olds, _)| olds[i].clone()).collect(),
                    ext,
                )),
            );
        }
        fields.insert(
            tuple_field(self.read_extents.len()),
            Tile::Scalar(ColumnValue::from_values(
                live.iter().map(|(_, item)| item.clone()).collect(),
                &self.item_extent,
            )),
        );
        Tile::SealedFunction {
            // Absolute positions: the window starts at `base` (consumed rows
            // compacted away), so `body_decision_at` finds a row by value.
            domain: ColumnValue::from_uints(
                (buf.base + start..buf.base + buf.rows.len()).collect(),
            ),
            codomain: Box::new(Tile::Record(fields)),
            // Never terminal: the buffer keeps growing (one attempt per round),
            // so the body must re-read it each pull rather than cache a
            // "complete" result.
            domain_predicate: Predicate::False,
            deleted: bit_set::BitSet::new(),
        }
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Advance the emit cursor past released positions so a re-pull (the
        // fanned body reads this source several times per round) does not
        // re-emit and duplicate a domain position through the `Memo` merge.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(max) = max_released_tick(pred)
        {
            self.release_cursor.advance_to(max);
        }
    }
}

/// The `commit` tag of the decision variant `` {`commit{𝑃} | `abort} ``. A union
/// column keys its arms by name, so the decode matches the tag the CCL side
/// built and neither end depends on the variant's arm order.
fn is_commit_tag(tag: &crate::ccl::FieldKey) -> bool {
    matches!(tag, crate::ccl::FieldKey::Name(n) if n == crate::ccl::V_COMMIT)
}

/// Extract a writer body's grant/deny *decision* at buffer position `pos`.
///
/// The body returns a **decision variant** `` {`commit{𝑃} | `abort} `` (see
/// [`crate::ccl::V_COMMIT`]/[`crate::ccl::V_ABORT`]): the codomain is a
/// `Scalar(Union)` column, one `Value::Union { tag, inner }` per position.
/// `abort` (any tag but `commit` — see [`is_commit_tag`]) is a whole-transaction deny — no writes, no
/// taps (carry / no proposal). `commit` carries the dense payload record `𝑃 =
/// {writes: (new₀, …), to_<defer>*(, to_<defer>__fire)*}`.
///
/// Returns `(commit, writes, tap_fired)`: `commit` gates grant vs deny; `writes[j]`
/// is the new value for `write_keys[j]` (carry writes then tap values, in that
/// order); and `tap_fired[t]` says whether tap `tap_fields[t]` fires at this
/// position (its `__fire` gate inside the payload, or `true` for an ungated tap).
/// A committing decision applies a carry write and a *fired* tap, but not a
/// non-fired tap.
fn body_decision_at(
    tile: &Tile,
    pos: usize,
    tap_fields: &[String],
) -> Option<(bool, Vec<Value>, Vec<bool>)> {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        return None;
    };
    // The decision codomain is a `Scalar(Union)` — one tagged variant per row.
    let Tile::Scalar(union_col) = codomain.as_ref() else {
        return None;
    };
    let row = (0..domain.len()).find(|&i| domain.index_at(i) == Value::UInt(pos))?;
    let Value::Union { tag, inner } = union_col.index_at(row) else {
        return None;
    };
    // `abort` — a whole-transaction deny: no proposal, no taps (carry).
    if !is_commit_tag(&tag) {
        return Some((false, Vec::new(), Vec::new()));
    }
    // `commit` — the payload record `{writes, to_<defer>*}`. The union column
    // already carried the values materialized at this row, so they are read
    // straight off the record with no per-column extraction step.
    let Value::Record(payload) = *inner else {
        return None;
    };
    // The write set is the writes tuple `(_0, …, _{w-1})` in index order, followed
    // by each reply tap's value — the order the caller's `write_keys` aligns with
    // (carries then taps).
    let mut writes = Vec::with_capacity(tap_fields.len());
    match payload.get(F_WRITES)? {
        // The normal case: the writes tuple is a record `{_0, …, _{w-1}}`. Each
        // entry may itself be record-valued (a store holding a record).
        Value::Record(writes_rec) => {
            for j in 0..writes_rec.len() {
                writes.push(writes_rec.get(&tuple_field(j))?.clone());
            }
        }
        // A read-only transaction's empty writes tuple `()` lowers to a unit
        // value (not a record): zero carry writes, only taps contribute.
        Value::Unit => {}
        _ => return None,
    }
    // Per tap, its value and whether it *fires* at this position. A tap with a
    // companion `<tap>__fire` field in the payload (a feed under cross-key routing)
    // fires only where that gate holds; a tap without one (a single-guard/spine
    // feed) always fires with its committing transaction.
    let mut tap_fired = Vec::with_capacity(tap_fields.len());
    for tap in tap_fields {
        writes.push(payload.get(tap)?.clone());
        let fire_field = format!("{tap}{}", crate::ccl::F_FIRE_SUFFIX);
        let fired = match payload.get(&fire_field) {
            Some(Value::Bool(b)) => *b,
            _ => true,
        };
        tap_fired.push(fired);
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
/// Each pull: read the cyclic store, fold to `(frontier, old)` for `key`, and —
/// once per `(item, frontier)` (idempotent retry) — push `(old, item)` to the
/// body buffer, pull the body for the new value, and append the proposal
/// `{snap: frontier, reads: {key ↦ old}, writes: {key ↦ new}}`. Advances to the
/// next item on `release` (the commit-ack). Retries (a fresh attempt at a new
/// frontier) append as new positions.
pub struct TransactWriter {
    tiling: Tiling,
    store_op: Box<dyn TileOperator>,
    body_op: Box<dyn TileOperator>,
    source_op: Box<dyn TileOperator>,
    buffer: BodyInputBuffer,
    /// Runtime keys the body reads a snapshot of, in body-parameter order
    /// (snapshot position `i` ↦ `read_keys[i]`).
    read_keys: Vec<Value>,
    /// Runtime keys the body writes, aligned with the decision's `writes` tuple
    /// followed by the `tap_fields` taps (`write_keys[j]` ↦ the `j`-th committed
    /// value). A reply (`resps << e`) rides the writer body as a `to_<defer>`
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
        source_op: Box<dyn TileOperator>,
        buffer: BodyInputBuffer,
        read_keys: Vec<Value>,
        write_keys: Vec<Value>,
        tap_fields: Vec<String>,
        key_extent: Extent,
        value_extent: Extent,
    ) -> Self {
        Self {
            tiling: proposal_stream_tiling(&key_extent, &value_extent),
            store_op,
            body_op,
            source_op,
            buffer,
            read_keys,
            write_keys,
            tap_fields,
        }
    }
}

impl TileOperator for TransactWriter {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // A new source item — a request arriving on a live source — is a new
        // transaction to drive. Forward the source's notification to this writer's
        // consumer (the `CommitOperator`), so a live arrival wakes the commit cycle
        // and, through it, any sink reading a store key or `to_<defer>` tap. Without
        // this the writer is never re-pulled on a live source, so a live
        // cross-endpoint read-only transaction's reply would never fire. The store
        // and body inputs need no notification: the writer pulls them on demand each
        // time the source drives it (and forwarding the cyclic store would loop).
        let consumer: SharedConsumer = Rc::new(RefCell::new(move || consumer.notify()));
        // The deferred-wakeup queue: while a source item remains to process, the
        // writer re-arms its own consumer (rather than looping inside `get`) so a
        // demand-driven driver re-pulls it — the one-step-per-pull cycle drive that
        // steps the store forward across pulls (a commit, a deny, or a not-ready
        // broadcast input each keep the writer non-terminal). See [`WakeupQueue`]
        // and the re-arm at the end of `get_impl`.
        let wakeups = scheduler.wakeup_queue();
        let sg = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.subscribe(sg, Box::new(|| {}), scheduler);
        let bg = self.body_op.tiling().universal_guard();
        let body_producer = self.body_op.subscribe(bg, Box::new(|| {}), scheduler);
        let srcg = self.source_op.tiling().universal_guard();
        // Forward the source's notification to this writer's consumer via a
        // fresh closure (a `Box<Rc<RefCell<dyn Consumer>>>` is not itself a
        // `Consumer` — the blanket impl needs a sized inner type).
        let src_consumer = {
            let c = consumer.clone();
            Box::new(move || c.borrow_mut().notify())
        };
        let source_producer = self.source_op.subscribe(srcg, src_consumer, scheduler);
        Box::new(TransactWriterProducer {
            base: ProducerBase::new(TransactWriterProducer::alloc_id(), &self.tiling),
            store_producer,
            body_producer,
            source_producer,
            consumer,
            wakeups,
            buffer: self.buffer.clone(),
            read_keys: self.read_keys.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            items: None,
            current: 0,
            committed_base: 0,
            emitted: Vec::new(),
            emitted_item: Vec::new(),
            latest_emit: None,
            pending: None,
            source_complete: false,
        })
    }
}

/// One accumulated proposal: `(snapshot, read-set, write-set)`.
type EmittedProposal = (CommitTs, HashMap<Value, Value>, HashMap<Value, Value>);

struct TransactWriterProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    body_producer: Box<dyn TileProducer>,
    source_producer: Box<dyn TileProducer>,
    /// This writer's consumer, re-armed through [`wakeups`](Self::wakeups) while an
    /// item remains to process — the one-step-per-pull cycle drive (see `get_impl`).
    consumer: SharedConsumer,
    /// The scheduler's deferred-wakeup queue — where a pull with pending work
    /// requests its own re-pull instead of looping in `get`.
    wakeups: WakeupQueue,
    buffer: BodyInputBuffer,
    read_keys: Vec<Value>,
    write_keys: Vec<Value>,
    /// Reply-tap decision fields, appended to each write set (see
    /// [`TransactWriter::tap_fields`]).
    tap_fields: Vec<String>,
    items: Option<Vec<Value>>,
    current: usize,
    /// Absolute proposal-stream position of `emitted[0]` — the number of leading
    /// proposals the consumer has committed-and-released, which `release_impl`
    /// has compacted away. The proposal stream is an **offset window**: its
    /// positions are absolute and consumer-indexed (`CommitProducer` reads them
    /// by value), so the released prefix is dropped without renumbering the live
    /// suffix. Bounds the writer's retained state on a long-lived store.
    committed_base: usize,
    /// Accumulated proposals not yet released — append-only within the live
    /// window. Each is `(snap, reads, writes)`: `reads`/`writes` are the
    /// multi-key read/write sets, where `reads` omits a key with no value yet (an
    /// append onto an empty store reads nothing, so it never goes stale — the
    /// empty-store bootstrap). The entry at vector index `i` is absolute position
    /// `committed_base + i`.
    emitted: Vec<EmittedProposal>,
    /// Source-item index per live emitted position (for idempotent
    /// release-advance), in lockstep with `emitted`.
    emitted_item: Vec<usize>,
    /// `(item, frontier)` of the latest emit — the retry-suppression idempotency
    /// key. Sound because a proposal is a *pure function of `(item, frontier)`*:
    /// the read set is `read_keys` folded against the store at `frontier`, and
    /// the write set is the body applied to that snapshot — so re-pulling at an
    /// unchanged `(item, frontier)` would re-derive a byte-identical proposal.
    /// Suppressing it keeps the append-only proposal stream from double-emitting
    /// the same transaction within one frontier (positions never shift).
    latest_emit: Option<(usize, CommitTs)>,
    /// `(item, frontier)` of a body-input row pushed whose decision is not yet
    /// ready — the decision reads a **broadcast cross-loop accumulator final**
    /// (`store := store − cnt`, `cnt` a *different*, completed loop) whose
    /// `ExtractFinal` is empty until that loop's `Recurse` drains, one position per
    /// body pull. While pending, the writer reuses this one row (re-pushing would
    /// duplicate a buffer position against the body's `Memo`) and re-arms itself
    /// via [`wakeups`](Self::wakeups) each pull; the `Memo` sees a legal monotonic
    /// empty→value growth at the position. Cleared once the decision resolves.
    /// Distinct from `latest_emit`, which marks a *proposal already emitted*.
    pending: Option<(usize, CommitTs)>,
    /// Whether the writer's source is *complete* — its most recent pull returned a
    /// terminal (`Predicate::True`) tile. A batch source (a list) is complete on
    /// the first pull; a live source (an HTTP request stream) never is. The writer
    /// reports its proposal stream terminal only when the source is complete *and*
    /// every item has been processed — never merely because it is momentarily
    /// drained (0 buffered items), which over a live source would prematurely
    /// declare the store (and any reply-tap stream) complete, so a later commit
    /// would conflict with that completeness claim.
    source_complete: bool,
}

impl TransactWriterProducer {
    fn render(&self) -> Tile {
        let n = self.emitted.len();
        let reads: Vec<Value> = self
            .emitted
            .iter()
            .map(|(_, reads, _)| map_to_value(reads))
            .collect();
        let writes: Vec<Value> = self
            .emitted
            .iter()
            .map(|(_, _, writes)| map_to_value(writes))
            .collect();
        // Terminal only when the source is complete *and* every item has been
        // processed. Gating on `source_complete` keeps a live-source writer
        // non-terminal even when momentarily drained, so the store (and any reply
        // tap read off it) is not prematurely declared complete.
        let terminal = self.source_complete
            && self
                .items
                .as_ref()
                .is_some_and(|it| self.current >= it.len());
        Tile::SealedFunction {
            // Absolute positions: the live window is `[committed_base, …)`; the
            // released prefix has been compacted away. Positions never renumber.
            domain: ColumnValue::from_uints(
                (self.committed_base..self.committed_base + n).collect(),
            ),
            codomain: Box::new(Tile::Record(HashMap::from([
                (
                    F_SNAP.to_string(),
                    Tile::Scalar(ColumnValue::from_uints(
                        self.emitted.iter().map(|(s, _, _)| *s).collect(),
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
            domain_predicate: if terminal {
                Predicate::True
            } else {
                Predicate::False
            },
            deleted: bit_set::BitSet::new(),
        }
    }

    /// Drop the body-input rows consumed up to `pos` and release the body
    /// producer's matching prefix, keeping the body-input window — and the body
    /// sub-operator's internal caches — bounded on a long-lived store. `pos` is
    /// the absolute position of the row whose decision was just read; positions
    /// are absolute, so the body's view slides forward without renumbering.
    fn compact_body_input(&mut self, pos: usize) {
        {
            let mut buf = self.buffer.borrow_mut();
            buf.rows.clear();
            buf.base = pos + 1;
        }
        self.body_producer
            .release(TileGuard::Function(FunctionGuard::Domain(
                Predicate::LessThanEq(Value::UInt(pos)),
            )));
    }

    /// Drop the live window's superseded proposals for the item about to be
    /// re-processed, keeping writer state O(1) under sustained contention.
    ///
    /// When the writer re-processes an item at a *new* frontier — a retry after a
    /// stale grant, or a grant→deny flip — its earlier proposal(s) for that item
    /// are provably dead: the `CommitProducer` owns this writer directly (no
    /// intervening fan-out), so it attempted every prior-pull proposal in the
    /// pull that rendered it; a *commit* would have released and prefix-compacted
    /// the item (advancing `current` past it), so a proposal still live here went
    /// stale. And because `current` does not advance while an item is stuck
    /// (committed items compact away, denied items advance with their orphans
    /// dropped here), the entire live window at this point is superseded
    /// proposals for this one item. Drop it and advance `committed_base`; the
    /// fresh proposal is appended at the next absolute position, so the
    /// consumer-indexed positions never renumber. Without this, a never-winning
    /// writer accumulates one lingering proposal per frontier for the store's
    /// lifetime (the old unbounded-`emitted` growth).
    fn drop_superseded(&mut self, item: usize) {
        debug_assert!(
            self.emitted_item.iter().all(|&it| it == item),
            "drop_superseded: live window holds a proposal for a non-current item \
             ({item} expected) — the stuck-item invariant (a leaving item's window \
             is cleared by commit-compaction or a deny drop) is violated"
        );
        let drop = self.emitted.len();
        if drop > 0 {
            self.emitted.clear();
            self.emitted_item.clear();
            self.committed_base += drop;
        }
    }
}

impl CyclicSequencingProducer for TransactWriterProducer {
    fn debug_assert_position_invariant(&self) {
        // Every emitted proposal records its source item in lockstep, so a
        // position denotes the same proposal in both vectors. These positions
        // are append-only and consumer-indexed (`CommitProducer` reads the
        // proposal stream by position), so they must never shift.
        debug_assert_eq!(
            self.emitted.len(),
            self.emitted_item.len(),
            "emitted proposals and their source-item indices grow in lockstep (append-only positions)"
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
        // Re-read the source each pull: a live source (an HTTP request stream)
        // grows over time, so caching the item list on the first pull would miss
        // requests that arrive afterward — e.g. a GET whose read-only writer is
        // first pulled while *another* endpoint's commits drive the store, before
        // any GET has arrived. The writer never releases its source, so `get`
        // returns the full current extent; positions are append-only and stable, so
        // `current` keeps indexing the same items as the list grows.
        let src = self
            .source_producer
            .get(self.source_producer.tiling().universal_guard());
        // The source is *complete* only when its tile is terminal. A batch source
        // (a list) is terminal on the first pull; a live source (an HTTP request
        // stream) never is — so the writer must not report its proposal stream
        // terminal merely because it is momentarily drained (see `render`).
        self.source_complete = src.is_terminal();
        self.items = Some(decode_source_items(&src));
        let n_items = self.items.as_ref().unwrap().len();
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
        let olds_at: Vec<Option<(CommitTs, Value)>> = self
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
        // released prefix, always keeping each key's latest write — the
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
        let release_through: Option<CommitTs> = if self.read_keys.is_empty() {
            snapshot
        } else {
            olds_at
                .iter()
                .filter_map(|o| o.as_ref().map(|(t, _)| *t))
                .min()
                .and_then(|oldest_read| oldest_read.checked_sub(1))
        };
        if let Some(through) = release_through {
            self.store_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::LessThanEq(Value::UInt(through)),
                )));
        }
        // Process the current item, unless a proposal for this `(item, frontier)`
        // is already emitted and awaiting commit (`latest_emit == key`) — re-running
        // would double-emit it into the append-only stream. `(item, frontier)` is
        // a sound key: the proposal (and the body-input row it derives from) is a
        // pure function of `(read_keys, frontier)`.
        if self.current < n_items
            && let Some(frontier) = snapshot
            && self.latest_emit != Some((self.current, frontier))
        {
            let key = (self.current, frontier);
            // Push the item's body-input row **once per `(item, frontier)`**; a
            // not-ready retry (a broadcast input still converging, the `None` arm
            // below) reuses it rather than re-pushing, which would duplicate a
            // buffer position against the body's `Memo`.
            if self.pending != Some(key) {
                let item = self.items.as_ref().unwrap()[self.current].clone();
                // The body reads snapshot position `i` as `p.i`. For a read key
                // with no value yet (the bootstrap case — an append onto an empty
                // collection store) we fabricate the item as a stand-in of the
                // right extent. Load-bearing assumption: a body that proposes a
                // write for an *absent* key is append-shaped, so it ignores the
                // snapshot at that position — the fabricated value is never
                // observed. (If a body ever read a fabricated snapshot, the read
                // set above would still omit the absent key, so the proposal could
                // not go stale on it.)
                let snap_in: Vec<Value> = olds
                    .iter()
                    .map(|o| o.clone().unwrap_or_else(|| item.clone()))
                    .collect();
                self.buffer.borrow_mut().rows.push((snap_in, item));
                self.pending = Some(key);
            }
            let pos = {
                let b = self.buffer.borrow();
                b.base + b.rows.len() - 1
            };
            let body_tile = self
                .body_producer
                .get(self.body_producer.tiling().universal_guard());
            match body_decision_at(&body_tile, pos, &self.tap_fields) {
                // Grant: propose the write set; the operator decides whether it
                // commits (release advances `current`) or is stale (retry). The
                // read set omits never-written keys (append → empty read).
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
                    // `n_reg` to a huge value in release and mis-index `tap_fired`.
                    debug_assert!(
                        self.write_keys.len() >= self.tap_fields.len(),
                        "commit operator: tap fields ({}) exceed write keys ({})",
                        self.tap_fields.len(),
                        self.write_keys.len()
                    );
                    let n_reg = self.write_keys.len() - self.tap_fields.len();
                    let writes: HashMap<Value, Value> = self
                        .write_keys
                        .iter()
                        .cloned()
                        .zip(new)
                        .enumerate()
                        .filter(|(i, _)| *i < n_reg || tap_fired[*i - n_reg])
                        .map(|(_, kv)| kv)
                        .collect();
                    // Re-proposing this item at a new frontier supersedes its
                    // prior stale proposal(s); drop them so the window stays O(1).
                    self.drop_superseded(self.current);
                    self.emitted.push((frontier, reads, writes));
                    self.emitted_item.push(self.current);
                    self.latest_emit = Some(key);
                    self.pending = None;
                    self.compact_body_input(pos);
                }
                // Deny: a purely local read-only decision (the body chose not to
                // write at this snapshot — e.g. `if pool >= r`). No proposal, no
                // tick consumed; advance past this item immediately, like the
                // hand-written `TokenWriter`'s `pool < cost` branch. Drop any
                // earlier grant-stale proposal for this item first (a grant→deny
                // flip on retry) so it is not orphaned in the window.
                Some((false, _, _)) => {
                    self.drop_superseded(self.current);
                    self.current += 1;
                    self.pending = None;
                    self.compact_body_input(pos);
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
                    // `ExtractFinal` is empty until the sibling loop's `Recurse`
                    // drains, one position per body pull. `current` is left
                    // unadvanced, so the pending item keeps this writer non-terminal
                    // and the unified re-arm below re-pulls it, each re-pull
                    // advancing the sibling loop one step until the decision fills in.
                }
            }
        }
        // One-step-per-pull convergence (the `Recurse` / #291 analog): this writer
        // steps a single source item per `get`, so after processing one it must
        // re-pull itself to reach the next — the notification-gated driver
        // (`src/main.rs`, `tests/cli_driver_convergence.rs`) re-pulls only on a
        // wakeup, never merely because a tile is non-terminal. Re-arm on the
        // deferred-wakeup queue whenever an item remains to process *now*
        // (`current < n_items`); this drives the cyclic store forward across pulls,
        // replacing the readers' retired producer-side drive-to-fixpoint. It covers
        // every non-terminal continuation uniformly:
        //  - a **commit** (grant): `current` advances on the commit-ack `release`,
        //    so the next pull processes the following item;
        //  - a **deny**: `current` already advanced here, with no commit — invisible
        //    in the store frontier, so a frontier-growth signal would miss it;
        //  - a **not-ready** decision (the `None` arm): `current` is unadvanced, so
        //    the pending item re-arms until the broadcast input converges.
        // A writer that is *drained but live* (`current >= n_items`, source not yet
        // complete) does **not** re-arm: a future arrival wakes it through the
        // source-forwarding consumer, so re-arming would busy-poll an idle server.
        // The writer's wakeup fans through the cyclic `FanOut` notify closure to
        // every store branch, so it also re-pulls the `AsOf` / `StoreValueStream`
        // readers that sample the store per pull.
        if self
            .items
            .as_ref()
            .is_some_and(|it| self.current < it.len())
        {
            self.wakeups.request(self.consumer.clone());
        }
        self.debug_assert_position_invariant();
        self.render()
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // commit-ack: advance past the item each released proposal was for, then
        // compact the released prefix out of the live window. Idempotent.
        self.debug_assert_position_invariant();
        let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard else {
            return;
        };
        // The entry at vector index `i` is absolute position `committed_base + i`
        // (positions are stable; the consumer releases by that absolute value).
        for (i, &item) in self.emitted_item.iter().enumerate() {
            if pred.contains(&Value::UInt(self.committed_base + i)) {
                self.current = self.current.max(item + 1);
            }
        }
        // Drop the released leading prefix and advance the window base. Releases
        // are prefixes (`LessThanEq(step)`, accumulated across commits), so the
        // released positions form a run from `committed_base` up. Dropping frees
        // the proposal records (their read/write maps) without renumbering the
        // live suffix — `CommitProducer` reads remaining positions by value.
        let mut drop = 0;
        while drop < self.emitted.len() && pred.contains(&Value::UInt(self.committed_base + drop)) {
            drop += 1;
        }
        if drop > 0 {
            self.emitted.drain(0..drop);
            self.emitted_item.drain(0..drop);
            self.committed_base += drop;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{FieldKey, TagMap, V_ABORT, V_COMMIT};
    use crate::interpreter::tile_operators::{Constant, FanOut, IterateExtent};
    use crate::interpreter::validate_tile;

    fn int(n: i64) -> Value {
        Value::Int(n)
    }

    fn acct(name: &str) -> Value {
        Value::String(name.into())
    }

    /// Build a read/write set or initial state from `(account, balance)` pairs.
    fn balances(pairs: &[(&str, i64)]) -> HashMap<Value, Value> {
        pairs.iter().map(|(k, v)| (acct(k), int(*v))).collect()
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
        let mut e = CommitEngine::for_induction();
        // prev read defaults to init (0) below the earliest change; the write at a
        // committing position is prev + item.
        e.step(0, None); // i=1, guard false → carry (x_0 = 0)
        e.step(1, None); // i=2, guard false → carry (x_1 = 0)
        e.step(2, Some(balances(&[("acc", 3)]))); // i=3 → x_2 = 0 + 3
        e.step(3, Some(balances(&[("acc", 7)]))); // i=4 → x_3 = 3 + 4

        assert_eq!(
            e.watermark(),
            3,
            "frontier reaches the final position, not the latest write"
        );
        // Folded reads: carries inherit (None → the reader's init default), writes resolve.
        assert_eq!(e.read_as_of(0, &acc), None); // carry → init 0
        assert_eq!(e.read_as_of(1, &acc), None); // carry → init 0
        assert_eq!(e.read_as_of(2, &acc), Some(int(3)));
        assert_eq!(e.read_as_of(3, &acc), Some(int(7))); // final total

        // The rendered store: a sparse changelog (2 change ticks) whose *length*
        // is the decided frontier region (4 positions), not the change count.
        let tile = e.render_full_store_tile();
        assert!(validate_tile(&tile));
        let Tile::Store {
            changes, frontier, ..
        } = &tile
        else {
            panic!("induction render is a Store");
        };
        assert_eq!(
            changes.len(),
            2,
            "only the two committing positions are changes"
        );
        assert_eq!(*frontier, Predicate::LessThanEq(Value::UInt(3)));
        assert_eq!(
            tile.len(),
            4,
            "Store length is the decided region [0, 3], not changes.len()"
        );
    }

    /// A test iteration source: one terminal `SealedFunction(pos → item)` tile
    /// over a fixed item list (the loop extent), mirroring a lowered `cast(iter,
    /// …)` loop source.
    struct ItemSource {
        tiling: Tiling,
        tile: Tile,
    }

    impl ItemSource {
        fn new(items: &[i64]) -> Self {
            let tiling = Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(value_extent())),
            };
            let tile = Tile::SealedFunction {
                domain: ColumnValue::from_uints((0..items.len()).collect()),
                codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                    items.iter().map(|n| int(*n)).collect(),
                    &value_extent(),
                ))),
                domain_predicate: Predicate::True,
                deleted: bit_set::BitSet::new(),
            };
            Self { tiling, tile }
        }
    }

    impl TileOperator for ItemSource {
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

    /// The `commit` payload extent for a single-key writer: `{writes: {_0: value}}`.
    fn commit_payload_extent() -> Extent {
        Extent::Record(HashMap::from([(
            F_WRITES.to_string(),
            Extent::Record(HashMap::from([(tuple_field(0), value_extent())])),
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

    /// A `` `commit({writes: {_0, _1, …}}) `` decision value from its per-key write values.
    fn commit_value(writes: Vec<Value>) -> Value {
        let writes_rec = Value::Record(
            writes
                .into_iter()
                .enumerate()
                .map(|(i, v)| (tuple_field(i), v))
                .collect(),
        );
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

    /// A single-accumulator induction-write decision body: over its `(prev, item)`
    /// input (a `BodyInputSource`), emits `` `commit({writes: {_0: prev + item}}) ``
    /// where `guard(item)` holds, else `` `abort `` (a carry — the accumulator holds).
    /// Models the recognized body of `for i in xs: if guard(i): acc += i`.
    struct AddIfBody {
        input: Box<dyn TileOperator>,
        tiling: Tiling,
        /// The guard threshold: `commit` iff `item > threshold` (`i64::MIN` ⇒ an
        /// unconditional loop, `commit` everywhere).
        threshold: i64,
    }

    impl AddIfBody {
        fn new(input: Box<dyn TileOperator>, threshold: i64) -> Self {
            let tiling = Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                // Decision variant `` {`commit{{writes: {_0}}} | `abort} `` — a
                // `Scalar(Union)` codomain (commit=0, abort=1).
                codomain: Box::new(Tiling::Scalar(decision_union_extent(
                    commit_payload_extent(),
                ))),
            };
            Self {
                input,
                tiling,
                threshold,
            }
        }
    }

    impl TileOperator for AddIfBody {
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
    }

    impl TileProducer for AddIfBodyProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            let in_tile = self.input.get(self.input.tiling().universal_guard());
            let Tile::SealedFunction {
                domain, codomain, ..
            } = in_tile
            else {
                panic!("AddIfBody input is a SealedFunction");
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
                    commit_value(vec![int(p + i)])
                } else {
                    abort_value()
                });
            }
            Tile::SealedFunction {
                domain,
                codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                    rows,
                    &decision_union_extent(commit_payload_extent()),
                ))),
                domain_predicate: Predicate::False,
                deleted: bit_set::BitSet::new(),
            }
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// Drive an `InductionStore` for a single-accumulator loop end-to-end through
    /// the tile protocol and return the converged store tile.
    fn drive_induction(items: &[i64], threshold: i64, init: i64) -> Tile {
        let buffer: BodyInputBuffer = Rc::new(RefCell::new(WriterBuffer::default()));
        let body_input = BodyInputSource::new(buffer.clone(), vec![value_extent()], value_extent());
        let body = AddIfBody::new(Box::new(body_input), threshold);
        let source = ItemSource::new(items);
        let acc = acct("acc");
        let mut op = InductionStore::new(
            vec![(
                acc.clone(),
                Box::new(Constant::new(int(init), value_extent())),
            )],
            Box::new(body),
            Box::new(source),
            buffer,
            vec![acc.clone()],
            vec![acc],
            Vec::new(),
            key_extent(),
            value_extent(),
        );
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        producer.get(producer.tiling().universal_guard())
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
        let Tile::Store { changes, .. } = &tile else {
            panic!("induction store output is a Store");
        };
        assert_eq!(
            changes.len(),
            3,
            "tick 0 (the init seed) plus the two firing positions (items 3, 4); the rest carry"
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
        let Tile::Store { changes, .. } = &tile else {
            panic!("induction store output is a Store");
        };
        assert_eq!(
            changes.len(),
            4,
            "tick 0 (the init seed) plus every committing position (a dense changelog)"
        );
    }

    /// Releasing a reader's consumed prefix bounds the changelog: the store GCs
    /// the FanOut-intersected prefix, **keeping each key's latest write**, so a
    /// long-lived loop's retained changelog is O(keys) rather than O(positions).
    /// `acc := 10; for i in [1,2,3]: acc += i` renders a 4-tick dense changelog;
    /// after a reader releases through tick 2, only the latest write survives —
    /// and the accumulator still reads its correct final value.
    #[test]
    fn induction_store_release_bounds_changelog_keeping_latest() {
        let buffer: BodyInputBuffer = Rc::new(RefCell::new(WriterBuffer::default()));
        let body_input = BodyInputSource::new(buffer.clone(), vec![value_extent()], value_extent());
        let body = AddIfBody::new(Box::new(body_input), i64::MIN); // unconditional
        let source = ItemSource::new(&[1, 2, 3]);
        let acc = acct("acc");
        let mut op = InductionStore::new(
            vec![(
                acc.clone(),
                Box::new(Constant::new(int(10), value_extent())),
            )],
            Box::new(body),
            Box::new(source),
            buffer,
            vec![acc.clone()],
            vec![acc.clone()],
            Vec::new(),
            key_extent(),
            value_extent(),
        );
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let full = producer.get(producer.tiling().universal_guard());
        let Tile::Store { changes, .. } = &full else {
            panic!("induction store output is a Store");
        };
        assert_eq!(
            changes.len(),
            4,
            "full dense changelog: seed + three writes"
        );

        // A reader consumed loop positions ≤ 1 → store ticks ≤ 2.
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(2)),
        )));

        let bounded = producer.get(producer.tiling().universal_guard());
        assert!(validate_tile(&bounded));
        assert_eq!(
            store_current(&bounded, &acc).map(|(_, v)| v),
            Some(int(16)),
            "the accumulator still reads its correct final value after GC"
        );
        let Tile::Store { changes, .. } = &bounded else {
            panic!("induction store output is a Store");
        };
        assert_eq!(
            changes.len(),
            1,
            "keep-latest GC drops the superseded prefix (ticks 0,1,2), keeping only \
             the latest write (tick 3) — the changelog no longer grows with positions"
        );
    }

    /// Build an `InductionStore` behind a fan and read `acc` densely over the loop
    /// extent via `StoreDenseRead`; return the dense `Fun(D, V)` values in order.
    fn dense_read(items: &[i64], threshold: i64, init: i64) -> Vec<i64> {
        let buffer: BodyInputBuffer = Rc::new(RefCell::new(WriterBuffer::default()));
        let body_input = BodyInputSource::new(buffer.clone(), vec![value_extent()], value_extent());
        let body = AddIfBody::new(Box::new(body_input), threshold);
        let source = ItemSource::new(items);
        let acc = acct("acc");
        let store = InductionStore::new(
            vec![(
                acc.clone(),
                Box::new(Constant::new(int(init), value_extent())),
            )],
            Box::new(body),
            Box::new(source),
            buffer,
            vec![acc.clone()],
            vec![acc.clone()],
            Vec::new(),
            key_extent(),
            value_extent(),
        );
        let fan = Rc::new(FanOut::new(Box::new(store)));
        let trigger = IterateExtent::new(Extent::uint_range(items.len()));
        let mut reader =
            StoreDenseRead::new(Box::new(trigger), fan.branch(), acc, value_extent(), true);
        let guard = reader.tiling().universal_guard();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        let tile = producer.get(producer.tiling().universal_guard());
        assert!(validate_tile(&tile));
        assert!(
            tile.is_terminal(),
            "a complete batch drives the dense read terminal"
        );
        let Tile::SealedFunction { codomain, .. } = tile else {
            panic!("dense read is a SealedFunction");
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
    /// dense function with no carries, exactly as the retired `.writes.(index)`
    /// projection produced.
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
            snapshot: 0,
            reads: balances(&[("acc", 0)]),
            writes: balances(&[("acc", 5)]),
        }); // tick 1: acc = 5
        e.attempt(Proposal {
            snapshot: 1,
            reads: HashMap::new(),
            writes: balances(&[("other", 9)]),
        }); // tick 2: a different key (acc carries)
        e.attempt(Proposal {
            snapshot: 2,
            reads: balances(&[("acc", 5)]),
            writes: balances(&[("acc", 8)]),
        }); // tick 3: acc = 8
        let store = e.render_full_store_tile();
        let acc = acct("acc");
        let queries: Vec<usize> = (0..=4).collect();
        for carry in [true, false] {
            let batched =
                fold_changelog_key_ascending(&store, queries.iter().copied(), &acc, carry);
            let per_tick: Vec<Option<Value>> = queries
                .iter()
                .map(|t| fold_changelog_key(&store, *t, &acc, carry))
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
        let buffer: BodyInputBuffer = Rc::new(RefCell::new(WriterBuffer::default()));
        let body_input = BodyInputSource::new(buffer.clone(), vec![value_extent()], value_extent());
        // Writes iff `item > 3`: over [5, 1, 1, 9] that fires at positions 0 and 3.
        let body = AddIfBody::new(Box::new(body_input), 3);
        let source = ItemSource::new(&[5, 1, 1, 9]);
        let acc = acct("acc");
        let store = InductionStore::new(
            vec![(acc.clone(), Box::new(Constant::new(int(0), value_extent())))],
            Box::new(body),
            Box::new(source),
            buffer,
            vec![acc.clone()],
            vec![acc.clone()],
            Vec::new(),
            key_extent(),
            value_extent(),
        );
        let fan = Rc::new(FanOut::new(Box::new(store)));
        let trigger = IterateExtent::new(Extent::uint_range(4));
        let mut reader =
            StoreDenseRead::new(Box::new(trigger), fan.branch(), acc, value_extent(), true);
        let guard = reader.tiling().universal_guard();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let read_values = |p: &mut Box<dyn TileProducer>| -> Vec<(usize, i64)> {
            let tile = p.get(p.tiling().universal_guard());
            let Tile::SealedFunction {
                domain, codomain, ..
            } = tile
            else {
                panic!("dense read is a SealedFunction");
            };
            let Tile::Scalar(col) = *codomain else {
                panic!("dense read codomain is a scalar column");
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
            Predicate::LessThanEq(Value::UInt(0)),
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
    struct ReleaseRecorder {
        inner: Box<dyn TileOperator>,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    struct ReleaseRecorderProducer {
        base: ProducerBase,
        inner: Box<dyn TileProducer>,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    impl TileOperator for ReleaseRecorder {
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
            Box::new(ReleaseRecorderProducer {
                base: ProducerBase::new(ReleaseRecorderProducer::alloc_id(), self.inner.tiling()),
                inner,
                releases: self.releases.clone(),
            })
        }
    }

    impl TileProducer for ReleaseRecorderProducer {
        impl_producer_base!();
        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            self.inner.get(projection_guard)
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
                && let Some(w) = max_released_tick(pred)
            {
                self.releases.borrow_mut().push(w);
            }
            self.inner.release(obsolete_guard);
        }
    }

    /// A carry reader's release forwards a store watermark that stops **below the
    /// carry source** of the first still-needed position — bounding the changelog
    /// without stranding a live carry. Over `[5, 1, 1, 9]` gated by `item > 3`,
    /// `acc` writes at ticks 1 (pos 0) and 4 (pos 3); ticks 0, 1, 4 write `acc`.
    /// Releasing dense position 0 leaves position 1 (reading tick 2) earliest; its
    /// carry source is tick 1, so the forwarded store release is `≤ 0` (not `≤ 1`,
    /// which the naive `pos + 1` rule would have stranded). Releasing through
    /// position 2 (position 3 reading tick 4 now earliest, carry source tick 4)
    /// forwards `≤ 3`, so keep-latest GC can reclaim the whole superseded prefix.
    #[test]
    fn carry_dense_reader_release_stops_below_carry_source() {
        let buffer: BodyInputBuffer = Rc::new(RefCell::new(WriterBuffer::default()));
        let body_input = BodyInputSource::new(buffer.clone(), vec![value_extent()], value_extent());
        let body = AddIfBody::new(Box::new(body_input), 3);
        let source = ItemSource::new(&[5, 1, 1, 9]);
        let acc = acct("acc");
        let store = InductionStore::new(
            vec![(acc.clone(), Box::new(Constant::new(int(0), value_extent())))],
            Box::new(body),
            Box::new(source),
            buffer,
            vec![acc.clone()],
            vec![acc.clone()],
            Vec::new(),
            key_extent(),
            value_extent(),
        );
        let fan = Rc::new(FanOut::new(Box::new(store)));
        let releases = Rc::new(RefCell::new(Vec::<usize>::new()));
        let recorder = ReleaseRecorder {
            inner: fan.branch(),
            releases: releases.clone(),
        };
        let trigger = IterateExtent::new(Extent::uint_range(4));
        let mut reader = StoreDenseRead::new(
            Box::new(trigger),
            Box::new(recorder),
            acc,
            value_extent(),
            true,
        );
        let guard = reader.tiling().universal_guard();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Drive the fold once so the reader caches which ticks wrote `acc`.
        let _ = producer.get(producer.tiling().universal_guard());

        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(0)),
        )));
        assert_eq!(
            releases.borrow().last().copied(),
            Some(0),
            "releasing dense pos 0 must forward store release ≤ 0 (carry source tick 1 survives)"
        );

        let _ = producer.get(producer.tiling().universal_guard());
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(2)),
        )));
        assert_eq!(
            releases.borrow().last().copied(),
            Some(3),
            "releasing through dense pos 2 must forward store release ≤ 3 (only tick 4 kept)"
        );
    }

    /// Two writers touch the *same* key from the same snapshot: the first
    /// commits, the second is stale (no tick consumed) and must retry.
    #[test]
    fn overlapping_keys_conflict() {
        let mut e = CommitEngine::new(balances(&[("alice", 100)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: 0,
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 70)]),
            }),
            CommitOutcome::Committed { ts: 1 }
        );
        // B read alice @snap 0, but alice was written at tick 1 → stale.
        assert_eq!(
            e.attempt(Proposal {
                snapshot: 0,
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 50)]),
            }),
            CommitOutcome::Stale
        );
        assert_eq!(e.watermark(), 1);
        assert_eq!(e.read_as_of(1, &acct("alice")), Some(int(70)));
    }

    /// Two writers touch *disjoint* keys from the same snapshot: both commit, no
    /// conflict — concurrency for free.
    #[test]
    fn disjoint_keys_commit_concurrently() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        assert_eq!(
            e.attempt(Proposal {
                snapshot: 0,
                reads: balances(&[("alice", 100)]),
                writes: balances(&[("alice", 70)]),
            }),
            CommitOutcome::Committed { ts: 1 }
        );
        // B read/write bob @snap 0; A wrote alice, not bob → no conflict.
        assert_eq!(
            e.attempt(Proposal {
                snapshot: 0,
                reads: balances(&[("bob", 50)]),
                writes: balances(&[("bob", 80)]),
            }),
            CommitOutcome::Committed { ts: 2 }
        );
        assert_eq!(e.read_as_of(2, &acct("alice")), Some(int(70)));
        assert_eq!(e.read_as_of(2, &acct("bob")), Some(int(80)));
    }

    /// A per-key read folds past ticks that wrote *other* keys — those ticks are
    /// decided-absent for this key, their value holding from the latest earlier
    /// change.
    #[test]
    fn read_folds_past_other_keys() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        e.attempt(Proposal {
            snapshot: 0,
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: alice
        e.attempt(Proposal {
            snapshot: 1,
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("bob", 20)]),
        }); // tick 2: bob

        // alice as of 2 folds past tick 2 (which wrote bob) back to tick 1.
        assert_eq!(e.read_as_of(2, &acct("alice")), Some(int(70)));
        assert_eq!(e.read_as_of(2, &acct("bob")), Some(int(20)));

        // The rendered store confirms tick 2 is decided-absent for alice — the
        // frontier snapshot still folds her value forward from tick 1.
        let tile = e.render_full_store_tile();
        assert_eq!(store_current(&tile, &acct("alice")), Some((2, int(70))));
        assert_eq!(store_current(&tile, &acct("bob")), Some((2, int(20))));
    }

    /// Read-side commit-log GC: `gc_released_prefix(through)` reclaims released
    /// versions at ticks `≤ through`, keeping each key's latest write (the
    /// carry-forward source). This is the engine half of the long-lived-store
    /// bound — the same rule for a superseded scalar and a merged collection
    /// prefix (both reduce to "drop everything below the key's latest").
    #[test]
    fn gc_released_prefix_keeps_latest_drops_released_history() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        // Three sequential writes — ticks 1, 2, 3 all write `n`.
        for i in 1..=3 {
            let snap = e.watermark();
            assert_eq!(
                e.attempt(Proposal {
                    snapshot: snap,
                    reads: balances(&[("n", i - 1)]),
                    writes: balances(&[("n", i)]),
                }),
                CommitOutcome::Committed { ts: i as CommitTs }
            );
        }
        // Consumers released through tick 2. Drop the released history `≤ 2`,
        // keeping `n`'s latest write (tick 3).
        e.gc_released_prefix(2);
        assert_eq!(e.read_as_of(3, &acct("n")), Some(int(3))); // latest kept
        assert_eq!(e.read_as_of(2, &acct("n")), None); // released history gone
        // Re-running with the same prefix is a no-op (idempotent); a never-rewritten
        // key's only (latest) entry is never dropped even below `through`.
        e.gc_released_prefix(2);
        assert_eq!(e.read_as_of(3, &acct("n")), Some(int(3)));
    }

    /// Repeated writes to one key, each reading the prior commit: every attempt
    /// commits, the timestamp domain stays dense (the `Recurse` degeneration).
    #[test]
    fn repeated_writes_to_one_key_are_dense() {
        let mut e = CommitEngine::new(balances(&[("n", 0)]));
        for i in 1..=4 {
            let snap = e.watermark();
            let Value::Int(prev) = e.read_as_of(snap, &acct("n")).unwrap() else {
                unreachable!()
            };
            assert_eq!(
                e.attempt(Proposal {
                    snapshot: snap,
                    reads: balances(&[("n", prev)]),
                    writes: balances(&[("n", prev + 1)]),
                }),
                CommitOutcome::Committed { ts: i }
            );
        }
        assert_eq!(e.watermark(), 4);
        assert_eq!(e.read_as_of(4, &acct("n")), Some(int(4)));
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
        let key = |i: usize| Value::String(format!("k{i}").into());
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
                                snapshot: snap,
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

    /// The full multi-key store renders as `CommitTimestamp ⇀ (Key ⇀ Value)`:
    /// per-tick write-set deltas encoded as `Value::Function` maps in a
    /// `Variants` column — heterogeneous key sets per tick, validating as a tile,
    /// and round-tripping back to maps. This is the encoding the multi-key
    /// operator and the E4 proposal wrapper rely on.
    #[test]
    fn full_store_renders_heterogeneous_deltas() {
        let mut e = CommitEngine::new(balances(&[("alice", 100), ("bob", 50)]));
        e.attempt(Proposal {
            snapshot: 0,
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: writes only alice
        e.attempt(Proposal {
            snapshot: 0,
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("alice", 70), ("bob", 30)]),
        }); // tick 2: writes alice AND bob (different key set than tick 1)

        let tile = e.render_full_store_tile();
        assert!(validate_tile(&tile));
        let Tile::Store {
            changes,
            deltas,
            frontier,
            ..
        } = &tile
        else {
            panic!("expected Store");
        };
        assert_eq!(changes, &ColumnValue::from_uints(vec![0, 1, 2]));
        assert_eq!(frontier, &Predicate::LessThanEq(Value::UInt(2)));
        let ColumnValue::Variants(deltas) = deltas else {
            panic!("expected a Variants column of map deltas");
        };
        // Tick 0 = init {alice, bob}; tick 1 = {alice}; tick 2 = {alice, bob}.
        assert_eq!(
            value_to_map(&deltas[0]),
            balances(&[("alice", 100), ("bob", 50)])
        );
        assert_eq!(value_to_map(&deltas[1]), balances(&[("alice", 70)]));
        assert_eq!(
            value_to_map(&deltas[2]),
            balances(&[("alice", 70), ("bob", 30)])
        );
    }

    // --- The engine as a live tile operator ---------------------------------

    /// Keys are account names (strings); values are balances (ints).
    fn key_extent() -> Extent {
        Extent::Base(BaseType::String)
    }
    fn value_extent() -> Extent {
        Extent::Base(BaseType::Int)
    }

    /// The decoded store: per-tick delta maps, sorted by tick.
    type StoreEntries = Vec<(usize, HashMap<Value, Value>)>;

    /// Decode a full store tile into `(frontier, entries)`, or `None` if the
    /// store is not yet decided (empty / undecided). Reads the [`Tile::Store`]
    /// changelog directly — the writer-side counterpart of
    /// [`CommitEngine::render_full_store_tile`].
    fn decode_store(tile: &Tile) -> Option<(usize, StoreEntries)> {
        let frontier = store_frontier(tile)?;
        let Tile::Store {
            changes, deltas, ..
        } = tile
        else {
            return None;
        };
        let entries = (0..changes.len())
            .map(|i| {
                let Value::UInt(tick) = changes.index_at(i) else {
                    unreachable!("store change ticks are UInt")
                };
                (tick, value_to_map(&deltas.index_at(i)))
            })
            .collect();
        Some((frontier, entries))
    }

    /// Fold the per-tick deltas with `tick ≤ t` into the cumulative state map.
    /// Later ticks overwrite earlier keys; ticks that wrote only other keys are
    /// folded past (decided-absent for the keys they omit).
    fn state_as_of(entries: &[(usize, HashMap<Value, Value>)], t: usize) -> HashMap<Value, Value> {
        let mut state = HashMap::new();
        for (tick, delta) in entries {
            if *tick > t {
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
    fn store_at(tile: &Tile, key: &Value) -> Option<(usize, i64)> {
        let (frontier, entries) = decode_store(tile)?;
        match state_as_of(&entries, frontier).get(key) {
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
        let mut op = CommitOperator::new(init, key_extent(), value_extent(), 1);
        (op.writer_input_setter(0))(input);
        let guard = op.tiling().universal_guard();
        op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new())
    }

    /// A test source operator that emits a fixed proposal stream as one
    /// terminal `SealedFunction(step → {snap, read, write})` tile.
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
            self.tile.clone()
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
            (0, balances(&[("pool", 100)]), balances(&[("pool", 30)])),
            (0, balances(&[("pool", 100)]), balances(&[("pool", 50)])),
        ]);
        let mut producer = subscribe_commit(Box::new(source), balances(&[("pool", 100)]));

        let tile = producer.get(producer.tiling().universal_guard());
        assert!(validate_tile(&tile));
        let Tile::Store {
            changes,
            frontier,
            terminal,
            ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        // Tick 1 (A) committed; B's grant was stale → no tick consumed. The
        // (materialized) writer is terminal, so the store is closed at watermark 1.
        assert_eq!(changes, &ColumnValue::from_uints(vec![0, 1]));
        assert_eq!(frontier, &Predicate::LessThanEq(Value::UInt(1)));
        assert!(terminal);
        assert_eq!(store_at(&tile, &acct("pool")), Some((1, 30)));
    }

    /// Sequential (non-conflicting) writers drive a dense store through the operator.
    #[test]
    fn live_producer_sequential() {
        let source = ProposalSource::new(&[
            (0, balances(&[("pool", 100)]), balances(&[("pool", 30)])),
            (1, balances(&[("pool", 30)]), balances(&[("pool", 20)])),
        ]);
        let mut producer = subscribe_commit(Box::new(source), balances(&[("pool", 100)]));

        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::Store {
            changes,
            frontier,
            terminal,
            ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        assert_eq!(changes, &ColumnValue::from_uints(vec![0, 1, 2]));
        // Both proposals committed and the writer is terminal → store closed at
        // watermark 2 (the frontier keeps its numeric watermark; terminality is
        // the separate flag).
        assert_eq!(frontier, &Predicate::LessThanEq(Value::UInt(2)));
        assert!(terminal);
        assert_eq!(store_at(&tile, &acct("pool")), Some((2, 20)));
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
        let commit = CommitOperator::new(balances(&[("n", 0)]), key_extent(), value_extent(), 1);
        let set_writer = commit.writer_input_setter(0);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        // The body reads a branch of the store (the operator's own output).
        let body = CounterBody::new(store_fan.branch(), acct("n"), 3);
        set_writer(Box::new(body));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Drive the cycle: bootstrap + 3 commits + a fixpoint pull, with margin.
        let mut latest = producer.get(producer.tiling().universal_guard());
        for _ in 0..6 {
            latest = producer.get(producer.tiling().universal_guard());
        }
        // Store: init 0 @0, then 1@1, 2@2, 3@3 — the counter reached 3.
        assert_eq!(store_at(&latest, &acct("n")), Some((3, 3)));
    }

    /// One accumulated proposal: `(snapshot, read set, write set)`.
    type EmittedProposal = (usize, HashMap<Value, Value>, HashMap<Value, Value>);

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
        Tile::SealedFunction {
            domain: ColumnValue::from_uints((base..base + emitted.len()).collect()),
            codomain: Box::new(Tile::Record(HashMap::from([
                (
                    F_SNAP.to_string(),
                    Tile::Scalar(ColumnValue::from_uints(
                        emitted.iter().map(|p| p.0).collect(),
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
            domain_predicate: if terminal {
                Predicate::True
            } else {
                Predicate::False
            },
            deleted: bit_set::BitSet::new(),
        }
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
        let commit =
            CommitOperator::new(balances(&[("pool", 100)]), key_extent(), value_extent(), 2);
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
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let mut latest = producer.get(producer.tiling().universal_guard());
        for _ in 0..6 {
            latest = producer.get(producer.tiling().universal_guard());
        }
        // Exactly one draw commits: 100−70=30 < 50 and 100−50=50 < 70, so
        // whichever commits first, the other denies. The round-robin drain picks
        // the winner, so the resting value is schedule-dependent (30 or 50) but
        // always a valid, non-negative outcome — exactly one commit either way.
        let (frontier, pool) = store_at(&latest, &acct("pool")).expect("pool decided");
        assert_eq!(frontier, 1, "exactly one commit");
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
        let commit =
            CommitOperator::new(balances(&[("pool", 100)]), key_extent(), value_extent(), 2);
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
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let mut latest = producer.get(producer.tiling().universal_guard());
        for _ in 0..10 {
            latest = producer.get(producer.tiling().universal_guard());
        }
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
                Some((frontier, entries)) if frontier >= self.t => {
                    match state_as_of(&entries, self.t).get(&self.key) {
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
        let commit = CommitOperator::new(balances(&[("n", 0)]), key_extent(), value_extent(), 1);
        let set_writer = commit.writer_input_setter(0);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_writer(Box::new(CounterBody::new(store_fan.branch(), acct("n"), 3)));

        let mut reader = StoreReadAsOf::new(store_fan.branch(), acct("n"), 2);
        let guard = reader.tiling().universal_guard();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Pulling the reader drives the cycle. Before the watermark reaches 2 the
        // read is ⊥ (empty); once it does, it resolves to the value at tick 2.
        let mut latest = Tile::Scalar(ColumnValue::from_ints(vec![]));
        for _ in 0..8 {
            latest = producer.get(producer.tiling().universal_guard());
        }
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
                    let state = state_as_of(&entries, frontier);
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
        let commit = CommitOperator::new(init, key_extent(), value_extent(), 2);
        let set_a = commit.writer_input_setter(0);
        let set_b = commit.writer_input_setter(1);
        let store_fan = Rc::new(FanOut::new_cyclic(Box::new(commit)));
        set_a(Box::new(BankWriter::new(store_fan.branch(), a)));
        set_b(Box::new(BankWriter::new(store_fan.branch(), b)));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let mut latest = producer.get(producer.tiling().universal_guard());
        for _ in 0..pulls {
            latest = producer.get(producer.tiling().universal_guard());
        }
        latest
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
        assert_eq!(store_at(&store, &acct("alice")), Some((2, 70)));
        assert_eq!(store_at(&store, &acct("bob")), Some((2, 130)));
        assert_eq!(store_at(&store, &acct("carol")), Some((2, 60)));
        assert_eq!(store_at(&store, &acct("dave")), Some((2, 140)));
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
        assert_eq!(store_at(&store, &acct("alice")), Some((2, 20)));
        assert_eq!(store_at(&store, &acct("bob")), Some((2, 130)));
        assert_eq!(store_at(&store, &acct("carol")), Some((2, 150)));
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
            self.tile.clone()
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
        let mut engine = CommitEngine::new(HashMap::from([(Value::Unit, int(100))]));
        engine.attempt(Proposal {
            snapshot: 0,
            reads: HashMap::new(),
            writes: HashMap::from([(Value::Unit, int(60))]),
        });
        let mut store_tile = engine.render_full_store_tile();
        let store_tiling = full_store_tiling(&Extent::Base(BaseType::String), &value_ext);

        // While committing, the stream is non-terminal but already carries both
        // the tick-0 init (100) and the committed value (60) — observable now.
        let mut stream = StoreValueStream::new(
            Box::new(FixedSource {
                tiling: store_tiling.clone(),
                tile: store_tile.clone(),
            }),
            Value::Unit,
            value_ext.clone(),
            true, // carry: hold the committed value forward
        );
        let g = stream.tiling().universal_guard();
        let mut p = stream.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        let t = p.get(p.tiling().universal_guard());
        assert!(!t.is_terminal());
        let Tile::SealedFunction { codomain, .. } = &t else {
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
            Value::Unit,
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
            snapshot: 0,
            reads: balances(&[("alice", 100)]),
            writes: balances(&[("alice", 70)]),
        }); // tick 1: alice
        e.attempt(Proposal {
            snapshot: 1,
            reads: balances(&[("bob", 50)]),
            writes: balances(&[("bob", 20)]),
        }); // tick 2: bob

        // Live: `frontier` carries the watermark `≤ 2`.
        let live = e.render_full_store_tile();
        assert_eq!(store_frontier(&live), Some(2));
        // `store_current` folds past tick 2 (which wrote only bob) back to tick 1
        // for alice, and reads bob directly at tick 2.
        assert_eq!(store_current(&live, &acct("alice")), Some((2, int(70))));
        assert_eq!(store_current(&live, &acct("bob")), Some((2, int(20))));
        assert_eq!(store_current(&live, &acct("carol")), None); // never written
        // The frontier snapshot is cross-key consistent.
        assert_eq!(
            store_snapshot_at(&live, 2),
            balances(&[("alice", 70), ("bob", 20)])
        );

        // Terminal: setting the separate `terminal` flag (the numeric frontier
        // `≤ 2` is kept, not rewritten) must fold identically.
        let mut terminal = live.clone();
        if let Tile::Store { terminal, .. } = &mut terminal {
            *terminal = true;
        }
        assert_eq!(store_frontier(&terminal), Some(2));
        assert_eq!(store_current(&terminal, &acct("alice")), Some((2, int(70))));
    }

    /// A non-store / undecided tile reads to `None` (the fallback every store
    /// read relies on).
    #[test]
    fn store_reads_reject_non_store_and_undecided() {
        assert_eq!(
            store_frontier(&Tile::Scalar(ColumnValue::from_ints(vec![1]))),
            None
        );
        // An empty changelog is undecided → no frontier.
        let undecided = Tile::Store {
            changes: ColumnValue::from_uints(vec![]),
            deltas: ColumnValue::Variants(vec![]),
            frontier: Predicate::LessThanEq(Value::UInt(0)),
            terminal: false,
        };
        assert_eq!(store_frontier(&undecided), None);
    }

    /// `read_initial_scalar` distinguishes a genuinely empty init (a scalar tile
    /// that stays empty) from a producer that never yields a scalar.
    #[test]
    fn read_initial_scalar_distinguishes_failure_modes() {
        // A non-empty scalar resolves immediately.
        let mut ok = FixedSource {
            tiling: Tiling::Scalar(Extent::Base(BaseType::Int)),
            tile: Tile::Scalar(ColumnValue::from_ints(vec![7])),
        };
        let g = ok.tiling().universal_guard();
        let mut p = ok.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        assert!(matches!(read_initial_scalar(&mut *p), Ok(v) if v == int(7)));

        // An always-empty scalar → Empty.
        let mut empty = FixedSource {
            tiling: Tiling::Scalar(Extent::Base(BaseType::Int)),
            tile: Tile::Scalar(ColumnValue::from_ints(vec![])),
        };
        let g = empty.tiling().universal_guard();
        let mut p = empty.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        assert!(matches!(
            read_initial_scalar(&mut *p),
            Err(InitDrainFailure::Empty)
        ));

        // A producer that never yields a scalar tile → Diverged. Its tiling is
        // the (non-scalar) SealedFunction shape so the producer accepts the tile;
        // `read_initial_scalar` still never sees a `Tile::Scalar`.
        let nonscalar_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut nonscalar = FixedSource {
            tiling: nonscalar_tiling,
            tile: Tile::SealedFunction {
                domain: ColumnValue::from_uints(vec![]),
                codomain: Box::new(Tile::Scalar(ColumnValue::from_ints(vec![]))),
                domain_predicate: Predicate::False,
                deleted: bit_set::BitSet::new(),
            },
        };
        let g = nonscalar.tiling().universal_guard();
        let mut p = nonscalar.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        assert!(matches!(
            read_initial_scalar(&mut *p),
            Err(InitDrainFailure::Diverged)
        ));
    }

    // ── Tile::Store step-function reads (Stage 2) ─────────────────────────────

    /// Build a `Tile::Store` changelog from `(tick, &[(account, balance)])`
    /// deltas (ticks must be strictly ascending) with the given decided
    /// `frontier`.
    fn store_tile(entries: &[(usize, &[(&str, i64)])], frontier: Predicate) -> Tile {
        let changes = ColumnValue::from_uints(entries.iter().map(|(t, _)| *t).collect());
        let deltas = ColumnValue::Variants(
            entries
                .iter()
                .map(|(_, m)| map_to_value(&balances(m)))
                .collect(),
        );
        let tile = Tile::Store {
            changes,
            deltas,
            frontier,
            terminal: false,
        };
        assert!(validate_tile(&tile), "store_tile built an invalid tile");
        tile
    }

    /// A three-tick store: tick 0 seeds both accounts, tick 1 writes only
    /// `alice`, tick 2 writes only `bob`. Decided through the watermark `w`.
    fn skew_store(w: usize) -> Tile {
        store_tile(
            &[
                (0, &[("alice", 100), ("bob", 50)]),
                (1, &[("alice", 70)]),
                (2, &[("bob", 40)]),
            ],
            Predicate::LessThanEq(Value::UInt(w)),
        )
    }

    #[test]
    fn store_frontier_reads_watermark_and_terminal() {
        let live = skew_store(2);
        assert_eq!(store_frontier(&live), Some(2));
        // A terminal store keeps its `LessThanEq(w)` watermark (terminality is the
        // separate flag), so `store_frontier` reads `w` directly — even when the
        // watermark is *past the latest change tick* (trailing carries). Here the
        // latest change is at tick 3 but the decided watermark is 5: the frontier is
        // 5, not 3 (the former `True`-reconstruction undercounted to the latest
        // change).
        let done = store_tile(
            &[(0, &[("alice", 100)]), (3, &[("alice", 70)])],
            Predicate::LessThanEq(Value::UInt(5)),
        );
        assert_eq!(store_frontier(&done), Some(5));
        // `Tile::len` counts decided *positions* (watermark + 1), spanning the
        // trailing carries at ticks 4 and 5 — not the 2 change ticks, nor the latest
        // change tick + 1 (4) the former `True`-reconstruction would have given.
        assert_eq!(done.len(), 6);
        // Empty changelog and non-store tiles have no frontier.
        assert_eq!(store_frontier(&store_tile(&[], Predicate::False)), None);
        assert_eq!(
            store_frontier(&Tile::Scalar(ColumnValue::Ints(vec![1]))),
            None
        );
    }

    #[test]
    fn store_value_at_folds_step_interpolation() {
        let s = skew_store(2);
        // `alice`: 100 at tick 0, 70 from tick 1 on.
        assert_eq!(store_value_at(&s, 0, &acct("alice")), Some(int(100)));
        assert_eq!(store_value_at(&s, 1, &acct("alice")), Some(int(70)));
        assert_eq!(store_value_at(&s, 2, &acct("alice")), Some(int(70)));
        // `bob`: 50 holds across tick 1 (which wrote only alice), 40 from tick 2.
        assert_eq!(store_value_at(&s, 0, &acct("bob")), Some(int(50)));
        assert_eq!(store_value_at(&s, 1, &acct("bob")), Some(int(50)));
        assert_eq!(store_value_at(&s, 2, &acct("bob")), Some(int(40)));
        // A key never written is absent regardless of `t`.
        assert_eq!(store_value_at(&s, 2, &acct("carol")), None);
    }

    #[test]
    fn store_snapshot_at_is_cross_key_consistent() {
        let s = skew_store(2);
        // Each snapshot is a coherent record at one commit time — the property a
        // bank of independent per-key reads (read-skew) cannot guarantee.
        assert_eq!(
            store_snapshot_at(&s, 0),
            balances(&[("alice", 100), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, 1),
            balances(&[("alice", 70), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, 2),
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
        assert_eq!(store_current(&live, &acct("alice")), Some((2, int(70))));
        assert_eq!(store_current(&live, &acct("bob")), Some((2, int(40))));
        // An undecided store (nothing committed yet) has no current value.
        let undecided = store_tile(&[(0, &[("alice", 100)])], Predicate::False);
        assert_eq!(store_current(&undecided, &acct("alice")), None);
    }

    #[test]
    fn decode_source_positioned_pairs_by_domain_and_sorts() {
        // An async source's domain arrives unordered (it enumerates a set of
        // arrived keys), and the codomain aligns to the domain *column*, not to
        // position. Decoding must pair each item with its actual domain position
        // and sort — otherwise the position-driven drive reads the wrong item at
        // each tick, and a scalar-final `ExtractFinal` over the dense read (which
        // relies on the highest position being last) picks a mid-loop value.
        let tile = Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![2, 0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_ints(vec![30, 10, 20]))),
            domain_predicate: Predicate::True,
            deleted: bit_set::BitSet::new(),
        };
        assert_eq!(
            decode_source_positioned(&tile),
            vec![(0, int(10)), (1, int(20)), (2, int(30))],
            "items must be paired with their domain position and sorted ascending"
        );
    }

    #[test]
    fn store_merge_appends_changes_and_advances_frontier() {
        // Two changelog fragments — a decided prefix and a later commit — merge
        // by appending ticks and unioning the frontier to the larger watermark.
        let mut s = store_tile(
            &[(0, &[("alice", 100), ("bob", 50)]), (1, &[("alice", 70)])],
            Predicate::LessThanEq(Value::UInt(1)),
        );
        s.merge(store_tile(
            &[(2, &[("bob", 40)])],
            Predicate::LessThanEq(Value::UInt(2)),
        ));
        // The merged changelog reads identically to a store built in one shot
        // (compared semantically — delta cells are `map_to_value` of a `HashMap`,
        // whose binding order is not significant).
        assert_eq!(store_frontier(&s), Some(2));
        assert_eq!(
            store_snapshot_at(&s, 0),
            balances(&[("alice", 100), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, 1),
            balances(&[("alice", 70), ("bob", 50)])
        );
        assert_eq!(
            store_snapshot_at(&s, 2),
            balances(&[("alice", 70), ("bob", 40)])
        );
        assert_eq!(store_current(&s, &acct("bob")), Some((2, int(40))));
    }

    #[test]
    fn validate_tile_rejects_malformed_store() {
        // Mismatched changes/deltas lengths.
        assert!(!validate_tile(&Tile::Store {
            changes: ColumnValue::from_uints(vec![0, 1]),
            deltas: ColumnValue::Variants(vec![map_to_value(&balances(&[("a", 1)]))]),
            frontier: Predicate::False,
            terminal: false,
        }));
        // Non-ascending change ticks.
        assert!(!validate_tile(&Tile::Store {
            changes: ColumnValue::from_uints(vec![2, 1]),
            deltas: ColumnValue::Variants(vec![
                map_to_value(&balances(&[("a", 1)])),
                map_to_value(&balances(&[("a", 2)])),
            ]),
            frontier: Predicate::False,
            terminal: false,
        }));
    }
}

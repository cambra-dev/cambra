//! The commit operator: a transaction engine as a tile operator.
//!
//! Implements the transactional time-domain machinery from
//! `docs/mutability-design.md` ("The commit operator, constructed"): concurrent
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

use crate::ccl::{F_COMMIT, F_WRITES};
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, FunctionGuard, Predicate, Scheduler, Tile, TileGuard,
    Tiling, Value,
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

    /// The watermark frontier: all ticks `≤ watermark()` are decided.
    pub fn watermark(&self) -> CommitTs {
        self.next_ts - 1
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
        Tile::Store {
            changes: ColumnValue::from_uints(ticks),
            deltas: ColumnValue::Variants(deltas),
            frontier: Predicate::LessThanEq(Value::UInt(self.watermark())),
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
    let guard = producer.tiling().universal_guard();
    let mut saw_empty_scalar = false;
    for _ in 0..MAX_INIT_PULLS {
        if let Tile::Scalar(cv) = producer.get(guard.clone()) {
            if !cv.is_empty() {
                return Ok(cv.index_at(0));
            }
            saw_empty_scalar = true;
        }
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

/// Backstop on [`StoreValueStreamProducer`]'s per-`get` store-convergence loop: a
/// live commit store drains one buffered commit per pull and stabilizes at a
/// fixpoint, but bound the loop so a non-converging cycle can't hang. Pending
/// commit counts in any real workload are tiny; this is purely a safety ceiling.
const MAX_STORE_CONVERGENCE_PULLS: usize = 1 << 20;

/// The frontier of a store tile's change ticks + `frontier` predicate (the
/// watermark decode behind [`store_frontier`]). `LessThanEq(w)` reads the
/// watermark directly; the terminal `True` flip reconstructs it from the last
/// (largest) change tick. `None` for an undecided/empty changelog.
fn frontier_from_domain(domain: &ColumnValue, domain_predicate: &Predicate) -> Option<CommitTs> {
    if domain.is_empty() {
        return None;
    }
    match domain_predicate {
        Predicate::LessThanEq(Value::UInt(f)) => Some(*f),
        Predicate::True => {
            debug_assert!(
                (0..domain.len()).all(|i| {
                    i == 0
                        || matches!(
                            (domain.index_at(i - 1), domain.index_at(i)),
                            (Value::UInt(a), Value::UInt(b)) if a <= b
                        )
                }),
                "store tile ticks are rendered in ascending order; the last is the watermark"
            );
            match domain.index_at(domain.len() - 1) {
                Value::UInt(t) => Some(t),
                _ => None,
            }
        }
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
/// watermark directly; the terminal `True` flip takes the last (largest) change
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
/// never written. Unlike an `ExtractLast` over a `SealedFunction`, this is
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
        Predicate::Or(arms) | Predicate::Union(arms) => {
            arms.iter().filter_map(max_released_tick).max()
        }
        _ => None,
    }
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

/// Field names of the proposal-stream codomain record. `F_WRITES`/`F_COMMIT`
/// are the writer-body *decision* fields — the contract between the letrec
/// phase (which builds the `{commit, writes}` record), inference (which types
/// it), and this engine (which reads it) — so they are shared from `crate::ccl`.
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
    /// `Mut[V, Txn]` keys; a literal init is just the trivial init
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
        // Drain each writer's new proposals in writer-index order. The order is
        // the serialization order: an earlier writer's commit can make a later
        // writer's same-pull proposal stale.
        //
        // FAIRNESS NOTE: this fixed low-to-high order can starve a higher-index
        // writer that contends with a lower-index one on a hot key — the lower
        // index always wins the tick and the higher index perpetually retries.
        // Correctness is unaffected (every proposal is a pure function of its
        // snapshot, so a starved writer just keeps re-proposing), but throughput
        // is skewed. A rotating start index (round-robin across pulls) would make
        // it fair; deferred as it needs care around the append-only proposal
        // positions and the idempotency key.
        for k in 0..self.writer_producers.len() {
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
        let mut store = self.engine.render_full_store_tile();
        // Signal terminality once every writer is done: the store is then fully
        // decided (no more commits), so the watermark `LessThanEq(w)` becomes
        // `True`. A downstream `read`/output gates on this to know the cycle has
        // converged (the harness re-pulls a non-terminal output to drive it).
        // A store with **no** writers is trivially terminal (no commit can ever
        // happen) — `all()` over the empty writer set is `true`, which is what we
        // want, so there is no `is_empty()` guard.
        if self.writer_terminal.iter().all(|&t| t)
            && let Tile::Store { frontier, .. } = &mut store
        {
            *frontier = Predicate::True;
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
        // versions, keeping each key's latest write. A full-render reader (an
        // `AsOf` over the whole log) releases nothing, pinning the watermark at 0
        // → no GC, which is correct: it still needs the whole log.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(through) = max_released_tick(pred)
        {
            self.engine.gc_released_prefix(through);
        }
    }
}

/// Extract a source stream's codomain elements (the items to transact over).
fn decode_source_items(tile: &Tile) -> Vec<Value> {
    match tile {
        Tile::SealedFunction {
            domain, codomain, ..
        } => match codomain.as_ref() {
            Tile::Scalar(cv) => (0..domain.len()).map(|i| cv.index_at(i)).collect(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
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
/// A bare scalar read of the transactional variable is `ExtractLast` over this
/// stream (the latest committed value — the final value, for a terminating
/// program); a live reader samples the latest entry as of its pull without
/// waiting for the store to finish.
pub struct StoreValueStream {
    tiling: Tiling,
    store_op: Box<dyn TileOperator>,
    key: Value,
    value_extent: Extent,
    /// Whether the key's value persists across commit ticks that don't write it.
    /// A **register** (`true`) carries its last committed value forward — reading
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
            released_through: None,
        })
    }
}

struct StoreValueStreamProducer {
    base: ProducerBase,
    store_producer: Box<dyn TileProducer>,
    key: Value,
    value_extent: Extent,
    /// See [`StoreValueStream::carry_forward`]: register (carry the last value
    /// across ticks that don't write the key) vs. reply tap (emit only at the
    /// tick that wrote it).
    carry_forward: bool,
    /// Highest commit tick a consumer has released (`None` = nothing released).
    /// The store's commit log only grows, so `get` emits each tick exactly once:
    /// only ticks beyond this cursor. A re-reading consumer (e.g. `ExtractLast`,
    /// which never releases) keeps this `None` and sees the full projection every
    /// pull; an accumulating consumer (`Memo`) releases what it has merged, so
    /// the next pull is the delta — without this, re-emitting merged ticks would
    /// double them in the consumer's cache.
    released_through: Option<usize>,
}

impl TileProducer for StoreValueStreamProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Drive the cyclic store to its current fixpoint before projecting. The
        // store's writers commit one step per pull, and a writer reading the store
        // sees the *previous* pull's frontier — so a freshly-arrived transaction
        // (e.g. a live cross-endpoint read-only reply reading the latest commit)
        // takes an extra pull to observe the newest commit and commit its own. A
        // live store never goes terminal but *stabilizes* once buffered commits
        // drain: pull until the decided frontier stops growing (bounded to backstop
        // a runaway cycle). This is the same convergence the `AsOf` join performs
        // over a live commit store.
        let sg = self.store_producer.tiling().universal_guard();
        let mut store = self.store_producer.get(sg.clone());
        for _ in 0..MAX_STORE_CONVERGENCE_PULLS {
            let prev = store_frontier(&store);
            let next = self.store_producer.get(sg.clone());
            let grew = store_frontier(&next) > prev;
            store = next;
            if !grew {
                break;
            }
        }
        // The store's watermark predicate (`frontier`) is carried through unchanged
        // — terminality flows to this stream. Fold the changelog directly.
        let Tile::Store {
            changes,
            deltas,
            frontier,
        } = &store
        else {
            return self.tiling().empty_tile();
        };
        let domain_predicate = frontier.clone();
        // Project each change tick's delta map to `key`'s value. A register carries
        // the last written value forward across ticks that don't touch `key` (so a
        // read sees the latest write ≤ that tick — the step interpolation); a reply
        // tap emits only at the tick that wrote it (a per-commit event — carrying it
        // forward would smear one writer's reply across another writer's commit
        // ticks on the shared clock). Scan every change to keep `carried` accurate
        // for the register case, but only *emit* ticks past `released_through` — the
        // log grows monotonically and an accumulating consumer has already merged
        // the released prefix.
        let mut ticks: Vec<usize> = Vec::with_capacity(changes.len());
        let mut values: Vec<Value> = Vec::with_capacity(changes.len());
        let mut carried: Option<Value> = None;
        for i in 0..changes.len() {
            let Value::UInt(tick) = changes.index_at(i) else {
                continue;
            };
            let delta = value_to_map(&deltas.index_at(i));
            let here = delta.get(&self.key);
            if let Some(v) = here {
                carried = Some(v.clone());
            }
            if self.released_through.is_some_and(|r| tick <= r) {
                continue;
            }
            let emit = if self.carry_forward {
                carried.as_ref()
            } else {
                here
            };
            if let Some(v) = emit {
                ticks.push(tick);
                values.push(v.clone());
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
        // re-emit a merged prefix) AND forward that prefix upstream to the store:
        // a consumer that merged commits `≤ max_tick` no longer needs them, so
        // this read branch releases them. The store reclaims a version only once
        // *every* branch (this reader, the writers) has released it — the cyclic
        // `FanOut` intersects — so forwarding here is safe and is what lets a
        // long-lived collection log shed its merged prefix.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard
            && let Some(max_tick) = max_released_tick(pred)
        {
            self.released_through =
                Some(self.released_through.map_or(max_tick, |r| r.max(max_tick)));
            self.store_producer
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::LessThanEq(Value::UInt(max_tick)),
                )));
        }
    }
}

/// As-of (temporal) join: for each position of a `trigger` stream, latch the
/// **current value** of the shared store's `key` at the moment that trigger
/// position is first observed.
///
/// `trigger : Fun(B, _)` (e.g. an HTTP request stream), `source` the shared
/// commit store (a [`Tile::Store`] fan branch), output `Fun(B, V)` — `key`'s
/// value as of each request. This is the **live cross-endpoint read**: a request
/// arriving "now" sees the store as committed by now. The reply is indexed by
/// the trigger (the enclosing request loop) — an *outer-indexed* read, not
/// commit-clock indexed. The pairing is by *processing time* — the only ordering
/// the tile model exposes between two independent streams — which is exactly "a
/// request sees what's committed."
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
/// One field of a multi-register [`AsOf`] snapshot: the record field the reply
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
    /// A single register → scalar codomain `Fun(B, Scalar(V))` — the bare or
    /// computed single-register live read.
    Scalar { key: Value, value_extent: Extent },
    /// A whole-snapshot record → `Fun(B, Record{field: Scalar(V)})` — the
    /// multi-register live read. Every field is folded from **one** source render
    /// at one commit frontier (§I-c), so a reply reading several registers sees a
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
    /// is `Scalar(V)` (single register) or `Record{field: Scalar(V)}` (snapshot).
    tiling: Tiling,
    /// The trigger stream `Fun(B, _)` — drives one output position each.
    trigger: Box<dyn TileOperator>,
    /// The shared commit store (a [`Tile::Store`] fan branch) — the sampled
    /// key(s)' current value(s) are latched per trigger position.
    source: Box<dyn TileOperator>,
    /// What to sample and emit — a single register or a whole snapshot record.
    output: AsOfOutput,
}

impl AsOf {
    /// `trigger : Fun(B, _)`, `source` the shared commit store (`Tiling::Store`),
    /// `key`/`value_extent` the register to sample → output
    /// `Fun(B, Scalar(value_extent))`.
    pub fn new(
        trigger: Box<dyn TileOperator>,
        source: Box<dyn TileOperator>,
        key: Value,
        value_extent: Extent,
    ) -> Self {
        Self::build(trigger, source, AsOfOutput::Scalar { key, value_extent })
    }

    /// The multi-register **snapshot** read: sample every `field`'s register at
    /// one commit snapshot → output `Fun(B, Record{field: Scalar(V)})`, from which
    /// the reply projects each register. This is the §I-c snapshot-consistent
    /// live read.
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
            released_through: None,
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
    /// Prefix release watermark: every trigger position `<= released_through` has
    /// been released and must never re-latch (see `release_impl`). `None` before
    /// any release. A request stream is a monotone `UInt` domain released as a
    /// prefix, so a single watermark captures the released region exactly.
    released_through: Option<usize>,
}

impl AsOfProducer {
    /// Whether trigger position `b` lies at or below the released-prefix
    /// watermark — i.e. the consumer has already taken it and it must not
    /// re-latch.
    fn is_released(&self, b: &Value) -> bool {
        matches!((self.released_through, b), (Some(w), Value::UInt(u)) if *u <= w)
    }

    /// Build the output tile from the currently-latched `(b ↦ snapshot)` pairs,
    /// under `domain_predicate`. The latched set is already compacted of released
    /// positions, so it emits exactly the live response window. The codomain is a
    /// `Scalar` column (single register) or a `Record` of per-field `Scalar`
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
        // Drive the source to its current fixpoint: a request observes the store
        // "as of now", which means applying every commit pending at this moment.
        // The source is a cyclic store whose writers commit one step per pull
        // (proposal → commit-ack via `release` → advance), so converging "now"
        // takes one pull per pending commit. A live source never goes terminal,
        // but it *stabilizes* once the currently-buffered writes drain — pull
        // until the decided **frontier** stops growing. We key on the frontier
        // (not domain *length*) precisely because we compact the source below it
        // at the end of this pull: compaction shrinks the domain but never lowers
        // the frontier, so a pull that does not advance the frontier decided
        // nothing new. (Bounded to backstop a runaway cycle.)
        let sg = self.source.tiling().universal_guard();
        // The first `get` is itself the baseline convergence step: it reads the
        // current snapshot and serves as the `prev` against which the first
        // in-loop pull is compared for growth.
        let mut source_tile = self.source.get(sg.clone());
        let mut converged = false;
        for _ in 0..MAX_STORE_CONVERGENCE_PULLS {
            let prev = store_frontier(&source_tile);
            let next = self.source.get(sg.clone());
            let grew = store_frontier(&next) > prev;
            source_tile = next;
            if !grew {
                converged = true;
                break;
            }
        }
        if !converged {
            // The source is still growing after the bound — a runaway cycle, or a
            // pending-commit count far larger than any real workload. Fail loudly
            // in debug; in release, refuse to latch a *known-stale* snapshot onto
            // a fresh trigger position. Re-emit only the already-latched (frozen,
            // correct) positions with a non-terminal (`False`) predicate, so the
            // consumer retries on a later pull rather than freezing a partial
            // source view. Re-emitting the prior frozen set is monotone-safe;
            // deferring new latches is harmless.
            debug_assert!(
                false,
                "AsOf source failed to converge in {MAX_STORE_CONVERGENCE_PULLS} pulls"
            );
            return self.emit_latched(Predicate::False);
        }
        // Fold the store snapshot **once**, at the current frontier, for every
        // sampled key — so a multi-register read sees all its registers at one
        // commit time (§I-c). `None` if any key has no decided value yet (they
        // share the store's frontier, so it's all-or-nothing). The frontier bound
        // is the same for every key, so it also drives the release below.
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
        // Latch each newly-seen trigger position to the source's *current*
        // snapshot. If the source has no decided value yet, latch nothing this
        // round — the trigger position is left un-seen and gets latched on a later
        // pull once the source has a value. (For a scalar store the render seeds
        // the init at tick 0, so this only delays a read that genuinely precedes
        // any source value.)
        //
        // Positions at or below `released_through` are skipped: the consumer has
        // already taken them, so they must never re-latch — even if the trigger
        // re-presents one (the trigger may compact lazily after a forwarded
        // release; its emitted domain still legally carries the position until it
        // does). This guard is what makes the `release_impl` compaction safe.
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
        // (Convergence keys on the frontier, so this compaction can't perturb the
        // drive loop above.)
        if let Some(f) = frontier
            && f > 0
        {
            self.source
                .release(TileGuard::Function(FunctionGuard::Domain(
                    Predicate::LessThanEq(Value::UInt(f - 1)),
                )));
        }
        // If the source has no decided value yet, a live trigger position that
        // has not latched is still *awaiting* one — its response is not decided.
        // Emitting the trigger's terminality here (a terminal-but-empty tile when
        // the trigger is a finite batch) would tell the consumer "done, no
        // response", stranding that request forever. Downgrade to a non-terminal
        // (`False`) predicate so the consumer re-pulls until the source produces a
        // value and the position latches. (A trigger with no live un-latched
        // position is genuinely complete, so its terminality rides through.)
        let awaiting = snapshot.is_none()
            && matches!(&trigger_tile, Tile::SealedFunction { domain, .. }
            if (0..domain.len()).any(|i| {
                let b = domain.index_at(i);
                !self.is_released(&b) && !self.seen.contains(&b)
            }));
        let emit_pred = if awaiting {
            Predicate::False
        } else {
            trigger_pred
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
        // watermark (`released_through`) — request positions form a monotone
        // `UInt` domain released as a prefix, so a single watermark captures the
        // released region — and the `get_impl` latch loop skips anything at or
        // below it. The source is compacted in `get_impl` (released below its
        // latest decided position, the only value future triggers need), not here;
        // `release_impl` handles only the trigger side.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &obsolete_guard {
            if pred.as_bool() == Some(true) {
                // Terminal release: the consumer is done with the whole domain.
                // Drop everything and latch nothing further (every UInt position
                // is below the watermark — `usize::MAX` stands in for "all").
                self.released_through = Some(usize::MAX);
                self.latched.clear();
                self.seen.clear();
            } else if let Some(w) = max_released_tick(pred) {
                self.released_through = Some(self.released_through.map_or(w, |cur| cur.max(w)));
                self.latched.retain(|(b, _)| {
                    let drop = matches!(b, Value::UInt(u) if *u <= w);
                    if drop {
                        self.seen.remove(b);
                    }
                    !drop
                });
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
            released_through: None,
        })
    }
}

struct BodyInputSourceProducer {
    base: ProducerBase,
    buffer: BodyInputBuffer,
    read_extents: Vec<Extent>,
    item_extent: Extent,
    /// Highest absolute buffer position a consumer has released (`None` = none).
    /// The body op fans this source through a `FanOut`/`Memo` that pulls it
    /// repeatedly within one round (once per fanned use — the `{commit, writes}`
    /// decision reads it in several places); re-emitting an already-released
    /// position would make the `Memo`'s append-merge duplicate that domain
    /// position (an invalid tile). Emitting only positions past this cursor makes
    /// the source delta-producing, exactly as the induction body's `fan_in` input
    /// is — so repeated pulls after a release contribute nothing.
    released_through: Option<usize>,
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
        let start = match self.released_through {
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
            self.released_through = Some(self.released_through.map_or(max, |r| r.max(max)));
        }
    }
}

/// Extract a writer body's grant/deny *decision* at buffer position `pos`.
///
/// The body returns a `{commit: Bool, writes: (new₀, …, new_{w-1})}` record (see
/// [`F_COMMIT`] / [`F_WRITES`]) — the `writes` field is itself a record tile
/// `{_0, …, _{w-1}}`. Returns `(commit, writes)`: `commit` gates grant (propose
/// the write set) vs deny (skip); `writes[j]` is the new value proposed for the
/// writer's `write_keys[j]`.
fn body_decision_at(tile: &Tile, pos: usize, tap_fields: &[String]) -> Option<(bool, Vec<Value>)> {
    let Tile::SealedFunction {
        domain, codomain, ..
    } = tile
    else {
        return None;
    };
    let Tile::Record(fields) = codomain.as_ref() else {
        return None;
    };
    let Tile::Scalar(commit_col) = fields.get(F_COMMIT)? else {
        return None;
    };
    let row = (0..domain.len()).find(|&i| domain.index_at(i) == Value::UInt(pos))?;
    let commit = matches!(commit_col.index_at(row), Value::Bool(true));
    // The write set is the writes tuple `(_0, …, _{w-1})` in index order,
    // followed by each reply tap's value — the order the caller's `write_keys`
    // aligns with (registers then taps). A tap is a sibling scalar field on the
    // decision record (`to_<defer>_k`), not part of the writes tuple.
    let mut writes = Vec::with_capacity(tap_fields.len());
    match fields.get(F_WRITES)? {
        // The normal case: the writes tuple is a record `{_0, …, _{w-1}}`. Each
        // entry may itself be record-valued (a store holding a record), so extract
        // via `field_value_at`.
        Tile::Record(writes_fields) => {
            for j in 0..writes_fields.len() {
                writes.push(field_value_at(writes_fields.get(&tuple_field(j))?, row)?);
            }
        }
        // A read-only transaction's empty writes tuple `()` lowers to a unit
        // scalar (not a record): zero register writes, only taps contribute.
        Tile::Scalar(_) => {}
        _ => return None,
    }
    for tap in tap_fields {
        // A reply tap may be fed a record (`out << {id, payload}`), so the field is
        // a `Tile::Record`, not a scalar column — assemble the record value.
        writes.push(field_value_at(fields.get(tap)?, row)?);
    }
    Some((commit, writes))
}

/// The value at position `row` of a decision-record field tile. A scalar field is
/// one column value; a **record**-valued field (e.g. a reply tap fed a record
/// `{id, payload}`) is assembled into a [`Value::Record`] from each of its fields'
/// values at `row`, recursively. `None` for a shape with no per-position value.
fn field_value_at(tile: &Tile, row: usize) -> Option<Value> {
    match tile {
        Tile::Scalar(col) => Some(col.index_at(row)),
        Tile::Record(fields) => {
            let mut m = HashMap::with_capacity(fields.len());
            for (name, field) in fields {
                m.insert(name.clone(), field_value_at(field, row)?);
            }
            Some(Value::Record(m))
        }
        _ => None,
    }
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
        let consumer = Rc::new(RefCell::new(move || consumer.notify()));
        let sg = self.store_op.tiling().universal_guard();
        let store_producer = self.store_op.subscribe(sg, Box::new(|| {}), scheduler);
        let bg = self.body_op.tiling().universal_guard();
        let body_producer = self.body_op.subscribe(bg, Box::new(|| {}), scheduler);
        let srcg = self.source_op.tiling().universal_guard();
        let source_producer = self
            .source_op
            .subscribe(srcg, Box::new(consumer.clone()), scheduler);
        Box::new(TransactWriterProducer {
            base: ProducerBase::new(TransactWriterProducer::alloc_id(), &self.tiling),
            store_producer,
            body_producer,
            source_producer,
            buffer: self.buffer.clone(),
            read_keys: self.read_keys.clone(),
            write_keys: self.write_keys.clone(),
            tap_fields: self.tap_fields.clone(),
            items: None,
            current: 0,
            committed_base: 0,
            emitted: Vec::new(),
            emitted_item: Vec::new(),
            last_emit: None,
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
    /// `(item, frontier)` of the last emit — the retry-suppression idempotency
    /// key. Sound because a proposal is a *pure function of `(item, frontier)`*:
    /// the read set is `read_keys` folded against the store at `frontier`, and
    /// the write set is the body applied to that snapshot — so re-pulling at an
    /// unchanged `(item, frontier)` would re-derive a byte-identical proposal.
    /// Suppressing it keeps the append-only proposal stream from double-emitting
    /// the same transaction within one frontier (positions never shift).
    last_emit: Option<(usize, CommitTs)>,
    /// Whether the writer's source is *complete* — its last pull returned a
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
        //    `<<` or `last = msg`): it reads no tick's value, only the frontier,
        //    so it releases the whole decided prefix.
        //  - **Non-empty read set** (a register drawdown, e.g. `pool = pool - r`):
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
        // `(item, frontier)` is a sound idempotency key because the proposal is a
        // pure function of `(read_keys, frontier)`: a retry at an unchanged
        // frontier re-derives an identical proposal, so suppressing it avoids
        // double-emitting one transaction into the append-only stream.
        if self.current < n_items
            && let Some(frontier) = snapshot
            && self.last_emit != Some((self.current, frontier))
        {
            let item = self.items.as_ref().unwrap()[self.current].clone();
            // The body reads snapshot position `i` as `p.i`. For a read key with
            // no value yet (the bootstrap case — an append onto an empty
            // collection store) we fabricate the item as a stand-in of the right
            // extent. Load-bearing assumption: a body that proposes a write for an
            // *absent* key is append-shaped, so it ignores the snapshot at that
            // position — the fabricated value is never observed. (If a body ever
            // read a fabricated snapshot, the read set above would still omit the
            // absent key, so the proposal could not go stale on it.)
            let snap_in: Vec<Value> = olds
                .iter()
                .map(|o| o.clone().unwrap_or_else(|| item.clone()))
                .collect();
            self.buffer.borrow_mut().rows.push((snap_in, item));
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
                Some((true, new)) => {
                    let reads: HashMap<Value, Value> = self
                        .read_keys
                        .iter()
                        .zip(&olds)
                        .filter_map(|(k, o)| o.clone().map(|v| (k.clone(), v)))
                        .collect();
                    let writes: HashMap<Value, Value> =
                        self.write_keys.iter().cloned().zip(new).collect();
                    self.emitted.push((frontier, reads, writes));
                    self.emitted_item.push(self.current);
                    self.last_emit = Some((self.current, frontier));
                    self.compact_body_input(pos);
                }
                // Deny: a purely local read-only decision (the body chose not to
                // write at this snapshot — e.g. `if pool >= r`). No proposal, no
                // tick consumed; advance past this item immediately, like the
                // hand-written `TokenWriter`'s `pool < cost` branch.
                Some((false, _)) => {
                    self.current += 1;
                    self.compact_body_input(pos);
                }
                // The body has not produced this position yet — undo the push
                // and retry next round (should not happen: the body maps the
                // buffer synchronously on the pull above).
                None => {
                    self.buffer.borrow_mut().rows.pop();
                }
            }
        }
        self.debug_assert_position_invariant();
        self.render()
    }
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Commit-ack: advance past the item each released proposal was for, then
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
                tile: proposal_tile(proposals, true),
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
            changes, frontier, ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        // Tick 1 (A) committed; B's grant was stale → no tick consumed. The
        // (materialized) writer is terminal, so the store is fully decided.
        assert_eq!(changes, &ColumnValue::from_uints(vec![0, 1]));
        assert_eq!(frontier, &Predicate::True);
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
            changes, frontier, ..
        } = &tile
        else {
            panic!("expected Store store tile");
        };
        assert_eq!(changes, &ColumnValue::from_uints(vec![0, 1, 2]));
        // Both proposals committed and the writer is terminal → store decided.
        assert_eq!(frontier, &Predicate::True);
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
                emitted: Vec::new(),
                n: self.n,
            })
        }
    }

    struct CounterBodyProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        key: Value,
        /// Accumulated proposals, append-only.
        emitted: Vec<EmittedProposal>,
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
            if self.emitted.len() < self.n {
                let store = store_at(
                    &self
                        .store_producer
                        .get(self.store_producer.tiling().universal_guard()),
                    &self.key,
                );
                if let Some((frontier, v)) = store {
                    self.emitted.push((
                        frontier,
                        HashMap::from([(self.key.clone(), int(v))]),
                        HashMap::from([(self.key.clone(), int(v + 1))]),
                    ));
                }
            }
            proposal_tile(&self.emitted, self.emitted.len() == self.n)
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// A single writer reads the store and proposes increments through the
    /// commit operator, reading its own committed output back via a cyclic
    /// `FanOut`. Each pull advances the cycle one step (the first pull
    /// bootstraps: the body sees the empty cached store and proposes nothing).
    #[test]
    fn single_writer_cycle() {
        let commit = CommitOperator::new(balances(&[("n", 0)]), key_extent(), value_extent(), 1);
        let set_writer = commit.writer_input_setter(0);
        let store_fan = Rc::new(crate::interpreter::tile_operators::FanOut::new_cyclic(
            Box::new(commit),
        ));
        // The body reads a branch of the store (the operator's own output).
        let body = CounterBody::new(store_fan.branch(), acct("n"), 3);
        set_writer(Box::new(body));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Drive the cycle: bootstrap + 3 commits + a fixpoint pull, with margin.
        let mut last = producer.get(producer.tiling().universal_guard());
        for _ in 0..6 {
            last = producer.get(producer.tiling().universal_guard());
        }
        // Store: init 0 @0, then 1@1, 2@2, 3@3 — the counter reached 3.
        assert_eq!(store_at(&last, &acct("n")), Some((3, 3)));
    }

    /// One accumulated proposal: `(snapshot, read set, write set)`.
    type EmittedProposal = (usize, HashMap<Value, Value>, HashMap<Value, Value>);

    /// Build a proposal-stream tile `step → {snap, reads, writes}` from
    /// accumulated grants, with the map-valued read/write sets riding `Variants`
    /// columns ([`map_to_value`]).
    fn proposal_tile(emitted: &[EmittedProposal], terminal: bool) -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::from_uints((0..emitted.len()).collect()),
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
                emitted: Vec::new(),
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
        emitted: Vec<EmittedProposal>,
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
                        self.emitted.push((
                            frontier,
                            HashMap::from([(self.key.clone(), int(pool))]),
                            HashMap::from([(self.key.clone(), int(pool - cost))]),
                        ));
                    }
                }
            }
            let done = self.current >= self.costs.len();
            proposal_tile(&self.emitted, done)
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {
            // The operator released our outstanding grant → the current request
            // committed → advance to the next request.
            self.current += 1;
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
        let store_fan = Rc::new(crate::interpreter::tile_operators::FanOut::new_cyclic(
            Box::new(commit),
        ));
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

        let mut last = producer.get(producer.tiling().universal_guard());
        for _ in 0..6 {
            last = producer.get(producer.tiling().universal_guard());
        }
        // A committed (pool 100 → 30) at tick 1; B's grant was stale, then it
        // denied. Exactly one commit; the pool rests at 30.
        assert_eq!(store_at(&last, &acct("pool")), Some((1, 30)));
    }

    /// Two writers each handle a *stream* of requests against a shared pool of
    /// 100, exercising per-request advancement via `release`. A = [70, 40],
    /// B = [50, 30]. Serialized: A's 70 commits (→30); B's 50 and A's 40 are both
    /// denied (only 30 left); B's 30 commits (→0). Total granted 70+30 = 100; the
    /// pool ends at 0 and never goes negative.
    #[test]
    fn token_pool_multi_request() {
        let commit =
            CommitOperator::new(balances(&[("pool", 100)]), key_extent(), value_extent(), 2);
        let set_a = commit.writer_input_setter(0);
        let set_b = commit.writer_input_setter(1);
        let store_fan = Rc::new(crate::interpreter::tile_operators::FanOut::new_cyclic(
            Box::new(commit),
        ));
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

        let mut last = producer.get(producer.tiling().universal_guard());
        for _ in 0..10 {
            last = producer.get(producer.tiling().universal_guard());
        }
        // Two commits (A's 70, B's 30); the pool rests at 0.
        assert_eq!(store_at(&last, &acct("pool")), Some((2, 0)));
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
        let store_fan = Rc::new(crate::interpreter::tile_operators::FanOut::new_cyclic(
            Box::new(commit),
        ));
        set_writer(Box::new(CounterBody::new(store_fan.branch(), acct("n"), 3)));

        let mut reader = StoreReadAsOf::new(store_fan.branch(), acct("n"), 2);
        let guard = reader.tiling().universal_guard();
        let mut producer = reader.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Pulling the reader drives the cycle. Before the watermark reaches 2 the
        // read is ⊥ (empty); once it does, it resolves to the value at tick 2.
        let mut last = Tile::Scalar(ColumnValue::from_ints(vec![]));
        for _ in 0..8 {
            last = producer.get(producer.tiling().universal_guard());
        }
        let Tile::Scalar(cv) = &last else { panic!() };
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
                emitted: Vec::new(),
            })
        }
    }

    struct BankWriterProducer {
        base: ProducerBase,
        store_producer: Box<dyn TileProducer>,
        transfers: Vec<(Value, Value, i64)>,
        current: usize,
        emitted: Vec<EmittedProposal>,
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
                            self.emitted.push((
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
            proposal_tile(&self.emitted, done)
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {
            self.current += 1;
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
        let store_fan = Rc::new(crate::interpreter::tile_operators::FanOut::new_cyclic(
            Box::new(commit),
        ));
        set_a(Box::new(BankWriter::new(store_fan.branch(), a)));
        set_b(Box::new(BankWriter::new(store_fan.branch(), b)));

        let mut external = store_fan.branch();
        let guard = external.tiling().universal_guard();
        let mut producer = external.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        let mut last = producer.get(producer.tiling().universal_guard());
        for _ in 0..pulls {
            last = producer.get(producer.tiling().universal_guard());
        }
        last
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
    /// stream (`Txn ⇀ Value`), observable as it commits — no terminal gate
    /// — with terminality flowing through from the store. `ExtractLast` over it
    /// is the scalar final read.
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
            true, // register: carry the committed value forward
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

        // Once the store is terminal, so is the stream — and `ExtractLast` over
        // it gives the final value 60 (the latest committed entry).
        if let Tile::Store { frontier, .. } = &mut store_tile {
            *frontier = Predicate::True;
        }
        let stream = StoreValueStream::new(
            Box::new(FixedSource {
                tiling: store_tiling,
                tile: store_tile,
            }),
            Value::Unit,
            value_ext.clone(),
            true, // register: carry the committed value forward
        );
        let default = Box::new(FixedSource {
            tiling: Tiling::Scalar(value_ext.clone()),
            tile: Tile::Scalar(ColumnValue::single(int(100))),
        });
        let mut last =
            crate::interpreter::tile_operators::ExtractLast::new(Box::new(stream), default);
        let g = last.tiling().universal_guard();
        let mut p = last.subscribe(g, Box::new(|| {}), &mut Scheduler::new());
        let t = p.get(p.tiling().universal_guard());
        let Tile::Scalar(cv) = &t else { panic!() };
        assert_eq!(cv.as_single(), Some(int(60)));
    }

    // --- Engine render → step-function fold ---------------------------------

    /// A rendered [`Tile::Store`] folds consistently whether live (the `frontier`
    /// predicate carries the watermark `≤ w`) or terminal (the predicate flips to
    /// `True` and the frontier is reconstructed from the last change tick).
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

        // Terminal: flipping `frontier` to `True` must reconstruct the frontier
        // from the last change tick, identically.
        let mut terminal = live.clone();
        if let Tile::Store { frontier, .. } = &mut terminal {
            *frontier = Predicate::True;
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
        // A fully-committed store flips `frontier` to `True`; the frontier is
        // then the last (largest) change tick.
        let done = store_tile(
            &[(0, &[("alice", 100)]), (3, &[("alice", 70)])],
            Predicate::True,
        );
        assert_eq!(store_frontier(&done), Some(3));
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
        // terminal `True`) — where an `ExtractLast` would hang waiting for
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
        }));
        // Non-ascending change ticks.
        assert!(!validate_tile(&Tile::Store {
            changes: ColumnValue::from_uints(vec![2, 1]),
            deltas: ColumnValue::Variants(vec![
                map_to_value(&balances(&[("a", 1)])),
                map_to_value(&balances(&[("a", 2)])),
            ]),
            frontier: Predicate::False,
        }));
    }
}

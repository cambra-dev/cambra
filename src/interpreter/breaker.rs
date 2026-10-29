//! The output of a pipeline breaker that materializes, shared by the workers that fill it and
//! the pipelines that read it. See `src/interpreter/design-parallel.md`, "A breaker's output".

#![cfg_attr(
    not(test),
    expect(dead_code, reason = "the plan constructs `PoolBreaker::Materialize`")
)]

use std::sync::{Arc, Mutex, PoisonError, RwLock, Weak};

use crate::interpreter::tile_operators::{LiveSource, MorselSource};
use crate::interpreter::{
    Consumer, FunctionGuard, LockNow, Predicate, Projection, Tile, TileGuard, Tiling, Value,
};

/// The rows a breaker holds for the pipelines behind it: the merged morsels, the keys ready to
/// read, and what each reading operator has released.
///
/// The workers of the pipeline before the breaker [`absorb`](Self::absorb) a morsel's rows and
/// [`publish`](Self::publish) its region. The pipelines behind read through
/// [`snapshot`](Self::snapshot), and their consumers hear each region published. The rows leave
/// when every reading operator has released them.
///
/// Locks, outermost first: `downstream`, the gated cell of a consumer's chain, a pipeline's
/// early state, a [`LiveSource`]'s state, `state`. `publish` and `add_downstream` hold
/// `downstream` while they notify, so a consumer's `notify` takes no lock that precedes it in
/// that order and does not subscribe; the source builder a notification can run takes none of
/// them. `state` is innermost: no call holds it while it takes another lock or runs a consumer,
/// and `claim` reads it through `first_keys` while it holds the source's state.
pub(crate) struct Materialized {
    tiling: Tiling,
    // shared-state-ok: the breaker's rows, the keys that are ready, and what each reader has
    // released, under one lock: a release takes all three, and a key is ready only once its rows
    // are in the tile. The yield predicate a downstream source reads is `ready`.
    state: RwLock<State>,
    // shared-state-ok: the consumers of the pipelines behind the breaker, one per reading
    // operator, notified when a region is ready. A consumer holds no tile.
    downstream: Mutex<Vec<Box<dyn Consumer>>>,
}

struct State {
    /// The merged morsels, less what every reader released.
    tile: Tile,
    /// The keys whose rows are in `tile` or were released from it.
    ready: Predicate,
    /// The ready keys every reader released, removed from `tile`.
    reclaimed: Predicate,
    /// Whether no further key will be absorbed.
    complete: bool,
    /// One record per reading operator.
    readers: Vec<Reader>,
    /// The sources [`Materialized::source`] handed out.
    sources: Vec<Weak<LiveSource>>,
}

/// What one reading operator has released, shared by its workers: the union of their morsels.
struct Reader {
    /// The operator's name for the pool, or `None` for a reader that is its own operator.
    name: Option<String>,
    released: Predicate,
}

impl Materialized {
    /// An empty output of rows shaped `tiling`.
    pub(crate) fn new(tiling: Tiling) -> Arc<Self> {
        Arc::new(Self {
            state: RwLock::new(State {
                tile: tiling.empty_tile(),
                ready: Predicate::False,
                reclaimed: Predicate::False,
                complete: false,
                readers: Vec::new(),
                sources: Vec::new(),
            }),
            downstream: Mutex::new(Vec::new()),
            tiling,
        })
    }

    /// Merge the rows of the morsel `guard` names and make its keys ready. The morsel states
    /// complete the region of `guard`, its keys are inside that region and disjoint from the
    /// keys absorbed before, which the claims of the pipeline before the breaker guarantee, and
    /// nothing is absorbed after [`complete`](Self::complete).
    ///
    /// The rows and their keys become visible together, before the region is published.
    pub(crate) fn absorb(&self, morsel: Tile, guard: &TileGuard) {
        let projection = Projection::of(guard).expect("a morsel's guard names keys");
        let region = keys_of(&projection);
        debug_assert!(
            morsel.within(&projection).is_ok(),
            "a morsel's rows are inside the region it was claimed at: {morsel:?} for {guard:?}"
        );
        debug_assert!(
            match &morsel {
                Tile::DataFunction {
                    domain_predicate, ..
                } => region.minus(domain_predicate).is_false(),
                _ => true,
            },
            "a morsel states its whole region complete: {morsel:?} for {guard:?}"
        );
        let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
        debug_assert!(
            !state.complete,
            "no morsel is absorbed after the breaker completed"
        );
        debug_assert!(
            state.ready.intersect(&region).is_false(),
            "a morsel's keys are disjoint from the keys ready: {region:?} against {:?}",
            state.ready
        );
        state.tile.merge(morsel);
        state.ready = state.ready.union(&region);
    }

    /// Tell the pipelines behind the breaker that the keys of `region` can be read. The caller
    /// has absorbed their rows, and holds none of this value's locks.
    pub(crate) fn publish(&self, region: &Projection) {
        debug_assert!(
            region.contained_in(&Projection::admitting(self.ready())),
            "a region is published after its rows were absorbed: {region:?} against {:?}",
            self.ready()
        );
        let mut downstream = self.downstream.lock_wait();
        for consumer in downstream.iter_mut() {
            consumer.notify(region);
        }
    }

    /// No further key will be absorbed: the collection is whole, and every consumer is told.
    pub(crate) fn complete(&self) {
        {
            let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
            debug_assert!(!state.complete, "a breaker completes once");
            state.complete = true;
        }
        let mut downstream = self.downstream.lock_wait();
        for consumer in downstream.iter_mut() {
            consumer.notify(&Projection::Everything);
        }
    }

    /// The rows of the region `guard` names that are in the output, stating complete the keys
    /// that are ready, or every key once the breaker completed.
    ///
    /// The whole held tile is cloned and then cut, so a snapshot costs in proportion to the rows
    /// the output holds, not to the rows it returns.
    pub(crate) fn snapshot(&self, guard: &TileGuard) -> Tile {
        let projection = Projection::of(guard).expect("a read names keys");
        let (mut tile, ready, complete) = {
            let state = self.state.read().unwrap_or_else(PoisonError::into_inner);
            (state.tile.clone(), state.ready.clone(), state.complete)
        };
        if let Tile::DataFunction {
            domain_predicate, ..
        } = &mut tile
        {
            *domain_predicate = if complete { Predicate::True } else { ready };
        }
        tile.restrict_to(&projection, &self.tiling);
        tile
    }

    /// The first `rows` keys of `region` that have rows in the output, in key order: what a
    /// source over the output answers. A key the region names that the pipeline before the
    /// breaker filtered out has no row and is skipped. It reads every held key.
    fn first_keys(&self, region: &Predicate, rows: u64) -> Vec<Value> {
        let state = self.state.read().unwrap_or_else(PoisonError::into_inner);
        let Tile::DataFunction { domain, .. } = &state.tile else {
            return Vec::new();
        };
        let mut keys: Vec<Value> = (0..domain.len())
            .map(|row| domain.index_at(row))
            .filter(|key| region.contains(key) && state.ready.contains(key))
            .collect();
        keys.sort_by(|a, b| {
            a.partial_cmp(b)
                .expect("the keys of one collection are ordered")
        });
        keys.truncate(usize::try_from(rows).unwrap_or(usize::MAX));
        keys
    }

    #[cfg(test)]
    pub(crate) fn first_keys_for_test(&self, region: &Predicate, rows: u64) -> Vec<Value> {
        self.first_keys(region, rows)
    }

    /// The keys that are ready to read.
    pub(crate) fn ready(&self) -> Predicate {
        self.state
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .ready
            .clone()
    }

    /// Whether the breaker completed.
    #[cfg(test)]
    pub(crate) fn is_complete(&self) -> bool {
        self.state
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .complete
    }

    /// The tiling of the rows.
    pub(crate) fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    /// A source over the output for one reading operator: it claims the keys that were
    /// published, which have rows by then. Each reading operator has a source of its own, since
    /// its claims are its own.
    pub(crate) fn source(self: &Arc<Self>) -> Arc<LiveSource> {
        let (ready, first_keys) = (self.clone(), self.clone());
        let source = Arc::new(LiveSource::new(
            move || ready.ready(),
            move |region, rows| first_keys.first_keys(region, rows),
        ));
        self.state
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .sources
            .push(Arc::downgrade(&source));
        source
    }

    /// Whether `source` is one this output handed out.
    pub(crate) fn feeds(&self, source: &Arc<dyn MorselSource>) -> bool {
        let wanted = Arc::as_ptr(source) as *const ();
        self.state
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .sources
            .iter()
            .filter_map(Weak::upgrade)
            .any(|ours| Arc::as_ptr(&ours) as *const () == wanted)
    }

    /// Register a reading operator, and say which record is its. Workers that read as one
    /// operator pass the same `name` and share a record; `None` is a reader of its own.
    ///
    /// Every reader registers before a row leaves: a reader that registered after a release
    /// would find reclaimed keys stated complete and absent.
    pub(crate) fn register_reader(&self, name: Option<String>) -> usize {
        let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
        debug_assert!(
            state.reclaimed.is_false(),
            "every reader registers before a row leaves: {:?} was reclaimed",
            state.reclaimed
        );
        if let Some(name) = &name
            && let Some(at) = state
                .readers
                .iter()
                .position(|r| r.name.as_ref() == Some(name))
        {
            return at;
        }
        state.readers.push(Reader {
            name,
            released: Predicate::False,
        });
        state.readers.len() - 1
    }

    /// Register a consumer of a pipeline behind the breaker. A consumer that registers after
    /// rows were absorbed hears of them at once.
    ///
    /// The consumer list is held from reading `ready` to pushing the consumer. Every publish that
    /// iterated the list before the push absorbed its rows first, so its region is inside the
    /// `ready` this reads, and every publish after the push reaches the consumer.
    pub(crate) fn add_downstream(&self, mut consumer: Box<dyn Consumer>) {
        let mut downstream = self.downstream.lock_wait();
        let ready = self.ready();
        if !ready.is_false() {
            consumer.notify(&Projection::admitting(ready));
        }
        downstream.push(consumer);
    }

    /// Reader `reader` has finished with the rows of `guard`'s region. The rows leave the output
    /// once every reader has released them.
    ///
    /// A release of everything before the breaker completed does not reclaim the rows absorbed
    /// after it: they are held until the next release finds every reader done with them. The
    /// release compacts the held tile, which costs in proportion to the rows it holds.
    pub(crate) fn release(&self, reader: usize, guard: &TileGuard) {
        let projection = Projection::of(guard).expect("a release names keys");
        let region = keys_of(&projection);
        let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
        // A release of everything names the keys that have not arrived too: a reader that is done
        // with the output says so whole.
        debug_assert!(
            projection == Projection::Everything || region.minus(&state.ready).is_false(),
            "a reader releases only rows that are ready: {region:?} against {:?}",
            state.ready
        );
        state.readers[reader].released = state.readers[reader].released.union(&region);
        let all = state
            .readers
            .iter()
            .map(|r| r.released.clone())
            .reduce(|a, b| a.intersect(&b))
            .expect("a reader released");
        let removable = all.intersect(&state.ready).minus(&state.reclaimed);
        if removable.is_false() {
            return;
        }
        state
            .tile
            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(
                removable.clone(),
            )));
        state.tile.compact();
        state.reclaimed = state.reclaimed.union(&removable);
    }

    /// The run is over and no producer reads the output: drop the readers' records and every row.
    /// A producer that was dropped without releasing does not pin rows past this call.
    pub(crate) fn retire_readers(&self) {
        let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
        state.readers.clear();
        let held = state.ready.minus(&state.reclaimed);
        if !held.is_false() {
            state
                .tile
                .remove_guarded(TileGuard::Function(FunctionGuard::Domain(held.clone())));
            state.tile.compact();
            state.reclaimed = state.reclaimed.union(&held);
        }
    }
}

/// The keys a projection names.
fn keys_of(projection: &Projection) -> Predicate {
    match projection {
        Projection::Everything => Predicate::True,
        Projection::Nothing => Predicate::False,
        Projection::Keys(keys) => keys.clone(),
        Projection::Fields(_) => panic!("a region of fields names no keys: {projection:?}"),
    }
}

//! A dispatcher of work packages between the pipelines of a program, shared by the threads that
//! claim them.
//!
//! A pipeline is a [`Breaker`] and the chain it owns; the breaker of a pipeline that another
//! reads is a [`BreakingProducer`]. The dispatcher holds the graph of pipelines, a window of
//! epochs in flight, and a queue of work packages per pipeline per epoch, each package one morsel
//! of at most `morsel_rows` held rows. A queue is appended to while it is open, each slot written
//! once, and read through atomic counters, so a claim takes no lock. A worker takes a lock to sleep
//! while there is nothing to claim, and a change that can end a sleep takes it to wake the
//! sleepers, only while there are some. The dispatcher holds no
//! breaker, so it is `Sync` while the breakers are not `Send`. The single-threaded driver, [`run`],
//! reaches the breakers through the handles its caller passes, indexed by pipeline. Nothing outside
//! unit tests calls it, and only unit tests drive the dispatcher from several threads. See
//! `src/interpreter/design-operators.md`, "The dispatcher".

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock, PoisonError, RwLock};
use std::thread;

use intervalsets::Bounding;

#[cfg(test)]
use crate::interpreter::CurryLevel;
use crate::interpreter::tile_operators::InputId;
use crate::interpreter::tile_operators::{
    Breaker, BreakingProducer, FunctionGuard, Tiling, cut_before, guard_minus, partition_gap,
};
use crate::interpreter::{
    Consumer, Extent, Predicate, Projection, SharedConsumer, TileGuard, Value,
};

#[cfg(test)]
mod loop_scope;

/// A pipeline, by its index in the [`Dispatcher`].
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct PipelineId(pub usize);

/// A guard for one pipeline's breaker to consume in one epoch: one morsel of a pushed guard, or of
/// a source pipeline's input.
#[cfg_attr(test, derive(Clone, Debug, PartialEq))]
pub struct WorkPackage {
    pub pipeline: PipelineId,
    pub guard: TileGuard,
    /// The epoch the package belongs to.
    pub epoch: u64,
    /// The package's position in its pipeline's queue for that epoch, which its acknowledgement
    /// marks.
    pub(crate) index: usize,
}

/// What a worker does next, as [`Dispatcher::try_claim`] answers.
#[cfg_attr(test, derive(Debug))]
pub enum Next {
    /// Hand the package to its pipeline's breaker, then [`acknowledge`](Dispatcher::acknowledge)
    /// it.
    Package(WorkPackage),
    /// Finish the pipeline's epoch, which the claim moved to finishing, then
    /// [`finish`](Dispatcher::finish) it: push what the epoch decided and no consume pushed,
    /// through the breaker's [`finish`][Breaker::finish], with `last` where the epoch is the run's
    /// last. `consumed` is the region the epoch's packages partition, which the pipeline
    /// consumed whole, and `None` when it had none.
    ///
    /// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
    Finish {
        pipeline: PipelineId,
        epoch: u64,
        consumed: Option<TileGuard>,
        last: bool,
    },
    /// Nothing is claimable and some pipeline has not finished: [`wait`](Dispatcher::wait) for a
    /// change after the generation.
    Wait(Generation),
    /// Every pipeline has finished the run's last epoch.
    Done,
    /// The run failed ([`Dispatcher::fail`]): stop, whatever has not finished.
    Failed,
}

/// The count of the dispatcher's changes that can make a claim succeed, as a claim observed it.
#[cfg_attr(test, derive(Debug))]
pub struct Generation(u64);

/// Where a pipeline is in one epoch. It is `Finishing` from the claim, or the
/// [`Dispatcher::begin_finish`], that moves it there until [`Dispatcher::finish`].
#[derive(PartialEq)]
#[repr(u8)]
enum Phase {
    Running,
    Finishing,
    Finished,
}

/// A [`Phase`] read and written atomically.
struct AtomicPhase(AtomicU8);

impl AtomicPhase {
    fn new(phase: Phase) -> Self {
        AtomicPhase(AtomicU8::new(phase as u8))
    }

    fn load(&self) -> Phase {
        match self.0.load(Ordering::Acquire) {
            0 => Phase::Running,
            1 => Phase::Finishing,
            2 => Phase::Finished,
            other => unreachable!("an atomic phase holds a phase, not {other}"),
        }
    }

    /// Move from `from` to `to`, and answer whether the phase was `from`. Of two moves from one
    /// phase, exactly one succeeds.
    fn moved(&self, from: Phase, to: Phase) -> bool {
        self.0
            .compare_exchange(from as u8, to as u8, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
    }
}

/// How many slots a queue's first bucket holds; bucket `b` holds `FIRST_BUCKET << b`.
const FIRST_BUCKET: usize = 32;

/// The bit of a queue's `reserved` count that says the queue is closed.
const CLOSED: usize = 1 << (usize::BITS - 1);

/// How many buckets a queue has: enough for every `usize` index.
const BUCKETS: usize = (usize::BITS - FIRST_BUCKET.trailing_zeros()) as usize;

/// How many epochs a dispatcher keeps in flight unless [`Dispatcher::window`] says otherwise.
const DEFAULT_WINDOW: usize = 4;

/// The epoch number that says the run's last epoch is not known yet.
const UNKNOWN: u64 = u64::MAX;

/// The work packages queued for one pipeline in one epoch. Packages are appended while the queue
/// is open, and a claim takes one by its index. An append reserves its indices and then writes
/// their slots, once, so a claim takes no lock: it reads a slot only once it is written. Nothing
/// is appended once the queue is closed, so a closed queue whose every package is acknowledged is
/// consumed.
struct Queue {
    /// The slots, `FIRST_BUCKET << b` in bucket `b`, which the first append that reaches it
    /// allocates. A bucket never moves once allocated, so a slot's address is stable.
    // shared-state-ok: the pipeline's packages, each slot written once by an append and read by
    // every claiming thread; what crosses it is a guard naming a region, never a tile.
    buckets: [OnceLock<Box<[Slot]>>; BUCKETS],
    /// How many indices appends have reserved, with [`CLOSED`] set once the queue is closed. A slot
    /// below the count is written or being written. One word holds both, so an append reserves
    /// only while the queue is open, and a read of the count after the close is the last.
    reserved: AtomicUsize,
    /// The union of the guards appended, which the packages partition; `None` while none is.
    /// Appends take it, and so does the move of the pipeline's epoch to finishing; a claim of a
    /// package never does.
    // shared-state-ok: the region a pipeline's packages partition, which appends grow and its
    // finish reads; what crosses it is a guard naming a region, never a tile.
    region: Mutex<Option<TileGuard>>,
}

/// One package's place in its queue.
#[derive(Default)]
struct Slot {
    // shared-state-ok: a package's guard, written once by the append that reserved the slot and
    // read by the claims after; it is a guard naming a region, never a tile.
    guard: OnceLock<TileGuard>,
    is_acknowledged: AtomicBool,
}

impl Queue {
    fn new() -> Self {
        Queue {
            buckets: std::array::from_fn(|_| OnceLock::new()),
            reserved: AtomicUsize::new(0),
            region: Mutex::new(None),
        }
    }

    /// The bucket index `index` lies in, and its place in that bucket.
    fn locate(index: usize) -> (usize, usize) {
        let shifted = index + FIRST_BUCKET;
        let bucket = (shifted.ilog2() - FIRST_BUCKET.ilog2()) as usize;
        (bucket, shifted - (FIRST_BUCKET << bucket))
    }

    /// The slot at `index`, `None` before an append has allocated its bucket.
    fn slot(&self, index: usize) -> Option<&Slot> {
        let (bucket, at) = Self::locate(index);
        self.buckets[bucket].get().map(|slots| &slots[at])
    }

    /// The guard of the package at `index`, `None` before its append has written it.
    fn written(&self, index: usize) -> Option<&TileGuard> {
        self.slot(index)?.guard.get()
    }

    /// Append `morsels` to the queue of `pipeline`, which partition a region no earlier append
    /// named, and answer whether the queue was open to take them. A closed queue takes nothing.
    ///
    /// # Panics
    ///
    /// In a debug build, when a morsel meets the region appended before.
    fn append(&self, pipeline: usize, morsels: &[TileGuard]) -> bool {
        if morsels.is_empty() {
            return !self.is_closed();
        }
        let Some(first) = self.reserve(morsels.len()) else {
            return false;
        };
        {
            let mut region = self.region.lock().unwrap_or_else(PoisonError::into_inner);
            for morsel in morsels {
                debug_assert!(
                    region
                        .as_ref()
                        .is_none_or(|region| region.intersect(morsel).is_empty()),
                    "pipeline {pipeline} consumes each region once: {morsel:?} meets {region:?}"
                );
                *region = Some(match region.take() {
                    None => morsel.clone(),
                    Some(region) => region.union(morsel),
                });
            }
        }
        for (index, morsel) in (first..).zip(morsels) {
            self.write(index, morsel.clone());
        }
        true
    }

    /// Append `guard` less the region appended before as one package, and answer whether the
    /// queue was open to take it. The difference and the region's growth are one step under the
    /// region's lock, so a region two pushes both name is queued once, whichever thread pushes
    /// first. Nothing new appends nothing.
    ///
    /// # Panics
    ///
    /// Where the guard algebra has no exact difference of `guard` and the region ([`guard_minus`]).
    fn append_unqueued(&self, guard: &TileGuard) -> bool {
        let mut region = self.region.lock().unwrap_or_else(PoisonError::into_inner);
        let fresh = match region.as_ref() {
            Some(region) => guard_minus(guard, region),
            None => guard.clone(),
        };
        if fresh.is_empty() {
            return !self.is_closed();
        }
        let Some(index) = self.reserve(1) else {
            return false;
        };
        *region = Some(match region.take() {
            None => fresh.clone(),
            Some(region) => region.union(&fresh),
        });
        drop(region);
        self.write(index, fresh);
        true
    }

    /// Reserve `count` indices while the queue is open, and answer the first; `None` once it is
    /// closed.
    fn reserve(&self, count: usize) -> Option<usize> {
        let mut reserved = self.reserved.load(Ordering::Acquire);
        loop {
            if reserved & CLOSED != 0 {
                return None;
            }
            match self.reserved.compare_exchange_weak(
                reserved,
                reserved + count,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(first) => return Some(first),
                Err(now) => reserved = now,
            }
        }
    }

    /// Write the package at `index`, which an append reserved.
    fn write(&self, index: usize, guard: TileGuard) {
        let (bucket, at) = Self::locate(index);
        let slots = self.buckets[bucket].get_or_init(|| {
            (0..FIRST_BUCKET << bucket)
                .map(|_| Slot::default())
                .collect()
        });
        let written = slots[at].guard.set(guard).is_ok();
        debug_assert!(written, "an append writes the slot it reserved, once");
    }

    /// How many indices appends have reserved.
    fn reserved(&self) -> usize {
        self.reserved.load(Ordering::Acquire) & !CLOSED
    }

    fn is_closed(&self) -> bool {
        self.reserved.load(Ordering::Acquire) & CLOSED != 0
    }

    /// Close the queue, and answer whether it was open.
    fn close(&self) -> bool {
        self.reserved.fetch_or(CLOSED, Ordering::AcqRel) & CLOSED == 0
    }

    /// The region the packages partition, `None` when there are none.
    fn region(&self) -> Option<TileGuard> {
        self.region
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

/// One pipeline's queue and progress in one epoch. A claim reads it without a lock.
struct EpochPipeline {
    queue: Queue,
    /// The index of the next package to claim. It never passes `queue.reserved`.
    claimed: AtomicUsize,
    /// How many of the pipeline's packages in the epoch have been acknowledged.
    acknowledged: AtomicUsize,
    phase: AtomicPhase,
    /// How many of the pipelines it reads have not finished the epoch. The finish that brings it
    /// to zero closes the queue.
    unfinished: AtomicUsize,
}

/// What the dispatcher keeps for one epoch, every pipeline's part of it. The window's slot holds
/// it from the epoch's opening until every pipeline has finished it.
struct EpochState {
    number: u64,
    pipelines: Vec<EpochPipeline>,
    /// How many pipelines have not finished the epoch. The finish that brings it to zero retires
    /// the epoch.
    unfinished: AtomicUsize,
}

impl EpochState {
    /// Epoch `number` of the pipelines `infos` describes.
    fn new(number: u64, infos: &[PipelineInfo]) -> Self {
        EpochState {
            number,
            pipelines: infos
                .iter()
                .map(|info| EpochPipeline {
                    queue: Queue::new(),
                    claimed: AtomicUsize::new(0),
                    acknowledged: AtomicUsize::new(0),
                    phase: AtomicPhase::new(Phase::Running),
                    unfinished: AtomicUsize::new(info.reads.len()),
                })
                .collect(),
            unfinished: AtomicUsize::new(infos.len()),
        }
    }
}

/// What the dispatcher knows of one pipeline: where it sits in the graph and how it consumes.
/// It is fixed before the dispatcher is shared, since the methods that set it take `&mut self`.
struct PipelineInfo {
    /// The pipelines it reads: the breakers its chain pulls.
    reads: Vec<usize>,
    /// The pipelines that read it: the queues its finish closes, and the pipelines its pushes may
    /// reach through its breaker's consumer.
    readers: Vec<usize>,
    /// Whether it consumes its morsels in queue order one at a time
    /// ([`order`](Dispatcher::order)).
    ordered: bool,
    /// Where it reads its breaker's input whole rather than what the pipelines it reads push
    /// ([`read_whole`](Dispatcher::read_whole)), that input's morsels.
    whole: Option<Vec<TileGuard>>,
    /// The pipelines it reads that it takes no push from, and whose finish of an epoch it waits
    /// for before it takes a package there ([`build`](Dispatcher::build)).
    builds: Vec<usize>,
    /// For a source, the most packages queued for it and not yet acknowledged that a notify finds
    /// before it queues more ([`limit`](Dispatcher::limit)); `usize::MAX` for none.
    limit: usize,
}

/// What the dispatcher keeps of one pipeline across epochs.
struct PipelineState {
    /// The region this pipeline's breaker has pushed to its reader, which each push grows by
    /// what it pushes. A push of a breaker's final guard pushes what is not in it.
    // shared-state-ok: the region a pipeline has pushed, which its pushes read and grow under the
    // lock; what crosses it is a guard naming a region, never a tile.
    pushed: Mutex<Option<TileGuard>>,
    /// For a source, whether it is closed: no more of its input arrives.
    closed: AtomicBool,
    /// How many of a source's packages have been queued, in every epoch.
    queued: AtomicUsize,
    /// How many of the pipeline's packages have been acknowledged, in every epoch.
    acknowledged: AtomicUsize,
    /// For an ordered pipeline, whether a package of it is in flight, in any epoch.
    in_flight: AtomicBool,
}

impl PipelineState {
    /// How many of the pipeline's packages are queued and not acknowledged. The acknowledgements
    /// are read first: a notify counts its packages queued before it appends them, so a package
    /// is acknowledged only after it was counted, and the queued count read after is at least as
    /// large, whichever threads queue and acknowledge meanwhile.
    fn outstanding(&self) -> usize {
        let acknowledged = self.acknowledged.load(Ordering::Acquire);
        self.queued.load(Ordering::Acquire) - acknowledged
    }
}

/// The graph of pipelines, the epochs in flight, the work packages queued for each pipeline in
/// each epoch, and what each has consumed.
pub struct Dispatcher {
    /// The most held rows a work package names.
    morsel_rows: usize,
    /// What each pipeline is, fixed before the dispatcher is shared.
    infos: Vec<PipelineInfo>,
    /// What each pipeline has done across epochs, which the workers change.
    states: Vec<PipelineState>,
    /// The window of epochs in flight: slot `e % window.len()` holds epoch `e` from its opening
    /// until every pipeline has finished it, and then epoch `e + window.len()`.
    // shared-state-ok: the epochs in flight, each swapped for the one a window later once every
    // pipeline has finished it; a claim takes the lock only to clone the epoch's handle, and what
    // crosses it is queues of guards naming regions, never a tile.
    window: Vec<RwLock<Arc<EpochState>>>,
    /// The epoch sources are notified into.
    current: AtomicU64,
    /// The run's last epoch, [`UNKNOWN`] until every source is closed.
    last: AtomicU64,
    /// Set once every pipeline has finished the last epoch.
    done: AtomicBool,
    /// Orders a seal and a close, which move `current` and close sources' queues.
    // shared-state-ok: the lock that orders seals and closes; it guards no data.
    sealing: Mutex<()>,
    /// Set by [`Dispatcher::fail`], and by every refusal before it panics ([`Dispatcher::ensure`]).
    failed: AtomicBool,
    /// Advances at every change that can make a claim succeed or end the run: an append, a seal,
    /// a close, an acknowledgement that frees an ordered pipeline's next package, completes a
    /// queue or returns credit to a limited source, a finish, and a failure. It also advances when
    /// a claim of an ordered pipeline that found nothing finds a package queued while it looked,
    /// for a claim that found the pipeline's flag held meanwhile.
    generation: AtomicU64,
    /// How many threads sleep in [`Dispatcher::wait`]. An advance takes the `sleep` lock only when
    /// it is not zero.
    sleepers: AtomicUsize,
    // shared-state-ok: the lock a sleeping worker waits under; it guards no data.
    sleep: Mutex<()>,
    /// Signalled, under `sleep`, whenever the generation advances while a thread sleeps.
    wake: Condvar,
    /// What the workers did, each event recorded before the change that lets a later event happen.
    #[cfg(test)]
    events: Mutex<Vec<Event>>,
    /// Whether `events` records; off, no test-only lock orders the acknowledgements.
    #[cfg(test)]
    recording: bool,
}

impl Dispatcher {
    /// The dispatcher of the pipelines `reads` describes: `reads[p]` lists the pipelines `p`
    /// reads. A work package names at most `morsel_rows` held rows. Epoch 0 is open, and the
    /// window holds [`DEFAULT_WINDOW`] epochs.
    ///
    /// # Panics
    ///
    /// When `morsel_rows` is zero, when a pipeline reads one that does not exist or reads one
    /// pipeline twice, or when the graph has a cycle. Several pipelines may read one: a `FanOut`
    /// between them keeps the release of one from removing what another has still to read. A
    /// pipeline may read several, and its queue in an epoch closes at the finish of the last of
    /// them. A pipeline in a cycle would wait for itself to finish.
    pub fn new(reads: Vec<Vec<usize>>, morsel_rows: usize) -> Self {
        assert!(morsel_rows > 0, "a morsel holds at least one row");
        let count = reads.len();
        let mut readers = vec![Vec::new(); count];
        for (pipeline, pipeline_reads) in reads.iter().enumerate() {
            for (at, &read) in pipeline_reads.iter().enumerate() {
                assert!(
                    !pipeline_reads[..at].contains(&read),
                    "pipeline {pipeline} reads pipeline {read} once"
                );
                assert!(
                    read < count,
                    "pipeline {pipeline} reads {read}, which is not one"
                );
                readers[read].push(pipeline);
            }
        }
        assert!(
            acyclic(&reads),
            "the pipelines read each other in a cycle: {reads:?}"
        );
        let infos: Vec<_> = reads
            .into_iter()
            .zip(readers)
            .map(|(reads, readers)| PipelineInfo {
                reads,
                readers,
                ordered: false,
                whole: None,
                builds: Vec::new(),
                limit: usize::MAX,
            })
            .collect();
        let states = (0..count)
            .map(|_| PipelineState {
                pushed: Mutex::new(None),
                closed: AtomicBool::new(false),
                queued: AtomicUsize::new(0),
                acknowledged: AtomicUsize::new(0),
                in_flight: AtomicBool::new(false),
            })
            .collect();
        let window = Self::slots(DEFAULT_WINDOW, &infos);
        Self {
            morsel_rows,
            infos,
            states,
            window,
            current: AtomicU64::new(0),
            last: AtomicU64::new(UNKNOWN),
            done: AtomicBool::new(false),
            sealing: Mutex::new(()),
            failed: AtomicBool::new(false),
            generation: AtomicU64::new(0),
            sleepers: AtomicUsize::new(0),
            sleep: Mutex::new(()),
            wake: Condvar::new(),
            #[cfg(test)]
            events: Mutex::new(Vec::new()),
            #[cfg(test)]
            recording: true,
        }
    }

    /// A window of `epochs` slots holding epochs `0..epochs`.
    fn slots(epochs: usize, infos: &[PipelineInfo]) -> Vec<RwLock<Arc<EpochState>>> {
        (0..epochs as u64)
            .map(|number| RwLock::new(Arc::new(EpochState::new(number, infos))))
            .collect()
    }

    /// Keep `epochs` epochs in flight in place of [`DEFAULT_WINDOW`]: a seal opens an epoch only
    /// once the epoch a window before it has retired. It replaces every epoch, so it comes before
    /// any notify, seal or close.
    ///
    /// # Panics
    ///
    /// When `epochs` is below two: a seal opens the next epoch while the current one is in
    /// flight, and the current one retires only once it is sealed, so one slot would hold both.
    /// Also when a source has been notified, sealed or closed already.
    pub fn window(&mut self, epochs: usize) {
        assert!(
            epochs >= 2,
            "a window holds the epoch a seal opens beside the one it seals"
        );
        assert!(
            self.current.load(Ordering::Acquire) == 0
                && self.states.iter().all(|pipeline| {
                    pipeline.queued.load(Ordering::Acquire) == 0
                        && !pipeline.closed.load(Ordering::Acquire)
                }),
            "a window is set before any notify, seal or close"
        );
        self.window = Self::slots(epochs, &self.infos);
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// current epoch, less what is queued for it there already: at the start, what a range brings
    /// that no push names ([`run_program`]), and in a loop's round, the row of a nested loop's
    /// store, which reads the pipelines inside the cycle around it by build edges
    /// (`loop_scope::LoopScope`).
    ///
    /// # Panics
    ///
    /// When `reader`'s queue in the current epoch has closed: every pipeline it reads has
    /// finished the epoch.
    #[cfg(test)]
    pub(crate) fn queue_for(&self, reader: PipelineId, guard: &TileGuard) {
        let current = self.current.load(Ordering::Acquire);
        let epoch = self
            .epoch(current)
            .expect("the window holds the current epoch");
        assert!(
            epoch.pipelines[reader.0].queue.append_unqueued(guard),
            "pipeline {} takes packages before the last pipeline it reads finishes",
            reader.0
        );
        self.advance();
    }

    /// Whether `pipeline` is a source, one that reads no pipeline.
    #[cfg(test)]
    pub(crate) fn is_source(&self, pipeline: PipelineId) -> bool {
        self.infos[pipeline.0].reads.is_empty()
    }

    /// Mark `reader`'s edge from `read`, a pipeline it reads, as a build edge: `reader` takes no
    /// push of `read`'s, and takes a package in an epoch only once `read` has finished it, since
    /// its chain reads `read`'s breaker, as a lookup reads its table, final for the epoch only
    /// then.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`.
    pub fn build(&mut self, reader: PipelineId, read: PipelineId) {
        assert!(
            self.infos[reader.0].reads.contains(&read.0),
            "pipeline {} builds on pipeline {}, which it reads",
            reader.0,
            read.0
        );
        self.infos[reader.0].builds.push(read.0);
    }

    /// Whether a claim may take `pipeline`'s packages in `epoch`: once every pipeline it builds on
    /// ([`build`](Self::build)) has finished the epoch.
    fn takes_from(&self, pipeline: usize, epoch: &EpochState) -> bool {
        self.infos[pipeline]
            .builds
            .iter()
            .all(|read| epoch.pipelines[*read].phase.load() == Phase::Finished)
    }

    /// Mark `pipeline`, which reads a pipeline, as consuming its breaker's input whole, `input`
    /// cut one package per morsel ([`seed`]), in the run's last epoch, in place of what the
    /// pipelines it reads push. A planner does so where no push reaches the reader restated in its
    /// keys, where two pipelines it reads can push one key, or where a pipeline it reads takes no
    /// push and names no region the planner could queue for the reader at the start
    /// (`run_program`). Its
    /// input is whole only once every epoch has run, so its queue in an earlier epoch closes
    /// empty, and it takes no push ([`Landing::queue`]).
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline.
    pub fn read_whole(&mut self, pipeline: PipelineId, input: &Tiling) {
        assert!(
            !self.infos[pipeline.0].reads.is_empty(),
            "pipeline {} reads its input whole only after a pipeline it reads; a source does so \
             from its start",
            pipeline.0
        );
        self.infos[pipeline.0].whole = Some(seed(input, self.morsel_rows));
    }

    /// Mark `pipeline` as consuming its morsels one at a time, epoch by epoch: every morsel of an
    /// epoch in the order it was queued, then the epoch's finish, then the next epoch's. Its
    /// breaker's state advances through them in order, as a loop's store decides its positions
    /// ascending.
    pub fn order(&mut self, pipeline: PipelineId) {
        self.infos[pipeline.0].ordered = true;
    }

    /// Let a notify of the source `pipeline` queue more only while fewer than `packages` of its
    /// packages are queued and not acknowledged, in every epoch: [`notify`](Self::notify) waits
    /// until then, and [`try_notify`](Self::try_notify) answers that it did not queue. A notify
    /// admitted below the limit queues all its morsels, so the packages outstanding exceed
    /// `packages` by at most one notify's morsels less one, for one thread that notifies.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline, or `packages` is zero.
    pub fn limit(&mut self, pipeline: PipelineId, packages: usize) {
        let p = pipeline.0;
        assert!(
            self.infos[p].reads.is_empty(),
            "pipeline {p} is limited only as a source: a reader is queued what is pushed to it"
        );
        assert!(packages > 0, "a source's limit is at least one package");
        self.infos[p].limit = packages;
    }

    /// The handle a breaker of `pipeline` pushes through, for its oldest epoch it has not
    /// finished. Its pushes land at [`finish`](Self::finish).
    #[cfg(test)]
    pub(crate) fn pushes(&self, pipeline: PipelineId) -> Pushes<'_> {
        self.state(pipeline);
        let epoch = Self::unfinished(pipeline.0, &self.epochs())
            .map_or(self.current.load(Ordering::Acquire), |epoch| epoch.number);
        self.pushes_in(pipeline, epoch)
    }

    /// The handle a breaker of `pipeline` pushes through for `epoch`.
    pub fn pushes_in(&self, pipeline: PipelineId, epoch: u64) -> Pushes<'_> {
        self.state(pipeline);
        Pushes {
            to: None,
            dispatcher: self,
            pipeline: pipeline.0,
            epoch,
            morsels: Vec::new(),
        }
    }

    /// The handle a worker thread holds while it claims: when the thread panics, dropping the
    /// handle fails the run, so no other worker waits for a package the panicking one claimed.
    pub fn worker(&self) -> Worker<'_> {
        Worker(self)
    }

    /// Fail the run, then panic with `message` unless `holds`: a dispatcher whose caller broke its
    /// protocol answers no claim after, and every waiter wakes.
    fn ensure(&self, holds: bool, message: impl FnOnce() -> String) {
        if !holds {
            self.refuse(message());
        }
    }

    /// Fail the run, then panic with `message`.
    fn refuse(&self, message: String) -> ! {
        self.fail();
        panic!("{message}");
    }

    /// The state of `pipeline` across epochs.
    ///
    /// # Panics
    ///
    /// When the dispatcher has no such pipeline.
    fn state(&self, pipeline: PipelineId) -> &PipelineState {
        let count = self.states.len();
        self.ensure(pipeline.0 < count, || {
            format!(
                "pipeline {} is one of the dispatcher's {count} pipelines",
                pipeline.0
            )
        });
        &self.states[pipeline.0]
    }

    /// Epoch `epoch`, while the window holds it.
    fn epoch(&self, epoch: u64) -> Option<Arc<EpochState>> {
        let slot = &self.window[(epoch % self.window.len() as u64) as usize];
        let state = slot.read().unwrap_or_else(PoisonError::into_inner).clone();
        (state.number == epoch).then_some(state)
    }

    /// The epochs open so far that the window holds, oldest first.
    fn epochs(&self) -> Vec<Arc<EpochState>> {
        let current = self.current.load(Ordering::Acquire);
        let mut epochs: Vec<_> = self
            .window
            .iter()
            .map(|slot| slot.read().unwrap_or_else(PoisonError::into_inner).clone())
            .filter(|epoch| epoch.number <= current)
            .collect();
        epochs.sort_by_key(|epoch| epoch.number);
        epochs
    }

    /// Advance the generation, and wake every sleeper when there is one.
    ///
    /// A sleeper counts itself under `sleep` before it reads the generation, and an advance writes
    /// the generation before it reads the count, all four sequentially consistent. So either the
    /// sleeper reads the new generation and does not sleep, or the advance reads its count and
    /// takes `sleep`, which the sleeper holds until it waits on `wake`.
    fn advance(&self) {
        self.generation.fetch_add(1, Ordering::SeqCst);
        if self.sleepers.load(Ordering::SeqCst) > 0 {
            let _sleep = self.sleep.lock().unwrap_or_else(PoisonError::into_inner);
            self.wake.notify_all();
        }
    }

    /// Queue a source pipeline's input whole in the current epoch and close the source: `input`,
    /// the tiling its breaker's input answers, as one package per morsel ([`seed`]). It queues as
    /// [`notify`](Self::notify) would, without waiting for any limit, the universal guard cut by
    /// the range of positions `input` states, then [`close`](Self::close)s the source.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline, or is closed.
    pub fn start_source(&self, pipeline: PipelineId, input: &Tiling) {
        let morsels = seed(input, self.morsel_rows);
        debug_assert!(
            partition_gap(&input.universal_guard(), &morsels).is_none(),
            "the morsels of a source's input partition it: {}",
            partition_gap(&input.universal_guard(), &morsels).unwrap_or_default()
        );
        self.append_to_source(pipeline, &morsels);
        self.close(pipeline);
    }

    /// Queue `guard`, a region of a source pipeline's input that has arrived, in the current
    /// epoch, as one package per morsel: every `morsel_rows` positions, where `guard` names finite
    /// runs of positions (`Value::UInt` keys), and whole otherwise. The workers claim them while
    /// the epoch runs.
    ///
    /// A source [limited](Self::limit) to as many packages outstanding as it has waits until one
    /// is acknowledged, so the thread that notifies is held back by the workers. After a failure
    /// it returns at once, having queued nothing.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline or is closed; in a debug build, when `guard` meets a
    /// region queued for it before in the epoch.
    pub fn notify(&self, pipeline: PipelineId, guard: &TileGuard) {
        loop {
            // Read before the check: an acknowledgement the check misses advances the generation
            // past this one, so the wait returns at once.
            let generation = self.generation.load(Ordering::SeqCst);
            if self.try_notify(pipeline, guard) {
                return;
            }
            self.wait(Generation(generation));
        }
    }

    /// [`notify`](Self::notify) without waiting: whether `guard` is queued, which it is not while
    /// the source has as many packages outstanding as its [limit](Self::limit). After a failure
    /// it queues nothing and answers `true`, since nothing will acknowledge a package.
    ///
    /// # Panics
    ///
    /// As [`notify`](Self::notify).
    pub fn try_notify(&self, pipeline: PipelineId, guard: &TileGuard) -> bool {
        if self.failed.load(Ordering::SeqCst) || guard.is_empty() {
            return true;
        }
        self.ensure_source(pipeline);
        if self.state(pipeline).outstanding() >= self.infos[pipeline.0].limit {
            return false;
        }
        let morsels = cut_positions(guard, self.morsel_rows);
        debug_assert!(
            partition_gap(guard, &morsels).is_none(),
            "the morsels of a notified guard partition it: {}",
            partition_gap(guard, &morsels).unwrap_or_default()
        );
        self.append_to_source(pipeline, &morsels);
        true
    }

    /// Refuse `pipeline` unless it is a source, one that reads no pipeline.
    fn ensure_source(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.infos[p].reads.is_empty(), || {
            format!("pipeline {p} is queued its input only as a source, which reads no pipeline")
        });
    }

    /// Append `morsels` to the source `pipeline`'s queue in the current epoch. A seal that closes
    /// that queue first leaves the append to the next epoch.
    fn append_to_source(&self, pipeline: PipelineId, morsels: &[TileGuard]) {
        let p = pipeline.0;
        self.ensure_source(pipeline);
        let state = self.state(pipeline);
        // Counted before the append makes the packages claimable, so an acknowledgement never
        // runs ahead of the count `outstanding` subtracts it from.
        state.queued.fetch_add(morsels.len(), Ordering::AcqRel);
        loop {
            self.ensure(!state.closed.load(Ordering::Acquire), || {
                format!("pipeline {p} is queued nothing once it is closed")
            });
            let current = self.current.load(Ordering::Acquire);
            // An epoch sealed after the read of `current` may have retired since, its slot taken
            // by the epoch a window later; the reread finds the epoch after it.
            let Some(epoch) = self.epoch(current) else {
                continue;
            };
            if epoch.pipelines[p].queue.append(p, morsels) {
                break;
            }
        }
        self.advance();
    }

    /// End the current epoch and open the next: every open source's queue in the current epoch
    /// closes, and later notifies land in the next. It waits while the window's slot for the next
    /// epoch still holds the epoch a window before it, so the window bounds the epochs in flight.
    /// After a failure it returns at once.
    ///
    /// # Panics
    ///
    /// When every source is closed: the last epoch has no epoch after it. The threads that seal
    /// and close order every seal before the last close, since a seal that waits for its slot
    /// while the last source closes is refused too.
    pub fn seal(&self) {
        loop {
            let generation = self.generation.load(Ordering::SeqCst);
            if self.try_seal() {
                return;
            }
            self.wait(Generation(generation));
        }
    }

    /// [`seal`](Self::seal) without waiting: whether the next epoch is open, which it is not while
    /// the window's slot for it holds an epoch in flight. After a failure it answers `true`.
    ///
    /// # Panics
    ///
    /// As [`seal`](Self::seal).
    pub fn try_seal(&self) -> bool {
        if self.failed.load(Ordering::SeqCst) {
            return true;
        }
        let _sealing = self.sealing.lock().unwrap_or_else(PoisonError::into_inner);
        self.ensure(self.last.load(Ordering::Acquire) == UNKNOWN, || {
            "a seal opens an epoch while a source is open".to_string()
        });
        let current = self.current.load(Ordering::Acquire);
        let Some(next) = self.epoch(current + 1) else {
            return false;
        };
        let sealed = self
            .epoch(current)
            .expect("the window holds the current epoch");
        for p in self.sources() {
            sealed.pipelines[p].queue.close();
        }
        // A source closed before is closed in every epoch after its close.
        for p in self.sources() {
            if self.states[p].closed.load(Ordering::Acquire) {
                next.pipelines[p].queue.close();
            }
        }
        self.current.store(current + 1, Ordering::Release);
        self.advance();
        true
    }

    /// The source pipelines, those that read none.
    fn sources(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.infos.len()).filter(|p| self.infos[*p].reads.is_empty())
    }

    /// Close a source pipeline: nothing more of its input arrives, its queue in the current epoch
    /// closes, and so does its queue in every epoch after. Once every source is closed, the
    /// current epoch is the run's last. A claim never finishes a source's epoch before its close
    /// or the seal of the epoch, so workers may claim before the sources start; they wait until
    /// then.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline, or is closed already.
    pub fn close(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        let state = self.state(pipeline);
        self.ensure(self.infos[p].reads.is_empty(), || {
            format!("pipeline {p} closes its queue only as a source, which reads no pipeline")
        });
        let _sealing = self.sealing.lock().unwrap_or_else(PoisonError::into_inner);
        let closed = !state.closed.swap(true, Ordering::AcqRel);
        self.ensure(closed, || format!("pipeline {p} closes its queue once"));
        let current = self.current.load(Ordering::Acquire);
        if self
            .sources()
            .all(|source| self.states[source].closed.load(Ordering::Acquire))
        {
            self.last.store(current, Ordering::Release);
        }
        self.epoch(current)
            .expect("the window holds the current epoch")
            .pipelines[p]
            .queue
            .close();
        self.advance();
    }

    /// The package at the front of `pipeline`'s queue in its oldest epoch that has one, recorded
    /// as claimed, where a claim may take one. An ordered pipeline has at most one package in
    /// flight, and takes it only from the oldest epoch it has not finished.
    fn claim_from(&self, pipeline: usize, epochs: &[Arc<EpochState>]) -> Option<WorkPackage> {
        if !self.infos[pipeline].ordered {
            return epochs
                .iter()
                .filter(|epoch| self.takes_from(pipeline, epoch))
                .find_map(|epoch| Self::claim_in(pipeline, epoch));
        }
        let state = &self.states[pipeline];
        // The flag is held while the claim looks, so at most one claim of the pipeline looks at
        // once, and kept for the package it takes.
        if state
            .in_flight
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            return None;
        }
        let package = Self::unfinished(pipeline, epochs)
            .filter(|epoch| self.takes_from(pipeline, epoch))
            .and_then(|epoch| Self::claim_in(pipeline, epoch));
        if package.is_none() {
            state.in_flight.store(false, Ordering::SeqCst);
            // A claim that found the flag held answered nothing for the pipeline, and may wait on
            // a generation that a package queued since this look began has reached. The flag's
            // operations and the generation's are sequentially consistent, so the generation read
            // after the release sees that package's advance and every write before it, and a
            // second look finds the package and wakes that claim.
            self.generation.load(Ordering::SeqCst);
            if Self::unfinished(pipeline, &self.epochs()).is_some_and(|epoch| {
                self.takes_from(pipeline, epoch) && Self::claimable(pipeline, epoch)
            }) {
                self.advance();
            }
        }
        package
    }

    /// The oldest of `epochs` that `pipeline` has not finished.
    fn unfinished(pipeline: usize, epochs: &[Arc<EpochState>]) -> Option<&EpochState> {
        epochs
            .iter()
            .map(|epoch| &**epoch)
            .find(|epoch| epoch.pipelines[pipeline].phase.load() != Phase::Finished)
    }

    /// Whether the package at the front of `pipeline`'s queue in `epoch` is written and not
    /// claimed.
    fn claimable(pipeline: usize, epoch: &EpochState) -> bool {
        let state = &epoch.pipelines[pipeline];
        let index = state.claimed.load(Ordering::Acquire);
        index < state.queue.reserved() && state.queue.written(index).is_some()
    }

    /// The package at the front of `pipeline`'s queue in `epoch`, recorded as claimed, where it
    /// has one written.
    fn claim_in(pipeline: usize, epoch: &EpochState) -> Option<WorkPackage> {
        let state = &epoch.pipelines[pipeline];
        loop {
            // A claim moves `claimed` by compare and exchange, so it never passes a package a
            // later append writes: the index it takes is one whose slot it read written.
            let index = state.claimed.load(Ordering::Acquire);
            if index >= state.queue.reserved() {
                return None;
            }
            let guard = state.queue.written(index)?;
            let taken = state
                .claimed
                .compare_exchange(index, index + 1, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok();
            if taken {
                return Some(WorkPackage {
                    pipeline: PipelineId(pipeline),
                    guard: guard.clone(),
                    epoch: epoch.number,
                    index,
                });
            }
        }
    }

    /// Whether `pipeline` may finish `epoch`: it is running in it, its queue there is closed and
    /// every package in it acknowledged, and the epoch is sealed or known to be the last. Its
    /// last epoch it finishes only after every earlier one, since the breaker's `finish` there is
    /// its last call, and an ordered pipeline finishes every epoch after the earlier ones.
    fn ready(&self, pipeline: usize, epoch: &EpochState, epochs: &[Arc<EpochState>]) -> bool {
        let state = &epoch.pipelines[pipeline];
        // One read of the count and the close: nothing is reserved after the close, so the count
        // of a closed queue is its last.
        let reserved = state.queue.reserved.load(Ordering::Acquire);
        let last = self.last.load(Ordering::Acquire);
        state.phase.load() == Phase::Running
            && reserved & CLOSED != 0
            && state.acknowledged.load(Ordering::Acquire) == reserved & !CLOSED
            && (epoch.number < self.current.load(Ordering::Acquire) || last != UNKNOWN)
            && ((epoch.number != last && !self.infos[pipeline].ordered)
                || epochs
                    .iter()
                    .filter(|earlier| earlier.number < epoch.number)
                    .all(|earlier| earlier.pipelines[pipeline].phase.load() == Phase::Finished))
    }

    /// What to do next, without blocking. A claim takes the package at the front of `preferred`'s
    /// queue where it may, and otherwise of the lowest pipeline whose queue it may take from, each
    /// pipeline's oldest epoch first; an ordered pipeline takes from the oldest epoch it has not
    /// finished, and is skipped while a package of it is in flight. With no package to claim, it
    /// moves the oldest epoch's lowest pipeline that may finish it to finishing and hands its
    /// finish out, so exactly one claim does so for each pipeline and epoch. Otherwise it answers
    /// [`Next::Done`] once every pipeline has finished the last epoch, and [`Next::Wait`] before.
    /// After a failure it answers [`Next::Failed`].
    pub fn try_claim(&self, preferred: Option<PipelineId>) -> Next {
        // Read before the scan: a change the scan misses advances the generation past this one,
        // so a wait on it returns at once.
        let generation = self.generation.load(Ordering::SeqCst);
        if self.failed.load(Ordering::SeqCst) {
            return Next::Failed;
        }
        let count = self.infos.len();
        if let Some(preferred) = preferred {
            self.state(preferred);
        }
        let epochs = self.epochs();
        let mut scan = preferred.map(|p| p.0).into_iter().chain(0..count);
        if let Some(package) = scan.find_map(|p| self.claim_from(p, &epochs)) {
            return Next::Package(package);
        }
        for epoch in &epochs {
            for p in 0..count {
                let begun = self.ready(p, epoch, &epochs)
                    && epoch.pipelines[p]
                        .phase
                        .moved(Phase::Running, Phase::Finishing);
                if begun {
                    return Next::Finish {
                        pipeline: PipelineId(p),
                        epoch: epoch.number,
                        consumed: epoch.pipelines[p].queue.region(),
                        last: epoch.number == self.last.load(Ordering::Acquire),
                    };
                }
            }
        }
        if self.done.load(Ordering::Acquire) {
            return Next::Done;
        }
        Next::Wait(Generation(generation))
    }

    /// What to do next, blocking while there is nothing to: [`try_claim`](Self::try_claim) and
    /// [`wait`](Self::wait) until it answers something other than [`Next::Wait`].
    pub fn claim(&self, preferred: Option<PipelineId>) -> Next {
        loop {
            match self.try_claim(preferred) {
                Next::Wait(generation) => self.wait(generation),
                next => return next,
            }
        }
    }

    /// Block until the generation has advanced past `generation`, or the run has failed. A change
    /// between the claim that read `generation` and this call has advanced it already, so the
    /// wait returns at once rather than missing it.
    pub fn wait(&self, generation: Generation) {
        let changed = || {
            self.generation.load(Ordering::SeqCst) != generation.0
                || self.failed.load(Ordering::SeqCst)
        };
        if changed() {
            return;
        }
        let mut sleep = self.sleep.lock().unwrap_or_else(PoisonError::into_inner);
        self.sleepers.fetch_add(1, Ordering::SeqCst);
        while !changed() {
            sleep = self
                .wake
                .wait(sleep)
                .unwrap_or_else(PoisonError::into_inner);
        }
        self.sleepers.fetch_sub(1, Ordering::SeqCst);
    }

    /// Record `package` as consumed. After a failure it records nothing.
    ///
    /// # Panics
    ///
    /// When `package` is not one a claim handed out for its pipeline and epoch and not yet
    /// acknowledged.
    pub fn acknowledge(&self, package: WorkPackage) {
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        let p = package.pipeline.0;
        let state = self.state(package.pipeline);
        // A package in flight keeps its epoch in the window: the epoch retires only once every
        // pipeline has finished it, after every package of it is acknowledged.
        let epoch = self.epoch(package.epoch);
        let in_epoch = epoch.as_ref().map(|epoch| &epoch.pipelines[p]);
        let held = in_epoch.is_some_and(|in_epoch| {
            package.index < in_epoch.claimed.load(Ordering::Acquire)
                && in_epoch.queue.slot(package.index).is_some_and(|slot| {
                    slot.guard.get() == Some(&package.guard)
                        && !slot.is_acknowledged.swap(true, Ordering::AcqRel)
                })
        });
        let refused = || match self.infos[p].ordered {
            true => format!(
                "ordered pipeline {p} consumes the morsel claimed for it, in queue order: {:?}",
                package.guard
            ),
            false => format!(
                "pipeline {p} consumes a package claimed for it: {:?}",
                package.guard
            ),
        };
        self.ensure(held, refused);
        let in_epoch = in_epoch.expect("an acknowledged package's epoch");
        // Recorded before the count that lets the next package of an ordered pipeline, or the
        // pipeline's finish of the epoch, be claimed.
        #[cfg(test)]
        self.record(Event::Consume {
            pipeline: package.pipeline,
            guard: package.guard,
        });
        state.acknowledged.fetch_add(1, Ordering::AcqRel);
        let acknowledged = in_epoch.acknowledged.fetch_add(1, Ordering::AcqRel) + 1;
        if self.infos[p].ordered {
            state.in_flight.store(false, Ordering::Release);
        }
        // An acknowledgement frees an ordered pipeline's next package, may let the pipeline
        // finish the epoch, and returns credit to a limited source's notify.
        if self.infos[p].ordered
            || self.infos[p].limit != usize::MAX
            || acknowledged == in_epoch.queue.reserved()
        {
            self.advance();
        }
    }

    /// Move `pipeline`'s oldest epoch it has not begun to finish to finishing, outside a claim,
    /// and answer that epoch and what the pipeline consumed in it.
    ///
    /// # Panics
    ///
    /// When the pipeline has finished every epoch, a package queued for it in the epoch has not
    /// been acknowledged, a pipeline it reads has not finished the epoch, its queue in the epoch
    /// is not closed, the epoch is neither sealed nor known to be the last, or the pipeline has not
    /// finished every earlier epoch where the epoch is the last or the pipeline is ordered.
    pub fn begin_finish(&self, pipeline: PipelineId) -> (u64, Option<TileGuard>) {
        let p = pipeline.0;
        self.state(pipeline);
        let epochs = self.epochs();
        let epoch = epochs
            .iter()
            .find(|epoch| epoch.pipelines[p].phase.load() == Phase::Running);
        self.ensure(epoch.is_some(), || format!("pipeline {p} finishes once"));
        let epoch = epoch.expect("refused above");
        let state = &epoch.pipelines[p];
        self.ensure(
            state.acknowledged.load(Ordering::Acquire) == state.queue.reserved(),
            || {
                format!(
                    "pipeline {p} finishes after its queue is empty and every package claimed \
                     for it was acknowledged"
                )
            },
        );
        self.ensure(
            self.infos[p]
                .reads
                .iter()
                .all(|read| epoch.pipelines[*read].phase.load() == Phase::Finished),
            || format!("pipeline {p} finishes after every pipeline it reads has finished"),
        );
        // A source's queue is closed by a seal or its close. A pipeline that reads others has its
        // queue filled and closed once the pushes of the last of them to finish landed, which
        // `finish` does after it marks that one finished.
        self.ensure(state.queue.is_closed(), || {
            format!("pipeline {p} finishes after its queue is closed")
        });
        self.ensure(self.ready(p, epoch, &epochs), || {
            format!(
                "pipeline {p} finishes an epoch once it is sealed or the last, and after every \
                 earlier epoch where it is the last or the pipeline is ordered"
            )
        });
        let begun = state.phase.moved(Phase::Running, Phase::Finishing);
        self.ensure(begun, || format!("pipeline {p} finishes once"));
        (epoch.number, state.queue.region())
    }

    /// Land what `pushes` holds now, while the pipeline runs in its epoch: each morsel climbs the
    /// breaker's consumer to the [`Entry`] of each pipeline that reads it, which queues it there,
    /// and the reader may claim the packages before the pipeline finishes the epoch. A breaker's
    /// push names only what it has decided ([`Pushes::push_final`]), so the reader's chain reads
    /// it final. After a failure it lands nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline has finished the epoch, or the window no longer holds it.
    pub fn land(&self, mut pushes: Pushes<'_>) {
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline lands its pushes through its own dispatcher"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        if self.failed.load(Ordering::SeqCst) || morsels.is_empty() {
            return;
        }
        let epoch = self.epoch(pushes.epoch);
        self.ensure(
            epoch
                .as_ref()
                .is_some_and(|epoch| epoch.pipelines[p].phase.load() != Phase::Finished),
            || format!("pipeline {p} lands its pushes in an epoch before it finishes there"),
        );
        self.land_in(
            &epoch.expect("refused above"),
            p,
            &morsels,
            pushes.to.as_ref(),
        );
        self.advance();
    }

    /// Push `morsels`, pushed by `pipeline` in `epoch`, through `to`, its breaker's consumer, one
    /// region of the breaker's keys per morsel, a projection at any level. Each reader's queue
    /// there stays open until the last pipeline it reads finishes the epoch.
    fn land_in(
        &self,
        epoch: &EpochState,
        pipeline: usize,
        morsels: &[TileGuard],
        to: Option<&SharedConsumer>,
    ) {
        if morsels.is_empty() {
            return;
        }
        let mut landing = Landing {
            target: Target::Queue {
                dispatcher: self,
                epoch,
            },
            from: pipeline,
            widened: false,
        };
        match to {
            Some(to) => {
                for morsel in morsels {
                    let region = Projection::of(morsel).unwrap_or_else(|why| {
                        self.refuse(format!(
                            "pipeline {pipeline} pushes regions of its keys: {why}"
                        ))
                    });
                    to.borrow_mut().push(&region, &mut landing);
                }
            }
            // A test's push ([`Pushes::push`]) names no consumer and lands in each reader as it is.
            #[cfg(test)]
            None => {
                for &reader in &self.infos[pipeline].readers {
                    for morsel in morsels {
                        landing.queue(PipelineId(reader), morsel);
                    }
                }
            }
            #[cfg(not(test))]
            None => unreachable!("a breaker's push names the consumer it climbs"),
        }
    }

    /// Mark the pipeline `pushes` belongs to finished in its epoch, land what it pushed, and close
    /// the queue for that epoch of each pipeline that reads it, where every other pipeline that
    /// one reads has finished the epoch. A reader may claim the packages
    /// landed there before, and finish the epoch only once its queue there is closed. The finish
    /// that is the last of the epoch's retires it, and the window's slot takes the epoch a window
    /// later. After a failure it records nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline is not finishing in the epoch, which a second finish of it finds, or a
    /// reader has begun to finish the epoch.
    pub fn finish(&self, mut pushes: Pushes<'_>) {
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline finishes through its own dispatcher's pushes"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        let epoch = self.epoch(pushes.epoch);
        let finished = epoch.as_ref().is_some_and(|epoch| {
            epoch.pipelines[p]
                .phase
                .moved(Phase::Finishing, Phase::Finished)
        });
        self.ensure(finished, || {
            format!("pipeline {p} finishes an epoch it has begun to finish")
        });
        let epoch = epoch.expect("refused above");
        // Recorded before the reader's queue is closed, which lets the reader finish.
        #[cfg(test)]
        self.record(Event::Finish(PipelineId(p)));
        self.land_in(&epoch, p, &morsels, pushes.to.as_ref());
        for &reader in &self.infos[p].readers {
            // The last of the pipelines it reads to finish the epoch closes the reader's queue;
            // the decrement orders every earlier finish's appends before it.
            let unfinished = epoch.pipelines[reader]
                .unfinished
                .fetch_sub(1, Ordering::AcqRel);
            debug_assert!(
                unfinished > 0,
                "pipeline {reader} counts a finish once per pipeline it reads"
            );
            if unfinished != 1 {
                continue;
            }
            let queue = &epoch.pipelines[reader].queue;
            let closing = match &self.infos[reader].whole {
                Some(input) if epoch.number == self.last.load(Ordering::Acquire) => input,
                _ => &Vec::new(),
            };
            let closed = queue.append(reader, closing) && queue.close();
            self.ensure(closed, || {
                format!("pipeline {reader} receives packages once")
            });
        }
        if epoch.unfinished.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.retire(&epoch);
        }
        self.advance();
    }

    /// Retire `epoch`, which every pipeline has finished: the run is done after its last epoch,
    /// and otherwise the window's slot takes the epoch a window later.
    fn retire(&self, epoch: &EpochState) {
        if epoch.number == self.last.load(Ordering::Acquire) {
            self.done.store(true, Ordering::Release);
            return;
        }
        let later = epoch.number + self.window.len() as u64;
        let slot = &self.window[(epoch.number % self.window.len() as u64) as usize];
        *slot.write().unwrap_or_else(PoisonError::into_inner) =
            Arc::new(EpochState::new(later, &self.infos));
    }

    /// How many of `pipeline`'s packages are queued and not acknowledged, in every epoch.
    #[cfg(test)]
    pub(crate) fn outstanding(&self, pipeline: PipelineId) -> usize {
        self.state(pipeline).outstanding()
    }

    /// End the run: every claim from now answers [`Next::Failed`], and every waiter wakes. A
    /// worker that panics calls it by dropping its [`Worker`], so the others stop instead of
    /// waiting for what it held.
    pub fn fail(&self) {
        self.failed.store(true, Ordering::SeqCst);
        self.advance();
    }

    #[cfg(test)]
    fn record(&self, event: Event) {
        if !self.recording {
            return;
        }
        self.events
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(event);
    }

    /// The package at the front of the queue of the lowest pipeline a claim may take from,
    /// recorded as claimed. Unlike a claim, it never begins a finish.
    #[cfg(test)]
    pub(crate) fn pop(&self) -> Option<WorkPackage> {
        let epochs = self.epochs();
        (0..self.infos.len()).find_map(|p| self.claim_from(p, &epochs))
    }

    /// The package at the front of `pipeline`'s queue, claimed, where a claim may take one.
    #[cfg(test)]
    pub(crate) fn claim_of(&self, pipeline: PipelineId) -> Option<WorkPackage> {
        self.claim_from(pipeline.0, &self.epochs())
    }

    /// Finish `pipeline`'s oldest unfinished epoch as a claim does, with `push` in place of the
    /// breaker: begin the epoch's finish, let `push` push, and mark the epoch finished. A source
    /// pipeline is closed first, whatever was queued for it.
    #[cfg(test)]
    pub(crate) fn finish_by_hand(&self, pipeline: PipelineId, push: impl FnOnce(&mut Pushes<'_>)) {
        if self.infos[pipeline.0].reads.is_empty()
            && !self.state(pipeline).closed.load(Ordering::Acquire)
        {
            self.close(pipeline);
        }
        let (epoch, _) = self.begin_finish(pipeline);
        let mut pushes = self.pushes_in(pipeline, epoch);
        push(&mut pushes);
        self.finish(pushes);
    }

    /// This dispatcher with its event log off.
    #[cfg(test)]
    pub(crate) fn unrecorded(mut self) -> Self {
        self.recording = false;
        self
    }

    /// How many threads sleep in [`wait`](Self::wait).
    #[cfg(test)]
    pub(crate) fn waiting(&self) -> usize {
        self.sleepers.load(Ordering::SeqCst)
    }

    /// What the workers did, each event before the events it let happen.
    #[cfg(test)]
    pub(crate) fn into_events(self) -> Vec<Event> {
        self.events
            .into_inner()
            .unwrap_or_else(PoisonError::into_inner)
    }
}

/// Whether no pipeline reaches itself through what it reads.
fn acyclic(reads: &[Vec<usize>]) -> bool {
    // 0: not visited, 1: on the path, 2: done.
    fn visit(pipeline: usize, reads: &[Vec<usize>], state: &mut [u8]) -> bool {
        match state[pipeline] {
            1 => return false,
            2 => return true,
            _ => {}
        }
        state[pipeline] = 1;
        let below = reads[pipeline]
            .iter()
            .all(|read| visit(*read, reads, state));
        state[pipeline] = 2;
        below
    }
    let mut state = vec![0; reads.len()];
    (0..reads.len()).all(|pipeline| visit(pipeline, reads, &mut state))
}

/// A worker thread's handle on the dispatcher it claims from ([`Dispatcher::worker`]).
pub struct Worker<'d>(&'d Dispatcher);

impl Drop for Worker<'_> {
    /// Fails the run when the thread is unwinding from a panic.
    fn drop(&mut self) {
        if thread::panicking() {
            self.0.fail();
        }
    }
}

/// What a breaker pushes through in one epoch: one morsel of its keys per work package. The
/// dispatcher [lands](Dispatcher::land) them, as the driver does after each consume, or
/// [finishes](Dispatcher::finish) the pipeline's epoch: each morsel climbs the breaker's consumer
/// as a push ([`Consumer::push`]), each operator on the way restates it in its own keys, and the
/// [`Entry`] of each breaker it reaches queues it for that breaker's pipeline in the epoch.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    pipeline: usize,
    epoch: u64,
    morsels: Vec<TileGuard>,
    /// The consumer the morsels climb, the pushing breaker's.
    to: Option<SharedConsumer>,
}

impl Pushes<'_> {
    /// Push what `breaker` has decided and the pipeline has not pushed before, its final guard
    /// less the region pushed, for the pipelines that read it: one package per morsel the breaker
    /// cuts it into, in the breaker's order. A push of nothing new pushes nothing, and so does a
    /// breaker no pipeline reads. The difference and the region's growth are one step under the
    /// region's lock, so two pushes of one pipeline from two threads push disjoint regions, and an
    /// epoch's finish pushes only what no earlier finish pushed.
    ///
    /// # Panics
    ///
    /// Where the guard algebra has no exact difference of the two ([`guard_minus`]); in a debug
    /// build, when the morsels do not partition what is pushed ([`partition_gap`]).
    pub fn push_final<B: BreakingProducer + ?Sized>(&mut self, breaker: &B) {
        if self.dispatcher.infos[self.pipeline].readers.is_empty() {
            return;
        }
        let to = breaker.base().downstream.clone();
        self.dispatcher.ensure(to.is_some(), || {
            format!(
                "{}, which pipeline {} reads, pushes to a consumer",
                breaker.name(),
                self.pipeline
            )
        });
        self.to = to;
        let decided = breaker.final_guard();
        let guard = self.record(|pushed| match pushed {
            Some(pushed) => guard_minus(&decided, pushed),
            None => decided.clone(),
        });
        self.cut(&guard, |guard, rows| breaker.morsels(guard, rows));
    }

    /// Add the region `next` computes from the region pushed so far to that region, under its
    /// lock, and answer it.
    fn record(&self, next: impl FnOnce(&Option<TileGuard>) -> TileGuard) -> TileGuard {
        let mut pushed = self.dispatcher.states[self.pipeline]
            .pushed
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let guard = next(&pushed);
        debug_assert!(
            pushed
                .as_ref()
                .is_none_or(|pushed| pushed.intersect(&guard).is_empty()),
            "the reader of pipeline {} consumes each region once: {guard:?} meets {pushed:?}",
            self.pipeline
        );
        if !guard.is_empty() {
            *pushed = Some(match pushed.take() {
                Some(pushed) => pushed.union(&guard),
                None => guard.clone(),
            });
        }
        guard
    }

    /// Push `guard`, cut by `cut` into morsels of at most the dispatcher's `morsel_rows` held
    /// rows, as [`push_final`](Self::push_final) pushes a breaker's final guard. It names no
    /// consumer, so each morsel lands in every reader's queue as it is, as it does through an
    /// [`Entry`] the breaker's consumer is.
    #[cfg(test)]
    pub(crate) fn push(
        &mut self,
        guard: &TileGuard,
        cut: impl FnOnce(&TileGuard, usize) -> Vec<TileGuard>,
    ) {
        if self.dispatcher.infos[self.pipeline].readers.is_empty() || guard.is_empty() {
            return;
        }
        self.record(|_| guard.clone());
        self.cut(guard, cut);
    }

    /// Cut `guard`, recorded as pushed, into the morsels it lands as.
    fn cut(&mut self, guard: &TileGuard, cut: impl FnOnce(&TileGuard, usize) -> Vec<TileGuard>) {
        if guard.is_empty() {
            return;
        }
        let morsels = cut(guard, self.dispatcher.morsel_rows);
        debug_assert!(
            partition_gap(guard, &morsels).is_none(),
            "the morsels of a pushed guard partition it: {}",
            partition_gap(guard, &morsels).unwrap_or_default()
        );
        self.morsels.extend(morsels);
    }
}

impl Drop for Pushes<'_> {
    /// Refuses to drop pushes that never landed, which would lose the reader's packages.
    fn drop(&mut self) {
        if !thread::panicking() {
            assert!(
                self.morsels.is_empty(),
                "pipeline {} lands its pushes through Dispatcher::land or Dispatcher::finish",
                self.pipeline
            );
        }
    }
}

/// Where a push lands: its target, which queues it in an epoch or, in a planner's probe, records
/// it; the pipeline that pushed it; and whether an operator on the path it is climbing widened
/// it.
pub struct Landing<'d> {
    target: Target<'d>,
    from: usize,
    widened: bool,
}

/// What a [`Landing`] does with the regions that reach an [`Entry`].
enum Target<'d> {
    /// Queues each in the reader's queue for the epoch.
    Queue {
        dispatcher: &'d Dispatcher,
        epoch: &'d EpochState,
    },
    /// Records each, for a planner that probes where a pipeline's pushes arrive and how.
    #[cfg(test)]
    Probe(Vec<Arrival>),
}

/// A region a probing push brought to an [`Entry`].
#[cfg(test)]
pub(crate) struct Arrival {
    /// The pipeline whose entry it reached.
    pub(crate) pipeline: PipelineId,
    /// The region as a guard of that pipeline's breaker's input.
    pub(crate) guard: TileGuard,
    /// Whether an operator on its path widened it ([`Landing::widened`]).
    pub(crate) widened: bool,
}

impl Landing<'_> {
    /// A landing that records where `from`'s push arrives, and queues nothing.
    #[cfg(test)]
    pub(crate) fn probe(from: PipelineId) -> Landing<'static> {
        Landing {
            target: Target::Probe(Vec::new()),
            from: from.0,
            widened: false,
        }
    }

    /// What a probing landing recorded.
    #[cfg(test)]
    pub(crate) fn arrivals(self) -> Vec<Arrival> {
        match self.target {
            Target::Probe(arrivals) => arrivals,
            Target::Queue { .. } => panic!("a landing that queues records no arrivals"),
        }
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// epoch, less what is queued for it there already: a push that reaches a breaker along two
    /// paths, as a filter reads one memo for its values and its predicate, is queued once. A
    /// reader that reads its input whole ([`Dispatcher::read_whole`]) takes no push, widened or
    /// not.
    ///
    /// # Panics
    ///
    /// When `reader` does not read the pipeline that pushed, or has begun to finish the epoch;
    /// when the push was widened on its way to a reader that reads its pushes; and where the
    /// guard algebra has no exact difference of `guard` and what is queued ([`guard_minus`]).
    pub fn queue(&mut self, reader: PipelineId, guard: &TileGuard) {
        let (dispatcher, epoch) = match &mut self.target {
            Target::Queue { dispatcher, epoch } => (*dispatcher, *epoch),
            #[cfg(test)]
            Target::Probe(arrivals) => {
                arrivals.push(Arrival {
                    pipeline: reader,
                    guard: guard.clone(),
                    widened: self.widened,
                });
                return;
            }
        };
        let (from, r) = (self.from, reader.0);
        dispatcher.state(reader);
        dispatcher.ensure(dispatcher.infos[r].reads.contains(&from), || {
            format!("pipeline {from} pushes to pipeline {r}, which reads it")
        });
        if dispatcher.infos[r].whole.is_some() || dispatcher.infos[r].builds.contains(&from) {
            return;
        }
        dispatcher.ensure(!self.widened, || {
            format!(
                "a push of pipeline {from} is widened to `Everything` on its way to pipeline {r}, \
                 which reads that pipeline once it has finished instead"
            )
        });
        let queue = &epoch.pipelines[r];
        dispatcher.ensure(queue.phase.load() == Phase::Running, || {
            format!("pipeline {r} receives packages before it finishes")
        });
        dispatcher.ensure(queue.queue.append_unqueued(guard), || {
            format!("pipeline {r} receives packages before the last pipeline it reads finishes")
        });
    }

    /// Push on through `push` as widened: an operator on this path turned the push's region
    /// into `Everything`, so the reader it reaches cannot tell which of its keys it names. A
    /// sibling path the push takes after `push` returns is not widened by this one.
    pub fn widened(&mut self, push: impl FnOnce(&mut Self)) {
        let was = std::mem::replace(&mut self.widened, true);
        push(self);
        self.widened = was;
    }

    /// Fail the run: the push re-entered a consumer it is passing through, so its chain is a
    /// cycle, which only a store closes.
    pub fn reentered(&mut self) {
        let message = format!(
            "a push of pipeline {} re-enters a consumer it is passing through",
            self.from
        );
        match &self.target {
            Target::Queue { dispatcher, .. } => dispatcher.ensure(false, || message),
            #[cfg(test)]
            Target::Probe(_) => panic!("{message}"),
        }
    }
}

/// The consumer at the input of a pipeline's breaker: a push that reaches it is queued as a work
/// package of the breaker's pipeline, and a notification passes to the consumer it wraps.
///
/// A push arrives as a region of the input's keys at any level, which `Entry` takes as a guard of
/// the input's tiling: `Everything` is the universal guard, and a region of keys is the guard of
/// those keys.
pub struct Entry {
    pipeline: Placement,
    input: Tiling,
    inner: Box<dyn Consumer>,
}

/// The pipeline an [`Entry`] queues for, which a planner sets once it has put the entry's breaker
/// in one: `None` before, as in a run that only pulls, where the entry queues nothing.
// shared-state-ok: the breaker and the entry at its input both hold it, the planner writes it
// before the run, and what crosses it is a pipeline's index, never a tile.
pub type Placement = Rc<Cell<Option<PipelineId>>>;

impl Entry {
    /// The entry of `pipeline`, whose breaker reads `input`, in front of `inner`.
    pub fn new(pipeline: PipelineId, input: Tiling, inner: Box<dyn Consumer>) -> Self {
        Entry {
            pipeline: Rc::new(Cell::new(Some(pipeline))),
            input,
            inner,
        }
    }

    /// The entry of a breaker that reads `input`, in front of `inner`, and its placement, which
    /// the breaker keeps for a planner to set ([`ProducerBase::placement`]).
    ///
    /// [`ProducerBase::placement`]: crate::interpreter::tile_operators::ProducerBase
    pub fn unplaced(input: Tiling, inner: Box<dyn Consumer>) -> (Self, Placement) {
        let pipeline: Placement = Rc::new(Cell::new(None));
        let entry = Entry {
            pipeline: pipeline.clone(),
            input,
            inner,
        };
        (entry, pipeline)
    }
}

impl Consumer for Entry {
    fn notify(&mut self, arrived: &Projection) {
        self.inner.notify(arrived);
    }

    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        if let Some(pipeline) = self.pipeline.get()
            && let Some(guard) = pushed_guard(region, &self.input)
        {
            landing.queue(pipeline, &guard);
        }
    }
}

/// The guard of `input` a push of `region` names at a pipeline's entry, and `None` where it names
/// nothing. It is closed over `input`, so a region under every tag of a tagged union is the
/// universal guard, as a pull of every arm is.
pub(crate) fn pushed_guard(region: &Projection, input: &Tiling) -> Option<TileGuard> {
    match region {
        Projection::Nothing => None,
        Projection::Everything => Some(input.universal_guard()),
        Projection::Keys { .. } => Some(region.guard(input).closed_over(input)),
    }
}

/// The morsels a source pipeline starts with: its breaker's input whole, cut every `rows` keys
/// where the input's tiling states a finite range of positions for its outermost keys, and one
/// morsel otherwise.
fn seed(input: &Tiling, rows: usize) -> Vec<TileGuard> {
    let guard = input.universal_guard();
    let Some(domain) = input.domain_extent() else {
        return vec![guard];
    };
    let (Extent::UIntRange(positions), TileGuard::Function(FunctionGuard::Domain(region))) =
        (&domain, &guard)
    else {
        return vec![guard];
    };
    let runs: Option<Vec<_>> = positions
        .intervals()
        .iter()
        .map(|run| {
            let (first, last) = (run.left()?, run.right()?);
            let first = u128::from(*first.value()) + u128::from(!first.is_closed());
            let last = u128::from(*last.value()) - u128::from(!last.is_closed());
            Some((first, last))
        })
        .collect();
    match runs {
        Some(runs) => cut_before(region, &cuts_every(runs, rows), &domain),
        None => vec![guard],
    }
}

/// `guard` cut every `rows` positions, where it names finite runs of positions (`Value::UInt`
/// keys of its outermost level), and whole otherwise: the morsels a source's arrived region is
/// queued as ([`Dispatcher::notify`]).
fn cut_positions(guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
    let TileGuard::Function(FunctionGuard::Domain(region @ Predicate::Intervals(runs))) = guard
    else {
        return vec![guard.clone()];
    };
    let position = |bound: Option<&intervalsets::Bound<Value>>, past: bool| match bound {
        Some(bound) => match bound.value() {
            Value::UInt(at) => {
                let at = u128::from(*at);
                Some(match (bound.is_closed(), past) {
                    (true, _) => at,
                    (false, false) => at + 1,
                    (false, true) => at.checked_sub(1)?,
                })
            }
            _ => None,
        },
        None => None,
    };
    let runs: Option<Vec<_>> = runs
        .intervals()
        .iter()
        .map(|run| Some((position(run.left(), false)?, position(run.right(), true)?)))
        .collect();
    match runs {
        Some(runs) => cut_before(
            region,
            &cuts_every(runs, rows),
            &Extent::Base(crate::interpreter::BaseType::UInt),
        ),
        None => vec![guard.clone()],
    }
}

/// The positions to cut `runs` before, every `rows` positions counted across them: the runs are
/// closed `(first, last)` pairs in ascending order, and the first position of all is no cut.
fn cuts_every(runs: Vec<(u128, u128)>, rows: usize) -> Vec<Value> {
    // Positions are counted in `u128`: a range covering every `u64` holds 2^64 of them.
    let mut cuts = Vec::new();
    let mut seen: u128 = 0;
    let rows = rows as u128;
    for (first, last) in runs {
        if last < first {
            continue;
        }
        let count = last - first + 1;
        // The first position of this run that is a multiple of `rows`; position 0 is no cut.
        let mut next = seen.max(1).div_ceil(rows) * rows;
        while next < seen + count {
            let key = u64::try_from(first + (next - seen)).expect("a position in the range");
            cuts.push(Value::UInt(key));
            next += rows;
        }
        seen += count;
    }
    cuts
}

/// A shared handle on a pipeline's breaker. A reader's chain reads the breaker through another
/// handle, so the driver borrows it for one call at a time.
// shared-state-ok: the driver's handle on a breaker it calls, and in a test the handle a reader's
// input reads the breaker through; no tile passes between operators through it.
pub type BreakerHandle = Rc<RefCell<dyn BreakingProducer>>;

/// What the workers did.
#[cfg(test)]
#[derive(Debug, PartialEq)]
pub(crate) enum Event {
    Consume {
        pipeline: PipelineId,
        guard: TileGuard,
    },
    Finish(PipelineId),
}

/// Run every pipeline to its end on the calling thread. A source pipeline, one that reads no
/// pipeline, starts with its breaker's input whole, as one package per morsel ([`seed`]), and is
/// closed, so the run is one epoch. The driver consumes the package of the lowest pipeline that
/// has one; when no pipeline has one, it finishes the lowest pipeline that may finish. It stops
/// when every pipeline has finished. Every breaker takes its consuming mode before the first
/// package, as in a compiled program's run.
///
/// # Panics
///
/// When a pipeline cannot finish though nothing is queued, which an acyclic graph rules out; in a
/// debug build, when a package's guard is not a guard of the tiling its breaker's input answers,
/// when a pipeline consumes a region it consumed before, or when a breaker's morsels do not
/// partition its final guard; and at any of the invariants [`finish_epoch`] asserts.
pub fn run(dispatcher: &Dispatcher, breakers: &[BreakerHandle]) {
    for breaker in breakers {
        breaker.borrow_mut().enter_consuming_mode();
    }
    assert_eq!(
        breakers.len(),
        dispatcher.infos.len(),
        "one breaker per pipeline"
    );
    drive(dispatcher, &mut handles(breakers));
}

/// Each pipeline's breaker, reached for one call at a time: through a handle ([`handles`]), or,
/// in a test, by walking a compiled program's producer chains (`run_program`).
type Reach<'r> = dyn FnMut(PipelineId, &mut Call<'_>) + 'r;

/// One call on a pipeline's breaker, which a [`Reach`] makes.
type Call<'c> = dyn FnMut(&mut dyn Breaker) + 'c;

/// The breakers `breakers` holds, by pipeline, each borrowed for one call.
fn handles(breakers: &[BreakerHandle]) -> impl FnMut(PipelineId, &mut Call<'_>) {
    move |pipeline, call| {
        let mut breaker = breakers[pipeline.0].borrow_mut();
        debug_assert!(
            breaker.as_producer().is_some(),
            "{} answers itself as a producer, so its pushes reach its readers",
            breaker.name()
        );
        call(&mut *breaker)
    }
}

/// [`run`] over the breakers `reach` reaches.
fn drive(dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
    start_with(dispatcher, reach);
    loop {
        match dispatcher.try_claim(None) {
            Next::Package(package) => consume_with(dispatcher, reach, package),
            Next::Finish {
                pipeline,
                epoch,
                consumed,
                last,
            } => finish_with(dispatcher, reach, pipeline, epoch, consumed, last),
            Next::Wait(_) => {
                panic!("an acyclic graph with nothing queued has a pipeline that may finish")
            }
            Next::Done => return,
            Next::Failed => panic!("a run on one thread fails only by panicking on it"),
        }
    }
}

/// Queue each source pipeline's input whole, as one package per morsel ([`seed`]), and close it.
/// [`run`] starts here.
fn start_with(dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
    for (pipeline, info) in dispatcher.infos.iter().enumerate() {
        if info.reads.is_empty() {
            let mut input = None;
            reach(PipelineId(pipeline), &mut |breaker| {
                input = Some(breaker.input_tiling(InputId::ONLY));
            });
            let input = input.expect("a reach calls the breaker it reaches");
            dispatcher.start_source(PipelineId(pipeline), &input);
        }
    }
}

/// Hand `package` to its pipeline's breaker, land what the breaker decided since its last push
/// ([`Pushes::push_final`]) where the breaker is a producer ([`Breaker::as_producer`]) that
/// pushes while consuming ([`BreakingProducer::pushes_while_consuming`]), then acknowledge the
/// package. The push lands
/// before the acknowledgement, which may let the pipeline finish the epoch.
///
/// # Panics
///
/// As [`Dispatcher::acknowledge`] says of a package; in a debug build, as [`run`] says of a
/// package.
#[cfg(test)]
pub(crate) fn consume(dispatcher: &Dispatcher, breakers: &[BreakerHandle], package: WorkPackage) {
    consume_with(dispatcher, &mut handles(breakers), package);
}

fn consume_with(dispatcher: &Dispatcher, reach: &mut Reach<'_>, package: WorkPackage) {
    let p = package.pipeline.0;
    // The pushes land once the reach has returned: a breaker reached through a fan-out slot is
    // called while the walk holds the fan-out, which the push climbs.
    let mut landed = None;
    reach(package.pipeline, &mut |breaker| {
        // A package carries a guard of the tiling of the pipeline that pushed it, or of this
        // breaker's own input for a source or a pipeline that reads it whole, so it fits only a
        // breaker whose input answers that tiling.
        debug_assert!(
            package
                .guard
                .check_from(&breaker.input_tiling(InputId::ONLY)),
            "pipeline {p} consumes a guard of the tiling its breaker's input answers: {:?}",
            package.guard
        );
        breaker.consume_impl(InputId::ONLY, package.guard.clone());
        if let Some(producer) = breaker.as_producer()
            && producer.pushes_while_consuming()
        {
            let mut pushes = dispatcher.pushes_in(package.pipeline, package.epoch);
            pushes.push_final(producer);
            landed = Some(pushes);
        }
    });
    if let Some(pushes) = landed {
        dispatcher.land(pushes);
    }
    dispatcher.acknowledge(package);
}

/// Finish `pipeline`'s oldest unfinished epoch, after checking what a finish rests on.
///
/// # Panics
///
/// When the pipeline has finished every epoch, its queue in the epoch is not closed or not empty,
/// a package claimed for it is in flight, a pipeline it reads has not finished the epoch, or its
/// breaker's input has not released every guard the pipeline consumed in the epoch. Also where the
/// guard algebra has no exact difference of a consumed guard and the guard the input released
/// ([`guard_minus`]).
pub fn finish_epoch(dispatcher: &Dispatcher, breakers: &[BreakerHandle], pipeline: PipelineId) {
    let (epoch, consumed) = dispatcher.begin_finish(pipeline);
    let last = epoch == dispatcher.last.load(Ordering::Acquire);
    finish_with(
        dispatcher,
        &mut handles(breakers),
        pipeline,
        epoch,
        consumed,
        last,
    );
}

/// Finish `pipeline`'s `epoch`, which has begun after consuming `consumed`: push what the epoch
/// decided and no consume pushed, through the breaker's [`finish`][Breaker::finish], then mark it
/// finished.
///
/// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
fn finish_with(
    dispatcher: &Dispatcher,
    reach: &mut Reach<'_>,
    pipeline: PipelineId,
    epoch: u64,
    consumed: Option<TileGuard>,
    last: bool,
) {
    let p = pipeline.0;
    let mut consumed = Some(consumed);
    // As in `consume_with`, the pushes land once the reach has returned.
    let mut finished = None;
    reach(pipeline, &mut |breaker| {
        let consumed = consumed
            .take()
            .expect("a reach calls the breaker it reaches once");
        let released = breaker.input_released(InputId::ONLY);
        dispatcher.ensure(
            consumed.is_none_or(|consumed| {
                // Closed over the input's tiling: where a row's level is a finite range of
                // positions, what the input released through the row's last position covers its
                // paths past it.
                released.is_universal()
                    || guard_minus(&consumed, &released)
                        .closed_over(&breaker.input_tiling(InputId::ONLY))
                        .is_empty()
            }),
            || {
                format!(
                    "pipeline {p} finishes after its input has released every guard the \
                     pipeline consumed"
                )
            },
        );
        let mut pushes = dispatcher.pushes_in(pipeline, epoch);
        breaker.finish(&mut pushes, last);
        finished = Some(pushes);
    });
    dispatcher.finish(finished.expect("a reach calls the breaker it reaches"));
}

/// Run a compiled program's pipelines through a dispatcher of `morsel_rows` on the calling
/// thread. `sinks` pairs each sink's consumer with the sink it writes to. The breakers are the
/// producers in the chains under the sinks' producers that are pipeline breakers
/// (`TileProducer::as_breaking_mut`), each store a reader slot reaches, and each sink's own
/// ([`SinkBreaker`]), whose pipeline no pipeline reads. A breaker's pipeline reads the pipelines
/// of the nearest breakers beneath it, and the [`Entry`] at the breaker's input, or the sink's
/// consumer, is placed in the pipeline. A pipeline pulls only its breaker's input, and a sink's
/// pipeline pulls the sink's producer, so a sink receives its producer's answer one package at a
/// time. A sink is done once its producer is released whole, which the run leaves to its caller
/// to read. It answers what it planned for each pipeline, in pipeline order.
///
/// A store that runs in rounds (`TileProducer::runs_in_rounds`) is the breaker of no pipeline. Its
/// loop's scope is one ([`loop_scope::LoopScope`]), and the breakers inside the store's cycle are
/// the pipelines of the scope's own dispatcher, with the scope of each loop nested in the loop
/// among them. A read between two dispatchers is a read of the scope that stands for the inner one
/// in the outer: a pipeline inside a cycle that reads one beneath it is its scope reading that
/// pipeline.
///
/// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
///
/// Each edge to a pipeline that reads another is probed before the run: the reading pipeline's
/// breaker pushes a region through its consumer, as a push in the run would climb it, and the
/// planner looks at what reaches the reader's entry ([`Landing::probe`]). Where it arrives as
/// it was restated, the reader reads the pushes (a stream edge). Where an operator on the way
/// widened it, or it never arrives, the reader takes no push of it, and waits for that pipeline's
/// finish of an epoch before it takes a package there ([`Dispatcher::build`], a build edge). A
/// reader with no stream edge, or with two whose pushes can name one key, reads its input whole
/// once every pipeline it reads has finished ([`Dispatcher::read_whole`]), and so does one with a
/// build edge whose push reaches it nowhere. A build edge is probed with `Everything` too, and so
/// is each range under a reader of pushes (an `IterateExtent`), such as a literal's positions, the
/// one producer with no input that keeps its consumer (`ProducerBase::leaf`). What those probes
/// bring that no stream edge's push can name is queued for the reader at the start of the run as
/// one region, which the reader takes once its build edges' pipelines have finished.
///
/// # Panics
///
/// When a pipeline reads directly a pipeline that another pipeline reads; where
/// `Planner::store_pipeline` refuses a store; where a nested loop's rounds pull an operator beneath
/// the keys it restates (`Planner::refusal_of_nested`); and where [`run`] panics.
#[cfg(test)]
pub(crate) fn run_program(sinks: &[SinkTarget], morsel_rows: usize) -> Vec<Planned> {
    let mut planner = Planner::default();
    let roots: Vec<_> = sinks
        .iter()
        .map(|(consumer, _)| consumer.borrow().producer_slot().clone())
        .collect();
    let mut sink_breakers = Vec::new();
    for (at, ((consumer, sink), root)) in sinks.iter().zip(&roots).enumerate() {
        let breaker =
            crate::interpreter::tile_operators::SinkBreaker::new(root.clone(), sink.clone());
        let under = {
            let mut root = root.borrow_mut();
            let producer = root.as_mut().expect("a root holds the producer it pulls");
            planner.pipelines_under(&mut **producer, "sink")
        };
        let pipeline = planner.add(Located::Sink(at), format!("SinkBreaker#{at}"), None, under);
        consumer.borrow_mut().place(
            PipelineId(planner.local[pipeline]),
            breaker.input_tiling(InputId::ONLY),
        );
        sink_breakers.push(RefCell::new(breaker));
    }
    planner.check_direct();
    let members = planner.members(None);
    let mut kept = Vec::new();
    let scopes: Vec<Option<RefCell<loop_scope::LoopScope>>> = members
        .located
        .iter()
        .map(|located| match located {
            Located::Scope { scope, .. } => Some(RefCell::new(planner.build_scope(
                *scope,
                morsel_rows,
                &mut kept,
            ))),
            _ => None,
        })
        .collect();
    if let Some(why) = planner.refusal_of_nested(&kept) {
        panic!("{why}");
    }
    let scope_at = |pipeline: PipelineId| {
        scopes[pipeline.0]
            .as_ref()
            .expect("a scope's pipeline holds its scope")
    };
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| match &members.located[pipeline.0] {
        Located::Sink(sink) => call(&mut *sink_breakers[*sink].borrow_mut()),
        Located::Store { store, .. } => {
            let mut store = store.borrow_mut();
            call(
                store
                    .as_breaking_mut()
                    .expect("a planned store is a pipeline breaker"),
            )
        }
        Located::Scope { .. } => call(&mut *scope_at(pipeline).borrow_mut()),
        Located::Chain(id) => {
            let mut call = Some(call);
            for root in &roots {
                let mut root = root.borrow_mut();
                let producer = root.as_mut().expect("a root holds the producer it pulls");
                if reach_in_chain(&mut **producer, *id, &mut call) {
                    return;
                }
            }
            panic!("pipeline {} has its breaker in a root's chain", pipeline.0)
        }
    };
    // A scope is no producer: its pipeline pushes the store's.
    let mut end_of = |pipeline: PipelineId| match &members.located[pipeline.0] {
        Located::Scope { .. } => Some(scope_at(pipeline).borrow().pushing_end()),
        _ => None,
    };
    let (dispatcher, mut planned) = plan_edges(
        &members.reads,
        &members.names,
        &members.leaves,
        &members.kinds,
        morsel_rows,
        &mut reach,
        &mut end_of,
    );
    // The run drives every breaker it planned, so each takes its consuming mode here, before any
    // package, and keeps it for the run; a loop's scope passes it to the breakers it keeps.
    for pipeline in 0..members.names.len() {
        reach(PipelineId(pipeline), &mut |breaker| {
            breaker.enter_consuming_mode()
        });
    }
    drive(&dispatcher, &mut reach);
    for (plan, scope) in planned.iter_mut().zip(&scopes) {
        if let Some(scope) = scope {
            plan.rounds = std::mem::take(&mut scope.borrow_mut().planned);
        }
    }
    planned
}

/// How a pipeline takes its packages, which [`plan_edges`] plans its edges by.
#[cfg(test)]
#[derive(Clone, Copy, PartialEq)]
enum Consumes {
    /// What the pipelines it reads push, as its edges' probes plan.
    Pushes,
    /// Its input whole, in order, once every pipeline it reads has finished: a store that steps
    /// itself, or a loop's scope.
    Whole,
    /// One region per epoch, which the scope it runs in queues it, once every pipeline it reads
    /// has finished the epoch: the scope of a loop nested in the scope's loop, one row per round.
    Rounds,
}

/// The dispatcher over the pipelines `reads` describes, with each edge into a pipeline that
/// reads another probed and planned as a stream edge, a build edge or a whole read, and the
/// regions no push names queued at the start ([`run_program`] says how). `kinds` says how each
/// pipeline takes its packages; `end_of` answers the consumer a pipeline pushes to where its
/// breaker is no producer that answers it.
#[cfg(test)]
fn plan_edges(
    reads: &[Vec<usize>],
    names: &[String],
    leaves: &[Vec<SharedConsumer>],
    kinds: &[Consumes],
    morsel_rows: usize,
    reach: &mut Reach<'_>,
    end_of: &mut dyn FnMut(PipelineId) -> Option<(SharedConsumer, bool)>,
) -> (Dispatcher, Vec<Planned>) {
    let mut dispatcher = Dispatcher::new(reads.to_vec(), morsel_rows);
    // A store decides its positions in order; a scope steps its store in order.
    for (pipeline, kind) in kinds.iter().enumerate() {
        if *kind != Consumes::Pushes {
            dispatcher.order(PipelineId(pipeline));
        }
    }
    let mut planned: Vec<Planned> = names
        .iter()
        .map(|name| Planned {
            name: name.clone(),
            whole: false,
            builds: Vec::new(),
            started: false,
            rounds: Vec::new(),
        })
        .collect();
    let mut starts = Vec::new();
    for (reader, read) in reads.iter().enumerate() {
        if read.is_empty() {
            continue;
        }
        let mut input = None;
        reach(PipelineId(reader), &mut |breaker| {
            input = Some(breaker.input_tiling(InputId::ONLY))
        });
        let input = input.expect("a reach calls the breaker it reaches");
        match kinds[reader] {
            // A store's pipeline reads its input whole once the pipelines beneath its cycle have
            // finished: a push from beneath stops at the store's entry rather than reach the
            // cycle.
            Consumes::Whole => {
                dispatcher.read_whole(PipelineId(reader), &input);
                planned[reader].whole = true;
                continue;
            }
            // A nested loop's scope takes the row the scope around it queues it once the pipelines
            // it reads have finished the round, since its rounds pull them.
            Consumes::Rounds => {
                for &build in read {
                    dispatcher.build(PipelineId(reader), PipelineId(build));
                    planned[reader].builds.push(build);
                }
                continue;
            }
            Consumes::Pushes => {}
        }
        let mut streams = Vec::new();
        let mut builds = Vec::new();
        // What the build edges and the leaves bring the reader, which no stream push names.
        let mut brought = Vec::new();
        for &read in read {
            // A nested loop's scope pushes its store once it is terminal, at the run's last epoch,
            // so a reader inside the cycle around it waits for its finish of each round instead.
            if kinds[read] == Consumes::Rounds {
                builds.push((read, true));
                continue;
            }
            let (pusher, keyed) =
                end_of(PipelineId(read)).unwrap_or_else(|| pushing_end(reach, PipelineId(read)));
            let bounded = match keyed {
                true => Projection::admitting(Predicate::point(Value::UInt(0))),
                false => Projection::Everything,
            };
            let arrived = probe(&pusher, PipelineId(read), &bounded, reader);
            let named = probe(&pusher, PipelineId(read), &Projection::Everything, reader);
            if arrived.is_empty() || arrived.iter().any(|arrival| arrival.widened) {
                builds.push((read, !named.is_empty()));
                brought.extend(named);
                continue;
            }
            streams.push(
                named
                    .into_iter()
                    .fold(input.empty_guard(), |names, arrival| {
                        names.union(&arrival.guard)
                    }),
            );
        }
        // A key two stream edges can both name would be consumed at the first push of it, while
        // the other pipeline may not have decided it yet. A build edge whose push reaches the
        // reader nowhere names no region to queue for it.
        let apart = streams.iter().enumerate().all(|(at, names)| {
            streams[..at]
                .iter()
                .all(|earlier| earlier.intersect(names).is_empty())
        });
        if streams.is_empty() || !apart || builds.iter().any(|(_, named)| !named) {
            dispatcher.read_whole(PipelineId(reader), &input);
            planned[reader].whole = true;
            continue;
        }
        for &(build, _) in &builds {
            dispatcher.build(PipelineId(reader), PipelineId(build));
            planned[reader].builds.push(build);
        }
        let pushed = streams
            .iter()
            .fold(input.empty_guard(), |pushed, names| pushed.union(names));
        for leaf in &leaves[reader] {
            brought.extend(probe(
                leaf,
                PipelineId(read[0]),
                &Projection::Everything,
                reader,
            ));
        }
        // A widened arrival names at least the region it brings, so queueing what of the arrivals
        // no push names consumes each region they bring once. The reader takes it once every
        // build edge's pipeline has finished the epoch.
        let left = brought.iter().fold(input.empty_guard(), |left, arrival| {
            left.union(&guard_minus(&arrival.guard, &pushed))
        });
        if !left.is_empty() {
            planned[reader].started = true;
            starts.push((PipelineId(reader), left));
        }
    }
    for (reader, guard) in &starts {
        dispatcher.queue_for(*reader, guard);
    }
    (dispatcher, planned)
}

/// A sink's consumer and the sink it writes to, as [`run_program`] takes them.
#[cfg(test)]
pub(crate) type SinkTarget = (
    Rc<RefCell<crate::interpreter::sinks::SinkConsumer>>,
    Arc<dyn crate::interpreter::DataSink>,
);

/// What [`run_program`] planned for one pipeline.
#[cfg(test)]
#[derive(Debug)]
pub(crate) struct Planned {
    /// Its breaker's name.
    pub(crate) name: String,
    /// Whether it reads its input whole, once every pipeline it reads has finished.
    pub(crate) whole: bool,
    /// The pipelines it reads whose finish it waits for, taking no push of theirs.
    pub(crate) builds: Vec<usize>,
    /// Whether the run queued it a region at the start: what its build edges and the ranges under
    /// it (`IterateExtent`) bring, less what its stream edges' pushes name.
    pub(crate) started: bool,
    /// For a loop's scope, what its nested dispatcher planned for each inner pipeline, and
    /// nothing otherwise.
    pub(crate) rounds: Vec<Planned>,
}

/// The consumer `pipeline`'s breaker pushes to, and whether its output has keys of its own, so a
/// bounded region of them can probe its readers' edges.
#[cfg(test)]
fn pushing_end(reach: &mut Reach<'_>, pipeline: PipelineId) -> (SharedConsumer, bool) {
    let mut end = None;
    reach(pipeline, &mut |breaker| {
        let producer = breaker.as_producer().unwrap_or_else(|| {
            panic!(
                "pipeline {} is read, so its breaker is a producer",
                pipeline.0
            )
        });
        let keyed = matches!(producer.tiling(), Tiling::DataFunction { .. });
        end = Some((producer.base().downstream.clone(), keyed));
    });
    let (downstream, keyed) = end.expect("a reach calls the breaker it reaches");
    let downstream = downstream.unwrap_or_else(|| {
        panic!(
            "pipeline {} is read, so its breaker pushes to a consumer",
            pipeline.0
        )
    });
    (downstream, keyed)
}

/// What a push of `region` through `consumer`, as `from`'s, brings to the entry of `reader`.
#[cfg(test)]
fn probe(
    consumer: &SharedConsumer,
    from: PipelineId,
    region: &Projection,
    reader: usize,
) -> Vec<Arrival> {
    let mut landing = Landing::probe(from);
    consumer.borrow_mut().push(region, &mut landing);
    landing
        .arrivals()
        .into_iter()
        .filter(|arrival| arrival.pipeline.0 == reader)
        .collect()
}

/// Where [`run_program`] finds a pipeline's breaker.
#[cfg(test)]
enum Located {
    /// In a sink's producer chain, or a store's, by its address ([`address`]).
    Chain(usize),
    /// The breaker of the sink of this index in `sinks` ([`SinkBreaker`]).
    ///
    /// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
    Sink(usize),
    /// The store of the cyclic fan-out `fan`, which steps itself.
    Store {
        fan: usize,
        store: crate::interpreter::tile_operators::StoreCell,
    },
    /// The scope of the store of the cyclic fan-out `fan`, which runs in rounds: the planner's
    /// scope of index `scope`.
    Scope { fan: usize, scope: usize },
}

/// A loop's scope as the planner walks it.
#[cfg(test)]
struct PlannedScope {
    store: crate::interpreter::tile_operators::StoreCell,
    /// The id of the store's cyclic fan-out, which the breakers inside its cycle read through a
    /// recurrence slot.
    fan: usize,
    /// The scope's pipeline, in the dispatcher of the scope around it, or the run's for an
    /// outermost loop; `None` until the walk of the store's chain has planned the pipelines it
    /// reads.
    pipeline: Option<usize>,
    /// How many pipelines its own dispatcher has.
    count: usize,
    /// How many scopes it runs inside: its rounds run at paths of `depth + 1` keys.
    depth: usize,
}

/// The pipelines of one dispatcher, in its pipeline order, with what [`plan_edges`] plans them
/// by.
#[cfg(test)]
struct Members<'p> {
    located: Vec<&'p Located>,
    reads: Vec<Vec<usize>>,
    names: Vec<String>,
    leaves: Vec<Vec<SharedConsumer>>,
    kinds: Vec<Consumes>,
    /// The placements of the entries of the breakers in chains.
    placements: Vec<Option<Placement>>,
}

/// The pipelines [`run_program`] reads off a program's producer chains, every dispatcher's: the
/// run's, and each loop scope's. A pipeline's index here is its id in the planner; `local` gives
/// its id in its dispatcher.
#[cfg(test)]
#[derive(Default)]
struct Planner {
    /// Per pipeline, the pipelines it reads, as the walk finds them, in whichever dispatcher.
    reads: Vec<Vec<usize>>,
    located: Vec<Located>,
    names: Vec<String>,
    /// Per pipeline, the consumers of the ranges in its chain (`ProducerBase::leaf`), above
    /// every breaker beneath it.
    leaves: Vec<Vec<SharedConsumer>>,
    /// Per pipeline, the scope whose dispatcher it runs in; `None` for the run's.
    within: Vec<Option<usize>>,
    /// Per pipeline, its id in its dispatcher.
    local: Vec<usize>,
    /// Per pipeline, the placement of its breaker's entry, where the breaker is in a chain.
    placements: Vec<Option<Placement>>,
    /// The edges `(read, reader)` whose reader's breaker reads the breaker of `read` directly.
    direct: Vec<(usize, usize)>,
    scopes: Vec<PlannedScope>,
    /// How many pipelines the run's dispatcher has.
    count: usize,
    /// The scopes whose store's chain the walk is in, outermost first.
    walking: Vec<usize>,
}

/// What a chain holds beneath a producer, up to the nearest breakers.
#[cfg(test)]
#[derive(Default)]
struct Beneath {
    /// The pipelines of the nearest breakers, each once, and whether that breaker is the producer
    /// itself rather than beneath it.
    pipelines: Vec<(usize, bool)>,
    /// The consumers of the ranges above those breakers (`ProducerBase::leaf`).
    leaves: Vec<SharedConsumer>,
    /// The constant collections above those breakers that are no function operand: producers
    /// with no input and keys of their own that keep no consumer, so no probe names their keys.
    unprobed: Vec<String>,
}

#[cfg(test)]
impl Beneath {
    /// Add `pipelines` to the pipelines beneath, each once: a reader that reaches a pipeline
    /// along two paths, as a filter reads its input for the values and the predicate, reads it
    /// once.
    fn read_once(&mut self, pipelines: Vec<(usize, bool)>) {
        for (pipeline, direct) in pipelines {
            if !self.pipelines.iter().any(|(seen, _)| *seen == pipeline) {
                self.pipelines.push((pipeline, direct));
            }
        }
    }
}

#[cfg(test)]
impl Planner {
    /// What the chain at `producer` holds up to the nearest breakers, planning each breaker
    /// reached in the dispatcher it runs in ([`dispatcher_of`](Self::dispatcher_of)); a pipeline
    /// is numbered after the pipelines it reads, and a breaker a second reader reaches keeps its
    /// pipeline. A recurrence slot holds nothing beneath it: its reader pulls the store.
    fn pipelines_under(
        &mut self,
        producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
        role: &str,
    ) -> Beneath {
        if producer.recurrence_of().is_some() {
            return Beneath::default();
        }
        if let Some(read) = producer.store_read() {
            return Beneath {
                pipelines: vec![(self.store_pipeline(read), false)],
                ..Beneath::default()
            };
        }
        let id = address(producer);
        if let Some(pipeline) = self
            .located
            .iter()
            .position(|at| matches!(at, Located::Chain(seen) if *seen == id))
        {
            return Beneath {
                pipelines: vec![(pipeline, true)],
                ..Beneath::default()
            };
        }
        let mut below = Beneath::default();
        let mut inputs = 0;
        let mut seen = 0;
        producer.visit_input_producers(&mut |_, _| seen += 1);
        producer.visit_input_producers_mut(&mut |role, input| {
            inputs += 1;
            let under = self.pipelines_under(input, role);
            below.read_once(under.pipelines);
            below.leaves.extend(under.leaves);
            below.unprobed.extend(under.unprobed);
        });
        debug_assert_eq!(
            inputs,
            seen,
            "{} visits as many inputs mutably as it lists, so the walk reaches every breaker \
             beneath it",
            producer.name()
        );
        let leaf = (inputs == 0)
            .then(|| producer.base().downstream.clone())
            .flatten();
        let placement = producer.base().placement.clone();
        // A function operand is a table its consumer looks values up in, and widens, so its keys
        // are no keys of the reader's input.
        if inputs == 0 && leaf.is_none() && role != "fn" && producer.tiling().is_data_function() {
            below.unprobed.push(producer.name());
        }
        if producer.as_breaking_mut().is_none() {
            below.leaves.extend(leaf);
            for (_, direct) in &mut below.pipelines {
                *direct = false;
            }
            return below;
        }
        let within = self.dispatcher_of(&*producer);
        let name = producer.name();
        let placement =
            placement.unwrap_or_else(|| panic!("{name} is placed in a pipeline by its entry"));
        let pipeline = self.add(Located::Chain(id), name, within, below);
        placement.set(Some(PipelineId(self.local[pipeline])));
        self.placements[pipeline] = Some(placement);
        Beneath {
            pipelines: vec![(pipeline, true)],
            ..Beneath::default()
        }
    }

    /// The scope whose dispatcher a breaker at `producer` runs in: the innermost scope being
    /// walked whose cycle `producer` is inside, and `None`, the run's, where it is inside none.
    fn dispatcher_of(
        &self,
        producer: &dyn crate::interpreter::tile_operators::TileProducer,
    ) -> Option<usize> {
        self.walking
            .iter()
            .rev()
            .copied()
            .find(|&scope| reaches_recurrence(producer, self.scopes[scope].fan))
    }

    /// The pipeline of the store `read` names, planning it the first time a reader reaches it:
    /// the scope's of a store that runs in rounds ([`scope_pipeline`](Self::scope_pipeline)),
    /// and otherwise the store's own. A store's own pipeline reads the pipelines beneath the
    /// store's cycle; the operators inside the cycle, its own breakers among them, stay in pull
    /// mode within it.
    ///
    /// # Panics
    ///
    /// For a store over a live source, whose arrivals no run notifies. For a store that steps
    /// itself outside a loop's scope: one nested in another, one per enclosing row, and one whose
    /// seed reads a pipeline. For a store inside the cycle of a store that steps itself.
    fn store_pipeline(&mut self, read: crate::interpreter::tile_operators::StoreRead) -> usize {
        if let Some(pipeline) = self.located.iter().position(|located| {
            matches!(
                located,
                Located::Store { fan, .. } | Located::Scope { fan, .. } if *fan == read.fan
            )
        }) {
            return pipeline;
        }
        assert!(
            read.sources.is_empty(),
            "a store over a live source {:?} runs in no pipeline: no run notifies its arrivals",
            read.sources
        );
        let within = self.dispatcher_of(&**read.store.borrow());
        // A nested store runs in the scope of the loop around it, a row of its store per round of
        // that loop.
        assert!(
            within.is_some() || matches!(read.store.borrow().tiling(), Tiling::Store { .. }),
            "a nested store, one per enclosing row, runs in no pipeline outside its loop's scope: \
             its frontier is per row: {}",
            read.store.borrow().tiling()
        );
        if read.store.borrow().runs_in_rounds() {
            return self.scope_pipeline(read, within);
        }
        let cell = read.store.clone();
        let mut store = cell.borrow_mut();
        let name = store.name();
        assert!(
            within.is_none(),
            "{name} steps itself and runs in no loop's scope: only an induction store, which runs \
             in rounds, sits inside one"
        );
        // The store's input is what its pipeline consumes, and a store with no consuming mode
        // says so here, before anything is planned for it.
        store
            .as_breaking_mut()
            .unwrap_or_else(|| panic!("{name} is a pipeline breaker"))
            .input_tiling(InputId::ONLY);
        let mut below = Beneath::default();
        store.visit_input_producers_mut(&mut |role, input| {
            let under = match role.starts_with("seed") {
                true => {
                    let under = self.pipelines_under(input, role);
                    // A nested loop's pipeline waits for the pipelines it reads to finish the
                    // round, its seed's among them; one in the run's dispatcher reads its input
                    // whole, which a seed is not part of.
                    assert!(
                        within.is_some() || under.pipelines.is_empty(),
                        "{name}'s {role} reads a pipeline; a store outside every loop's scope \
                         reads its seed from none"
                    );
                    under
                }
                false => self.beneath_cycle(input, read.fan),
            };
            below.read_once(under.pipelines);
        });
        let breaker = store
            .as_breaking_mut()
            .unwrap_or_else(|| panic!("{name} is a pipeline breaker"));
        let placement = breaker
            .base()
            .placement
            .clone()
            .unwrap_or_else(|| panic!("{name} is placed in a pipeline by its entry"));
        // A store reads its input whole once the pipelines beneath it have finished, so neither
        // ranges nor constants beneath it bring a key no push names.
        let pipeline = self.add(
            Located::Store {
                fan: read.fan,
                store: read.store,
            },
            name,
            within,
            Beneath {
                pipelines: below.pipelines,
                ..Beneath::default()
            },
        );
        placement.set(Some(PipelineId(self.local[pipeline])));
        self.placements[pipeline] = Some(placement);
        pipeline
    }

    /// The pipeline of the scope of the store `read` names, which runs in rounds, in the
    /// dispatcher of the scope `within` (`None` for the run's). The walk of the store's chain
    /// plans the breakers inside its cycle as the pipelines of the scope's own dispatcher. The
    /// store is in none, and its entry stays unplaced, so a push to it queues nothing. The
    /// scope's pipeline reads the pipelines beneath the cycle.
    fn scope_pipeline(
        &mut self,
        read: crate::interpreter::tile_operators::StoreRead,
        within: Option<usize>,
    ) -> usize {
        let scope = self.scopes.len();
        self.scopes.push(PlannedScope {
            store: read.store.clone(),
            fan: read.fan,
            pipeline: None,
            count: 0,
            depth: self.walking.len(),
        });
        self.walking.push(scope);
        let mut below = Beneath::default();
        let name = {
            let mut store = read.store.borrow_mut();
            store.visit_input_producers_mut(&mut |role, input| {
                below.read_once(self.pipelines_under(input, role).pipelines);
            });
            store.name()
        };
        self.walking.pop();
        let pipeline = self.add(
            Located::Scope {
                fan: read.fan,
                scope,
            },
            format!("LoopScope({name})"),
            within,
            Beneath {
                pipelines: below.pipelines,
                ..Beneath::default()
            },
        );
        self.scopes[scope].pipeline = Some(pipeline);
        pipeline
    }

    /// What a store's input `producer`, inside the cycle of the fan-out `fan`, holds beneath it:
    /// the pipelines beneath the cycle. A subtree that reaches no recurrence slot of `fan` is
    /// outside the cycle and planned as any chain is; inside it, a breaker is no pipeline.
    ///
    /// # Panics
    ///
    /// Where another store's fan-out is read inside the cycle.
    fn beneath_cycle(
        &mut self,
        producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
        fan: usize,
    ) -> Beneath {
        if !reaches_recurrence(producer, fan) {
            return self.pipelines_under(producer, "input");
        }
        assert!(
            producer.store_read().is_none(),
            "{} reads a store inside another store's cycle, one that steps itself, which no round \
             reaches: a store there runs in no pipeline",
            producer.name()
        );
        let mut below = Beneath::default();
        let (mut inputs, mut seen) = (0, 0);
        producer.visit_input_producers(&mut |_, _| seen += 1);
        producer.visit_input_producers_mut(&mut |_, input| {
            inputs += 1;
            let under = self.beneath_cycle(input, fan);
            below.read_once(under.pipelines);
        });
        debug_assert_eq!(
            inputs,
            seen,
            "{} visits as many inputs mutably as it lists, so the walk of a store's cycle reaches \
             every pipeline beneath it",
            producer.name()
        );
        below
    }

    /// Plan a pipeline at `located`, named `name`, in the dispatcher of the scope `within`
    /// (`None` for the run's), reading what `below` holds, and answer its id in the planner. Its
    /// id in its dispatcher is the count of the pipelines planned there before it.
    fn add(
        &mut self,
        located: Located,
        name: String,
        within: Option<usize>,
        below: Beneath,
    ) -> usize {
        let pipeline = self.located.len();
        // A source reads its input whole, so it consumes whatever keys a constant brings. A
        // reader of pushes takes only what the pushes and the ranges' probes name.
        debug_assert!(
            below.pipelines.is_empty() || below.unprobed.is_empty(),
            "{name} reads pushes, and {:?} beneath it bring keys no push or probe names: a \
             constant collection beneath a reader of pushes is a function operand",
            below.unprobed
        );
        for &(read, direct) in &below.pipelines {
            if direct {
                self.direct.push((read, pipeline));
            }
        }
        let count = match within {
            None => &mut self.count,
            Some(scope) => &mut self.scopes[scope].count,
        };
        self.local.push(*count);
        *count += 1;
        self.located.push(located);
        self.names.push(name);
        self.within.push(within);
        self.placements.push(None);
        self.reads
            .push(below.pipelines.iter().map(|(read, _)| *read).collect());
        self.leaves.push(below.leaves);
        pipeline
    }

    /// Check that no pipeline is read directly by two: only a fan-out slot keeps one reader's
    /// release from removing what another still reads.
    fn check_direct(&self) {
        for &(read, reader) in &self.direct {
            let readers = self
                .reads
                .iter()
                .filter(|reads| reads.contains(&read))
                .count();
            assert!(
                readers == 1,
                "{} reads {} directly, which another pipeline reads too; only a fan-out slot \
                 keeps one reader's release from removing what another still reads",
                self.names[reader],
                self.names[read]
            );
        }
    }

    /// The pipeline of the planner's scope `scope`.
    fn scope_pipeline_of(&self, scope: usize) -> usize {
        self.scopes[scope]
            .pipeline
            .expect("a scope's pipeline is planned once the walk of its store's chain returns")
    }

    /// The dispatcher `pipeline` runs in, then each dispatcher around it, out to the run's.
    fn dispatchers_around(&self, pipeline: usize) -> Vec<Option<usize>> {
        let mut around = vec![self.within[pipeline]];
        while let Some(Some(scope)) = around.last() {
            around.push(self.within[self.scope_pipeline_of(*scope)]);
        }
        around
    }

    /// The pipeline of `dispatcher` that stands for `pipeline`, which runs in it or inside a
    /// scope it runs: `pipeline` itself, or the pipeline of the scope around it in `dispatcher`.
    fn stand_in(&self, mut pipeline: usize, dispatcher: Option<usize>) -> usize {
        while self.within[pipeline] != dispatcher {
            let scope = self.within[pipeline].unwrap_or_else(|| {
                panic!(
                    "{} runs inside the dispatcher of scope {dispatcher:?}",
                    self.names[pipeline]
                )
            });
            pipeline = self.scope_pipeline_of(scope);
        }
        pipeline
    }

    /// The pipelines of the dispatcher of the scope `within` (`None` for the run's), in its
    /// pipeline order. A read between two dispatchers is a read, in the innermost dispatcher
    /// around both, between the pipelines that stand for them there; a scope's pipeline reads
    /// none of its own pipelines.
    fn members(&self, within: Option<usize>) -> Members<'_> {
        let ids: Vec<usize> = (0..self.located.len())
            .filter(|pipeline| self.within[*pipeline] == within)
            .collect();
        debug_assert!(
            ids.iter()
                .enumerate()
                .all(|(local, pipeline)| self.local[*pipeline] == local),
            "a dispatcher numbers its pipelines in the order the planner plans them"
        );
        let mut reads = vec![Vec::new(); ids.len()];
        for (reader, pipeline_reads) in self.reads.iter().enumerate() {
            for &read in pipeline_reads {
                let around = self.dispatchers_around(read);
                let common = self
                    .dispatchers_around(reader)
                    .into_iter()
                    .find(|dispatcher| around.contains(dispatcher))
                    .expect("every dispatcher runs inside the run's");
                if common != within {
                    continue;
                }
                let (reader, read) = (self.stand_in(reader, common), self.stand_in(read, common));
                let at = &mut reads[self.local[reader]];
                if reader != read && !at.contains(&self.local[read]) {
                    at.push(self.local[read]);
                }
            }
        }
        Members {
            located: ids
                .iter()
                .map(|pipeline| &self.located[*pipeline])
                .collect(),
            reads,
            names: ids
                .iter()
                .map(|pipeline| self.names[*pipeline].clone())
                .collect(),
            leaves: ids
                .iter()
                .map(|pipeline| self.leaves[*pipeline].clone())
                .collect(),
            kinds: ids
                .iter()
                .map(|pipeline| match &self.located[*pipeline] {
                    Located::Store { .. } => {
                        debug_assert!(
                            within.is_none(),
                            "a store that steps itself runs in the run's dispatcher; an induction \
                             store inside a loop's scope is a nested loop's scope"
                        );
                        Consumes::Whole
                    }
                    Located::Scope { .. } if within.is_none() => Consumes::Whole,
                    Located::Scope { .. } => Consumes::Rounds,
                    Located::Chain(_) | Located::Sink(_) => Consumes::Pushes,
                })
                .collect(),
            placements: ids
                .iter()
                .map(|pipeline| self.placements[*pipeline].clone())
                .collect(),
        }
    }

    /// The loop scope of the planner's scope `scope`.
    /// Each scope's address and the breakers it keeps are added to `kept`: the inner pipelines
    /// its rounds queue or push packages to ([`refusal_of_nested`](Self::refusal_of_nested)).
    fn build_scope(
        &self,
        scope: usize,
        morsel_rows: usize,
        kept: &mut Vec<(usize, Vec<usize>)>,
    ) -> loop_scope::LoopScope {
        let members = self.members(Some(scope));
        let at = members
            .located
            .iter()
            .map(|located| match located {
                Located::Chain(id) => loop_scope::Member::Chain(*id),
                Located::Scope { scope, .. } => loop_scope::Member::Scope(Box::new(RefCell::new(
                    self.build_scope(*scope, morsel_rows, kept),
                ))),
                Located::Store { .. } | Located::Sink(_) => unreachable!(
                    "a scope's pipelines are the breakers inside its cycle and the scopes of the \
                     loops nested in it"
                ),
            })
            .collect();
        let built =
            loop_scope::LoopScope::new(self.scopes[scope].store.clone(), at, members, morsel_rows);
        kept.push((scope, built.chain_breakers()));
        built
    }

    /// Why the run cannot run a loop nested in another in rounds, or `None` where it can:
    /// an operator a round of the loop's scope pulls beneath the outermost keys restates no
    /// projection at the level it is pulled at ([`unrestated`]). `kept` holds each scope's
    /// breakers, as [`build_scope`](Self::build_scope) gathers them. The walk starts at each
    /// breaker a nested scope keeps, at the level of its rounds, and ends at every breaker that
    /// consumes, in any dispatcher, since that breaker's consume pulls its inputs; a breaker
    /// whose pipeline its dispatcher would read whole runs in pull mode and passes the pull on.
    fn refusal_of_nested(&self, kept: &[(usize, Vec<usize>)]) -> Option<String> {
        let consuming: Vec<usize> = (0..self.located.len())
            .filter(|&pipeline| self.within[pipeline].is_none())
            .filter_map(|pipeline| match self.located[pipeline] {
                Located::Chain(id) => Some(id),
                _ => None,
            })
            .chain(kept.iter().flat_map(|(_, ids)| ids.iter().copied()))
            .collect();
        kept.iter().find_map(|(scope, breakers)| {
            let planned = &self.scopes[*scope];
            if planned.depth == 0 {
                return None;
            }
            let level = CurryLevel::new(planned.depth);
            let store = planned.store.borrow();
            breakers.iter().find_map(|&id| {
                let mut found = None;
                store.visit_input_producers(&mut |_, input| {
                    if found.is_none() {
                        found = at_address(
                            input,
                            id,
                            &mut Some(
                                |breaker: &dyn crate::interpreter::tile_operators::TileProducer| {
                                    unrestated(breaker, Some(level), &consuming, true)
                                },
                            ),
                        );
                    }
                });
                debug_assert!(
                    found.is_some(),
                    "a breaker scope {scope} keeps sits in its store's chain, inside the cycle"
                );
                found.flatten()
            })
        })
    }
}

/// A producer's identity in its chain: the address of its boxed state, which does not move while
/// the chain stands. `TileProducer::producer_id` counts per producer type, so two producers of
/// different types share one.
#[cfg(test)]
fn address(producer: &dyn crate::interpreter::tile_operators::TileProducer) -> usize {
    std::ptr::from_ref(producer).cast::<()>() as usize
}

/// Why a round of a loop's scope cannot pull the chain at `producer`, or `None` where every
/// operator it pulls beneath the outermost keys restates the keys it is pulled at. `pulled` is the
/// level `producer` is pulled at, `None` where it is pulled whole or at the outermost keys, and
/// each operator passes its level to its inputs as it declares (`TileProducer::input_level`). The
/// walk ends at a recurrence slot or another store's read, whose store answers from its snapshot,
/// and, past the breaker it starts at (`start`), at every breaker in `consuming`, whose consume
/// pulls its inputs and whose own scope checks them.
#[cfg(test)]
fn unrestated(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    pulled: Option<CurryLevel>,
    consuming: &[usize],
    start: bool,
) -> Option<String> {
    if producer.recurrence_of().is_some() || producer.store_read().is_some() {
        return None;
    }
    let pulled = pulled.filter(|&pulled| pulled != CurryLevel::OUTERMOST);
    if let Some(pulled) = pulled
        && producer.restates().refuses(pulled)
    {
        let name = producer.name();
        let kind = name.split('#').next().unwrap_or(&name);
        return Some(format!(
            "{kind} in a nested loop's cycle is pulled at the keys of {pulled} and restates {}",
            producer.restates()
        ));
    }
    if pulled.is_none() || (!start && consuming.contains(&address(producer))) {
        return None;
    }
    let mut why = None;
    producer.visit_input_producers(&mut |role, input| {
        let beneath = pulled.and_then(|pulled| producer.input_level(role, pulled));
        why = why
            .take()
            .or_else(|| unrestated(input, beneath, consuming, false));
    });
    why
}

/// Call `f` with the producer at address `id` ([`address`]) in the chain under `producer`, and
/// answer what it answers; `None` where the chain holds no such producer. The walk crosses a
/// nested store's read, since a scope's breakers include the ones its nested loop's source is
/// read through, and stops at a recurrence slot, which closes a store's cycle.
#[cfg(test)]
fn at_address<R>(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    id: usize,
    f: &mut Option<impl FnOnce(&dyn crate::interpreter::tile_operators::TileProducer) -> R>,
) -> Option<R> {
    if address(producer) == id {
        return f.take().map(|f| f(producer));
    }
    if producer.recurrence_of().is_some() {
        return None;
    }
    let mut found = None;
    producer.visit_input_producers(&mut |_, input| {
        if found.is_none() {
            found = at_address(input, id, f);
        }
    });
    found
}

/// Whether the chain under `producer` reads the fan-out `fan` through a recurrence slot: whether
/// it is inside that fan-out's store's cycle. The walk stops at every recurrence slot, the one
/// edge that closes a cycle.
#[cfg(test)]
fn reaches_recurrence(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    fan: usize,
) -> bool {
    if let Some(through) = producer.recurrence_of() {
        return through == fan;
    }
    let mut reaches = false;
    producer.visit_input_producers(&mut |_, input| {
        reaches = reaches || reaches_recurrence(input, fan);
    });
    reaches
}

/// Call `call` with the breaker at address `id` in the chain under `producer`, and answer whether
/// it was found.
#[cfg(test)]
fn reach_in_chain(
    producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
    id: usize,
    call: &mut Option<&mut Call<'_>>,
) -> bool {
    if address(producer) == id {
        let breaker = producer
            .as_breaking_mut()
            .expect("a pipeline's producer is a breaker");
        (call.take().expect("a breaker is reached once"))(breaker);
        return true;
    }
    let mut found = false;
    producer.visit_input_producers_mut(&mut |_, input| {
        found = found || reach_in_chain(input, id, call);
    });
    found
}

#[cfg(test)]
mod tests {
    use intervalsets::{Interval, IntervalSet};

    use super::*;
    use crate::interpreter::BaseType;

    /// A range covering every `u64` is cut without overflowing its count of positions.
    #[test]
    fn a_seed_over_every_u64_is_cut_at_the_multiples_of_rows() {
        let input = Tiling::data_function(
            Extent::UIntRange(IntervalSet::from(Interval::closed(0, u64::MAX))),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let morsels = seed(&input, 1 << 63);
        assert_eq!(morsels.len(), 2);
        assert_eq!(partition_gap(&input.universal_guard(), &morsels), None);
        let TileGuard::Function(FunctionGuard::Domain(second)) = &morsels[1] else {
            panic!("a morsel of keys")
        };
        assert!(second.contains(&Value::UInt(1 << 63)));
        assert!(!second.contains(&Value::UInt((1 << 63) - 1)));
    }

    /// A range of several runs is cut every `rows` positions counted across the runs: positions
    /// `0..=3` and `6..=8` at `rows` 2 are cut before `2`, `6` and `8`.
    #[test]
    fn a_seed_over_several_runs_counts_positions_across_them() {
        let runs = IntervalSet::new(vec![Interval::closed(0, 3), Interval::closed(6, 8)]);
        let input = Tiling::data_function(
            Extent::UIntRange(runs),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let morsels = seed(&input, 2);
        assert_eq!(partition_gap(&input.universal_guard(), &morsels), None);
        let held: Vec<Vec<u64>> = morsels
            .iter()
            .map(|morsel| {
                let TileGuard::Function(FunctionGuard::Domain(keys)) = morsel else {
                    panic!("a morsel of keys")
                };
                [0, 1, 2, 3, 6, 7, 8]
                    .into_iter()
                    .filter(|key| keys.contains(&Value::UInt(*key)))
                    .collect()
            })
            .collect();
        assert_eq!(held, vec![vec![0, 1], vec![2, 3], vec![6, 7], vec![8]]);
    }
}

#[cfg(test)]
mod planner_walk_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{TestTileProducer, two_levels_of_ints};
    use crate::interpreter::tile_operators::{
        MemoProducer, ProducerBase, TileProducer, impl_producer_base,
    };

    /// A memo over a producer that restates the outermost keys only.
    fn memo_over_outermost() -> MemoProducer {
        let (tile, tiling) = two_levels_of_ints();
        MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        )
    }

    /// An inner pipeline's breaker is pulled at the paths of its scope's rounds and pulls its
    /// input there, so an input that restates only the outermost keys refuses the scope.
    #[test]
    fn a_breaker_pulled_beneath_the_outermost_keys_refuses_an_input_that_restates_none() {
        let memo = memo_over_outermost();
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[address(&memo)], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a nested loop's cycle is pulled at the keys of level 1 and restates \
                 the outermost keys only"
            )
        );
    }

    /// A breaker that consumes ends the walk: its consume pulls its inputs, and its own scope
    /// checks them. One in pull mode passes the pull on to its inputs.
    #[test]
    fn a_consuming_breaker_ends_the_walk_and_one_in_pull_mode_passes_it_on() {
        let (_, tiling) = two_levels_of_ints();
        let outer = MemoProducer::over(Box::new(memo_over_outermost()), &tiling);
        let mut inner = 0;
        outer.visit_input_producers(&mut |_, input| inner = address(input));
        let level = Some(CurryLevel::new(1));
        assert_eq!(unrestated(&outer, level, &[inner], true), None);
        assert!(
            unrestated(&outer, level, &[], true)
                .is_some_and(|why| why.starts_with("TestTile in a nested loop's cycle"))
        );
    }

    /// A breaker in no inner pipeline is pulled whole, so nothing beneath it is pulled at a
    /// round's paths.
    #[test]
    fn a_breaker_pulled_whole_refuses_nothing_beneath_it() {
        let memo = memo_over_outermost();
        assert_eq!(unrestated(&memo, None, &[], true), None);
    }

    /// A producer that restates every level and reads its one input whole
    /// (`TileProducer::input_level` answers `None`).
    struct ReadsWhole {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    impl TileProducer for ReadsWhole {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn restates(&self) -> crate::interpreter::Restates {
            crate::interpreter::Restates::Every
        }

        fn input_level(&self, _role: &str, _level: CurryLevel) -> Option<CurryLevel> {
            None
        }

        fn get_impl(&mut self, _guard: TileGuard) -> crate::interpreter::Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// An input a producer reads whole is pulled at no level beneath the outermost keys, so one
    /// that restates the outermost keys only does not refuse the scope.
    #[test]
    fn an_input_read_whole_refuses_nothing() {
        let (tile, tiling) = two_levels_of_ints();
        let reads_whole = ReadsWhole {
            base: ProducerBase::unowned(ReadsWhole::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling.clone())),
        };
        let memo = MemoProducer::over(Box::new(reads_whole), &tiling);
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[address(&memo)], true);
        assert_eq!(why, None);
    }
}

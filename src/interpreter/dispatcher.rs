//! A dispatcher of work packages between the pipelines of a program, shared by the threads that
//! claim them.
//!
//! A pipeline is a [`BreakingProducer`] and the chain it owns. The dispatcher holds the graph of
//! pipelines, a window of epochs in flight, and a queue of work packages per pipeline per
//! epoch, each package one morsel of at most `morsel_rows` held rows. A queue is appended to
//! while it is open, each slot written once, and read through atomic counters, so a claim takes
//! no lock. A worker takes a lock to sleep while there is nothing to claim, and a change that can
//! end a sleep takes it to wake the sleepers, only while there are some. The dispatcher holds no
//! breaker, so it is `Sync` while the breakers are not `Send`. The single-threaded driver, [`run`],
//! reaches the breakers through the handles its caller passes, indexed by pipeline. Nothing outside
//! unit tests calls it, and only unit tests drive the dispatcher from several threads. See
//! `src/interpreter/design-operators.md`, "The dispatcher".

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock, PoisonError, RwLock};
use std::thread;

use intervalsets::Bounding;

use crate::interpreter::tile_operators::{
    BreakingProducer, FunctionGuard, Tiling, cut_before, guard_minus, partition_gap,
};
use crate::interpreter::{Extent, Predicate, TileGuard, Value};

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
    /// Finish the pipeline's epoch, which the claim moved to finalizing, then
    /// [`finish`](Dispatcher::finish) it: push what the epoch decided, through the breaker's
    /// `finalize` where `last` says the epoch is the run's last, and through
    /// [`Pushes::push_final`] otherwise. `consumed` is the region the epoch's packages partition,
    /// which the pipeline consumed whole, and `None` when it had none.
    Finalize {
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

/// Where a pipeline is in one epoch. It is `Finalizing` from the claim, or the
/// [`Dispatcher::begin_finalize`], that moves it there until [`Dispatcher::finish`].
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
enum Phase {
    Running,
    Finalizing,
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
            1 => Phase::Finalizing,
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
    /// Appends take it, and so does the move of the pipeline's epoch to finalizing; a claim of a
    /// package never does.
    // shared-state-ok: the region a pipeline's packages partition, which appends grow and its
    // finalize reads; what crosses it is a guard naming a region, never a tile.
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
        // The indices are reserved together, and only while the queue is open.
        let mut reserved = self.reserved.load(Ordering::Acquire);
        let first = loop {
            if reserved & CLOSED != 0 {
                return false;
            }
            if morsels.is_empty() {
                return true;
            }
            match self.reserved.compare_exchange_weak(
                reserved,
                reserved + morsels.len(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(first) => break first,
                Err(now) => reserved = now,
            }
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
            let (bucket, at) = Self::locate(index);
            let slots = self.buckets[bucket].get_or_init(|| {
                (0..FIRST_BUCKET << bucket)
                    .map(|_| Slot::default())
                    .collect()
            });
            let written = slots[at].guard.set(morsel.clone()).is_ok();
            debug_assert!(written, "an append writes the slot it reserved, once");
        }
        true
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
    fn new(number: u64, pipelines: usize) -> Self {
        EpochState {
            number,
            pipelines: (0..pipelines)
                .map(|_| EpochPipeline {
                    queue: Queue::new(),
                    claimed: AtomicUsize::new(0),
                    acknowledged: AtomicUsize::new(0),
                    phase: AtomicPhase::new(Phase::Running),
                })
                .collect(),
            unfinished: AtomicUsize::new(pipelines),
        }
    }
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
    /// The pipelines each pipeline reads: the breakers its chain pulls.
    reads: Vec<Vec<usize>>,
    /// The pipeline that reads each pipeline, if any: its parent, which its push reaches.
    parent: Vec<Option<usize>>,
    /// Per pipeline, whether it consumes its morsels in queue order one at a time
    /// ([`order`](Dispatcher::order)). Set before the dispatcher is shared.
    ordered: Vec<bool>,
    /// Per source pipeline, the most packages queued for it and not yet acknowledged that a
    /// notify finds before it queues more ([`limit`](Dispatcher::limit)); `usize::MAX` for none.
    /// Set before the dispatcher is shared.
    credit: Vec<usize>,
    pipelines: Vec<PipelineState>,
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
    /// When `morsel_rows` is zero, when a pipeline reads one that does not exist, reads more than
    /// one pipeline, or is read by two, or when the graph has a cycle. A breaker has one input, so
    /// its pipeline reads at most one other. Two readers of one breaker need a `FanOut` between
    /// them: the release of one would remove what the other has still to read. A pipeline in a
    /// cycle would wait for itself to finish.
    pub fn new(reads: Vec<Vec<usize>>, morsel_rows: usize) -> Self {
        assert!(morsel_rows > 0, "a morsel holds at least one row");
        let count = reads.len();
        let mut parent = vec![None; count];
        for (pipeline, read) in reads.iter().enumerate() {
            assert!(
                read.len() <= 1,
                "pipeline {pipeline} reads pipelines {read:?}; a breaker has one input"
            );
            for &child in read {
                assert!(
                    child < count,
                    "pipeline {pipeline} reads {child}, which is not one"
                );
                if let Some(other) = parent[child].replace(pipeline) {
                    panic!(
                        "pipeline {child} is read by pipelines {other} and {pipeline}; a breaker \
                         read by two pipelines needs a FanOut"
                    );
                }
            }
        }
        assert!(
            acyclic(&reads),
            "the pipelines read each other in a cycle: {reads:?}"
        );
        let pipelines = (0..count)
            .map(|_| PipelineState {
                pushed: Mutex::new(None),
                closed: AtomicBool::new(false),
                queued: AtomicUsize::new(0),
                acknowledged: AtomicUsize::new(0),
                in_flight: AtomicBool::new(false),
            })
            .collect();
        Self {
            morsel_rows,
            reads,
            parent,
            ordered: vec![false; count],
            credit: vec![usize::MAX; count],
            pipelines,
            window: Self::slots(DEFAULT_WINDOW, count),
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
    fn slots(epochs: usize, pipelines: usize) -> Vec<RwLock<Arc<EpochState>>> {
        (0..epochs as u64)
            .map(|number| RwLock::new(Arc::new(EpochState::new(number, pipelines))))
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
                && self.pipelines.iter().all(|pipeline| {
                    pipeline.queued.load(Ordering::Acquire) == 0
                        && !pipeline.closed.load(Ordering::Acquire)
                }),
            "a window is set before any notify, seal or close"
        );
        self.window = Self::slots(epochs, self.reads.len());
    }

    /// Mark `pipeline` as consuming its morsels one at a time, epoch by epoch: every morsel of an
    /// epoch in the order it was queued, then the epoch's finish, then the next epoch's. Its
    /// breaker's state advances through them in order, as a loop's store decides its positions
    /// ascending.
    pub fn order(&mut self, pipeline: PipelineId) {
        self.ordered[pipeline.0] = true;
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
            self.reads[p].is_empty(),
            "pipeline {p} is limited only as a source: a reader is queued what is pushed to it"
        );
        assert!(packages > 0, "a source's limit is at least one package");
        self.credit[p] = packages;
    }

    /// The handle a breaker of `pipeline` pushes through, for its oldest epoch it has not
    /// finished. Its pushes land at [`finish`](Self::finish).
    pub fn pushes(&self, pipeline: PipelineId) -> Pushes<'_> {
        self.state(pipeline);
        let epoch = Self::unfinished(pipeline.0, &self.epochs())
            .map_or(self.current.load(Ordering::Acquire), |epoch| epoch.number);
        self.pushes_in(pipeline, epoch)
    }

    /// The handle a breaker of `pipeline` pushes through for `epoch`.
    pub fn pushes_in(&self, pipeline: PipelineId, epoch: u64) -> Pushes<'_> {
        self.state(pipeline);
        Pushes {
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
            self.fail();
            panic!("{}", message());
        }
    }

    /// The state of `pipeline` across epochs.
    ///
    /// # Panics
    ///
    /// When the dispatcher has no such pipeline.
    fn state(&self, pipeline: PipelineId) -> &PipelineState {
        let count = self.pipelines.len();
        self.ensure(pipeline.0 < count, || {
            format!(
                "pipeline {} is one of the dispatcher's {count} pipelines",
                pipeline.0
            )
        });
        &self.pipelines[pipeline.0]
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
        if self.state(pipeline).outstanding() >= self.credit[pipeline.0] {
            return false;
        }
        self.append_to_source(pipeline, &cut_positions(guard, self.morsel_rows));
        true
    }

    /// Refuse `pipeline` unless it is a source, one that reads no pipeline.
    fn ensure_source(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.reads[p].is_empty(), || {
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
            if self.pipelines[p].closed.load(Ordering::Acquire) {
                next.pipelines[p].queue.close();
            }
        }
        self.current.store(current + 1, Ordering::Release);
        self.advance();
        true
    }

    /// The source pipelines, those that read none.
    fn sources(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.reads.len()).filter(|p| self.reads[*p].is_empty())
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
        self.ensure(self.reads[p].is_empty(), || {
            format!("pipeline {p} closes its queue only as a source, which reads no pipeline")
        });
        let _sealing = self.sealing.lock().unwrap_or_else(PoisonError::into_inner);
        let closed = !state.closed.swap(true, Ordering::AcqRel);
        self.ensure(closed, || format!("pipeline {p} closes its queue once"));
        let current = self.current.load(Ordering::Acquire);
        if self
            .sources()
            .all(|source| self.pipelines[source].closed.load(Ordering::Acquire))
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
        if !self.ordered[pipeline] {
            return epochs
                .iter()
                .find_map(|epoch| Self::claim_in(pipeline, epoch));
        }
        let state = &self.pipelines[pipeline];
        // The flag is held while the claim looks, so at most one claim of the pipeline looks at
        // once, and kept for the package it takes.
        if state
            .in_flight
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            return None;
        }
        let package =
            Self::unfinished(pipeline, epochs).and_then(|epoch| Self::claim_in(pipeline, epoch));
        if package.is_none() {
            state.in_flight.store(false, Ordering::SeqCst);
            // A claim that found the flag held answered nothing for the pipeline, and may wait on
            // a generation that a package queued since this look began has reached. The flag's
            // operations and the generation's are sequentially consistent, so the generation read
            // after the release sees that package's advance and every write before it, and a
            // second look finds the package and wakes that claim.
            self.generation.load(Ordering::SeqCst);
            if Self::unfinished(pipeline, &self.epochs())
                .is_some_and(|epoch| Self::claimable(pipeline, epoch))
            {
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
    /// last epoch it finishes only after every earlier one, since the breaker's `finalize` is its
    /// last call, and an ordered pipeline finishes every epoch after the earlier ones.
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
            && ((epoch.number != last && !self.ordered[pipeline])
                || epochs
                    .iter()
                    .filter(|earlier| earlier.number < epoch.number)
                    .all(|earlier| earlier.pipelines[pipeline].phase.load() == Phase::Finished))
    }

    /// What to do next, without blocking. A claim takes the package at the front of `preferred`'s
    /// queue where it may, and otherwise of the lowest pipeline whose queue it may take from, each
    /// pipeline's oldest epoch first; an ordered pipeline takes from the oldest epoch it has not
    /// finished, and is skipped while a package of it is in flight. With no package to claim, it
    /// moves the oldest epoch's lowest pipeline that may finish it to finalizing and hands its
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
        let count = self.reads.len();
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
                        .moved(Phase::Running, Phase::Finalizing);
                if begun {
                    return Next::Finalize {
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
        let refused = || match self.ordered[p] {
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
        if self.ordered[p] {
            state.in_flight.store(false, Ordering::Release);
        }
        // An acknowledgement frees an ordered pipeline's next package, may let the pipeline
        // finish the epoch, and returns credit to a limited source's notify.
        if self.ordered[p]
            || self.credit[p] != usize::MAX
            || acknowledged == in_epoch.queue.reserved()
        {
            self.advance();
        }
    }

    /// Move `pipeline`'s oldest epoch it has not begun to finish to finalizing, outside a claim,
    /// and answer that epoch and what the pipeline consumed in it.
    ///
    /// # Panics
    ///
    /// When the pipeline has finished every epoch, a package queued for it in the epoch has not
    /// been acknowledged, a pipeline it reads has not finished the epoch, its queue in the epoch
    /// is not closed, the epoch is neither sealed nor known to be the last, or the pipeline has not
    /// finished every earlier epoch where the epoch is the last or the pipeline is ordered.
    pub fn begin_finalize(&self, pipeline: PipelineId) -> (u64, Option<TileGuard>) {
        let p = pipeline.0;
        self.state(pipeline);
        let epochs = self.epochs();
        let epoch = epochs
            .iter()
            .find(|epoch| epoch.pipelines[p].phase.load() == Phase::Running);
        self.ensure(epoch.is_some(), || format!("pipeline {p} finalizes once"));
        let epoch = epoch.expect("refused above");
        let state = &epoch.pipelines[p];
        self.ensure(
            state.acknowledged.load(Ordering::Acquire) == state.queue.reserved(),
            || {
                format!(
                    "pipeline {p} finalizes after its queue is empty and every package claimed \
                     for it was acknowledged"
                )
            },
        );
        self.ensure(
            self.reads[p]
                .iter()
                .all(|read| epoch.pipelines[*read].phase.load() == Phase::Finished),
            || format!("pipeline {p} finalizes after every pipeline it reads has finished"),
        );
        // A source's queue is closed by a seal or its close. A pipeline that reads another has
        // its queue filled and closed once that one's pushes landed, which `finish` does after it
        // marks that one finished.
        self.ensure(state.queue.is_closed(), || {
            format!("pipeline {p} finalizes after its queue is closed")
        });
        self.ensure(self.ready(p, epoch, &epochs), || {
            format!(
                "pipeline {p} finalizes an epoch once it is sealed or the last, and after every \
                 earlier epoch where it is the last or the pipeline is ordered"
            )
        });
        let begun = state.phase.moved(Phase::Running, Phase::Finalizing);
        self.ensure(begun, || format!("pipeline {p} finalizes once"));
        (epoch.number, state.queue.region())
    }

    /// Mark the pipeline `pushes` belongs to finished in its epoch, land what it pushed in its
    /// parent's queue for that epoch, and close that queue. The parent may claim and finish the
    /// epoch only once its queue there is closed. The finish that is the last of the epoch's
    /// retires it, and the window's slot takes the epoch a window later. After a failure it
    /// records nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline is not finalizing in the epoch, which a second finish of it finds, or its
    /// parent has begun to finish the epoch.
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
                .moved(Phase::Finalizing, Phase::Finished)
        });
        self.ensure(finished, || {
            format!("pipeline {p} finishes after its finalize began")
        });
        let epoch = epoch.expect("refused above");
        // Recorded before the parent's queue is closed, which lets the parent claim.
        #[cfg(test)]
        self.record(Event::Finalize(PipelineId(p)));
        if let Some(parent) = self.parent[p] {
            let queue = &epoch.pipelines[parent];
            self.ensure(queue.phase.load() == Phase::Running, || {
                format!("pipeline {parent} receives packages before it finalizes")
            });
            let landed = queue.queue.append(parent, &morsels) && queue.queue.close();
            self.ensure(landed, || {
                format!("pipeline {parent} receives packages once")
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
            Arc::new(EpochState::new(later, self.reads.len()));
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
    /// recorded as claimed. Unlike a claim, it never begins a finalize.
    #[cfg(test)]
    pub(crate) fn pop(&self) -> Option<WorkPackage> {
        let epochs = self.epochs();
        (0..self.reads.len()).find_map(|p| self.claim_from(p, &epochs))
    }

    /// The package at the front of `pipeline`'s queue, claimed, where a claim may take one.
    #[cfg(test)]
    pub(crate) fn claim_of(&self, pipeline: PipelineId) -> Option<WorkPackage> {
        self.claim_from(pipeline.0, &self.epochs())
    }

    /// Finalize `pipeline`'s oldest unfinished epoch through `finalize`, a breaker's finalize
    /// called by hand, between the steps a claim's finalize goes through: begin, push, finish. A
    /// source a test finalizes by hand is closed first, whatever was queued for it.
    #[cfg(test)]
    pub(crate) fn finalize_by_hand(
        &self,
        pipeline: PipelineId,
        finalize: impl FnOnce(&mut Pushes<'_>),
    ) {
        if self.reads[pipeline.0].is_empty() && !self.state(pipeline).closed.load(Ordering::Acquire)
        {
            self.close(pipeline);
        }
        let (epoch, _) = self.begin_finalize(pipeline);
        let mut pushes = self.pushes_in(pipeline, epoch);
        finalize(&mut pushes);
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

/// What a breaker pushes through in one epoch: one work package per morsel for the pipeline that
/// reads it. The packages land when the dispatcher [finishes](Dispatcher::finish) the pipeline's
/// epoch, in its reader's queue for that epoch.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    pipeline: usize,
    epoch: u64,
    morsels: Vec<TileGuard>,
}

impl Pushes<'_> {
    /// Push what `breaker` has decided and the pipeline has not pushed before, its final guard
    /// less the region pushed, for the pipeline that reads it: one package per morsel the breaker
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
        if self.dispatcher.parent[self.pipeline].is_none() {
            return;
        }
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
        let mut pushed = self.dispatcher.pipelines[self.pipeline]
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
    /// rows, as [`push_final`](Self::push_final) pushes a breaker's final guard.
    #[cfg(test)]
    pub(crate) fn push(
        &mut self,
        guard: &TileGuard,
        cut: impl FnOnce(&TileGuard, usize) -> Vec<TileGuard>,
    ) {
        if self.dispatcher.parent[self.pipeline].is_none() || guard.is_empty() {
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
    /// Refuses to drop pushes that never landed, which would lose the parent's packages.
    fn drop(&mut self) {
        if !thread::panicking() {
            assert!(
                self.morsels.is_empty(),
                "pipeline {} lands its pushes through Dispatcher::finish",
                self.pipeline
            );
        }
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

/// A shared handle on a pipeline's breaker. A parent's chain reads the breaker through another
/// handle, so the driver borrows it for one call at a time.
// shared-state-ok: the driver's handle on a breaker it calls, and in a test the handle a parent's
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
    Finalize(PipelineId),
}

/// Run every pipeline to its end on the calling thread. A source pipeline, one that reads no
/// pipeline, starts with its breaker's input whole, as one package per morsel ([`seed`]), and is
/// closed, so the run is one epoch. The driver consumes the package of the lowest pipeline that
/// has one; when no pipeline has one, it finishes the lowest pipeline that may finish. It stops
/// when every pipeline has finished.
///
/// # Panics
///
/// When a pipeline cannot finish though nothing is queued, which an acyclic graph rules out; in a
/// debug build, when a package's guard is not a guard of the tiling its breaker's input answers,
/// when a pipeline consumes a region it consumed before, or when a breaker's morsels do not
/// partition its final guard; and at any of the invariants [`finalize`] asserts.
pub fn run(dispatcher: &Dispatcher, breakers: &[BreakerHandle]) {
    assert_eq!(
        breakers.len(),
        dispatcher.reads.len(),
        "one breaker per pipeline"
    );
    start(dispatcher, breakers);
    loop {
        match dispatcher.try_claim(None) {
            Next::Package(package) => consume(dispatcher, breakers, package),
            Next::Finalize {
                pipeline,
                epoch,
                consumed,
                last,
            } => finalize_begun(dispatcher, breakers, pipeline, epoch, consumed, last),
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
pub(crate) fn start(dispatcher: &Dispatcher, breakers: &[BreakerHandle]) {
    for (pipeline, read) in dispatcher.reads.iter().enumerate() {
        if read.is_empty() {
            let input = breakers[pipeline].borrow().input_tiling();
            dispatcher.start_source(PipelineId(pipeline), &input);
        }
    }
}

/// Hand `package` to its pipeline's breaker, then acknowledge it.
///
/// # Panics
///
/// As [`Dispatcher::acknowledge`] says of a package; in a debug build, as [`run`] says of a
/// package.
pub(crate) fn consume(dispatcher: &Dispatcher, breakers: &[BreakerHandle], package: WorkPackage) {
    let p = package.pipeline.0;
    {
        let mut breaker = breakers[p].borrow_mut();
        // A package carries a guard of the tiling of the pipeline that pushed it, or of this
        // breaker's own input for a source, so it fits only a breaker whose input answers that
        // tiling.
        debug_assert!(
            package.guard.check_from(&breaker.input_tiling()),
            "pipeline {p} consumes a guard of the tiling its breaker's input answers: {:?}",
            package.guard
        );
        breaker.consume_impl(package.guard.clone());
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
pub fn finalize(dispatcher: &Dispatcher, breakers: &[BreakerHandle], pipeline: PipelineId) {
    let (epoch, consumed) = dispatcher.begin_finalize(pipeline);
    let last = epoch == dispatcher.last.load(Ordering::Acquire);
    finalize_begun(dispatcher, breakers, pipeline, epoch, consumed, last);
}

/// Finish `pipeline`'s `epoch`, which has begun after consuming `consumed`: push what the epoch
/// decided, through the breaker's `finalize` where `last` says it is the run's last epoch and
/// through [`Pushes::push_final`] otherwise, then mark it finished.
fn finalize_begun(
    dispatcher: &Dispatcher,
    breakers: &[BreakerHandle],
    pipeline: PipelineId,
    epoch: u64,
    consumed: Option<TileGuard>,
    last: bool,
) {
    let p = pipeline.0;
    let mut breaker = breakers[p].borrow_mut();
    let released = breaker.input_released();
    assert!(
        consumed.is_none_or(|consumed| {
            released.is_universal() || guard_minus(&consumed, &released).is_empty()
        }),
        "pipeline {p} finalizes after its input has released every guard the pipeline consumed"
    );
    let mut pushes = dispatcher.pushes_in(pipeline, epoch);
    match last {
        true => breaker.finalize(&mut pushes),
        false => pushes.push_final(&*breaker),
    }
    dispatcher.finish(pushes);
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

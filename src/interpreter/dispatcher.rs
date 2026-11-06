//! A dispatcher of work packages between the pipelines of a program, shared by the threads that
//! claim them.
//!
//! A pipeline is a [`Breaker`] and the chain it owns; the breaker of a pipeline that another reads
//! is a [`BreakingProducer`]. The dispatcher holds the graph of pipelines and a queue of work
//! packages per pipeline, each package one morsel of at most `morsel_rows` held rows. Each pipeline
//! finishes once, when nothing more can be queued for it. A queue is appended to while it is open,
//! each slot written once, and read through atomic counters, so a claim takes no lock. A worker
//! takes a lock to sleep while there is nothing to claim, and a change that can end a sleep takes
//! it to wake the sleepers, only while there are some. The dispatcher holds no breaker, so it is
//! `Sync` while the breakers are not `Send`. The single-threaded driver, [`run`], reaches the
//! breakers through the handles its caller passes, indexed by pipeline. Nothing outside unit tests
//! calls it, and only unit tests drive the dispatcher from several threads. See
//! `src/interpreter/design-operators.md`, "The dispatcher".

use std::cell::{Cell, RefCell};
use std::rc::Rc;
#[cfg(test)]
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, OnceLock, PoisonError};
use std::thread;

use intervalsets::Bounding;

use crate::interpreter::tile_operators::InputId;
use crate::interpreter::tile_operators::{
    Breaker, BreakingProducer, FunctionGuard, Tiling, cut_before, guard_minus, partition_gap,
};
use crate::interpreter::{
    Consumer, Extent, Predicate, Projection, SharedConsumer, TileGuard, Value,
};

/// A pipeline, by its index in the [`Dispatcher`].
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct PipelineId(pub usize);

/// A guard for one pipeline's breaker to consume: one morsel of a pushed guard, or of a source
/// pipeline's input.
#[cfg_attr(test, derive(Clone, Debug, PartialEq))]
pub struct WorkPackage {
    pub pipeline: PipelineId,
    pub guard: TileGuard,
    /// The package's position in its pipeline's queue, which its acknowledgement marks.
    pub(crate) index: usize,
}

/// What a worker does next, as [`Dispatcher::try_claim`] answers.
#[cfg_attr(test, derive(Debug))]
pub enum Next {
    /// Hand the package to its pipeline's breaker, then [`acknowledge`](Dispatcher::acknowledge)
    /// it.
    Package(WorkPackage),
    /// Finish the pipeline, which the claim moved to finishing, then
    /// [`finish`](Dispatcher::finish) it: push what it decided and no consume pushed, through the
    /// breaker's [`finish`][Breaker::finish], its last call. `consumed` is the region the
    /// pipeline's packages partition, which it consumed whole, and `None` when it had none.
    ///
    /// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
    Finish {
        pipeline: PipelineId,
        consumed: Option<TileGuard>,
    },
    /// Nothing is claimable and some pipeline has not finished: [`wait`](Dispatcher::wait) for a
    /// change after the generation.
    Wait(Generation),
    /// Every pipeline has finished.
    Done,
    /// The run failed ([`Dispatcher::fail`]): stop, whatever has not finished.
    Failed,
}

/// The count of the dispatcher's changes that can make a claim succeed, as a claim observed it.
#[cfg_attr(test, derive(Debug))]
pub struct Generation(u64);

/// Where a pipeline is. It is `Finishing` from the claim, or the
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

/// The work packages queued for one pipeline. Packages are appended while the queue
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
    /// Appends take it, and so does the move of the pipeline to finishing; a claim of a
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
    /// Whether it parks the rows pushes bring until the pipelines it reads have decided them
    /// ([`park`](Dispatcher::park)).
    parks: bool,
    /// Per pipeline it reads, in the order of its `reads`, the region of its input that
    /// pipeline's pushes reach, `None` where they reach all of it
    /// ([`reaches`](Dispatcher::reaches)).
    reach: Vec<Option<TileGuard>>,
    /// For a source, the most packages queued for it and not yet acknowledged that a notify finds
    /// before it queues more ([`limit`](Dispatcher::limit)); `usize::MAX` for none.
    limit: usize,
}

/// One pipeline's queue, progress, and record of pushed and decided regions.
struct PipelineState {
    queue: Queue,
    /// The index of the next package to claim. It never passes `queue.reserved`.
    claimed: AtomicUsize,
    phase: AtomicPhase,
    /// How many pipelines it reads have not finished. The last finish closes its queue.
    unfinished: AtomicUsize,
    /// The region this pipeline's breaker has pushed to its reader, which each push grows by
    /// what it pushes. A push of a breaker's final guard pushes what is not in it.
    // shared-state-ok: the region a pipeline has pushed, which its pushes read and grow under the
    // lock; what crosses it is a guard naming a region, never a tile.
    pushed: Mutex<Option<TileGuard>>,
    /// For a source, whether it is closed: no more of its input arrives.
    closed: AtomicBool,
    /// Per pipeline its breaker's input reads, in the order of its `reads`, what that pipeline
    /// has decided of the input ([`Decided`]).
    // shared-state-ok: guards naming regions of the pipeline's input, which the decided pushes
    // of the pipelines it reads grow under the lock; never a tile.
    decided: Mutex<Vec<Decided>>,
    /// For a pipeline that parks ([`Dispatcher::park`]), the rows pushes brought that the
    /// pipelines it reads have not decided yet.
    // shared-state-ok: guards naming regions of the pipeline's input, which the pushes and the
    // decided pushes that release them read and write under the lock; never a tile.
    parked: Mutex<Vec<TileGuard>>,
    /// For a pipeline that parks, every row a push has brought it, queued or parked,,
    /// `None` for none: two pushes can name one row, and the pipeline reads each row once
    /// ([`queue_or_park`](Dispatcher::queue_or_park)).
    // shared-state-ok: a guard naming a region of the pipeline's input, which the pushes to it grow
    // under the `parked` lock; never a tile.
    brought: Mutex<Option<TileGuard>>,
    /// How many of a source's packages have been queued.
    queued: AtomicUsize,
    /// How many of the pipeline's packages have been acknowledged,.
    acknowledged: AtomicUsize,
    /// For an ordered pipeline, whether a package of it is in flight,.
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

/// What a pipeline a reader reads has decided of the reader's breaker's input.
#[derive(Clone, Debug, Default)]
pub(crate) enum Decided {
    /// Nothing yet.
    #[default]
    Nothing,
    /// The region its decided pushes have named.
    Region(TileGuard),
    /// All of what it contributes: it is wholly decided.
    Whole,
}

impl Decided {
    fn grown(self, guard: &TileGuard) -> Decided {
        match self {
            Decided::Whole => Decided::Whole,
            Decided::Nothing => Decided::Region(guard.clone()),
            Decided::Region(region) => Decided::Region(region.union(guard)),
        }
    }
}

/// The graph of pipelines, the work packages queued for each pipeline, and what each has consumed.
pub struct Dispatcher {
    /// The most held rows a work package names.
    morsel_rows: usize,
    /// What each pipeline is, fixed before the dispatcher is shared.
    infos: Vec<PipelineInfo>,
    /// What each pipeline has done, which the workers change.
    states: Vec<PipelineState>,
    /// How many pipelines have not finished. The finish that brings it to zero ends the run.
    unfinished: AtomicUsize,
    /// Set once every pipeline has finished.
    done: AtomicBool,
    /// Set by [`Dispatcher::fail`], and by every refusal before it panics ([`Dispatcher::ensure`]).
    failed: AtomicBool,
    /// Advances at every change that can make a claim succeed or end the run: an append, a close,
    /// an acknowledgement that frees an ordered pipeline's next package, completes a queue or
    /// returns credit to a limited source, a finish, and a failure. It also advances when a claim
    /// of an ordered pipeline that found nothing finds a package queued while it looked, for a
    /// claim that found the pipeline's flag held meanwhile.
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
    /// reads. A work package names at most `morsel_rows` held rows.
    ///
    /// # Panics
    ///
    /// When `morsel_rows` is zero, when a pipeline reads one that does not exist or reads one
    /// pipeline twice, or when the graph has a cycle. Several pipelines may read one: a `FanOut`
    /// between them keeps the release of one from removing what another has still to read. A
    /// pipeline may read several, and its queue  closes at the finish of the last of
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
                parks: false,
                reach: Vec::new(),
                limit: usize::MAX,
            })
            .collect();
        let states = infos
            .iter()
            .map(|info| PipelineState {
                queue: Queue::new(),
                claimed: AtomicUsize::new(0),
                phase: AtomicPhase::new(Phase::Running),
                unfinished: AtomicUsize::new(info.reads.len()),
                pushed: Mutex::new(None),
                closed: AtomicBool::new(false),
                decided: Mutex::new(Vec::new()),
                parked: Mutex::new(Vec::new()),
                brought: Mutex::new(None),
                queued: AtomicUsize::new(0),
                acknowledged: AtomicUsize::new(0),
                in_flight: AtomicBool::new(false),
            })
            .collect();
        Self {
            morsel_rows,
            infos,
            states,
            unfinished: AtomicUsize::new(count),
            done: AtomicBool::new(false),
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

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// run, less what is queued for it there already: what a range brings that no push
    /// names ([`run_program`]).
    #[cfg(test)]
    pub(crate) fn queue_at_start(&self, reader: PipelineId, guard: &TileGuard) {
        if self.infos[reader.0].parks {
            self.queue_or_park(reader.0, guard);
            return;
        }
        assert!(
            self.states[reader.0].queue.append_unqueued(guard),
            "pipeline {} takes packages before the last pipeline it reads finishes",
            reader.0
        );
    }

    /// Mark `pipeline`, which reads a pipeline, as consuming its breaker's input whole, `input`
    /// cut one package per morsel ([`seed`]), once the pipelines it reads have finished, in place of what the
    /// pipelines it reads push. A planner does so where no push reaches the reader restated in its
    /// keys, where two pipelines it reads can push one key, or where a pipeline it reads takes no
    /// push and names no region the planner could queue for the reader at the start
    /// (`run_program`). Its
    /// input is whole once every pipeline it reads has finished, and it takes no push
    /// ([`Landing::queue`]).
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

    /// Mark `pipeline` as consuming its morsels one at a time in queue order. Its
    /// breaker's state advances through them in order, as a loop's store decides its positions
    /// ascending.
    pub fn order(&mut self, pipeline: PipelineId) {
        self.infos[pipeline.0].ordered = true;
    }

    /// Let a notify of the source `pipeline` queue more only while fewer than `packages` of its
    /// packages are queued and not acknowledged: [`notify`](Self::notify) waits
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

    /// Park the rows pushes bring `pipeline` until every pipeline it reads has decided them, and
    /// read each row once: a push brings the rows it names less what pushes brought before, and
    /// queues the part the pipelines it reads have decided ([`decided_part`](Self::decided_part)).
    /// Each decided push of a pipeline it reads releases the parked rows it decides into its queue
    /// (`src/interpreter/design-operators.md`, "Parking arrivals until a read is decided").
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline.
    pub fn park(&mut self, pipeline: PipelineId) {
        let p = pipeline.0;
        assert!(
            !self.infos[p].reads.is_empty(),
            "pipeline {p} parks its rows on the pipelines it reads"
        );
        self.infos[p].parks = true;
    }

    /// Record that the pushes of `read`, a pipeline `reader` reads, reach `region` of its input,
    /// and no more of it: a row outside `region` does not depend on `read`, so it waits for nothing
    /// of it ([`park`](Self::park)). A read with no such record reaches all of the input.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`.
    pub fn reaches(&mut self, reader: PipelineId, read: PipelineId, region: TileGuard) {
        let info = &mut self.infos[reader.0];
        let at = info
            .reads
            .iter()
            .position(|&r| r == read.0)
            .unwrap_or_else(|| panic!("pipeline {} reads pipeline {}", reader.0, read.0));
        if info.reach.len() < info.reads.len() {
            info.reach.resize(info.reads.len(), None);
        }
        info.reach[at] = Some(region);
    }

    /// The part of `guard`, a region of `reader`'s input, that every pipeline `reader` reads has
    /// decided: per read, the rows it reaches that it has decided, and the rows it does not reach
    /// ([`reaches`](Self::reaches)).
    fn decided_part(&self, reader: usize, guard: &TileGuard) -> TileGuard {
        let decided = self.states[reader]
            .decided
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let info = &self.infos[reader];
        (0..info.reads.len()).fold(guard.clone(), |part, at| {
            let reach = info.reach.get(at).cloned().flatten();
            match (decided.get(at).unwrap_or(&Decided::Nothing), reach) {
                (Decided::Whole, _) => part,
                (Decided::Region(region), Some(reach)) => {
                    part.intersect(region).union(&guard_minus(&part, &reach))
                }
                (Decided::Region(region), None) => part.intersect(region),
                (Decided::Nothing, Some(reach)) => guard_minus(&part, &reach),
                (Decided::Nothing, None) => guard_minus(&part, &part),
            }
        })
    }

    /// Queue `guard`, rows a push brings `reader`, which parks,  where every pipeline it
    /// reads has decided them, and park the rest ([`park`](Self::park)). Only what of `guard` no
    /// push brought before,, is new.
    fn queue_or_park(&self, reader: usize, guard: &TileGuard) {
        let mut parked = self.states[reader]
            .parked
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let fresh = {
            let mut brought = self.states[reader]
                .brought
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let fresh = match brought.as_ref() {
                Some(brought) => guard_minus(guard, brought),
                None => guard.clone(),
            };
            if fresh.is_empty() {
                return;
            }
            *brought = Some(match brought.take() {
                Some(before) => before.union(&fresh),
                None => fresh.clone(),
            });
            fresh
        };
        let decided = self.decided_part(reader, &fresh);
        let rest = guard_minus(&fresh, &decided);
        if !rest.is_empty() {
            parked.push(rest);
        }
        drop(parked);
        if decided.is_empty() {
            return;
        }
        let appended = self.states[reader].queue.append_unqueued(&decided);
        self.ensure(appended, || {
            format!(
                "pipeline {reader} receives packages before the last pipeline it reads finishes"
            )
        });
    }

    /// Append the part of what `reader` parked that the pipelines it reads have now decided to its
    /// queue , and keep the rest parked ([`park`](Self::park)). A decided push lands
    /// before the pushing pipeline counts its finish toward `reader`'s close, so `reader`'s queue
    ///  is open.
    fn release_parked(&self, reader: usize) {
        let released: Vec<TileGuard> = {
            let mut parked = self.states[reader]
                .parked
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let mut released = Vec::new();
            let mut kept = Vec::new();
            for morsel in std::mem::take(&mut *parked) {
                let part = self.decided_part(reader, &morsel);
                let rest = guard_minus(&morsel, &part);
                if !part.is_empty() {
                    released.push(part);
                }
                if !rest.is_empty() {
                    kept.push(rest);
                }
            }
            *parked = kept;
            released
        };
        let queue = &self.states[reader].queue;
        let appended = released.iter().all(|morsel| queue.append_unqueued(morsel));
        self.ensure(appended, || {
            format!("pipeline {reader} has not finished when a decided push covers what it parked")
        });
    }

    /// Grow what `source`, a pipeline `reader` reads, has decided of `reader`'s input by `guard`,
    /// or record it whole where `guard` is `None`, and release what `reader` parked that is now
    /// decided.
    fn record_decided(&self, reader: usize, source: usize, guard: Option<&TileGuard>) {
        let reads = &self.infos[reader].reads;
        let at = reads.iter().position(|&r| r == source);
        self.ensure(at.is_some(), || {
            format!(
                "pipeline {source} pushes a decided region to pipeline {reader}, which reads it"
            )
        });
        let at = at.expect("refused above");
        {
            let mut decided = self.states[reader]
                .decided
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if decided.len() < reads.len() {
                decided.resize(reads.len(), Decided::Nothing);
            }
            let before = std::mem::take(&mut decided[at]);
            decided[at] = match guard {
                Some(guard) => before.grown(guard),
                None => Decided::Whole,
            };
        }
        if self.infos[reader].parks {
            self.release_parked(reader);
        }
    }

    /// Push `decided`, the region of its keys `pipeline`'s breaker has decided, through `to`, the
    /// breaker's consumer, and record what reaches each reader's entry as decided by `pipeline`
    /// ([`decided_of`](Self::decided_of)). Where `decided` is every key, each reader the push
    /// reached no entry of reads `pipeline` by pull, which reads all of it: it records `pipeline`
    /// whole.
    fn land_decided(
        &self,
        pipeline: usize,
        decided: Option<&Projection>,
        to: Option<&SharedConsumer>,
    ) {
        let (Some(decided), Some(to)) = (decided, to) else {
            return;
        };
        if *decided == Projection::Nothing {
            return;
        }
        let whole = *decided == Projection::Everything;
        let mut landing = Landing {
            target: Target::Decided {
                dispatcher: self,
                whole,
                reached: Vec::new(),
            },
            from: pipeline,
            widened: false,
        };
        to.borrow_mut().push(decided, &mut landing);
        let Target::Decided { reached, .. } = landing.target else {
            unreachable!("a decided landing stays one");
        };
        if whole {
            for &reader in &self.infos[pipeline].readers {
                if !reached.contains(&reader) {
                    self.record_decided(reader, pipeline, None);
                }
            }
        }
    }

    /// What `source`, a pipeline `reader` reads, has decided of `reader`'s breaker's input.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `source`.
    #[cfg(test)]
    pub(crate) fn decided_of(&self, reader: PipelineId, source: PipelineId) -> Decided {
        let at = self.infos[reader.0]
            .reads
            .iter()
            .position(|&r| r == source.0)
            .unwrap_or_else(|| panic!("pipeline {} reads pipeline {}", reader.0, source.0));
        self.states[reader.0]
            .decided
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(at)
            .cloned()
            .unwrap_or_default()
    }

    /// The handle a breaker of `pipeline` pushes through. Its pushes land at
    /// [`land`](Self::land) or [`finish`](Self::finish).
    pub fn pushes(&self, pipeline: PipelineId) -> Pushes<'_> {
        self.state(pipeline);
        Pushes {
            to: None,
            dispatcher: self,
            pipeline: pipeline.0,
            morsels: Vec::new(),
            decided: None,
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

    /// The state of `pipeline`.
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

    /// Queue a source pipeline's input whole and close the source: `input`,
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

    /// Queue `guard`, a region of a source pipeline's input that has arrived, as
    /// one package per morsel: every `morsel_rows` positions, where `guard` names finite
    /// runs of positions (`Value::UInt` keys), and whole otherwise. Workers claim them as queued.
    ///
    /// A source [limited](Self::limit) to as many packages outstanding as it has waits until one
    /// is acknowledged, so the thread that notifies is held back by the workers. After a failure
    /// it returns at once, having queued nothing.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline or is closed; in a debug build, when `guard` meets a
    /// region queued for it before.
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

    /// Append `morsels` to the source `pipeline`'s queue.
    fn append_to_source(&self, pipeline: PipelineId, morsels: &[TileGuard]) {
        let p = pipeline.0;
        self.ensure_source(pipeline);
        let state = self.state(pipeline);
        // Count before publication, so an acknowledgement cannot run ahead of the count.
        state.queued.fetch_add(morsels.len(), Ordering::AcqRel);
        let appended = state.queue.append(p, morsels);
        self.ensure(appended, || {
            format!("pipeline {p} is queued nothing once it is closed")
        });
        self.advance();
    }

    /// Close a source pipeline: nothing more of its input arrives. Workers may finish it once
    /// every package has been acknowledged.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline or is closed already.
    pub fn close(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        self.ensure_source(pipeline);
        let state = self.state(pipeline);
        let closed = !state.closed.swap(true, Ordering::AcqRel);
        self.ensure(closed, || format!("pipeline {p} closes its queue once"));
        state.queue.close();
        self.advance();
    }

    /// The package at the front of `pipeline`'s queue, recorded as claimed, where a claim may take
    /// one. An ordered pipeline has at most one package in flight.
    fn claim_from(&self, pipeline: usize) -> Option<WorkPackage> {
        if !self.infos[pipeline].ordered {
            return self.claim_in(pipeline);
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
        let package = self.claim_in(pipeline);
        if package.is_none() {
            state.in_flight.store(false, Ordering::SeqCst);
            // A claim that found the flag held answered nothing for the pipeline, and may wait on
            // a generation that a package queued since this look began has reached. The flag's
            // operations and the generation's are sequentially consistent, so the generation read
            // after the release sees that package's advance and every write before it, and a
            // second look finds the package and wakes that claim.
            self.generation.load(Ordering::SeqCst);
            if self.claimable(pipeline) {
                self.advance();
            }
        }
        package
    }

    /// Whether the package at the front of `pipeline`'s queue is written and not claimed.
    fn claimable(&self, pipeline: usize) -> bool {
        let state = &self.states[pipeline];
        let index = state.claimed.load(Ordering::Acquire);
        index < state.queue.reserved() && state.queue.written(index).is_some()
    }

    /// The package at the front of `pipeline`'s queue, recorded as claimed, where it has one
    /// written.
    fn claim_in(&self, pipeline: usize) -> Option<WorkPackage> {
        let state = &self.states[pipeline];
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
                    index,
                });
            }
        }
    }

    /// Whether `pipeline` may finish: it is running, its queue is closed and every package in it
    /// acknowledged. Its queue closes once nothing more can be queued for it, so the finish is
    /// its last.
    fn ready(&self, pipeline: usize) -> bool {
        let state = &self.states[pipeline];
        // One read of the count and the close: nothing is reserved after the close, so the count
        // of a closed queue is its last.
        let reserved = state.queue.reserved.load(Ordering::Acquire);
        state.phase.load() == Phase::Running
            && reserved & CLOSED != 0
            && state.acknowledged.load(Ordering::Acquire) == reserved & !CLOSED
    }

    /// What to do next, without blocking. A claim takes the package at the front of `preferred`'s
    /// queue where it may, and otherwise of the lowest pipeline whose queue it may take from; an
    /// ordered pipeline is skipped while a package of it is in flight. With no package to claim,
    /// it moves the lowest pipeline that may finish to finishing and hands its finish out, so
    /// exactly one claim does so for each pipeline. Otherwise it answers [`Next::Done`] once every
    /// pipeline has finished, and [`Next::Wait`] before. After a failure it answers
    /// [`Next::Failed`].
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
        let mut scan = preferred.map(|p| p.0).into_iter().chain(0..count);
        if let Some(package) = scan.find_map(|p| self.claim_from(p)) {
            return Next::Package(package);
        }
        for p in 0..count {
            let begun =
                self.ready(p) && self.states[p].phase.moved(Phase::Running, Phase::Finishing);
            if begun {
                return Next::Finish {
                    pipeline: PipelineId(p),
                    consumed: self.states[p].queue.region(),
                };
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
    /// When `package` is not one a claim handed out for its pipeline and not yet acknowledged.
    pub fn acknowledge(&self, package: WorkPackage) {
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        let p = package.pipeline.0;
        let state = self.state(package.pipeline);
        let held = package.index < state.claimed.load(Ordering::Acquire)
            && state.queue.slot(package.index).is_some_and(|slot| {
                slot.guard.get() == Some(&package.guard)
                    && !slot.is_acknowledged.swap(true, Ordering::AcqRel)
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
        // Recorded before the count that lets the next package of an ordered pipeline, or the
        // pipeline's finish, be claimed.
        #[cfg(test)]
        self.record(Event::Consume {
            pipeline: package.pipeline,
            guard: package.guard,
        });
        let acknowledged = state.acknowledged.fetch_add(1, Ordering::AcqRel) + 1;
        if self.infos[p].ordered {
            state.in_flight.store(false, Ordering::Release);
        }
        // An acknowledgement frees an ordered pipeline's next package, may let the pipeline
        // finish or a pipeline that follows it claim, and returns credit to a limited source's
        // notify.
        if self.infos[p].ordered
            || self.infos[p].limit != usize::MAX
            || acknowledged == state.queue.reserved()
        {
            self.advance();
        }
    }

    /// Move `pipeline` to finishing, outside a claim, and answer what it consumed.
    ///
    /// # Panics
    ///
    /// When the pipeline has begun to finish already, a package queued for it has not been
    /// acknowledged, a pipeline it reads has not finished, or its queue is not closed.
    pub fn begin_finish(&self, pipeline: PipelineId) -> Option<TileGuard> {
        let p = pipeline.0;
        self.state(pipeline);
        let state = &self.states[p];
        self.ensure(state.phase.load() == Phase::Running, || {
            format!("pipeline {p} finishes once")
        });
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
                .all(|read| self.states[*read].phase.load() == Phase::Finished),
            || format!("pipeline {p} finishes after every pipeline it reads has finished"),
        );
        // A source's queue is closed by its close. A pipeline that reads others has its queue
        // filled and closed once the pushes of the pipeline it reads have landed, which
        // `finish` does after it marks that pipeline finished.
        self.ensure(state.queue.is_closed(), || {
            format!("pipeline {p} finishes after its queue is closed")
        });
        let begun = state.phase.moved(Phase::Running, Phase::Finishing);
        self.ensure(begun, || format!("pipeline {p} finishes once"));
        state.queue.region()
    }

    /// Land what `pushes` holds now, while the pipeline runs: each morsel climbs the breaker's
    /// consumer to the [`Entry`] of each pipeline that reads it, which queues it there, and the
    /// reader may claim the packages before the pipeline finishes. A breaker's push names only what
    /// it has decided ([`Pushes::push_final`]), so the reader's chain reads it final. After a
    /// failure it lands nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline has finished.
    pub fn land(&self, mut pushes: Pushes<'_>) {
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline lands its pushes through its own dispatcher"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        let decided = pushes.decided.take();
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        self.land_decided(p, decided.as_ref(), pushes.to.as_ref());
        if morsels.is_empty() {
            return;
        }
        self.ensure(self.states[p].phase.load() != Phase::Finished, || {
            format!("pipeline {p} lands its pushes before it finishes")
        });
        self.land_in(p, &morsels, pushes.to.as_ref());
        self.advance();
    }

    /// Push `morsels`, pushed by `pipeline`, through `to`, its breaker's consumer, one region of
    /// the breaker's keys per morsel, a projection at any level. Each reader's queue stays open
    /// until the last pipeline it reads finishes.
    fn land_in(&self, pipeline: usize, morsels: &[TileGuard], to: Option<&SharedConsumer>) {
        if morsels.is_empty() {
            return;
        }
        let mut landing = Landing {
            target: Target::Queue { dispatcher: self },
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

    /// Mark the pipeline `pushes` belongs to finished, land what it pushed, and close the queue of
    /// each pipeline that reads it, where every other pipeline that one reads has finished. A
    /// reader may claim the packages landed there before, and finish only once its queue is
    /// closed. The last finish ends the run. After a failure it records nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline is not finishing, which a second finish of it finds, or a reader has
    /// begun to finish.
    pub fn finish(&self, mut pushes: Pushes<'_>) {
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline finishes through its own dispatcher's pushes"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        let decided = pushes.decided.take();
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        let finished = self.states[p]
            .phase
            .moved(Phase::Finishing, Phase::Finished);
        self.ensure(finished, || {
            format!("pipeline {p} finishes once it has begun to finish")
        });
        // Recorded before the reader's queue is closed, which lets the reader finish.
        #[cfg(test)]
        self.record(Event::Finish(PipelineId(p)));
        self.land_in(p, &morsels, pushes.to.as_ref());
        self.land_decided(p, decided.as_ref(), pushes.to.as_ref());
        // Every pipeline it reads has finished and decided all of it, so nothing stays parked.
        {
            let parked = self.states[p]
                .parked
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            self.ensure(parked.is_empty(), || {
                format!(
                    "pipeline {p} finishes with rows parked that the \
                     pipelines it reads never decided: {parked:?}"
                )
            });
        }
        for &reader in &self.infos[p].readers {
            // The last of the pipelines it reads to finish closes the reader's queue;
            // the decrement orders every earlier finish's appends before it.
            let unfinished = self.states[reader]
                .unfinished
                .fetch_sub(1, Ordering::AcqRel);
            debug_assert!(
                unfinished > 0,
                "pipeline {reader} counts a finish once per pipeline it reads"
            );
            if unfinished != 1 {
                continue;
            }
            let queue = &self.states[reader].queue;
            let closing = match &self.infos[reader].whole {
                Some(input) => input,
                _ => &Vec::new(),
            };
            let closed = queue.append(reader, closing) && queue.close();
            self.ensure(closed, || {
                format!("pipeline {reader} receives packages once")
            });
        }
        if self.unfinished.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.done.store(true, Ordering::Release);
        }
        self.advance();
    }

    /// How many of `pipeline`'s packages are queued and not acknowledged.
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
        (0..self.infos.len()).find_map(|p| self.claim_from(p))
    }

    /// The package at the front of `pipeline`'s queue, claimed, where a claim may take one.
    #[cfg(test)]
    pub(crate) fn claim_of(&self, pipeline: PipelineId) -> Option<WorkPackage> {
        self.claim_from(pipeline.0)
    }

    /// Finish `pipeline` as a claim does, with `push` in place of the
    /// breaker: begin its finish, let `push` push, and mark it finished. A source
    /// pipeline is closed first, whatever was queued for it.
    #[cfg(test)]
    pub(crate) fn finish_by_hand(&self, pipeline: PipelineId, push: impl FnOnce(&mut Pushes<'_>)) {
        if self.infos[pipeline.0].reads.is_empty()
            && !self.state(pipeline).closed.load(Ordering::Acquire)
        {
            self.close(pipeline);
        }
        self.begin_finish(pipeline);
        let mut pushes = self.pushes(pipeline);
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

/// What a breaker pushes through: one morsel of its keys per work package. The dispatcher
/// [lands](Dispatcher::land) them, as the driver does after each consume, or
/// [finishes](Dispatcher::finish) the pipeline: each morsel climbs the breaker's consumer as a push
/// ([`Consumer::push`]), each operator on the way restates it in its own keys, and the [`Entry`] of
/// each breaker it reaches queues it for that breaker's pipeline.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    pipeline: usize,
    morsels: Vec<TileGuard>,
    /// The consumer the morsels climb, the pushing breaker's.
    to: Option<SharedConsumer>,
    /// The region of its keys the breaker has decided, pushed through `to` beside the morsels
    /// ([`Landing::is_decided`]); `None` where it pushed none.
    decided: Option<Projection>,
}

impl Pushes<'_> {
    /// Push what `breaker` has decided and the pipeline has not pushed before, its final guard
    /// less the region pushed, for the pipelines that read it: one package per morsel the breaker
    /// cuts it into, in the breaker's order. A push of nothing new pushes nothing, and so does a
    /// breaker no pipeline reads. The difference and the region's growth are one step under the
    /// region's lock, so two pushes of one pipeline from two threads push disjoint regions, and an
    /// finish pushes only what no earlier push named.
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
        // The decided region is the breaker's statement of it, released or not: a released key
        // stays decided. A region no projection spells is pushed as nothing decided, which
        // delays a reader and never misleads it.
        self.decided = decided_projection(
            breaker.decided().closed_over(breaker.tiling()),
            breaker.tiling(),
        );
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

/// Where a push lands: its target, which queues it or, in a planner's probe, records it; the
/// pipeline that pushed it; and whether an operator on the path it is climbing widened it.
pub struct Landing<'d> {
    target: Target<'d>,
    from: usize,
    widened: bool,
}

/// What a [`Landing`] does with the regions that reach an [`Entry`].
enum Target<'d> {
    /// Queues each in the reader's queue.
    Queue { dispatcher: &'d Dispatcher },
    /// Grows, for each, what the pushing pipeline has decided of the reader's input
    /// ([`Dispatcher::decided_of`]), and queues nothing. `whole` says the pushing pipeline is
    /// wholly decided, and `reached` lists the readers whose entry the push reached.
    Decided {
        dispatcher: &'d Dispatcher,
        whole: bool,
        reached: Vec<usize>,
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
            Target::Queue { .. } | Target::Decided { .. } => {
                panic!("a landing that queues or records decided regions records no arrivals")
            }
        }
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// run, less what is queued for it already: a push that reaches a breaker along two
    /// paths, as a filter reads one memo for its values and its predicate, is queued once. A
    /// reader that reads its input whole ([`Dispatcher::read_whole`]) takes no push, widened or
    /// not.
    ///
    /// # Panics
    ///
    /// When `reader` does not read the pipeline that pushed, or has begun to finish;
    /// when the push was widened on its way to a reader that reads its pushes; and where the
    /// guard algebra has no exact difference of `guard` and what is queued ([`guard_minus`]).
    pub fn queue(&mut self, reader: PipelineId, guard: &TileGuard) {
        let dispatcher = match &mut self.target {
            Target::Queue { dispatcher } => *dispatcher,
            Target::Decided {
                dispatcher,
                whole,
                reached,
            } => {
                reached.push(reader.0);
                // A wholly decided source is decided along whatever its push was restated to on
                // the way, as an arm of a union restates it under its tag.
                let guard = (!(*whole || guard.is_universal())).then_some(guard);
                return dispatcher.record_decided(reader.0, self.from, guard);
            }
            #[cfg(test)]
            Target::Probe(arrivals) => {
                arrivals.push(Arrival {
                    pipeline: reader,
                    guard: guard.clone(),
                });
                return;
            }
        };
        let (from, r) = (self.from, reader.0);
        dispatcher.state(reader);
        dispatcher.ensure(dispatcher.infos[r].reads.contains(&from), || {
            format!("pipeline {from} pushes to pipeline {r}, which reads it")
        });
        if dispatcher.infos[r].whole.is_some() {
            return;
        }
        let queue = &dispatcher.states[r];
        dispatcher.ensure(queue.phase.load() == Phase::Running, || {
            format!("pipeline {r} receives packages before it finishes")
        });
        // A reader that parks reads each row once, when every pipeline it reads has decided it: a
        // push brings the rows it names, widened or not, less what a push brought before, and the
        // decided pushes release them ([`Dispatcher::park`]).
        if dispatcher.infos[r].parks {
            dispatcher.queue_or_park(r, guard);
            return;
        }
        dispatcher.ensure(!self.widened, || {
            format!(
                "a push of pipeline {from} is widened to `Everything` on its way to pipeline {r}, \
                 which neither parks nor reads that pipeline once it has finished"
            )
        });
        dispatcher.ensure(queue.queue.append_unqueued(guard), || {
            format!("pipeline {r} receives packages before the last pipeline it reads finishes")
        });
    }

    /// Whether the region climbing is a decided region rather than a change: an operator restates
    /// a decided region by keeping what it names where it keeps the keys, and where it widens them
    /// by naming nothing until the region is every key, since each of its keys depends on every
    /// key of its input.
    pub fn is_decided(&self) -> bool {
        matches!(self.target, Target::Decided { .. })
    }

    /// Whether the region climbing is a decided region of a source that is wholly decided: an
    /// operator that widens its input's keys passes it as every key, since what that source
    /// contributes to each of the operator's keys is decided, and the reader intersects what its
    /// other sources decided.
    pub fn is_wholly_decided(&self) -> bool {
        matches!(self.target, Target::Decided { whole: true, .. })
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
            Target::Queue { dispatcher, .. } | Target::Decided { dispatcher, .. } => {
                dispatcher.ensure(false, || message)
            }
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
/// `held`, a breaker's decided region of its output `tiling`, as a projection: every key where it
/// names every position of the finite range of positions the output's outermost keys range over,
/// as a store or an aggregate under a loop of positions `0..n` states the positions it decided,
/// which `TileGuard::closed_over` leaves as they are. `None` where no projection spells it.
fn decided_projection(held: TileGuard, tiling: &Tiling) -> Option<Projection> {
    if let (
        Some(Extent::UIntRange(positions)),
        TileGuard::Function(FunctionGuard::Domain(region @ Predicate::Intervals(_))),
    ) = (tiling.domain_extent(), &held)
    {
        let covered = positions.intervals().iter().all(|run| {
            let (Some(first), Some(last)) = (run.left(), run.right()) else {
                return false;
            };
            let first = *first.value() + u64::from(!first.is_closed());
            let Some(last) = last.value().checked_sub(u64::from(!last.is_closed())) else {
                return true;
            };
            if first > last {
                return true;
            }
            let through = Predicate::at_or_below(Value::UInt(last));
            let run = match first.checked_sub(1) {
                Some(before) => through.minus(&Predicate::at_or_below(Value::UInt(before))),
                None => through,
            };
            region.subsumes(&run)
        });
        if covered {
            return Some(Projection::Everything);
        }
    }
    Projection::of(&held).ok()
}

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
/// closed. The driver consumes the package of the lowest pipeline that
/// has one; when no pipeline has one, it finishes the lowest pipeline that may finish. It stops
/// when every pipeline has finished. Every breaker takes its consuming mode before the first
/// package, as in a compiled program's run.
///
/// # Panics
///
/// When a pipeline cannot finish though nothing is queued, which an acyclic graph rules out; in a
/// debug build, when a package's guard is not a guard of the tiling its breaker's input answers,
/// when a pipeline consumes a region it consumed before, or when a breaker's morsels do not
/// partition its final guard; and at any of the invariants [`finish_pipeline`] asserts.
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
            Next::Finish { pipeline, consumed } => {
                finish_with(dispatcher, reach, pipeline, consumed)
            }
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
/// before the acknowledgement, which may let the pipeline finish.
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
            let mut pushes = dispatcher.pushes(package.pipeline);
            pushes.push_final(producer);
            landed = Some(pushes);
        }
    });
    if let Some(pushes) = landed {
        dispatcher.land(pushes);
    }
    dispatcher.acknowledge(package);
}

/// Finish `pipeline` after checking that its queue is closed, every package is acknowledged,
/// every pipeline it reads has finished, and its input released every guard it consumed.
/// Where no exact guard difference is representable, `guard_minus` panics.
pub fn finish_pipeline(dispatcher: &Dispatcher, breakers: &[BreakerHandle], pipeline: PipelineId) {
    let consumed = dispatcher.begin_finish(pipeline);
    finish_with(dispatcher, &mut handles(breakers), pipeline, consumed);
}

/// Finish `pipeline`, which has begun after consuming `consumed`: push what it
/// decided and no consume pushed, through the breaker's [`finish`][Breaker::finish], then mark it
/// finished.
///
/// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
fn finish_with(
    dispatcher: &Dispatcher,
    reach: &mut Reach<'_>,
    pipeline: PipelineId,
    consumed: Option<TileGuard>,
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
        let mut pushes = dispatcher.pushes(pipeline);
        breaker.finish(&mut pushes);
        finished = Some(pushes);
    });
    dispatcher.finish(finished.expect("a reach calls the breaker it reaches"));
}

/// Run a compiled program's pipelines through a dispatcher of `morsel_rows` on the calling
/// thread. `sinks` pairs each sink's consumer with the sink it writes to. The breakers are the
/// producers in the chains under the sinks' producers that are pipeline breakers
/// (`TileProducer::as_breaking_mut`), and each sink's own ([`SinkBreaker`]), whose pipeline no
/// pipeline reads. A breaker's pipeline reads the pipelines of the nearest breakers beneath it,
/// and the [`Entry`] at the breaker's input, or the sink's consumer, is placed in the pipeline. A
/// pipeline pulls only its breaker's input, and a sink's pipeline pulls the sink's producer, so a
/// sink receives its producer's answer one package at a time. A sink is done once its producer is
/// released whole, which the run leaves to its caller to read. It answers what it planned for
/// each pipeline, in pipeline order.
///
/// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
///
/// Each edge to a pipeline that reads another is probed before the run: the read pipeline's
/// breaker pushes `Everything` through its consumer, as a push in the run would climb it, and the
/// planner records what reaches the reader's entry as the region that pipeline reaches
/// ([`Landing::probe`], [`Dispatcher::reaches`]). A reader that a pipeline it reads reaches at no
/// entry, or that nothing brings a row, reads its input whole once every pipeline it reads has
/// finished ([`Dispatcher::read_whole`]). Every other reader parks the rows its pushes bring until
/// the pipelines it reads have decided them ([`Dispatcher::park`]). Each range under a reader of
/// pushes (an `IterateExtent`), such as a literal's positions, the one producer with no input that
/// keeps its consumer (`ProducerBase::leaf`), is probed too. What the ranges bring that no push can
/// name is queued for the reader at the start of the run as one region, parked as a push's rows
/// are.
///
/// # Panics
///
/// When a producer in the chains reads one of `stores`, or a pipeline reads directly a pipeline
/// that another pipeline reads; and where [`run`] panics.
#[cfg(test)]
pub(crate) fn run_program(
    sinks: &[SinkTarget],
    stores: &[Rc<crate::interpreter::tile_operators::FanOut>],
    morsel_rows: usize,
) -> Vec<Planned> {
    let mut planner = Planner {
        stores,
        reads: Vec::new(),
        located: Vec::new(),
        names: Vec::new(),
        leaves: Vec::new(),
        direct: Vec::new(),
    };
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
        let pipeline = planner.located.len();
        consumer
            .borrow_mut()
            .place(PipelineId(pipeline), breaker.input_tiling(InputId::ONLY));
        planner.located.push(Located::Sink(at));
        planner.names.push(format!("SinkBreaker#{at}"));
        planner.place(pipeline, under);
        sink_breakers.push(RefCell::new(breaker));
    }
    let Planner {
        reads,
        located,
        names,
        leaves,
        direct,
        ..
    } = planner;
    for &(read, reader) in &direct {
        let readers = reads.iter().filter(|reads| reads.contains(&read)).count();
        assert!(
            readers == 1,
            "{} reads {} directly, which another pipeline reads too; only a fan-out slot keeps \
             one reader's release from removing what another still reads",
            names[reader],
            names[read]
        );
    }
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| match located[pipeline.0] {
        Located::Sink(sink) => call(&mut *sink_breakers[sink].borrow_mut()),
        Located::Chain(id) => {
            let mut call = Some(call);
            for root in &roots {
                let mut root = root.borrow_mut();
                let producer = root.as_mut().expect("a root holds the producer it pulls");
                if reach_in_chain(&mut **producer, id, &mut call) {
                    return;
                }
            }
            panic!("pipeline {} has its breaker in a root's chain", pipeline.0)
        }
    };
    let mut dispatcher = Dispatcher::new(reads.clone(), morsel_rows);
    let mut planned: Vec<Planned> = names
        .iter()
        .map(|name| Planned {
            name: name.clone(),
            whole: false,
            started: false,
            held: false,
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
        // What the pushes of the pipelines it reads name of its input, `None` before any.
        let mut pushed: Option<TileGuard> = None;
        // Whether a pipeline it reads pushes nothing that reaches it, so it reads that one by pull.
        let mut unreached = false;
        for &read in read {
            let (pusher, _) = pushing_end(&mut reach, PipelineId(read));
            let named = probe(&pusher, PipelineId(read), &Projection::Everything, reader);
            if named.is_empty() {
                unreached = true;
                continue;
            }
            let named = named
                .into_iter()
                .fold(input.empty_guard(), |names, arrival| {
                    names.union(&arrival.guard)
                });
            // A row outside what a push of every key lands as depends on nothing of `read`, so
            // it waits for nothing of it.
            dispatcher.reaches(PipelineId(reader), PipelineId(read), named.clone());
            pushed = Some(match pushed {
                Some(before) => before.union(&named),
                None => named,
            });
        }
        // What the ranges beneath it bring that no push names, which the run queues it at the
        // start.
        let left = leaves[reader]
            .iter()
            .flat_map(|leaf| probe(leaf, PipelineId(read[0]), &Projection::Everything, reader))
            .fold(input.empty_guard(), |left, arrival| {
                left.union(&match &pushed {
                    Some(pushed) => guard_minus(&arrival.guard, pushed),
                    None => arrival.guard,
                })
            });
        // A reader parks the rows its pushes and its start bring until the pipelines it reads
        // have decided them, and reads each row once ([`Dispatcher::park`]). It reads its input
        // whole where a pipeline it reads reaches it by pull, or where nothing brings it a row.
        if unreached || (pushed.is_none() && left.is_empty()) {
            dispatcher.read_whole(PipelineId(reader), &input);
            planned[reader].whole = true;
            continue;
        }
        dispatcher.park(PipelineId(reader));
        planned[reader].held = true;
        if !left.is_empty() {
            planned[reader].started = true;
            starts.push((PipelineId(reader), left));
        }
    }
    for (reader, guard) in &starts {
        dispatcher.queue_at_start(*reader, guard);
    }
    // The run drives every breaker it planned, so each takes its consuming mode here, before any
    // package, and keeps it for the run.
    for pipeline in 0..names.len() {
        reach(PipelineId(pipeline), &mut |breaker| {
            breaker.enter_consuming_mode()
        });
    }
    drive(&dispatcher, &mut reach);
    planned
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
    /// Whether the run queued it a region at the start: what the ranges under it (`IterateExtent`)
    /// bring, less what the pushes of the pipelines it reads name.
    pub(crate) started: bool,
    /// Whether it parks the rows pushes bring until the pipelines it reads have decided them
    /// ([`Dispatcher::park`]).
    pub(crate) held: bool,
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
    /// In a sink's producer chain, by its address ([`address`]).
    Chain(usize),
    /// The breaker of the sink of this index in `sinks` ([`SinkBreaker`]).
    ///
    /// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
    Sink(usize),
}

/// The pipelines [`run_program`] reads off a program's producer chains.
#[cfg(test)]
struct Planner<'p> {
    stores: &'p [Rc<crate::interpreter::tile_operators::FanOut>],
    reads: Vec<Vec<usize>>,
    located: Vec<Located>,
    names: Vec<String>,
    /// Per pipeline, the consumers of the ranges in its chain (`ProducerBase::leaf`), above
    /// every breaker beneath it.
    leaves: Vec<Vec<SharedConsumer>>,
    /// The edges `(read, reader)` whose reader's breaker reads the breaker of `read` directly.
    direct: Vec<(usize, usize)>,
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
impl Planner<'_> {
    /// What the chain at `producer` holds up to the nearest breakers, planning each breaker
    /// reached; a pipeline is numbered after the pipelines it reads, and a breaker a second
    /// reader reaches keeps its pipeline.
    fn pipelines_under(
        &mut self,
        producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
        role: &str,
    ) -> Beneath {
        assert!(
            store_of(producer, self.stores).is_none(),
            "{} reads a store, and a store is no pipeline breaker, so no pipeline runs it",
            producer.name()
        );
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
            for (pipeline, direct) in under.pipelines {
                if !below.pipelines.iter().any(|(seen, _)| *seen == pipeline) {
                    below.pipelines.push((pipeline, direct));
                }
            }
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
        let Some(breaker) = producer.as_breaking_mut() else {
            below.leaves.extend(leaf);
            for (_, direct) in &mut below.pipelines {
                *direct = false;
            }
            return below;
        };
        let pipeline = self.located.len();
        placement
            .unwrap_or_else(|| panic!("{} is placed in a pipeline by its entry", breaker.name()))
            .set(Some(PipelineId(pipeline)));
        self.located.push(Located::Chain(id));
        self.names.push(breaker.name());
        self.place(pipeline, below);
        Beneath {
            pipelines: vec![(pipeline, true)],
            ..Beneath::default()
        }
    }

    /// Record that `pipeline`, the last one located, reads what `below` holds.
    fn place(&mut self, pipeline: usize, below: Beneath) {
        debug_assert_eq!(
            pipeline + 1,
            self.located.len(),
            "a pipeline reads the pipelines beneath it once it is located, and before any other is"
        );
        // A source reads its input whole, so it consumes whatever keys a constant brings. A
        // reader of pushes takes only what the pushes and the ranges' probes name.
        debug_assert!(
            below.pipelines.is_empty() || below.unprobed.is_empty(),
            "{} reads pushes, and {:?} beneath it bring keys no push or probe names: a constant \
             collection beneath a reader of pushes is a function operand",
            self.names[pipeline],
            below.unprobed
        );
        for &(read, direct) in &below.pipelines {
            if direct {
                self.direct.push((read, pipeline));
            }
        }
        self.reads
            .push(below.pipelines.iter().map(|(read, _)| *read).collect());
        self.leaves.push(below.leaves);
    }
}

/// A producer's identity in its chain: the address of its boxed state, which does not move while
/// the chain stands. `TileProducer::producer_id` counts per producer type, so two producers of
/// different types share one.
#[cfg(test)]
fn address(producer: &dyn crate::interpreter::tile_operators::TileProducer) -> usize {
    std::ptr::from_ref(producer).cast::<()>() as usize
}

/// The index in `stores` of the fan-out `producer` is a slot of, where it is one: a slot lists
/// its fan-out's input as `"input"`, here the store, built by the operator the fan-out wraps.
#[cfg(test)]
fn store_of(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    stores: &[Rc<crate::interpreter::tile_operators::FanOut>],
) -> Option<usize> {
    let mut store = None;
    producer.visit_input_producers(&mut |name, input| {
        if name == "input" {
            store = input.operator_id();
        }
    });
    let store = store?;
    stores
        .iter()
        .position(|fan| fan.with_input(|operator| operator.operator_id()) == Some(store))
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

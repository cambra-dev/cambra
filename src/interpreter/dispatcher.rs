//! A dispatcher of work packages between the pipelines of a program, shared by the threads that
//! claim them.
//!
//! A pipeline is a [`Breaker`] and the chain it owns; the breaker of a pipeline that
//! another reads is a [`BreakingProducer`]. The dispatcher holds the graph of pipelines and a queue
//! of work packages per pipeline, each package one morsel. A cut targets `morsel_rows` held rows
//! where the shape supports cutting, and a shape that does not is one morsel. Each pipeline
//! finishes once, after its queue closes and every package is acknowledged. A per-pipeline lock
//! protects ready and in-flight packages; acknowledgement removes an in-flight entry. Operator
//! execution holds no queue lock. A worker sleeps while there is nothing to claim, and a change
//! that can end a sleep wakes the sleepers. The dispatcher holds no breaker, so it is `Sync` while
//! the breakers are not `Send`. The single-threaded driver, [`run`], reaches the breakers through
//! the handles its caller passes, indexed by pipeline. Nothing outside unit tests calls it, and
//! only unit tests drive the dispatcher from several threads. See
//! `src/interpreter/design-dispatcher.md`, "The dispatcher".

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
#[cfg(test)]
use std::sync::Arc;
#[cfg(test)]
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, PoisonError};
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
    /// The package's index in its pipeline, never reused within a run.
    pub(crate) index: usize,
}

/// What a worker does next, as [`Dispatcher::try_claim`] answers.
#[cfg_attr(test, derive(Debug))]
pub enum Next {
    /// Hand the package to its pipeline's breaker, then [`acknowledge`](Dispatcher::acknowledge)
    /// it.
    Package(WorkPackage),
    /// Finish the pipeline, which the claim moved to finishing, then
    /// [`finish`](Dispatcher::finish) it: push what it completed and no consume pushed, through the
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

/// The bit of a queue's `reserved` count that says the queue is closed.
const CLOSED: usize = 1 << (usize::BITS - 1);

/// Unclaimed and in-flight packages of one pipeline. Acknowledged packages retain no entry.
struct Queue {
    // shared-state-ok: package lifecycle and guards naming input regions; never tiles.
    state: Mutex<QueueState>,
    /// Reservations include packages whose append still holds the queue lock. Closing freezes
    /// the count, so a finish compares acknowledgements against that count without taking a lock.
    reserved: AtomicUsize,
}

#[derive(Default)]
struct QueueState {
    /// External arrivals have ended; upstream pipelines may still append work.
    arrivals_closed: bool,
    ready: VecDeque<(usize, TileGuard)>,
    in_flight: HashMap<usize, TileGuard>,
    /// Deduplication and finish need the consumed region after individual packages are removed.
    region: Option<TileGuard>,
    /// Admission and waiting-to-ready transfers share the queue lock.
    waiting_for_inputs: Vec<TileGuard>,
    /// Union of guards currently waiting for input completion.
    waiting_region: Option<TileGuard>,
}

impl QueueState {
    fn wait_for_inputs(&mut self, morsel: TileGuard) {
        grow(&mut self.waiting_region, &morsel);
        self.waiting_for_inputs.push(morsel);
    }
}

impl Queue {
    fn append(&self, pipeline: usize, morsels: &[TileGuard]) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.append_locked(&mut state, pipeline, morsels)
    }

    fn new() -> Self {
        Queue {
            state: Mutex::new(QueueState::default()),
            reserved: AtomicUsize::new(0),
        }
    }

    /// Append morsels partitioning a region no earlier append named. A closed queue takes nothing.
    /// Everything that can panic runs before the reservation, so a panic leaves no index reserved
    /// that no package fills.
    ///
    /// # Panics
    ///
    /// In a debug build, when a morsel meets the region appended before.
    fn append_locked(
        &self,
        state: &mut QueueState,
        pipeline: usize,
        morsels: &[TileGuard],
    ) -> bool {
        let mut region: Option<TileGuard> = None;
        for morsel in morsels {
            let before = region.as_ref().or(state.region.as_ref());
            debug_assert!(
                before.is_none_or(|region| region.intersect(morsel).is_empty()),
                "pipeline {pipeline} consumes each region once: {morsel:?} meets {before:?}"
            );
            region = Some(grown(before, morsel));
        }
        let Some(first) = self.reserve(morsels.len()) else {
            return false;
        };
        if region.is_some() {
            state.region = region;
        }
        state.ready.extend((first..).zip(morsels.iter().cloned()));
        true
    }

    /// Append the region not already queued, atomically with recording it for deduplication.
    ///
    /// # Panics
    ///
    /// Where the guard algebra has no exact difference of `guard` and the region ([`guard_minus`]).
    fn append_unqueued(&self, guard: &TileGuard) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.append_unqueued_locked(&mut state, guard)
    }

    fn append_unqueued_locked(&self, state: &mut QueueState, guard: &TileGuard) -> bool {
        let fresh = match state.region.as_ref() {
            Some(region) => guard_minus(guard, region),
            None => guard.clone(),
        };
        if fresh.is_empty() {
            return !self.is_closed();
        }
        // The union can panic, so it runs before the reservation.
        let region = grown(state.region.as_ref(), &fresh);
        let Some(index) = self.reserve(1) else {
            return false;
        };
        state.region = Some(region);
        state.ready.push_back((index, fresh));
        true
    }

    /// Move the oldest ready package to in-flight while its dependencies permit the claim.
    fn claim(
        &self,
        pipeline: usize,
        ordered: bool,
        can_claim: impl FnOnce() -> bool,
    ) -> Option<WorkPackage> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        // An append publishes prerequisite work before queuing this package. Inspect dependencies
        // after observing it under the lock; the check reads counters and takes no queue lock.
        if state.ready.is_empty() || (ordered && !state.in_flight.is_empty()) || !can_claim() {
            return None;
        }
        let (index, guard) = state.ready.pop_front()?;
        state.in_flight.insert(index, guard.clone());
        Some(WorkPackage {
            pipeline: PipelineId(pipeline),
            guard,
            index,
        })
    }

    /// Remove a matching claim. Monotonic indices distinguish repeated reads of the same guard.
    fn acknowledge(&self, package: &WorkPackage, on_ack: impl FnOnce()) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if state.in_flight.get(&package.index) != Some(&package.guard) {
            return false;
        }
        on_ack();
        state.in_flight.remove(&package.index);
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

    /// The union of every appended region, including acknowledged packages.
    fn region(&self) -> Option<TileGuard> {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .region
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
    /// Whether it holds the rows pushes bring until the pipelines it reads have completed them
    /// ([`wait_for_inputs`](Dispatcher::wait_for_inputs)).
    waits_for_inputs: bool,
    /// Per pipeline it reads, in the order of its `reads`, the region of its input that
    /// pipeline's pushes reach, `None` where they reach all of it
    /// ([`reaches`](Dispatcher::reaches)).
    reach: Vec<Option<TileGuard>>,
    /// For a source, the most packages queued for it and not yet acknowledged that a notify finds
    /// before it queues more ([`limit`](Dispatcher::limit)); `usize::MAX` for none.
    limit: usize,
}

/// One pipeline's queue, progress, and record of pushed and completed regions.
struct PipelineState {
    queue: Queue,
    phase: AtomicPhase,
    /// How many pipelines it reads have not finished. The last finish closes its queue.
    unfinished: AtomicUsize,
    /// The region this pipeline's breaker has pushed to its reader, which each push grows by
    /// what it pushes. A push of a breaker's final guard pushes what is not in it.
    // shared-state-ok: the region a pipeline has pushed, which its pushes read and grow under the
    // lock; what crosses it is a guard naming a region, never a tile.
    pushed: Mutex<Option<TileGuard>>,
    /// Per pipeline its breaker's input reads, in the order of its `reads`, what that pipeline
    /// has completed of the input ([`Completion`]).
    // shared-state-ok: guards naming regions of the pipeline's input, which the completed pushes
    // of the pipelines it reads grow under the lock; never a tile.
    complete: Mutex<Vec<Completion>>,
    /// How many of the pipeline's packages have been acknowledged.
    acknowledged: AtomicUsize,
}

impl PipelineState {
    /// Reservations include every claimable package. Read acknowledgements first so the
    /// subsequent reservation count cannot fall behind them.
    fn outstanding(&self) -> usize {
        let acknowledged = self.acknowledged.load(Ordering::Acquire);
        self.queue.reserved() - acknowledged
    }
}

/// What a pipeline a reader reads has completed of the reader's breaker's input.
#[derive(Clone, Default)]
#[cfg_attr(test, derive(Debug))]
pub(crate) enum Completion {
    /// Nothing yet.
    #[default]
    Nothing,
    /// The region its completed pushes have named.
    Region(TileGuard),
    /// All of what it contributes: it is wholly completed.
    Whole,
}

impl Completion {
    fn grown(self, guard: &TileGuard) -> Completion {
        match self {
            Completion::Whole => Completion::Whole,
            Completion::Nothing => Completion::Region(guard.clone()),
            Completion::Region(region) => Completion::Region(region.union(guard)),
        }
    }
}

#[cfg(test)]
type TransitionHook = Box<dyn FnOnce() + Send>;

/// The graph of pipelines, the work packages queued for each pipeline, and what each has consumed.
pub struct Dispatcher {
    /// The held rows a cut of a work package targets, where its shape supports cutting.
    morsel_rows: usize,
    /// What each pipeline is, fixed before the dispatcher is shared.
    infos: Vec<PipelineInfo>,
    /// What each pipeline has done, which the workers change.
    states: Vec<PipelineState>,
    /// How many pipelines have not finished. The finish that brings it to zero ends the run.
    unfinished: AtomicUsize,
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
    #[cfg(test)]
    transition_hooks: [OnceLock<Mutex<Option<TransitionHook>>>; 2],
}

impl Dispatcher {
    #[cfg(test)]
    fn run_transition_hook(&self, finishing: bool) {
        let Some(hook) = self.transition_hooks[usize::from(finishing)].get() else {
            return;
        };
        let hook = hook.lock().unwrap_or_else(PoisonError::into_inner).take();
        if let Some(hook) = hook {
            hook();
        }
    }

    /// The dispatcher of the pipelines `reads` describes: `reads[p]` lists the pipelines `p`
    /// reads. A cut of a work package targets `morsel_rows` held rows where the shape supports
    /// cutting, and leaves any other shape whole.
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
                waits_for_inputs: false,
                reach: Vec::new(),
                limit: usize::MAX,
            })
            .collect();
        let states = infos
            .iter()
            .map(|info| PipelineState {
                queue: Queue::new(),

                phase: AtomicPhase::new(Phase::Running),
                unfinished: AtomicUsize::new(info.reads.len()),
                pushed: Mutex::new(None),

                complete: Mutex::new(Vec::new()),
                acknowledged: AtomicUsize::new(0),
            })
            .collect();
        Self {
            morsel_rows,
            infos,
            states,
            unfinished: AtomicUsize::new(count),
            failed: AtomicBool::new(false),
            generation: AtomicU64::new(0),
            sleepers: AtomicUsize::new(0),
            sleep: Mutex::new(()),
            wake: Condvar::new(),
            #[cfg(test)]
            events: Mutex::new(Vec::new()),
            #[cfg(test)]
            recording: true,
            #[cfg(test)]
            transition_hooks: std::array::from_fn(|_| OnceLock::new()),
        }
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// run, less what is queued for it there already: what a range brings that no push
    /// names ([`run_program`]).
    #[cfg(test)]
    pub(crate) fn queue_at_start(&self, reader: PipelineId, guard: &TileGuard) {
        if self.infos[reader.0].waits_for_inputs {
            self.queue_or_wait_for_inputs(reader.0, guard);
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
    /// breaker's state advances through them in order, as a loop's store completes its positions
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

    /// Park the rows pushes bring `pipeline` until every pipeline it reads has completed them, and
    /// read each row once: a push brings the rows it names less what pushes brought before, and
    /// queues the part the pipelines it reads have completed ([`complete_part`](Self::complete_part)).
    /// Each completed push of a pipeline it reads releases the held rows it completes into its queue
    /// (`src/interpreter/design-dispatcher.md`, "Waiting for input completion").
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline.
    pub fn wait_for_inputs(&mut self, pipeline: PipelineId) {
        let p = pipeline.0;
        assert!(
            !self.infos[p].reads.is_empty(),
            "pipeline {p} waits_for_inputs its rows on the pipelines it reads"
        );
        self.infos[p].waits_for_inputs = true;
    }

    /// Record that the pushes of `read`, a pipeline `reader` reads, reach `region` of its input,
    /// and no more of it: a row outside `region` does not depend on `read`, so it waits for nothing
    /// of it ([`wait_for_inputs`](Self::wait_for_inputs)). A read with no such record reaches all of the input.
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
    /// completed: per read, the rows it reaches that it has completed, and the rows it does not reach
    /// ([`reaches`](Self::reaches)).
    fn complete_part(&self, reader: usize, guard: &TileGuard) -> TileGuard {
        let complete = self.states[reader]
            .complete
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let info = &self.infos[reader];
        (0..info.reads.len()).fold(guard.clone(), |part, at| {
            let reach = info.reach.get(at).cloned().flatten();
            match (complete.get(at).unwrap_or(&Completion::Nothing), reach) {
                (Completion::Whole, _) => part,
                (Completion::Region(region), Some(reach)) => {
                    part.intersect(region).union(&guard_minus(&part, &reach))
                }
                (Completion::Region(region), None) => part.intersect(region),
                (Completion::Nothing, Some(reach)) => guard_minus(&part, &reach),
                (Completion::Nothing, None) => guard_minus(&part, &part),
            }
        })
    }

    /// Queue `guard`, rows a push brings `reader`, which waits for input completion,  where every pipeline it
    /// reads has completed them, and hold the rest ([`wait_for_inputs`](Self::wait_for_inputs)). Only what of `guard` no
    /// push brought before,, is new.
    fn queue_or_wait_for_inputs(&self, reader: usize, guard: &TileGuard) {
        let queue = &self.states[reader].queue;
        let mut state = queue.state.lock().unwrap_or_else(PoisonError::into_inner);
        let mut fresh = match &state.region {
            Some(queued) => guard_minus(guard, queued),
            None => guard.clone(),
        };
        if let Some(waiting) = &state.waiting_region {
            fresh = guard_minus(&fresh, waiting);
        }
        if fresh.is_empty() {
            return;
        }
        let complete = self.complete_part(reader, &fresh);
        let rest = guard_minus(&fresh, &complete);
        if !rest.is_empty() {
            state.wait_for_inputs(rest);
        }
        if complete.is_empty() {
            return;
        }
        let appended = queue.append_unqueued_locked(&mut state, &complete);
        self.ensure(appended, || {
            format!(
                "pipeline {reader} receives packages before the last pipeline it reads finishes"
            )
        });
    }
    /// Append the part of what `reader` held that the pipelines it reads have now completed to its
    /// queue , and keep the rest held ([`wait_for_inputs`](Self::wait_for_inputs)). A completed push lands
    /// before the pushing pipeline counts its finish toward `reader`'s close, so `reader`'s queue
    ///  is open.
    fn queue_ready_inputs(&self, reader: usize) {
        let queue = &self.states[reader].queue;
        let mut state = queue.state.lock().unwrap_or_else(PoisonError::into_inner);
        let mut released = Vec::new();
        let mut kept = Vec::new();
        for morsel in std::mem::take(&mut state.waiting_for_inputs) {
            let part = self.complete_part(reader, &morsel);
            let rest = guard_minus(&morsel, &part);
            if !part.is_empty() {
                released.push(part);
            }
            if !rest.is_empty() {
                kept.push(rest);
            }
        }
        state.waiting_region = None;
        for guard in kept {
            state.wait_for_inputs(guard);
        }
        if released.is_empty() {
            return;
        }
        let appended = released
            .iter()
            .all(|guard| queue.append_unqueued_locked(&mut state, guard));
        self.ensure(appended, || {
            format!(
                "pipeline {reader} has not finished when a complete push covers its waiting inputs"
            )
        });
        self.advance();
    }
    /// Grow what `source`, a pipeline `reader` reads, has completed of `reader`'s input by `guard`,
    /// or record it whole where `guard` is `None`, and release what `reader` held that is now
    /// completed.
    fn record_complete(&self, reader: usize, source: usize, guard: Option<&TileGuard>) {
        let reads = &self.infos[reader].reads;
        let at = reads.iter().position(|&r| r == source);
        self.ensure(at.is_some(), || {
            format!(
                "pipeline {source} pushes a complete region to pipeline {reader}, which reads it"
            )
        });
        let at = at.expect("refused above");
        {
            let mut complete = self.states[reader]
                .complete
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if complete.len() < reads.len() {
                complete.resize(reads.len(), Completion::Nothing);
            }
            let before = std::mem::take(&mut complete[at]);
            complete[at] = match guard {
                Some(guard) => before.grown(guard),
                None => Completion::Whole,
            };
        }
        if self.infos[reader].waits_for_inputs {
            self.queue_ready_inputs(reader);
        }
    }

    /// Push `complete`, the region of its keys `pipeline`'s breaker has completed, through `to`, the
    /// breaker's consumer, and record what reaches each reader's entry as completed by `pipeline`
    /// ([`complete_of`](Self::complete_of)). Where `complete` is every key, each reader the push
    /// reached no entry of reads `pipeline` by pull, which reads all of it: it records `pipeline`
    /// whole.
    fn land_complete(
        &self,
        pipeline: usize,
        complete: Option<&Projection>,
        to: Option<&SharedConsumer>,
    ) {
        let (Some(complete), Some(to)) = (complete, to) else {
            return;
        };
        if *complete == Projection::Nothing {
            return;
        }
        let whole = *complete == Projection::Everything;
        let mut landing = Landing {
            target: Target::Completion {
                dispatcher: self,
                whole,
                reached: Vec::new(),
            },
            from: pipeline,
            widened: false,
        };
        to.borrow_mut().push(complete, &mut landing);
        let Target::Completion { reached, .. } = landing.target else {
            unreachable!("a complete landing stays one");
        };
        if whole {
            for &reader in &self.infos[pipeline].readers {
                if !reached.contains(&reader) {
                    self.record_complete(reader, pipeline, None);
                }
            }
        }
    }

    /// What `source`, a pipeline `reader` reads, has completed of `reader`'s breaker's input.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `source`.
    #[cfg(test)]
    pub(crate) fn complete_of(&self, reader: PipelineId, source: PipelineId) -> Completion {
        let at = self.infos[reader.0]
            .reads
            .iter()
            .position(|&r| r == source.0)
            .unwrap_or_else(|| panic!("pipeline {} reads pipeline {}", reader.0, source.0));
        self.states[reader.0]
            .complete
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
            complete: None,
        }
    }

    /// The handle a worker thread holds while it claims: when the thread panics, dropping the
    /// handle fails the run, so no other worker waits for a package the panicking one claimed.
    pub fn worker(&self) -> Worker<'_> {
        Worker(self)
    }

    /// The handle a thread holds while it publishes, worker or not: when the thread panics,
    /// dropping it fails the run as a [`Worker`] does, so no thread waits for what the panicking
    /// publication would have published, a package, a close or a finish.
    fn publisher(&self) -> Worker<'_> {
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
        let _publisher = self.publisher();
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
        let _publisher = self.publisher();
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
        let queue = &state.queue;
        let mut admission = queue.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.ensure(!admission.arrivals_closed, || {
            format!("pipeline {p} is queued nothing once it is closed to arrivals")
        });
        #[cfg(test)]
        self.run_transition_hook(false);
        let appended = queue.append_locked(&mut admission, p, morsels);
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
        let _publisher = self.publisher();
        let p = pipeline.0;
        self.ensure_source(pipeline);
        let state = self.state(pipeline);
        let mut admission = state
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        self.ensure(!admission.arrivals_closed, || {
            format!("pipeline {p} closes its queue once")
        });
        admission.arrivals_closed = true;
        state.queue.close();
        self.advance();
    }

    /// The package at the front of `pipeline`'s queue, recorded as claimed, where a claim may take
    /// one. An ordered pipeline has at most one package in flight.
    fn claim_from(&self, pipeline: usize) -> Option<WorkPackage> {
        self.claim_in(pipeline)
    }

    /// Claim the oldest ready package after observing its dependencies' progress.
    fn claim_in(&self, pipeline: usize) -> Option<WorkPackage> {
        let state = &self.states[pipeline];
        state
            .queue
            .claim(pipeline, self.infos[pipeline].ordered, || true)
    }

    /// Whether `pipeline` may finish: it is running, its queue is closed and every package in it
    /// acknowledged. Its queue closes once nothing more can be queued for it, so the finish is
    /// its last.
    fn ready_to_finish(&self, pipeline: usize) -> bool {
        let state = &self.states[pipeline];
        // One read of the count and the close: nothing is reserved after the close, so the count
        // of a closed queue is its last.
        let reserved = state.queue.reserved.load(Ordering::Acquire);
        #[cfg(test)]
        self.run_transition_hook(true);
        state.phase.load() == Phase::Running
            && reserved & CLOSED != 0
            && state.acknowledged.load(Ordering::Acquire) == reserved & !CLOSED
    }

    /// Claim the finish only from a closed queue's final reservation count.
    fn try_begin_finish(&self, pipeline: usize) -> bool {
        self.ready_to_finish(pipeline)
            && self.states[pipeline]
                .phase
                .moved(Phase::Running, Phase::Finishing)
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
            let begun = self.try_begin_finish(p);
            if begun {
                return Next::Finish {
                    pipeline: PipelineId(p),
                    consumed: self.states[p].queue.region(),
                };
            }
        }
        if self.unfinished.load(Ordering::Acquire) == 0 {
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
        let mut acknowledged = 0;
        let held = state.queue.acknowledge(&package, || {
            // Record consumption before unlocking the next ordered claim or publishing finish.
            #[cfg(test)]
            self.record(Event::Consume {
                pipeline: package.pipeline,
                guard: package.guard.clone(),
            });
            acknowledged = state.acknowledged.fetch_add(1, Ordering::AcqRel) + 1;
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
    /// acknowledged, a pipeline it reads has not finished, its queue is not closed.
    pub fn begin_finish(&self, pipeline: PipelineId) -> Option<TileGuard> {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.try_begin_finish(p), || {
            format!("pipeline {p} finishes once, after its queue is closed and consumed")
        });
        self.states[p].queue.region()
    }

    /// Land what `pushes` holds now, while the pipeline runs: each morsel climbs the breaker's
    /// consumer to the [`Entry`] of each pipeline that reads it, which queues it there, and the
    /// reader may claim the packages before the pipeline finishes. A breaker's push names only what
    /// it has completed ([`Pushes::push_final`]), so the reader's chain reads it final. After a
    /// failure it lands nothing.
    ///
    /// # Panics
    ///
    /// When the pipeline has finished.
    pub fn land(&self, mut pushes: Pushes<'_>) {
        let _publisher = self.publisher();
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline lands its pushes through its own dispatcher"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        let complete = pushes.complete.take();
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        self.land_complete(p, complete.as_ref(), pushes.to.as_ref());
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
        let _publisher = self.publisher();
        debug_assert!(
            std::ptr::eq(pushes.dispatcher, self),
            "a pipeline finishes through its own dispatcher's pushes"
        );
        let p = pushes.pipeline;
        let morsels = std::mem::take(&mut pushes.morsels);
        let complete = pushes.complete.take();
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
        self.land_complete(p, complete.as_ref(), pushes.to.as_ref());
        // Every pipeline it reads has finished and completed all of it, so nothing stays held.
        {
            let waiting_for_inputs = self.states[p]
                .queue
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            self.ensure(waiting_for_inputs.waiting_for_inputs.is_empty(), || {
                format!(
                    "pipeline {p} finishes with rows waiting_for_inputs that the \
                     pipelines it reads never complete: {:?}",
                    waiting_for_inputs.waiting_for_inputs
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
        self.unfinished.fetch_sub(1, Ordering::AcqRel);
        self.advance();
    }

    /// How many of `pipeline`'s packages are queued and not acknowledged.
    #[cfg(test)]
    pub(crate) fn outstanding(&self, pipeline: PipelineId) -> usize {
        self.state(pipeline).outstanding()
    }

    /// End the run: every claim from now answers [`Next::Failed`], and every waiter wakes. A thread
    /// that panics while it holds a [`Worker`], claiming or publishing, calls it by dropping the
    /// handle, so the others stop instead of waiting for what it held or would have published.
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
            && !self
                .state(pipeline)
                .queue
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .arrivals_closed
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

/// A handle on the dispatcher that fails the run when its thread unwinds: a worker holds one while
/// it claims ([`Dispatcher::worker`]), and a call that publishes holds one while it publishes.
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
    /// The region of its keys the breaker has completed, pushed through `to` beside the morsels
    /// ([`Landing::is_complete`]); `None` where it pushed none.
    complete: Option<Projection>,
}

impl Pushes<'_> {
    /// Push what `breaker` has completed and the pipeline has not pushed before, its final guard
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
        // The completed region is the breaker's statement of it, released or not: a released key
        // stays completed. A region no projection spells is pushed as nothing completed, which
        // delays a reader and never misleads it.
        self.complete = complete_projection(
            breaker.complete().closed_over(breaker.tiling()),
            breaker.tiling(),
        );
        let complete = breaker.final_guard();
        let guard = self.record(|pushed| match pushed {
            Some(pushed) => guard_minus(&complete, pushed),
            None => complete.clone(),
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

    /// Push `guard`, cut by `cut` into morsels that target the dispatcher's `morsel_rows` held
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
    /// Refuses to drop pushes that never landed, which would lose the reader's packages or the
    /// completion a reader waits on. A push can carry a completion and no morsel.
    fn drop(&mut self) {
        if !thread::panicking() {
            self.dispatcher
                .ensure(self.morsels.is_empty() && self.complete.is_none(), || {
                    format!(
                        "pipeline {} lands its pushes through Dispatcher::land or \
                         Dispatcher::finish",
                        self.pipeline
                    )
                });
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
    /// Grows, for each, what the pushing pipeline has completed of the reader's input
    /// ([`Dispatcher::complete_of`]), and queues nothing. `whole` says the pushing pipeline is
    /// wholly completed, and `reached` lists the readers whose entry the push reached.
    Completion {
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
            Target::Queue { .. } | Target::Completion { .. } => {
                panic!("a landing that queues or records complete regions records no arrivals")
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
            Target::Completion {
                dispatcher,
                whole,
                reached,
            } => {
                reached.push(reader.0);
                // A wholly completed source is completed along whatever its push was restated to on
                // the way, as an arm of a union restates it under its tag.
                let guard = (!(*whole || guard.is_universal())).then_some(guard);
                return dispatcher.record_complete(reader.0, self.from, guard);
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
        // A reader that waits for input completion reads each row once, when every pipeline it reads has completed it: a
        // push brings the rows it names, widened or not, less what a push brought before, and the
        // completed pushes release them ([`Dispatcher::wait_for_inputs`]).
        if dispatcher.infos[r].waits_for_inputs {
            dispatcher.queue_or_wait_for_inputs(r, guard);
            return;
        }
        dispatcher.ensure(!self.widened, || {
            format!(
                "a push of pipeline {from} is widened to `Everything` on its way to pipeline {r}, \
                 which neither waits_for_inputs nor reads that pipeline once it has finished"
            )
        });
        dispatcher.ensure(queue.queue.append_unqueued(guard), || {
            format!("pipeline {r} receives packages before the last pipeline it reads finishes")
        });
    }

    /// Whether the region climbing is a completed region rather than a change: an operator restates
    /// a completed region by keeping what it names where it keeps the keys, and where it widens them
    /// by naming nothing until the region is every key, since each of its keys depends on every
    /// key of its input.
    pub fn is_complete(&self) -> bool {
        matches!(self.target, Target::Completion { .. })
    }

    /// Whether the region climbing is a completed region of a source that is wholly completed: an
    /// operator that widens its input's keys passes it as every key, since what that source
    /// contributes to each of the operator's keys is completed, and the reader intersects what its
    /// other sources completed.
    pub fn is_wholly_complete(&self) -> bool {
        matches!(self.target, Target::Completion { whole: true, .. })
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
            Target::Queue { dispatcher, .. } | Target::Completion { dispatcher, .. } => {
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
/// `held`, a breaker's completed region of its output `tiling`, as a projection: every key where it
/// names every position of the finite range of positions the output's outermost keys range over,
/// as a store or an aggregate under a loop of positions `0..n` states the positions it completed,
/// which `TileGuard::closed_over` leaves as they are. `None` where no projection spells it.
fn complete_projection(held: TileGuard, tiling: &Tiling) -> Option<Projection> {
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
    match closed_runs(positions, |at| Some(u128::from(*at)), None) {
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
    match closed_runs(runs, uint_position, None) {
        Some(runs) => cut_before(
            region,
            &cuts_every(runs, rows),
            &Extent::Base(crate::interpreter::BaseType::UInt),
        ),
        None => vec![guard.clone()],
    }
}

/// The runs of `runs` as closed `(first, last)` pairs of positions, in ascending order. `at` reads
/// an end's position, and an open end moves one position inward. An unbounded first end takes
/// `unbounded`'s first, and an unbounded last end its last. `None` where `at` reads no position,
/// where a run has an unbounded end and `unbounded` is `None`, or where an open last end sits at
/// position 0.
fn closed_runs<T: intervalsets::numeric::Domain>(
    runs: &intervalsets::IntervalSet<T>,
    at: impl Fn(&T) -> Option<u128>,
    unbounded: Option<(u128, u128)>,
) -> Option<Vec<(u128, u128)>> {
    runs.intervals()
        .iter()
        .map(|run| {
            let first = match run.left() {
                Some(bound) => at(bound.value())? + u128::from(!bound.is_closed()),
                None => unbounded?.0,
            };
            let last = match run.right() {
                Some(bound) => at(bound.value())?.checked_sub(u128::from(!bound.is_closed()))?,
                None => unbounded?.1,
            };
            Some((first, last))
        })
        .collect()
}

/// `value`'s position, where it is a `Value::UInt`.
fn uint_position(value: &Value) -> Option<u128> {
    match value {
        Value::UInt(at) => Some(u128::from(*at)),
        _ => None,
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

/// Hand `package` to its pipeline's breaker, land what the breaker completed since its last push
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
/// completed and no consume pushed, through the breaker's [`finish`][Breaker::finish], then mark it
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
/// finished ([`Dispatcher::read_whole`]). Every other reader holds the rows its pushes bring until
/// the pipelines it reads have completed them ([`Dispatcher::wait_for_inputs`]). Each range under a reader of
/// pushes (an `IterateExtent`), such as a literal's positions, the one producer with no input that
/// keeps its consumer (`ProducerBase::leaf`), is probed too. What the ranges bring that no push can
/// name is queued for the reader at the start of the run as one region, held as a push's rows
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
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| match &located[pipeline.0] {
        Located::Sink(sink) => call(&mut *sink_breakers[*sink].borrow_mut()),
        Located::Chain(handle) => call(&mut *handle.borrow_mut()),
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
        // A reader holds the rows its pushes and its start bring until the pipelines it reads
        // have completed them, and reads each row once ([`Dispatcher::wait_for_inputs`]). It reads its input
        // whole where a pipeline it reads reaches it by pull, or where nothing brings it a row.
        if unreached || (pushed.is_none() && left.is_empty()) {
            dispatcher.read_whole(PipelineId(reader), &input);
            planned[reader].whole = true;
            continue;
        }
        dispatcher.wait_for_inputs(PipelineId(reader));
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
    /// Whether it holds the rows pushes bring until the pipelines it reads have completed them
    /// ([`Dispatcher::wait_for_inputs`]).
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
    /// The shared cell owning a breaker subscription.
    Chain(BreakerHandle),
    /// The breaker of the sink of this index in `sinks` ([`SinkBreaker`]).
    ///
    /// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
    Sink(usize),
}

/// Visit `producer`'s inputs mutably, and answer how many it has. The planner finds the pipelines
/// beneath a producer by walking its inputs mutably, and reads the role each input has there, so
/// this checks that `visit_input_producers_mut` visits what `visit_input_producers` lists: the
/// same producers, by address, in the same order and under the same roles.
///
/// # Panics
///
/// Where the two walks differ, naming the first input at which they do.
#[cfg(test)]
fn visit_inputs_checked(
    producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
    visit: &mut dyn FnMut(&str, &mut dyn crate::interpreter::tile_operators::TileProducer),
) -> usize {
    use crate::interpreter::tile_operators::TileProducer;
    fn address(input: &dyn TileProducer) -> usize {
        std::ptr::from_ref(input).cast::<()>() as usize
    }
    let mut listed = Vec::new();
    producer.visit_input_producers(&mut |role, input| {
        listed.push((role.to_owned(), address(input)));
    });
    // The producer is borrowed mutably while it walks, so its name is read before.
    let name = producer.name();
    let mut at = 0;
    producer.visit_input_producers_mut(&mut |role, input| {
        let expected = listed.get(at);
        if !expected.is_some_and(|(listed, address_listed)| {
            listed == role && *address_listed == address(&*input)
        }) {
            panic!(
                "{name} visits {} under `{role}` mutably as its input {at}, where it lists {:?}",
                input.name(),
                expected.map(|(role, _)| role)
            );
        }
        at += 1;
        visit(role, input);
    });
    assert_eq!(
        at,
        listed.len(),
        "{name} visits {at} inputs mutably and lists {}",
        listed.len()
    );
    at
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
        let handle = producer
            .base()
            .breaker_handle
            .as_ref()
            .and_then(std::rc::Weak::upgrade);
        if let Some(pipeline) = self
            .located
            .iter()
            .position(|at| matches!((at, &handle), (Located::Chain(seen), Some(handle)) if Rc::ptr_eq(seen, handle)))
        {
            return Beneath {
                pipelines: vec![(pipeline, true)],
                ..Beneath::default()
            };
        }
        let mut below = Beneath::default();
        let inputs = visit_inputs_checked(producer, &mut |role, input| {
            let under = self.pipelines_under(input, role);
            for (pipeline, direct) in under.pipelines {
                if !below.pipelines.iter().any(|(seen, _)| *seen == pipeline) {
                    below.pipelines.push((pipeline, direct));
                }
            }
            below.leaves.extend(under.leaves);
            below.unprobed.extend(under.unprobed);
        });
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
        self.located.push(Located::Chain(
            handle.expect("a subscribed breaker owns a handle"),
        ));
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

fn grow(region: &mut Option<TileGuard>, guard: &TileGuard) {
    *region = Some(grown(region.as_ref(), guard));
}

/// `region` with `guard` added, or `guard` alone where there is no region yet.
fn grown(region: Option<&TileGuard>, guard: &TileGuard) -> TileGuard {
    match region {
        Some(before) => before.union(guard),
        None => guard.clone(),
    }
}

#[cfg(test)]
mod tests {
    mod input_walks {
        use crate::interpreter::tile_operators::test_helpers::{
            TestTileProducer, two_levels_of_ints,
        };
        use crate::interpreter::tile_operators::{
            ProducerBase, TileGuard, TileProducer, impl_producer_base,
        };
        use crate::interpreter::{Tile, Tiling};

        /// How a [`TwoInputs`] walks its inputs mutably.
        enum Walk {
            AsListed,
            Swapped,
            RolesSwapped,
            FirstTwice,
        }

        /// A producer of two inputs, `a` then `b`, whose mutable walk is `walk`.
        struct TwoInputs {
            base: ProducerBase,
            a: Box<dyn TileProducer>,
            b: Box<dyn TileProducer>,
            walk: Walk,
        }

        impl TileProducer for TwoInputs {
            impl_producer_base!();

            fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
                visit("a", &*self.a);
                visit("b", &*self.b);
            }

            fn visit_input_producers_mut(
                &mut self,
                visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
            ) {
                match self.walk {
                    Walk::AsListed => {
                        visit("a", &mut *self.a);
                        visit("b", &mut *self.b);
                    }
                    Walk::Swapped => {
                        visit("a", &mut *self.b);
                        visit("b", &mut *self.a);
                    }
                    Walk::RolesSwapped => {
                        visit("b", &mut *self.a);
                        visit("a", &mut *self.b);
                    }
                    Walk::FirstTwice => {
                        visit("a", &mut *self.a);
                        visit("b", &mut *self.a);
                    }
                }
            }

            fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
                self.tiling().empty_tile()
            }

            fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
        }

        fn two_inputs(walk: Walk) -> TwoInputs {
            let (tile, tiling): (Tile, Tiling) = two_levels_of_ints();
            TwoInputs {
                base: ProducerBase::unowned(TwoInputs::alloc_id(), &tiling),
                a: Box::new(TestTileProducer::new(tile.clone(), tiling.clone())),
                b: Box::new(TestTileProducer::new(tile, tiling)),
                walk,
            }
        }

        /// A mutable walk that visits what the listing does is visited through, input by input.
        #[test]
        fn a_walk_as_listed_visits_each_input_once() {
            let mut roles = Vec::new();
            let inputs = super::super::visit_inputs_checked(
                &mut two_inputs(Walk::AsListed),
                &mut |role, _| roles.push(role.to_owned()),
            );
            assert_eq!(inputs, 2);
            assert_eq!(roles, ["a", "b"]);
        }

        /// A mutable walk that swaps two inputs keeps the count and panics, naming the input.
        #[test]
        #[should_panic(expected = "mutably as its input 0, where it lists")]
        fn a_walk_that_swaps_two_inputs_panics() {
            super::super::visit_inputs_checked(&mut two_inputs(Walk::Swapped), &mut |_, _| {});
        }

        /// A mutable walk that visits each input under the other's role keeps the producers and
        /// the count and panics.
        #[test]
        #[should_panic(expected = "under `b` mutably as its input 0, where it lists")]
        fn a_walk_that_swaps_two_roles_panics() {
            super::super::visit_inputs_checked(&mut two_inputs(Walk::RolesSwapped), &mut |_, _| {});
        }

        /// A mutable walk that visits one input twice keeps the count and panics.
        #[test]
        #[should_panic(expected = "mutably as its input 1, where it lists")]
        fn a_walk_that_repeats_an_input_panics() {
            super::super::visit_inputs_checked(&mut two_inputs(Walk::FirstTwice), &mut |_, _| {});
        }
    }

    #[test]
    fn concurrent_admission_and_completion_queue_each_region_once() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::sync::Barrier;
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1).unrecorded();
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        let start = Barrier::new(9);
        thread::scope(|scope| {
            for worker in 0..8 {
                let dispatcher = &dispatcher;
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    for key in 0..32 {
                        let guard = keys_between(key, key);
                        if worker % 2 == 0 {
                            dispatcher.queue_or_wait_for_inputs(reader.0, &guard);
                            dispatcher.record_complete(1, 0, Some(&guard));
                        } else {
                            dispatcher.record_complete(1, 0, Some(&guard));
                            dispatcher.queue_or_wait_for_inputs(reader.0, &guard);
                        }
                    }
                });
            }
            start.wait();
        });
        let mut regions = Vec::new();
        while let Some(package) = dispatcher.claim_of(reader) {
            regions.push(package.guard.clone());
            dispatcher.acknowledge(package);
        }
        assert_eq!(regions.len(), 32);
        assert_eq!(partition_gap(&keys_between(0, 31), &regions), None);
        assert!(
            dispatcher.states[1]
                .queue
                .state
                .lock()
                .unwrap()
                .waiting_for_inputs
                .is_empty()
        );
        // Acknowledgement does not erase admission history. A round still repeats the region.
        dispatcher.queue_or_wait_for_inputs(reader.0, &keys_between(0, 31));
        assert!(dispatcher.claim_of(reader).is_none());
    }

    #[rstest::rstest]
    fn waiting_for_inputs_membership_compacts_and_drains(#[values(100, 1000, 10000)] count: u64) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1).unrecorded();
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        for key in 0..count {
            dispatcher.queue_or_wait_for_inputs(reader.0, &keys_between(key, key));
        }
        {
            let state = dispatcher.states[1].queue.state.lock().unwrap();
            assert_eq!(state.waiting_for_inputs.len(), count as usize);
            assert_eq!(state.waiting_region, Some(keys_between(0, count - 1)));
        }
        dispatcher.record_complete(1, 0, None);
        let state = dispatcher.states[1].queue.state.lock().unwrap();
        assert!(state.waiting_for_inputs.is_empty());
        assert!(state.waiting_region.is_none());
        assert_eq!(state.ready.len(), count as usize);
    }

    #[test]
    fn concurrent_ordered_claims_reserve_one_package() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::sync::Barrier;
        let mut dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let source = PipelineId(0);
        dispatcher.order(source);
        dispatcher.notify(source, &keys_between(0, 1));
        let start = Barrier::new(8);
        let packages = thread::scope(|scope| {
            let claims: Vec<_> = (0..8)
                .map(|_| {
                    scope.spawn(|| {
                        start.wait();
                        dispatcher.claim_of(source)
                    })
                })
                .collect();
            claims
                .into_iter()
                .filter_map(|claim| claim.join().unwrap())
                .collect::<Vec<_>>()
        });
        assert_eq!(packages.len(), 1);
        for package in packages {
            dispatcher.acknowledge(package);
        }
        let next = dispatcher
            .claim_of(source)
            .expect("acknowledgement unlocks the next claim");
        assert_eq!(next.guard, keys_between(1, 1));
        dispatcher.acknowledge(next);
        assert!(dispatcher.claim_of(source).is_none());
    }

    use intervalsets::{Interval, IntervalSet};

    use super::*;
    use crate::interpreter::BaseType;

    /// Each run's ends close inward where open, an unbounded end takes the given default or none,
    /// and a bound that is no position reads none.
    #[rstest::rstest]
    #[case::closed(Interval::closed(Value::UInt(2), Value::UInt(5)), None, Some((2, 5)))]
    #[case::open_first(Interval::open_closed(Value::UInt(2), Value::UInt(5)), None, Some((3, 5)))]
    #[case::open_last(Interval::closed_open(Value::UInt(2), Value::UInt(5)), None, Some((2, 4)))]
    #[case::unbounded_last(
        Interval::closed_unbound(Value::UInt(4)),
        Some((0, u128::from(u64::MAX))),
        Some((4, u128::from(u64::MAX)))
    )]
    #[case::unbounded_first(
        Interval::unbound_closed(Value::UInt(3)),
        Some((0, u128::from(u64::MAX))),
        Some((0, 3))
    )]
    #[case::unbounded_without_a_default(Interval::closed_unbound(Value::UInt(4)), None, None)]
    #[case::not_a_position(Interval::closed(Value::Int(1), Value::Int(2)), None, None)]
    fn closed_runs_reads_each_end(
        #[case] run: Interval<Value>,
        #[case] unbounded: Option<(u128, u128)>,
        #[case] expected: Option<(u128, u128)>,
    ) {
        let runs = IntervalSet::from(run);
        assert_eq!(
            closed_runs(&runs, uint_position, unbounded),
            expected.map(|run| vec![run])
        );
    }

    /// An append reserves its indices only once nothing left can panic: an append of a guard the
    /// region has no union with panics and leaves the queue as it was.
    #[test]
    fn an_append_that_panics_reserves_nothing() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let queue = Queue::new();
        let mut state = QueueState::default();
        assert!(queue.append_locked(&mut state, 0, &[keys_between(0, 1)]));
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            queue.append_locked(&mut state, 0, &[TileGuard::Scalar(Predicate::True)])
        }));
        assert!(
            unwound.is_err(),
            "a scalar guard has no union with a region of keys"
        );
        assert_eq!(queue.reserved(), 1);
        assert_eq!(state.ready.len(), 1);
        assert_eq!(state.region, Some(keys_between(0, 1)));
    }

    fn retained_package_guards(queue: &Queue) -> usize {
        let state = queue.state.lock().unwrap();
        state.ready.len() + state.in_flight.len()
    }

    #[rstest::rstest]
    fn acknowledged_packages_leave_no_queue_history(#[values(false, true)] ordered: bool) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let mut dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let source = PipelineId(0);
        dispatcher.limit(source, 1);
        if ordered {
            dispatcher.order(source);
        }
        for index in 0..4096 {
            let guard = keys_between(index, index);
            assert!(dispatcher.try_notify(source, &guard));
            assert_eq!(retained_package_guards(&dispatcher.states[0].queue), 1);
            let package = dispatcher.claim_of(source).expect("the delivered package");
            assert_eq!(package.index, index as usize);
            assert_eq!(package.guard, guard);
            assert!(!dispatcher.try_notify(source, &keys_between(index + 1, index + 1)));
            dispatcher.acknowledge(package);
            assert_eq!(retained_package_guards(&dispatcher.states[0].queue), 0);
            assert_eq!(dispatcher.outstanding(source), 0);
        }
        dispatcher.close(source);
        let Next::Finish { pipeline, consumed } = dispatcher.try_claim(None) else {
            panic!("the drained source finishes")
        };
        assert_eq!(pipeline, source);
        assert_eq!(consumed, Some(keys_between(0, 4095)));
        dispatcher.finish(dispatcher.pushes(pipeline));
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }

    #[test]
    fn a_held_package_does_not_retain_later_acknowledged_packages() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let mut dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let source = PipelineId(0);
        dispatcher.limit(source, 2);
        dispatcher.notify(source, &keys_between(0, 0));
        let first = dispatcher.claim_of(source).expect("the held package");
        for index in 1..1024 {
            let guard = keys_between(index, index);
            assert!(dispatcher.try_notify(source, &guard));
            let package = dispatcher.claim_of(source).expect("a later package");
            assert_eq!(package.index, index as usize);
            assert_eq!(retained_package_guards(&dispatcher.states[0].queue), 2);
            dispatcher.acknowledge(package);
            assert_eq!(retained_package_guards(&dispatcher.states[0].queue), 1);
            assert_eq!(dispatcher.outstanding(source), 1);
        }
        dispatcher.close(source);
        assert!(matches!(dispatcher.try_claim(None), Next::Wait(_)));
        dispatcher.acknowledge(first);
        assert_eq!(retained_package_guards(&dispatcher.states[0].queue), 0);
        let Next::Finish { consumed, .. } = dispatcher.try_claim(None) else {
            panic!("the source finishes after the held acknowledgement")
        };
        assert_eq!(consumed, Some(keys_between(0, 1023)));
        dispatcher.finish(dispatcher.pushes(source));
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }

    #[test]
    fn acknowledgement_keeps_the_region_used_for_deduplication() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let queue = Queue::new();
        assert!(queue.append_unqueued(&keys_between(0, 2)));
        let first = queue.claim(0, false, || true).unwrap();
        assert!(queue.acknowledge(&first, || {}));
        assert_eq!(retained_package_guards(&queue), 0);
        assert!(queue.append_unqueued(&keys_between(1, 4)));
        let second = queue.claim(0, false, || true).unwrap();
        assert_eq!(second.guard, keys_between(3, 4));
        assert!(queue.acknowledge(&second, || {}));
        assert!(queue.append_unqueued(&keys_between(0, 4)));
        assert!(queue.state.lock().unwrap().ready.is_empty());
        assert_eq!(queue.reserved(), 2);
        assert!(queue.close());
        assert!(!queue.append_unqueued(&keys_between(0, 4)));
        assert_eq!(queue.region(), Some(keys_between(0, 4)));
    }

    #[test]
    fn an_empty_dispatcher_is_done() {
        let dispatcher = Dispatcher::new(vec![], 1);
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }

    #[rstest::rstest]
    fn a_finish_snapshot_cannot_miss_an_arrival_before_close(#[values(false, true)] manual: bool) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::sync::{Arc, Barrier};

        let dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let snapshot = Arc::new(Barrier::new(2));
        let resume = Arc::new(Barrier::new(2));
        let (seen, go) = (snapshot.clone(), resume.clone());
        *dispatcher.transition_hooks[1]
            .get_or_init(|| Mutex::new(None))
            .lock()
            .unwrap() = Some(Box::new(move || {
            seen.wait();
            go.wait();
        }));
        thread::scope(|scope| {
            let worker = scope.spawn(|| {
                if manual {
                    assert!(
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            dispatcher.begin_finish(PipelineId(0));
                        }))
                        .is_err()
                    );
                } else {
                    assert!(matches!(dispatcher.try_claim(None), Next::Wait(_)));
                }
            });
            snapshot.wait();
            dispatcher.notify(PipelineId(0), &keys_between(0, 0));
            dispatcher.close(PipelineId(0));
            resume.wait();
            worker.join().unwrap();
        });
        assert!(dispatcher.states[0].phase.load() == Phase::Running);
        assert_eq!(dispatcher.states[0].queue.reserved(), 1);
        assert_eq!(dispatcher.states[0].acknowledged.load(Ordering::Acquire), 0);
        if !manual {
            let Next::Package(package) = dispatcher.try_claim(None) else {
                panic!("the arrival remains claimable")
            };
            dispatcher.acknowledge(package);
            assert!(matches!(dispatcher.try_claim(None), Next::Finish { .. }));
            dispatcher.finish(dispatcher.pushes(PipelineId(0)));
            assert!(matches!(dispatcher.try_claim(None), Next::Done));
        }
    }

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

//! A dispatcher of work packages between the pipelines of a program, shared by the threads that
//! claim them.
//!
//! A pipeline is a [`Breaker`] and the chain it owns; the breaker of a pipeline that another reads
//! is a [`BreakingProducer`]. The dispatcher holds the graph of pipelines and a queue of work
//! packages per pipeline, each package one morsel of at most `morsel_rows` held rows. Each pipeline
//! finishes once, after its queue closes and every package is acknowledged. A per-pipeline lock
//! protects ready and in-flight packages; acknowledgement removes an in-flight entry. Operator
//! execution holds no queue lock. A worker sleeps while there is nothing to claim, and a change
//! that can end a sleep wakes the sleepers. The dispatcher holds no breaker, so it is
//! `Sync` while the breakers are not `Send`. The single-threaded driver, [`run`], reaches the
//! breakers through the handles its caller passes, indexed by pipeline. Nothing outside unit tests
//! calls it, and only unit tests drive the dispatcher from several threads. See
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
pub(crate) mod loop_scope;

#[cfg(test)]
use crate::interpreter::tile_operators::StoreCell;
#[cfg(test)]
use loop_scope::{Member, induction};

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
    waiting_for_inputs: Vec<WaitingInput>,
    /// Union of guards currently waiting for input completion.
    waiting_region: Option<TileGuard>,
}

impl QueueState {
    fn wait_for_inputs(&mut self, morsel: WaitingInput) {
        grow(&mut self.waiting_region, &morsel.guard);
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

    /// Append a repeated read of a loop's row, including its end, as a distinct package.
    #[cfg(test)]
    fn append_again(&self, guard: &TileGuard) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.append_again_locked(&mut state, guard)
    }

    fn append_again_locked(&self, state: &mut QueueState, guard: &TileGuard) -> bool {
        // The union can panic, so it runs before the reservation.
        let region = grown(state.region.as_ref(), guard);
        let Some(index) = self.reserve(1) else {
            return false;
        };
        state.region = Some(region);
        state.ready.push_back((index, guard.clone()));
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
    /// The pipelines it reads that it takes no push from, and whose quiescence it waits
    /// for before it takes a package there ([`follow`](Dispatcher::follow)).
    follows: Vec<usize>,
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
    ingress: Option<std::ops::Range<usize>>,
}

/// A region a pipeline held ([`Dispatcher::wait_for_inputs`]), and whether a release may hand out the part
/// of it that is completed and keep the rest. A row a loop's round queues is read for the row's end,
/// which its reads state only once they have completed all of it, so it is released whole.
#[derive(Debug)]
struct WaitingInput {
    guard: TileGuard,
    splits: bool,
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
    followers_held: AtomicBool,
    held: AtomicBool,
}

impl PipelineState {
    fn new(reads: usize) -> Self {
        Self {
            queue: Queue::new(),

            phase: AtomicPhase::new(Phase::Running),
            unfinished: AtomicUsize::new(reads),
            pushed: Mutex::new(None),

            complete: Mutex::new(Vec::new()),
            acknowledged: AtomicUsize::new(0),

            followers_held: AtomicBool::new(false),
            held: AtomicBool::new(false),
        }
    }

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
    /// The most held rows a work package names.
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
                follows: Vec::new(),
                waits_for_inputs: false,
                reach: Vec::new(),
                limit: usize::MAX,
                ingress: None,
            })
            .collect();
        let states = infos
            .iter()
            .map(|info: &PipelineInfo| PipelineState::new(info.reads.len()))
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

    #[cfg(test)]
    /// Append a configured graph before execution and return its pipeline offset.
    pub(crate) fn append_graph(&mut self, mut graph: Dispatcher) -> usize {
        assert_eq!(
            self.morsel_rows, graph.morsel_rows,
            "composed graphs share their morsel size"
        );
        assert!(
            graph.states.iter_mut().all(|state| state.queue.reserved()
                == state
                    .queue
                    .state
                    .get_mut()
                    .unwrap_or_else(PoisonError::into_inner)
                    .ready
                    .len()
                && state.phase.load() == Phase::Running),
            "a graph is composed before it executes"
        );
        let offset = self.infos.len();
        for info in &mut graph.infos {
            for pipeline in info
                .reads
                .iter_mut()
                .chain(&mut info.readers)
                .chain(&mut info.follows)
            {
                *pipeline += offset;
            }
            if let Some(ingress) = &mut info.ingress {
                ingress.start += offset;
                ingress.end += offset;
            }
        }
        *self.unfinished.get_mut() += graph.states.len();
        self.infos.append(&mut graph.infos);
        self.states.append(&mut graph.states);
        offset
    }
    #[cfg(test)]
    /// Add a pipeline after its dependencies, before execution starts.
    pub(crate) fn add_pipeline(&mut self, reads: Vec<PipelineId>) -> PipelineId {
        let pipeline = self.infos.len();
        let reads: Vec<usize> = reads.into_iter().map(|read| read.0).collect();
        for (at, &read) in reads.iter().enumerate() {
            assert!(
                read < pipeline && !reads[..at].contains(&read),
                "a new pipeline reads existing pipelines once"
            );
            self.infos[read].readers.push(pipeline);
        }
        self.states.push(PipelineState::new(reads.len()));
        self.infos.push(PipelineInfo {
            reads,
            readers: Vec::new(),
            ordered: false,
            whole: None,
            follows: Vec::new(),
            limit: usize::MAX,
            waits_for_inputs: false,
            reach: Vec::new(),
            ingress: None,
        });
        *self.unfinished.get_mut() += 1;
        PipelineId(pipeline)
    }
    #[cfg(test)]
    /// Accept pushes at this entry only from the configured input graph.
    pub(crate) fn restrict_ingress(&mut self, pipeline: PipelineId, from: std::ops::Range<usize>) {
        assert!(
            from.start <= from.end && from.end <= self.infos.len(),
            "an ingress range names planned pipelines"
        );
        self.infos[pipeline.0].ingress = Some(from);
    }
    #[cfg(test)]
    /// Hold a pipeline's packages and finish until it is activated by its execution handler.
    /// The serial coordinator changes holds between claims; a hold does not revoke a claim.
    pub(crate) fn hold_pipeline(&self, pipeline: PipelineId, held: bool) {
        if self.state(pipeline).held.swap(held, Ordering::SeqCst) != held {
            self.advance();
        }
    }
    /// The count of the dispatcher's changes so far ([`Generation`]): an equal count read twice
    /// says nothing was queued, consumed or finished between.
    #[cfg(test)]
    pub(crate) fn changes(&self) -> u64 {
        self.generation.load(Ordering::SeqCst)
    }

    /// Whether `pipeline` has consumed every package queued for it, and every pipeline it reads is
    /// quiescent too: no package of theirs is outstanding. A breaker that pushes only what
    /// `push_held` asks of it, as `MapAggregate`, can be quiescent before its readers took what it
    /// completed, which is why a loop's round holds its followers until its pushes settle
    /// ([`hold_followers`](Self::hold_followers)).
    fn quiescent(&self, pipeline: usize) -> bool {
        // The pipelines it reads first: a push lands before the acknowledgement of the package
        // that made it, so a read found quiescent has queued all it pushed before this pipeline's
        // counts are read, and a package in flight on another thread is seen.
        if !self.infos[pipeline]
            .reads
            .iter()
            .all(|&read| self.quiescent(read))
        {
            return false;
        }
        // Acknowledged before reserved: the count only grows and never passes the reservations,
        // so the two equal says no package of the pipeline was outstanding when the second was
        // read.
        let state = &self.states[pipeline];
        let acknowledged = state.acknowledged.load(Ordering::SeqCst);
        acknowledged == state.queue.reserved.load(Ordering::SeqCst) & !CLOSED
    }

    #[cfg(test)]
    /// The serial coordinator changes these holds between claims, after settling held pushes.
    /// A hold does not revoke a claim or wait for a worker already consuming a package.
    ///
    /// Hold the given pipelines that follow others ([`follow`](Self::follow)) from taking a
    /// package, or release them. A loop's round holds them while the pipelines they follow push
    /// what they completed. A breaker that pushes only what `push_held` asks it to, as `MapAggregate`,
    /// is quiescent before its readers have taken what it completed. See
    /// `src/interpreter/design-dispatcher.md`, "A loop in rounds".
    pub(crate) fn hold_followers(
        &self,
        pipelines: impl IntoIterator<Item = PipelineId>,
        held: bool,
    ) {
        for pipeline in pipelines {
            self.state(pipeline)
                .followers_held
                .store(held, Ordering::SeqCst);
        }
        self.advance();
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader` in the
    /// run, less what is queued for it there already: at the start, what a range brings
    /// that no push names ([`run_program`]), and in a loop's round, the row of a nested loop's
    /// store, which follows the pipelines inside the cycle around it ([`follow`](Self::follow),
    /// `InductionStoreProducer`).
    ///
    /// # Panics
    ///
    /// When `reader`'s queue has closed: every pipeline it reads has finished.
    #[cfg(test)]
    pub(crate) fn queue_for(&self, reader: PipelineId, guard: &TileGuard) {
        self.queue_in_current(reader, guard, false);
    }

    /// [`queue_for`](Self::queue_for) for a loop's round: the row of a nested loop's store, which
    /// follows the pipelines inside the cycle around it ([`follow`](Self::follow)), or a row the
    /// closing round has every inner pipeline read again (`InductionStoreProducer`). A reader that
    /// waits for input completion takes the row again whatever it took before, and only once the pipelines it reads
    /// have completed all of it, the row's end with its rows ([`WaitingInput`]).
    #[cfg(test)]
    pub(crate) fn queue_round(&self, reader: PipelineId, guard: &TileGuard) {
        self.queue_in_current(reader, guard, true);
    }

    #[cfg(test)]
    fn queue_in_current(&self, reader: PipelineId, guard: &TileGuard, round: bool) {
        let _publisher = self.publisher();
        if self.infos[reader.0].waits_for_inputs {
            self.queue_or_wait_for_inputs(reader.0, guard, round);
            self.advance();
            return;
        }
        let queue = &self.states[reader.0].queue;
        let appended = match round {
            true => queue.append_again(guard),
            false => queue.append_unqueued(guard),
        };
        assert!(
            appended,
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

    /// Order `reader`'s rounds after `read`'s, a pipeline it reads, in a loop's scope: `reader`
    /// takes no push of `read`'s, and takes a package in a round, only once `read` is
    /// quiescent. A scope's planner orders two edges so, where a pipeline cannot hold: a nested
    /// loop's scope after the pipelines its rounds pull, and a reader after a nested loop's scope,
    /// which pushes its store only once it is terminal.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`.
    pub fn follow(&mut self, reader: PipelineId, read: PipelineId) {
        assert!(
            self.infos[reader.0].reads.contains(&read.0),
            "pipeline {} follows pipeline {}, which it reads",
            reader.0,
            read.0
        );
        self.infos[reader.0].follows.push(read.0);
    }

    /// Whether a claim may take `pipeline`'s packages: once every pipeline it follows
    /// ([`follow`](Self::follow)) is quiescent ([`quiescent`](Self::quiescent)).
    fn takes_from(&self, pipeline: usize) -> bool {
        let follows = &self.infos[pipeline].follows;
        follows.is_empty()
            || (!self.states[pipeline].followers_held.load(Ordering::SeqCst)
                && follows.iter().all(|&read| self.quiescent(read)))
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

    /// Whether every pipeline `reader` reads has completed what of `guard`, a region of its input,
    /// it reaches ([`reaches`](Self::reaches)).
    fn reads_complete(&self, reader: usize, guard: &TileGuard) -> bool {
        guard_minus(guard, &self.complete_part(reader, guard)).is_empty()
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

    /// The completed part of a region that may split, or the whole region once completed otherwise.
    /// A round's row waits for its end as well as its values before it can be queued.
    fn ready_part(&self, reader: usize, guard: &TileGuard, splits: bool) -> TileGuard {
        match splits {
            true => self.complete_part(reader, guard),
            false if self.reads_complete(reader, guard) => guard.clone(),
            false => guard_minus(guard, guard),
        }
    }

    /// Queue `guard`, rows a push or the dispatcher's caller brings `reader`, which waits for input completion, where
    /// every pipeline it reads has completed them, and hold the rest ([`wait_for_inputs`](Self::wait_for_inputs)). Of a
    /// push, only what no push or queue brought before is new. What the caller queues is queued
    /// whole (`again`): a loop's closing round has each inner pipeline read its row again, which
    /// then states the row complete.
    fn queue_or_wait_for_inputs(&self, reader: usize, guard: &TileGuard, again: bool) {
        let mut queue_state = self.states[reader]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let fresh = if again {
            guard.clone()
        } else {
            let mut fresh = match &queue_state.region {
                Some(queued) => guard_minus(guard, queued),
                None => guard.clone(),
            };
            if let Some(waiting) = &queue_state.waiting_region {
                fresh = guard_minus(&fresh, waiting);
            }
            fresh
        };
        if fresh.is_empty() {
            return;
        }
        let complete = self.ready_part(reader, &fresh, !again);
        let rest = guard_minus(&fresh, &complete);
        if !rest.is_empty() {
            queue_state.wait_for_inputs(WaitingInput {
                guard: rest,
                splits: !again,
            });
        }
        if complete.is_empty() {
            return;
        }
        let queue = &self.states[reader].queue;
        let appended = match again {
            true => queue.append_again_locked(&mut queue_state, &complete),
            false => queue.append_unqueued_locked(&mut queue_state, &complete),
        };
        self.ensure(appended, || {
            format!(
                "pipeline {reader} receives packages before the last pipeline it reads finishes"
            )
        });
    }

    /// Append the morsels `reader` held that the pipelines it reads have now completed to its
    /// queue ([`wait_for_inputs`](Self::wait_for_inputs)). A completed push lands before the pushing pipeline counts its
    /// finish toward `reader`'s close, so `reader`'s queue is open.
    fn queue_ready_inputs(&self, reader: usize) {
        let mut queue_state = self.states[reader]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let mut released = Vec::new();
        let mut kept = Vec::new();
        for morsel in std::mem::take(&mut queue_state.waiting_for_inputs) {
            let part = self.ready_part(reader, &morsel.guard, morsel.splits);
            let rest = guard_minus(&morsel.guard, &part);
            if !part.is_empty() {
                released.push((part, !morsel.splits));
            }
            if !rest.is_empty() {
                kept.push(WaitingInput {
                    guard: rest,
                    splits: morsel.splits,
                });
            }
        }
        queue_state.waiting_region = None;
        queue_state.waiting_for_inputs = Vec::new();
        for morsel in kept {
            queue_state.wait_for_inputs(morsel);
        }
        if released.is_empty() {
            return;
        }
        let queue = &self.states[reader].queue;
        // A pipeline that takes arrivals holds the morsels its sources' notifies cut, which count
        // toward a source's packages; any other holds the rows pushes bring, which two pushes can
        // both name, so each is queued less what is queued already.
        let appended = released.iter().all(|(morsel, again)| match *again {
            true => queue.append_again_locked(&mut queue_state, morsel),
            false => queue.append_unqueued_locked(&mut queue_state, morsel),
        });
        self.ensure(appended, || {
            format!(
                "pipeline {reader} has not finished when a complete push covers its waiting inputs"
            )
        });
        // A sleeping worker learns of the rows released; a push that releases none changes no
        // queue, so the fixpoints of a live pass and a loop's round, which wait for the generation
        // to stand still, end.
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
        if self.states[pipeline].held.load(Ordering::SeqCst) {
            return None;
        }
        self.claim_in(pipeline)
    }

    /// Claim the oldest ready package after observing its dependencies' progress.
    fn claim_in(&self, pipeline: usize) -> Option<WorkPackage> {
        let state = &self.states[pipeline];
        state
            .queue
            .claim(pipeline, self.infos[pipeline].ordered, || {
                self.takes_from(pipeline)
            })
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
        !state.held.load(Ordering::SeqCst)
            && state.phase.load() == Phase::Running
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
    /// acknowledged, a pipeline it reads has not finished, its queue is not closed, or it is held.
    pub fn begin_finish(&self, pipeline: PipelineId) -> Option<TileGuard> {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.try_begin_finish(p), || {
            format!("pipeline {p} finishes once, after its queue is closed and consumed and its hold is released")
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
    fn accepts_entry(&self, pipeline: PipelineId) -> bool {
        match &self.target {
            Target::Queue { dispatcher } | Target::Completion { dispatcher, .. } => dispatcher
                .infos[pipeline.0]
                .ingress
                .as_ref()
                .is_none_or(|from| from.contains(&self.from)),
            #[cfg(test)]
            Target::Probe(_) => true,
        }
    }

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
        let info = &dispatcher.infos[r];
        if info.whole.is_some() || info.follows.contains(&from) {
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
            dispatcher.queue_or_wait_for_inputs(r, guard, false);
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
            && landing.accepts_entry(pipeline)
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

#[cfg(test)]
/// Have the selected pipelines push what their breakers hold and no push named before. A run after a pause
/// or a reload starts over breakers an earlier run consumed into, and has no finish before its
/// sources close, so its start is where its readers learn what the breakers already hold; each
/// round of an induction run, which no finish ends either, does the same. See
/// `src/interpreter/design-dispatcher.md`, "A loop in rounds".
fn push_held(
    dispatcher: &Dispatcher,
    reach: &mut Reach<'_>,
    pipelines: impl IntoIterator<Item = PipelineId>,
) {
    for pipeline in pipelines {
        let mut landed = None;
        reach(pipeline, &mut |breaker| {
            if let Some(producer) = breaker.as_producer() {
                let mut pushes = dispatcher.pushes(pipeline);
                pushes.push_final(producer);
                landed = Some(pushes);
            }
        });
        if let Some(pushes) = landed {
            dispatcher.land(pushes);
        }
    }
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
/// (`TileProducer::as_breaking_mut`), each store a reader slot reaches, and each sink's own
/// ([`SinkBreaker`]), whose pipeline no pipeline reads. A breaker's pipeline reads the pipelines
/// of the nearest breakers beneath it, and the [`Entry`] at the breaker's input, or the sink's
/// consumer, is placed in the pipeline. A pipeline pulls only its breaker's input, and a sink's
/// pipeline pulls the sink's producer, so a sink receives its producer's answer one package at a
/// time. A sink is done once its producer is released whole, which the run leaves to its caller
/// to read. It answers what it planned for each pipeline, in pipeline order.
///
/// An induction store owns its loop request and store-step control. The planner configures the
/// cycle's body graph locally, then appends it to the same dispatcher as the request pipeline.
/// A dependency that crosses a scope boundary targets the scope's request pipeline. The request
/// remains in flight until its positions and closing rows have stepped.
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
/// When a pipeline reads directly a pipeline that another pipeline reads; where
/// `Planner::store_pipeline` refuses a store; where a nested loop's rounds pull an operator beneath
/// the keys it restates (`Planner::refusal_of_nested`); and where [`run`] panics.
#[cfg(test)]
pub(crate) fn run_program(sinks: &[SinkTarget], morsel_rows: usize) -> Vec<Planned> {
    let mut runs = InductionRuns::new();
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
    let scopes: Vec<Option<StoreCell>> = members
        .located
        .iter()
        .map(|located| match located {
            Located::Scope { scope, .. } => {
                Some(planner.build_scope(*scope, morsel_rows, &mut kept, &mut runs))
            }
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
        Located::Scope { .. } => call(&mut *induction(scope_at(pipeline))),
        Located::Chain(handle) => call(&mut *handle.borrow_mut()),
    };
    // A scope is no producer: its pipeline pushes the store's.
    let mut end_of = |pipeline: PipelineId| match &members.located[pipeline.0] {
        Located::Scope { .. } => Some(induction(scope_at(pipeline)).pushing_end()),
        _ => None,
    };
    let (mut dispatcher, mut planned) = plan_edges(
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
    let execution = Execution::new(&scopes, &mut dispatcher);
    let mut root_reach = reach;
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
        execution.reach(pipeline, &mut root_reach, call)
    };
    execution.drive(&dispatcher, &mut reach);
    for (plan, scope) in planned.iter_mut().zip(&scopes) {
        if let Some(scope) = scope {
            plan.rounds = std::mem::take(&mut induction(scope).run.as_mut().unwrap().planned);
        }
    }
    planned
}

/// Owns installed scheduling metadata from planning through every run exit, including unwinding.
#[cfg(test)]
pub(super) struct InductionRuns {
    stores: Vec<StoreCell>,
}

#[cfg(test)]
impl InductionRuns {
    pub(super) fn new() -> Self {
        Self { stores: Vec::new() }
    }

    fn install(&mut self, store: &StoreCell, run: loop_scope::InductionRun) {
        assert!(
            induction(store).run.is_none(),
            "a store has one run owner at a time"
        );
        self.stores.push(store.clone());
        induction(store).run = Some(run);
    }
}

#[cfg(test)]
impl Drop for InductionRuns {
    fn drop(&mut self) {
        for store in &self.stores {
            induction(store).clear_run();
        }
    }
}

// Body owners belong to the execution table, outside producer run metadata; a store retains
// no handle to itself through its handlers.
#[cfg(test)]
enum Handler {
    Root,
    Body(BreakerHandle),
    Request(StoreCell),
    Step(StoreCell),
}

#[cfg(test)]
pub(super) struct Execution {
    handlers: Vec<Handler>,
    roots: usize,
}

#[cfg(test)]
impl Execution {
    pub(super) fn new(scopes: &[Option<StoreCell>], dispatcher: &mut Dispatcher) -> Self {
        let mut execution = Self {
            handlers: scopes
                .iter()
                .map(|scope| match scope {
                    Some(store) => Handler::Request(store.clone()),
                    None => Handler::Root,
                })
                .collect(),
            roots: scopes.len(),
        };
        for pipeline in 0..execution.roots {
            if let Handler::Request(store) = &execution.handlers[pipeline] {
                let store = store.clone();
                execution.attach_store(&store, dispatcher, PipelineId(pipeline));
            }
        }
        execution
    }

    fn attach_store(
        &mut self,
        store: &StoreCell,
        dispatcher: &mut Dispatcher,
        pipeline: PipelineId,
    ) {
        let (graph, members) = {
            let mut producer = induction(store);
            let run = producer.run.as_mut().expect("an induction run is planned");
            (
                run.body_graph
                    .take()
                    .expect("a body graph is attached once"),
                run.members.clone(),
            )
        };
        let base = dispatcher.append_graph(graph);
        assert_eq!(
            base,
            self.handlers.len(),
            "each global pipeline has one handler"
        );
        self.handlers
            .extend(members.iter().map(|member| match member {
                Member::Chain(handle) => Handler::Body(handle.clone()),
                Member::Scope(child) => Handler::Request(child.clone()),
            }));
        for (local, member) in members.iter().enumerate() {
            dispatcher.restrict_ingress(PipelineId(base + local), base..base + members.len());
            if let Member::Scope(child) = member {
                self.attach_store(child, dispatcher, PipelineId(base + local));
            }
        }
        let body: Vec<_> = (base..base + members.len()).map(PipelineId).collect();
        let step = dispatcher.add_pipeline(body.clone());
        dispatcher.order(step);
        for &member in &body {
            dispatcher.follow(step, member);
            dispatcher.hold_pipeline(member, true);
        }
        dispatcher.hold_pipeline(step, true);
        assert_eq!(
            step.0,
            self.handlers.len(),
            "each global pipeline has one handler"
        );
        self.handlers.push(Handler::Step(store.clone()));
        induction(store)
            .run
            .as_mut()
            .expect("an induction run is planned")
            .shared = Some(loop_scope::SharedLoop {
            pipeline,
            base,
            step,
            active: false,
            followers_released: false,
            finishing: None,
        });
    }

    pub(super) fn reach(&self, pipeline: PipelineId, root: &mut Reach<'_>, call: &mut Call<'_>) {
        match &self.handlers[pipeline.0] {
            Handler::Root => root(pipeline, call),
            Handler::Body(handle) => call(&mut *handle.borrow_mut()),
            Handler::Request(store) | Handler::Step(store) => call(&mut *induction(store)),
        }
    }

    fn scopes(&self) -> impl Iterator<Item = &StoreCell> {
        self.handlers.iter().filter_map(|handler| match handler {
            Handler::Request(store) => Some(store),
            _ => None,
        })
    }

    fn complete(&self, dispatcher: &Dispatcher, scope: &StoreCell, package: Option<WorkPackage>) {
        if let Some(package) = package {
            let mut pushes = dispatcher.pushes(package.pipeline);
            let store = induction(scope);
            if store.pushes_while_consuming() {
                pushes.push_final(&*store);
            }
            drop(store);
            dispatcher.land(pushes);
            dispatcher.acknowledge(package);
        }
    }

    fn hold_followers(&self, dispatcher: &Dispatcher) {
        for scope in self.scopes() {
            induction(scope).hold_followers(dispatcher);
        }
    }

    pub(super) fn consume(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        package: WorkPackage,
    ) {
        match &self.handlers[package.pipeline.0] {
            Handler::Step(scope) => {
                induction(scope).complete_round();
                dispatcher.acknowledge(package);
                let completed = induction(scope).queue_package_round(dispatcher);
                self.complete(dispatcher, scope, completed);
            }
            Handler::Request(scope) => {
                let completed = induction(scope).begin_shared(dispatcher, package);
                self.complete(dispatcher, scope, completed);
            }
            Handler::Root | Handler::Body { .. } => consume_with(dispatcher, reach, package),
        }
        self.hold_followers(dispatcher);
    }

    pub(super) fn finish(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        pipeline: PipelineId,
        consumed: Option<TileGuard>,
    ) {
        match &self.handlers[pipeline.0] {
            Handler::Step(_) => dispatcher.finish(dispatcher.pushes(pipeline)),
            Handler::Request(scope) => induction(scope).begin_shared_finish(dispatcher, consumed),
            Handler::Root | Handler::Body { .. } => {
                finish_with(dispatcher, reach, pipeline, consumed)
            }
        }
        self.hold_followers(dispatcher);
    }

    pub(super) fn resume(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        let mut progressed = false;
        for scope in self.scopes() {
            let finished = induction(scope).take_shared_finish(dispatcher);
            if let Some((pipeline, consumed)) = finished {
                finish_with(dispatcher, reach, pipeline, consumed);
                induction(scope).unplace_shared();
                progressed = true;
                continue;
            }
            let pipelines = induction(scope).settlement_pipelines();
            let before = dispatcher.changes();
            push_held(dispatcher, reach, pipelines);
            // No other claim executes during this scope's publication pass on the serial
            // coordinator, so a generation change here belongs to these pushes.
            if dispatcher.changes() != before {
                progressed = true;
            } else {
                progressed |= induction(scope).release_followers(dispatcher);
            }
        }
        progressed
    }

    fn drive(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
        for pipeline in 0..self.roots {
            if dispatcher.is_source(PipelineId(pipeline)) {
                let mut input = None;
                reach(PipelineId(pipeline), &mut |breaker| {
                    input = Some(breaker.input_tiling(InputId::ONLY))
                });
                let input = input.expect("a planned source has a breaker input");
                dispatcher.start_source(PipelineId(pipeline), &input);
            }
        }
        loop {
            match dispatcher.try_claim(None) {
                Next::Package(package) => self.consume(dispatcher, reach, package),
                Next::Finish { pipeline, consumed } => {
                    self.finish(dispatcher, reach, pipeline, consumed)
                }
                Next::Wait(_) if self.resume(dispatcher, reach) => {}
                Next::Wait(_) => {
                    panic!("an acyclic run with no ready loop has a pipeline that may finish")
                }
                Next::Done => return,
                Next::Failed => panic!("a run on one thread fails only by panicking on it"),
            }
        }
    }
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
    /// One region per round, which the scope it runs in queues it, once every pipeline it reads
    /// has finished: the scope of a loop nested in the scope's loop, one row per round.
    Rounds,
}

/// The dispatcher over the pipelines `reads` describes, with every pipeline that reads another
/// parking the rows its pushes bring until the pipelines it reads have completed them, reading its
/// input whole where a pipeline it reads reaches it along no route, and queued at the start the
/// regions no push names ([`run_program`] says how). `kinds` says how each
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
    // A store completes its positions in order; a scope steps its store in order.
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
            started: false,
            held: false,
            follows: Vec::new(),
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
                for &follow in read {
                    dispatcher.follow(PipelineId(reader), PipelineId(follow));
                    planned[reader].follows.push(follow);
                }
                continue;
            }
            Consumes::Pushes => {}
        }
        // The nested loops' scopes it reads, whose finish of each round it waits for.
        let mut follows = Vec::new();
        // What the pushes of the pipelines it reads name of its input, `None` before any.
        let mut pushed: Option<TileGuard> = None;
        // Whether a pipeline it reads pushes nothing that reaches it, so it reads that one by pull.
        let mut unreached = false;
        for &read in read {
            // A nested loop's scope pushes its store once it is terminal, at its finish,
            // so a reader inside the cycle around it waits for its finish of each round instead.
            if kinds[read] == Consumes::Rounds {
                follows.push(read);
                continue;
            }
            let (pusher, _) =
                end_of(PipelineId(read)).unwrap_or_else(|| pushing_end(reach, PipelineId(read)));
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
        for &follow in &follows {
            dispatcher.follow(PipelineId(reader), PipelineId(follow));
            planned[reader].follows.push(follow);
        }
        dispatcher.wait_for_inputs(PipelineId(reader));
        planned[reader].held = true;
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
    /// Whether the run queued it a region at the start: what the ranges under it (`IterateExtent`)
    /// bring, less what the pushes of the pipelines it reads name.
    pub(crate) started: bool,
    /// Whether it holds the rows pushes bring until the pipelines it reads have completed them
    /// ([`Dispatcher::wait_for_inputs`]).
    pub(crate) held: bool,
    /// The nested loops' scopes it reads, whose finish of each round it waits for, taking no push
    /// of theirs ([`Dispatcher::follow`]).
    pub(crate) follows: Vec<usize>,
    /// For a loop's scope, its body planning tree in local pipeline order; empty otherwise.
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
    /// The shared cell owning a breaker subscription.
    Chain(BreakerHandle),
    /// The breaker of the sink of this index in `sinks` ([`SinkBreaker`]).
    ///
    /// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
    Sink(usize),
    /// The store of the cyclic fan-out `fan`, which steps itself.
    Store { fan: usize, store: StoreCell },
    /// The scope of the store of the cyclic fan-out `fan`, which runs in rounds: the planner's
    /// scope of index `scope`.
    Scope { fan: usize, scope: usize },
}

/// The placements a planning pass sets for its probes, which it clears when it drops: when the
/// pass returns, and when a probe unwinds, so no entry is left claiming a pipeline of a pass that
/// did not finish.
#[cfg(test)]
struct ClearsPlacements<'p>(&'p [Option<Placement>]);

#[cfg(test)]
impl Drop for ClearsPlacements<'_> {
    fn drop(&mut self) {
        for placement in self.0.iter().flatten() {
            placement.set(None);
        }
    }
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

/// A loop's scope as the planner walks it.
#[cfg(test)]
struct PlannedScope {
    store: StoreCell,
    /// The id of the store's cyclic fan-out, which the breakers inside its cycle read through a
    /// recurrence slot.
    fan: usize,
    /// The request pipeline's discovery index; `None` until the store's chain has been walked.
    pipeline: Option<usize>,
    /// The number of direct body pipelines before attachment to the shared dispatcher.
    count: usize,
    /// How many scopes it runs inside: its rounds run at paths of `depth + 1` keys.
    depth: usize,
}

/// One planning group's pipelines in local order, with the inputs to [`plan_edges`].
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

/// Pipelines discovered in a program's producer chains. An index here identifies a pipeline
/// during discovery; `local` identifies it within its root or body planning group. Attachment
/// assigns global runtime IDs after each group has been configured.
#[cfg(test)]
#[derive(Default)]
struct Planner {
    /// Per pipeline, its discovered dependencies, including reads across scope boundaries.
    reads: Vec<Vec<usize>>,
    located: Vec<Located>,
    names: Vec<String>,
    /// Per pipeline, the consumers of the ranges in its chain (`ProducerBase::leaf`), above
    /// every breaker beneath it.
    leaves: Vec<Vec<SharedConsumer>>,
    /// Per pipeline, its enclosing scope; `None` for the root planning group.
    within: Vec<Option<usize>>,
    /// Per pipeline, its local index within its planning group.
    local: Vec<usize>,
    /// Per pipeline, the placement of its breaker's entry, where the breaker is in a chain.
    placements: Vec<Option<Placement>>,
    /// The edges `(read, reader)` whose reader's breaker reads the breaker of `read` directly.
    direct: Vec<(usize, usize)>,
    scopes: Vec<PlannedScope>,
    /// The number of root pipelines before body graphs and store steps are appended.
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
    /// in its enclosing scope ([`dispatcher_of`](Self::dispatcher_of)); a pipeline
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
            below.read_once(under.pipelines);
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
        let pipeline = self.add(
            Located::Chain(handle.expect("a subscribed breaker owns a handle")),
            name,
            within,
            below,
        );
        placement.set(Some(PipelineId(self.local[pipeline])));
        self.placements[pipeline] = Some(placement);
        Beneath {
            pipelines: vec![(pipeline, true)],
            ..Beneath::default()
        }
    }

    /// The innermost scope being walked whose cycle contains the breaker at `producer`, or
    /// `None` for a breaker outside every scope.
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
        if read.store.borrow_mut().as_induction_store_mut().is_some() {
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
        visit_inputs_checked(&mut *store, &mut |role, input| {
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

    /// The request pipeline for the induction store `read` names, within the enclosing planning
    /// group `within` (`None` for the root). The cycle's breakers form a body group configured
    /// separately and attached to the shared dispatcher. The store's entry stays unplaced;
    /// request and step packages reach its controller through the execution handler. The request
    /// pipeline reads the pipelines beneath the cycle.
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
            visit_inputs_checked(&mut *store, &mut |role, input| {
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
            format!("InductionRequest({name})"),
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
        visit_inputs_checked(producer, &mut |_, input| {
            let under = self.beneath_cycle(input, fan);
            below.read_once(under.pipelines);
        });
        below
    }

    /// Plan a pipeline at `located`, named `name`, in the scope `within` (`None` for the root),
    /// reading what `below` holds, and answer its discovery index. Its local index counts the
    /// pipelines previously planned in that group.
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

    /// The scope containing `pipeline`, then each enclosing scope, ending at the root group.
    fn dispatchers_around(&self, pipeline: usize) -> Vec<Option<usize>> {
        let mut around = vec![self.within[pipeline]];
        while let Some(Some(scope)) = around.last() {
            around.push(self.within[self.scope_pipeline_of(*scope)]);
        }
        around
    }

    /// The representative of `pipeline` in planning group `dispatcher`: the pipeline itself,
    /// or the request pipeline of the enclosing scope visible in that group.
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

    /// Pipelines of scope `within` (`None` for the root) in local planning order. A read across
    /// scope boundaries becomes a dependency between their representatives in their common
    /// enclosing group. A request pipeline reads none of its own body pipelines.
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
    /// its rounds queue or push packages to ([`unrestated_in_rounds`](Self::unrestated_in_rounds)).
    pub(super) fn build_scope(
        &self,
        scope: usize,
        morsel_rows: usize,
        kept_scopes: &mut Vec<(usize, Vec<BreakerHandle>)>,
        runs: &mut InductionRuns,
    ) -> StoreCell {
        let pipelines = self.members(Some(scope));
        let members: Vec<Member> = pipelines
            .located
            .iter()
            .map(|located| match located {
                Located::Chain(handle) => Member::Chain(handle.clone()),
                Located::Scope { scope, .. } => {
                    Member::Scope(self.build_scope(*scope, morsel_rows, kept_scopes, runs))
                }
                Located::Store { .. } | Located::Sink(_) => {
                    unreachable!("a loop body has chains and induction requests")
                }
            })
            .collect();
        let store = self.scopes[scope].store.clone();
        let mut kept: Vec<usize> = (0..members.len()).collect();
        let (inner, planned, reads) = loop {
            let reads = reads_of_kept(&pipelines.reads, &kept);
            // A breaker in no pipeline keeps no entry: an id the planner gave it may be a kept
            // pipeline's here, and a probe would take it for an arrival there.
            for placement in pipelines.placements.iter().flatten() {
                placement.set(None);
            }
            let placed = ClearsPlacements(&pipelines.placements);
            for (at, &pipeline) in kept.iter().enumerate() {
                for placement in pipelines.placements[pipeline].iter() {
                    placement.set(Some(PipelineId(at)));
                }
            }
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                loop_scope::reach_member(&members[kept[pipeline.0]], call)
            };
            let names: Vec<String> = kept.iter().map(|&at| pipelines.names[at].clone()).collect();
            let leaves: Vec<_> = kept
                .iter()
                .map(|&at| pipelines.leaves[at].clone())
                .collect();
            let kinds: Vec<Consumes> = kept.iter().map(|&at| pipelines.kinds[at]).collect();
            // External reads target the request pipeline; body sources are queued by the
            // controller. Each nested induction store has one request pipeline, so no direct
            // body pipelines share a breaker's pushes.
            let (inner, planned) = plan_edges(
                &reads,
                &names,
                &leaves,
                &kinds,
                morsel_rows,
                &mut reach,
                &mut |pipeline| match &members[kept[pipeline.0]] {
                    Member::Scope(scope) => Some(induction(scope).pushing_end()),
                    Member::Chain(_) => None,
                },
            );
            drop(placed);
            let whole: Vec<usize> = planned
                .iter()
                .enumerate()
                .filter(|(at, plan)| plan.whole && pipelines.kinds[kept[*at]] == Consumes::Pushes)
                .map(|(at, _)| kept[at])
                .collect();
            if whole.is_empty() {
                break (inner, planned, reads);
            }
            kept.retain(|pipeline| !whole.contains(pipeline));
        };
        assert!(
            reads.iter().any(Vec::is_empty),
            "{} has a pipeline inside its cycle that reads none, the drive's",
            store.borrow().name()
        );
        let mut members: Vec<Option<Member>> = members.into_iter().map(Some).collect();
        let members: Vec<Member> = kept
            .iter()
            .map(|&at| members[at].take().expect("a pipeline is kept once"))
            .collect();
        // Reporting preserves the scope hierarchy; execution later remaps every body graph.
        let mut planned = planned;
        for (plan, member) in planned.iter_mut().zip(&members) {
            if let Member::Scope(scope) = member {
                plan.rounds = std::mem::take(
                    &mut induction(scope)
                        .run
                        .as_mut()
                        .expect("a nested run is planned")
                        .planned,
                );
            }
        }
        let starts: Vec<PipelineId> = (0..members.len())
            .filter(|&at| reads[at].is_empty() || !matches!(members[at], Member::Chain(_)))
            .map(PipelineId)
            .collect();
        let placements = kept
            .iter()
            .map(|&at| pipelines.placements[at].clone().into_iter().collect())
            .collect();
        let mut drives = Vec::new();
        for &start in &starts {
            if inner.is_source(start) && matches!(members[start.0], Member::Chain(_)) {
                let mut drive = false;
                loop_scope::reach_member(&members[start.0], &mut |breaker| {
                    drive = breaker
                        .as_producer()
                        .is_some_and(|producer| producer.next_position().is_some());
                });
                if drive {
                    drives.push(start);
                }
            }
        }
        let [drive] = drives.as_slice() else {
            panic!("an induction run has exactly one drive")
        };
        assert!(
            members.iter().all(|member| match member {
                Member::Scope(child) => !Rc::ptr_eq(&store, child),
                Member::Chain(_) => true,
            }),
            "run metadata does not retain its own store cell"
        );
        let run =
            loop_scope::InductionRun::new(inner, members, placements, starts, planned, *drive);
        runs.install(&store, run);
        kept_scopes.push((scope, induction(&store).chain_breakers()));
        store
    }

    /// Why the run cannot run a loop nested in another in rounds, or `None` where it can:
    /// an operator a round of the loop's scope pulls beneath the outermost keys restates no
    /// projection at the level it is pulled at ([`unrestated`]). `kept` holds each scope's
    /// breakers, as [`build_scope`](Self::build_scope) gathers them. The walk starts at each
    /// breaker a nested scope keeps, at the level of its rounds, and ends at every breaker that
    /// consumes, since that breaker's consume pulls its inputs; a breaker left in pull mode
    /// because its pipeline would read whole passes the pull on.
    fn refusal_of_nested(&self, kept: &[(usize, Vec<BreakerHandle>)]) -> Option<String> {
        let consuming: Vec<BreakerHandle> = (0..self.located.len())
            .filter(|&pipeline| self.within[pipeline].is_none())
            .filter_map(|pipeline| match &self.located[pipeline] {
                Located::Chain(handle) => Some(handle.clone()),
                _ => None,
            })
            .chain(kept.iter().flat_map(|(_, handles)| handles.iter().cloned()))
            .collect();
        kept.iter().find_map(|(scope, breakers)| {
            let planned = &self.scopes[*scope];
            if planned.depth == 0 {
                return None;
            }
            let level = CurryLevel::new(planned.depth);
            breakers
                .iter()
                .find_map(|handle| unrestated(&*handle.borrow(), Some(level), &consuming, true))
        })
    }
}

/// Why a round of a loop's scope cannot pull the chain at `producer`, or `None` where every
/// operator it pulls beneath the outermost keys restates the keys it is pulled at. `pulled` is the
/// level `producer` is pulled at, `None` where it is pulled whole, and each operator passes its
/// level to its inputs as it declares (`TileProducer::input_level`). A pull at the outermost keys
/// is walked too: every producer restates those keys, but an operator such as `Uncurry` pulls
/// its input beneath them. The walk ends at a recurrence slot or another store's read, whose
/// store answers from its snapshot, and, past the breaker it starts at (`start`), at every breaker
/// in `consuming`, whose consume pulls its inputs and whose own scope checks them.
#[cfg(test)]
fn unrestated(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    pulled: Option<CurryLevel>,
    consuming: &[BreakerHandle],
    start: bool,
) -> Option<String> {
    if producer.recurrence_of().is_some() || producer.store_read().is_some() {
        return None;
    }
    if let Some(pulled) = pulled
        && producer.restates().refuses(pulled)
    {
        let name = producer.name();
        let kind = name.split('#').next().unwrap_or(&name);
        return Some(format!(
            "{kind} in a loop's cycle is pulled at the keys of {pulled} and restates {}",
            producer.restates()
        ));
    }
    if pulled.is_none()
        || (!start
            && producer
                .base()
                .breaker_handle
                .as_ref()
                .and_then(std::rc::Weak::upgrade)
                .is_some_and(|handle| consuming.iter().any(|seen| Rc::ptr_eq(seen, &handle))))
    {
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
    /// The placements a planning pass sets are cleared when a probe in the pass unwinds.
    #[test]
    fn placements_a_pass_sets_are_cleared_when_it_unwinds() {
        use std::cell::Cell;
        use std::rc::Rc;
        let placement = || Some(Rc::new(Cell::new(None)));
        let placements: Vec<Option<Placement>> = vec![placement(), None, placement()];
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _placed = ClearsPlacements(&placements);
            for placement in placements.iter().flatten() {
                placement.set(Some(PipelineId(0)));
            }
            panic!("a probe panics");
        }));
        assert!(unwound.is_err());
        assert!(
            placements
                .iter()
                .flatten()
                .all(|placement| placement.get().is_none())
        );
    }

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
                            dispatcher.queue_for(reader, &guard);
                            dispatcher.record_complete(1, 0, Some(&guard));
                        } else {
                            dispatcher.record_complete(1, 0, Some(&guard));
                            dispatcher.queue_for(reader, &guard);
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
        dispatcher.queue_for(reader, &keys_between(0, 31));
        assert!(dispatcher.claim_of(reader).is_none());
        dispatcher.queue_round(reader, &keys_between(0, 31));
        let repeated = dispatcher
            .claim_of(reader)
            .expect("an explicit repeated round");
        assert_eq!(repeated.guard, keys_between(0, 31));
        dispatcher.acknowledge(repeated);
    }

    #[rstest::rstest]
    fn waiting_for_inputs_membership_compacts_and_drains(#[values(100, 1000, 10000)] count: u64) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1).unrecorded();
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        for key in 0..count {
            dispatcher.queue_for(reader, &keys_between(key, key));
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

    #[rstest::rstest]
    fn composition_rejects_a_graph_after_a_claim(#[values(false, true)] acknowledged: bool) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let graph = Dispatcher::new(vec![vec![]], 1);
        graph.notify(PipelineId(0), &keys_between(0, 0));
        let package = graph.claim_of(PipelineId(0)).unwrap();
        if acknowledged {
            graph.acknowledge(package);
        }
        let mut outer = Dispatcher::new(vec![], 1);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| outer.append_graph(graph)))
                .is_err()
        );
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

    #[rstest::rstest]
    fn overlapping_rows_are_queued_once_as_their_read_decides(
        #[values(false, true)] complete_first: bool,
    ) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        let first = keys_between(0, 2);
        let second = keys_between(1, 3);
        let beginning = keys_between(0, 0);
        let rest = keys_between(1, 3);
        let mut claimed = Vec::new();
        if complete_first {
            dispatcher.record_complete(1, 0, Some(&beginning));
        }
        dispatcher.queue_for(reader, &first);
        dispatcher.queue_for(reader, &second);
        while let Some(package) = dispatcher.claim_of(reader) {
            claimed.push(package.guard.clone());
            dispatcher.acknowledge(package);
        }
        assert_eq!(claimed.len(), usize::from(complete_first));
        if complete_first {
            assert_eq!(claimed[0], beginning);
        }
        dispatcher.record_complete(1, 0, Some(&beginning));
        while let Some(package) = dispatcher.claim_of(reader) {
            claimed.push(package.guard.clone());
            dispatcher.acknowledge(package);
        }
        assert_eq!(claimed, [beginning]);
        let before = dispatcher.changes();
        dispatcher.record_complete(1, 0, Some(&keys_between(0, 0)));
        assert_eq!(dispatcher.changes(), before);
        assert!(dispatcher.claim_of(reader).is_none());
        dispatcher.record_complete(1, 0, Some(&rest));
        while let Some(package) = dispatcher.claim_of(reader) {
            claimed.push(package.guard.clone());
            dispatcher.acknowledge(package);
        }
        assert_eq!(partition_gap(&keys_between(0, 3), &claimed), None);
    }

    #[rstest::rstest]
    fn repeated_rounds_wait_for_their_whole_row(#[values(false, true)] complete_first: bool) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        let row = keys_between(0, 3);
        dispatcher.record_complete(1, 0, Some(&keys_between(0, 1)));
        if complete_first {
            dispatcher.record_complete(1, 0, Some(&keys_between(2, 3)));
        }
        dispatcher.queue_round(reader, &row);
        if !complete_first {
            assert!(dispatcher.claim_of(reader).is_none());
            let before = dispatcher.changes();
            dispatcher.record_complete(1, 0, Some(&keys_between(0, 2)));
            assert_eq!(dispatcher.changes(), before);
            assert!(dispatcher.claim_of(reader).is_none());
            dispatcher.record_complete(1, 0, Some(&keys_between(3, 3)));
        }
        let package = dispatcher.claim_of(reader).expect("the row is complete");
        assert_eq!(package.guard, row);
        dispatcher.acknowledge(package);
        assert!(dispatcher.claim_of(reader).is_none());
        dispatcher.queue_round(reader, &row);
        let package = dispatcher
            .claim_of(reader)
            .expect("a round reads the row again");
        assert_eq!(package.guard, row);
        dispatcher.acknowledge(package);
        assert!(dispatcher.claim_of(reader).is_none());
    }

    /// A repeated read of a row appends a package of its own, but an append of a guard the region
    /// has no union with panics and leaves the queue as it was.
    #[test]
    fn a_repeated_read_that_panics_reserves_nothing() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let queue = Queue::new();
        assert!(queue.append_again(&keys_between(0, 1)));
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            queue.append_again(&TileGuard::Scalar(Predicate::True))
        }));
        assert!(
            unwound.is_err(),
            "a scalar guard has no union with a region of keys"
        );
        assert_eq!(queue.reserved(), 1);
        let state = queue.state.lock().unwrap_or_else(PoisonError::into_inner);
        assert_eq!(state.ready.len(), 1);
        assert_eq!(state.region, Some(keys_between(0, 1)));
    }

    /// A loop's rounds read one row again and again, and each round's package leaves no entry once
    /// it is acknowledged; the region stays the row.
    #[test]
    fn rounds_of_a_row_leave_no_queue_history() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX).unrecorded();
        let reader = PipelineId(1);
        dispatcher.wait_for_inputs(reader);
        let row = keys_between(0, 3);
        dispatcher.record_complete(1, 0, Some(&row));
        for _ in 0..1024 {
            dispatcher.queue_round(reader, &row);
            let package = dispatcher.claim_of(reader).expect("the round's package");
            assert_eq!(retained_package_guards(&dispatcher.states[1].queue), 1);
            dispatcher.acknowledge(package);
            assert_eq!(retained_package_guards(&dispatcher.states[1].queue), 0);
        }
        let state = dispatcher.states[1]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        assert_eq!(state.region, Some(row));
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
    fn repeated_rounds_reject_stale_or_mismatched_acknowledgements() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let queue = Queue::new();
        let guard = keys_between(0, 0);
        assert!(queue.append_again(&guard));
        let first = queue.claim(0, false, || true).unwrap();
        assert!(queue.acknowledge(&first, || {}));
        assert!(queue.append_again(&guard));
        let second = queue.claim(0, false, || true).unwrap();
        assert!(second.index > first.index);
        assert!(!queue.acknowledge(&first, || {}));
        let mut wrong = second.clone();
        wrong.guard = keys_between(1, 1);
        assert!(!queue.acknowledge(&wrong, || {}));
        assert_eq!(retained_package_guards(&queue), 1);
        assert!(queue.acknowledge(&second, || {}));
        assert!(!queue.acknowledge(&second, || {}));
        assert_eq!(retained_package_guards(&queue), 0);
        assert_eq!(queue.region(), Some(guard));
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
        assert!(!queue.append_again(&keys_between(0, 0)));
        assert_eq!(queue.region(), Some(keys_between(0, 4)));
    }

    #[test]
    fn an_empty_dispatcher_is_done_until_a_pipeline_is_added() {
        let mut dispatcher = Dispatcher::new(vec![], 1);
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
        let source = dispatcher.add_pipeline(vec![]);
        assert!(matches!(dispatcher.try_claim(None), Next::Wait(_)));
        dispatcher.close(source);
        assert!(matches!(dispatcher.try_claim(None), Next::Finish { .. }));
        dispatcher.finish(dispatcher.pushes(source));
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }

    #[rstest::rstest]
    fn manual_finish_respects_the_serial_coordinators_hold(#[values(false, true)] released: bool) {
        let dispatcher = Dispatcher::new(vec![vec![]], 1);
        let source = PipelineId(0);
        dispatcher.close(source);
        dispatcher.hold_pipeline(source, true);
        if released {
            dispatcher.hold_pipeline(source, false);
            assert!(dispatcher.begin_finish(source).is_none());
            dispatcher.finish(dispatcher.pushes(source));
            assert!(matches!(dispatcher.try_claim(None), Next::Done));
        } else {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    dispatcher.begin_finish(source);
                }))
                .is_err()
            );
            assert!(dispatcher.states[0].phase.load() == Phase::Running);
            assert!(matches!(dispatcher.try_claim(None), Next::Failed));
        }
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

#[cfg(test)]
mod planner_walk_tests {
    use super::*;
    use crate::interpreter::Tile;
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
    /// input there, so `unrestated` names an input that restates only the outermost keys.
    #[test]
    fn a_breaker_pulled_beneath_the_outermost_keys_finds_an_input_that_restates_none() {
        let memo = memo_over_outermost();
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a loop's cycle is pulled at the keys of level 1 and restates \
                 the outermost keys only"
            )
        );
    }

    /// A breaker that consumes ends the walk: its consume pulls its inputs, and its own scope
    /// checks them. An inline breaker passes the read on to its inputs.
    #[test]
    fn a_placed_breaker_ends_the_walk_and_an_inline_one_passes_it_on() {
        let (_, tiling) = two_levels_of_ints();
        let inner = crate::interpreter::tile_operators::share_breaker(memo_over_outermost());
        let mut handle = None;
        inner.visit_input_producers(&mut |_, input| {
            handle = input
                .base()
                .breaker_handle
                .as_ref()
                .and_then(std::rc::Weak::upgrade);
        });
        let outer = MemoProducer::over(inner, &tiling);
        let level = Some(CurryLevel::new(1));
        assert_eq!(
            unrestated(
                &outer,
                level,
                &[handle.expect("the inner breaker has a handle")],
                true
            ),
            None
        );
        assert!(
            unrestated(&outer, level, &[], true)
                .is_some_and(|why| why.starts_with("TestTile in a loop's cycle"))
        );
    }

    /// A breaker in no inner pipeline is pulled whole, so nothing beneath it is pulled at a
    /// round's paths.
    #[test]
    fn a_breaker_pulled_whole_finds_nothing_beneath_it() {
        let memo = memo_over_outermost();
        assert_eq!(unrestated(&memo, None, &[], true), None);
    }

    /// A producer that restates every level and pulls its one input a level beneath the level it
    /// is pulled at, whatever that input restates.
    struct Deepens {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    impl TileProducer for Deepens {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn restates(&self) -> crate::interpreter::Restates {
            crate::interpreter::Restates::Every
        }

        fn input_level(&self, _role: &str, level: CurryLevel) -> Option<CurryLevel> {
            Some(CurryLevel::new(level.index() + 1))
        }

        fn get_impl(&mut self, _guard: TileGuard) -> Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// A pull at the outermost keys is walked: an operator that pulls its input beneath the keys
    /// it is pulled at reaches an input that restates the outermost keys only at level 1.
    #[test]
    fn an_outermost_pull_that_an_operator_deepens_finds_an_input_that_restates_none() {
        let (tile, tiling) = two_levels_of_ints();
        let deepens = Deepens {
            base: ProducerBase::unowned(Deepens::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling.clone())),
        };
        let memo = MemoProducer::over(Box::new(deepens), &tiling);
        let why = unrestated(&memo, Some(CurryLevel::OUTERMOST), &[], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a loop's cycle is pulled at the keys of level 1 and restates the \
                 outermost keys only"
            )
        );
    }

    /// A collection three levels deep, `0 ↦ {0 ↦ {0 ↦ 10, 1 ↦ 11}, 1 ↦ {0 ↦ 20, 1 ↦ 21}}`, read
    /// through a producer that restates its outermost keys only and logs the guards it is pulled
    /// at.
    struct OutermostOnly {
        tile: Tile,
        tiling: Tiling,
        pulled: Rc<RefCell<Vec<TileGuard>>>,
    }

    impl OutermostOnly {
        fn new() -> Self {
            use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Tiling};
            use bit_set::BitSet;
            let tiling = Tiling::data_function(
                Extent::uint_range(1),
                Tiling::data_function(
                    Extent::uint_range(2),
                    Tiling::data_function(
                        Extent::uint_range(2),
                        Tiling::Scalar(Extent::Base(BaseType::Int)),
                    ),
                ),
            );
            let tile = Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::UInts(vec![0, 1]),
                    Box::new(Tile::grouped(
                        vec![0, 2],
                        ColumnValue::UInts(vec![0, 1, 0, 1]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 11, 20, 21]))),
                        Predicate::True,
                        BitSet::new(),
                    )),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            );
            Self {
                tile,
                tiling,
                pulled: Default::default(),
            }
        }
    }

    struct OutermostOnlyProducer {
        base: ProducerBase,
        tile: Tile,
        pulled: Rc<RefCell<Vec<TileGuard>>>,
    }

    impl crate::interpreter::tile_operators::TileOperator for OutermostOnly {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(
            &self,
            _visit: &mut dyn FnMut(crate::interpreter::operator_graph::InputEdgeSpec<'_>),
        ) {
        }

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut crate::interpreter::Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(OutermostOnlyProducer {
                base: ProducerBase::unowned(OutermostOnlyProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                pulled: self.pulled.clone(),
            })
        }
    }

    impl TileProducer for OutermostOnlyProducer {
        impl_producer_base!();

        fn get_impl(&mut self, guard: TileGuard) -> Tile {
            self.pulled.borrow_mut().push(guard.clone());
            let mut tile = self.tile.clone();
            tile.restrict_to(&guard.projection(&self.name()), self.tiling());
            tile
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// An `Uncurry` beneath a standing level, over an input that restates its outermost keys
    /// only, is pulled in a round at the pairs of a row. It pulls its input at the row, the level
    /// it declares, so the walk accepts it, and the walk and the pull agree on the level.
    #[test]
    fn an_uncurry_over_an_input_that_restates_the_outermost_keys_is_walked_at_its_pull() {
        use crate::interpreter::tile_operators::{TileOperator, Uncurry};
        use crate::interpreter::{Predicate, Projection, Scheduler, Value, tuple_field};
        let input = OutermostOnly::new();
        let pulled = input.pulled.clone();
        let mut uncurry = Uncurry::new_at(Box::new(input), CurryLevel::new(1));
        let mut producer = uncurry.subscribe(
            uncurry.tiling().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        );
        let round = CurryLevel::new(1);
        assert_eq!(unrestated(&*producer, Some(round), &[], true), None);
        let declared = producer.input_level("input", round);
        assert_eq!(declared, Some(CurryLevel::OUTERMOST));
        let pair = Value::Record(
            [
                (tuple_field(0), Value::UInt(1)),
                (tuple_field(1), Value::UInt(0)),
            ]
            .into_iter()
            .collect(),
        );
        let path = [Value::UInt(0), pair];
        let answer = producer
            .get(Projection::keys_at(round, Predicate::exactly(&path)).guard(producer.tiling()));
        assert_eq!(answer.paths_at(round), std::slice::from_ref(&path.to_vec()));
        let [guard] = pulled.borrow().clone().try_into().expect("one pull");
        assert_eq!(
            Projection::of(&guard).expect("a projection").level(),
            declared
        );
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

        fn get_impl(&mut self, _guard: TileGuard) -> Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// An input a producer reads whole is pulled at no level beneath the outermost keys, so
    /// `unrestated` names none that restates the outermost keys only.
    #[test]
    fn an_input_read_whole_finds_nothing() {
        let (tile, tiling) = two_levels_of_ints();
        let reads_whole = ReadsWhole {
            base: ProducerBase::unowned(ReadsWhole::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling.clone())),
        };
        let memo = MemoProducer::over(Box::new(reads_whole), &tiling);
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[], true);
        assert_eq!(why, None);
    }
}

#[cfg(test)]
/// The reads of the pipelines `kept` holds, numbered by their place in it: a read of a pipeline
/// that is not kept is a read of the pipelines it reads.
fn reads_of_kept(reads: &[Vec<usize>], kept: &[usize]) -> Vec<Vec<usize>> {
    fn expand(reads: &[Vec<usize>], kept: &[usize], read: usize, into: &mut Vec<usize>) {
        match kept.iter().position(|&pipeline| pipeline == read) {
            Some(at) if !into.contains(&at) => into.push(at),
            Some(_) => {}
            None => {
                for &beneath in &reads[read] {
                    expand(reads, kept, beneath, into);
                }
            }
        }
    }
    kept.iter()
        .map(|&pipeline| {
            let mut into = Vec::new();
            for &read in &reads[pipeline] {
                expand(reads, kept, read, &mut into);
            }
            into
        })
        .collect()
}

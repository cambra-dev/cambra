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

pub(crate) mod loop_scope;
mod plan;

pub use plan::{
    Ended, Planned, Refused, Run, RunObserver, Targets, run_program, run_program_into,
    run_program_polling,
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

/// Where a pipeline is in the run. It is `Finishing` from the claim, or the
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
    /// Admission and transfers from waiting to ready share this lock with queue history.
    waiting_for_inputs: Vec<WaitingInput>,
    /// Cached union of guards waiting for input completion. Admission subtracts it without scanning the backlog.
    waiting_region: Option<TileGuard>,
}

impl QueueState {
    fn wait_for_inputs(&mut self, morsel: WaitingInput) {
        grow(&mut self.waiting_region, &morsel.guard);
        self.waiting_for_inputs.push(morsel);
    }
}

impl Queue {
    fn new() -> Self {
        Queue {
            state: Mutex::new(QueueState::default()),
            reserved: AtomicUsize::new(0),
        }
    }

    /// Append morsels partitioning a region no earlier append named. A closed queue takes nothing.
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
        let Some(first) = self.reserve(morsels.len()) else {
            return false;
        };
        for (index, morsel) in (first..).zip(morsels) {
            debug_assert!(
                state
                    .region
                    .as_ref()
                    .is_none_or(|region| region.intersect(morsel).is_empty()),
                "pipeline {pipeline} consumes each region once: {morsel:?} meets {:?}",
                state.region
            );
            grow(&mut state.region, morsel);
            state.ready.push_back((index, morsel.clone()));
        }
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
        let Some(index) = self.reserve(1) else {
            return false;
        };
        grow(&mut state.region, &fresh);
        state.ready.push_back((index, fresh));
        true
    }

    /// Append a repeated read of a loop's row, including its end, as a distinct package.
    fn append_again(&self, guard: &TileGuard) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.append_again_locked(&mut state, guard)
    }

    fn append_again_locked(&self, state: &mut QueueState, guard: &TileGuard) -> bool {
        let Some(index) = self.reserve(1) else {
            return false;
        };
        grow(&mut state.region, guard);
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
    /// Whether it reads its breaker's input whole rather than what the pipelines it reads push
    /// ([`read_whole`](Dispatcher::read_whole)).
    whole: bool,
    /// The pipelines it reads that it takes no push from, and that it waits to be quiescent before
    /// it takes a package ([`follow`](Dispatcher::follow)).
    follows: Vec<usize>,
    /// For a source, the most packages queued for it and not yet acknowledged that a notify finds
    /// before it queues more ([`limit`](Dispatcher::limit)); `usize::MAX` for none.
    limit: usize,
    /// The pipeline whose record of what it pushed this one's pushes read and grow: itself, or the
    /// first of the pipelines whose breaker this one shares
    /// ([`share_pushes`](Dispatcher::share_pushes)).
    pushes_with: usize,
    /// Whether it takes the arrivals of live sources although it reads pipelines
    /// ([`take_arrivals`](Dispatcher::take_arrivals)).
    arrivals: bool,
    /// The pipelines it reads whose pushes arrive as its own keys, which no arrival names: a push
    /// of one queues the rows it names fresh, though the pipeline takes arrivals
    /// ([`queue_pushes_of`](Dispatcher::queue_pushes_of)).
    pushed_rows: Vec<usize>,
    /// Whether arrivals wait until the pipelines it reads have completed them
    /// ([`wait_for_inputs`](Dispatcher::wait_for_inputs)).
    waits_for_inputs: bool,
    /// Whether it is a store's seed input, which the store's other pipelines read and wait for
    /// the consume of ([`opens_before`](Dispatcher::opens_before)).
    opens: bool,
    /// Per pipeline it reads, in the order of its `reads`, the region of its input that
    /// pipeline's pushes reach along routes that keep its keys, `None` where they reach all of
    /// it ([`reaches`](Dispatcher::reaches)).
    reach: Vec<Option<TileGuard>>,
    /// Per pipeline it reads, in the order of its `reads`, whether it completes the input only once
    /// it is whole ([`completes_whole_only`](Dispatcher::completes_whole_only)).
    whole_only: Vec<bool>,
    required_keys: Vec<Vec<Value>>,
    ingress: Option<std::ops::Range<usize>>,
}

/// A region awaiting input completion ([`Dispatcher::wait_for_inputs`]), and whether a release may hand out the part
/// of it that is complete and keep the rest. A morsel a source's notify cut counts as one of that
/// source's packages, and a row a loop's round queues is read for the row's end, which its reads
/// state only once they have completed all of it, so both are released whole.
#[derive(Debug)]
struct WaitingInput {
    guard: TileGuard,
    splits: bool,
}

/// A pipeline's queue, progress counters, and published regions, completion and input waits for one run.
struct PipelineState {
    queue: Queue,
    phase: AtomicPhase,
    /// How many of the pipelines it reads have not finished, plus one for the close of its
    /// arrivals where it takes arrivals and reads pipelines ([`Dispatcher::take_arrivals`]).
    /// Whichever brings it to zero closes the queue.
    unfinished: AtomicUsize,
    /// The region this pipeline's breaker has pushed to its reader, which each push grows by
    /// what it pushes. A push of a breaker's final guard pushes what is not in it.
    // shared-state-ok: the region a pipeline has pushed, which its pushes read and grow under the
    // lock; what crosses it is a guard naming a region, never a tile.
    pushed: Mutex<Option<TileGuard>>,
    /// Per source of its breaker's input, what that source has completed of it: one per pipeline it
    /// reads, in the order of its `reads`, then one for the ranges in its own chain
    /// ([`Completion`]).
    // shared-state-ok: guards naming regions of the pipeline's input, which the complete pushes
    // of its sources grow under the lock; never a tile.
    complete: Mutex<Vec<Completion>>,
    /// How many of the pipeline's packages have been acknowledged.
    acknowledged: AtomicUsize,
    /// Whether this pipeline waits for its loop's round to settle before following its reads.
    followers_held: AtomicBool,
    held: AtomicBool,
}

/// What one source of a pipeline's breaker's input has completed of that input: a pipeline it
/// reads, or the ranges in its own chain.
#[derive(Clone, Debug, Default)]
pub(crate) enum Completion {
    /// Nothing yet.
    #[default]
    Nothing,
    /// The region its complete pushes have named.
    Region(TileGuard),
    /// All of what it contributes: it is wholly complete, and a push of it reaches the input only
    /// widened, or it is read by pull, which reads all of it.
    Whole,
}

impl Completion {
    /// Whether it covers `guard`, a region of the input, as the end-of-run check reads it.
    #[cfg(debug_assertions)]
    pub(crate) fn covers(&self, guard: &TileGuard) -> bool {
        match self {
            Completion::Nothing => guard.is_empty(),
            Completion::Region(region) => guard_minus(guard, region).is_empty(),
            Completion::Whole => true,
        }
    }

    fn grown(self, guard: &TileGuard) -> Completion {
        match self {
            Completion::Whole => Completion::Whole,
            Completion::Nothing => Completion::Region(guard.clone()),
            Completion::Region(region) => Completion::Region(region.union(guard)),
        }
    }
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
    /// returns credit to a limited source, a finish, and a failure.
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
    /// pipeline may read several, and its queue closes at the finish of the last of them, and for
    /// one that takes arrivals beside them also at its close
    /// ([`take_arrivals`](Self::take_arrivals)). A pipeline in a cycle would wait for itself to
    /// finish.
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
            .enumerate()
            .map(|(pipeline, (reads, readers))| PipelineInfo {
                reads,
                readers,
                ordered: false,
                whole: false,
                follows: Vec::new(),
                limit: usize::MAX,
                pushes_with: pipeline,
                arrivals: false,
                pushed_rows: Vec::new(),
                waits_for_inputs: false,
                opens: false,
                reach: Vec::new(),
                whole_only: Vec::new(),
                required_keys: Vec::new(),
                ingress: None,
            })
            .collect();
        let states = infos
            .iter()
            .map(|info: &PipelineInfo| PipelineState::new(info.reads.len()))
            .collect();
        Self {
            morsel_rows,
            unfinished: AtomicUsize::new(infos.len()),
            infos,
            states,
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
                .chain(&mut info.pushed_rows)
            {
                *pipeline += offset;
            }
            info.pushes_with += offset;
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
            whole: false,
            follows: Vec::new(),
            limit: usize::MAX,
            pushes_with: pipeline,
            arrivals: false,
            pushed_rows: Vec::new(),
            waits_for_inputs: false,
            opens: false,
            reach: Vec::new(),
            whole_only: Vec::new(),
            required_keys: Vec::new(),
            ingress: None,
        });
        *self.unfinished.get_mut() += 1;
        PipelineId(pipeline)
    }

    /// Accept pushes at this entry only from the configured input graph.
    pub(crate) fn restrict_ingress(&mut self, pipeline: PipelineId, from: std::ops::Range<usize>) {
        assert!(
            from.start <= from.end && from.end <= self.infos.len(),
            "an ingress range names planned pipelines"
        );
        self.infos[pipeline.0].ingress = Some(from);
    }

    /// Hold a pipeline's packages and finish until it is activated by its execution handler.
    /// The serial coordinator changes holds between claims; a hold does not revoke a claim.
    pub(crate) fn hold_pipeline(&self, pipeline: PipelineId, held: bool) {
        if self.state(pipeline).held.swap(held, Ordering::SeqCst) != held {
            self.advance();
        }
    }

    /// The count of the dispatcher's changes so far ([`Generation`]): an equal count read twice
    /// says nothing was queued, consumed or finished between.
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

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader`, less
    /// what is queued for it already: at the start, what a range brings that no push names
    /// ([`run_program`]). A reader configured by [`wait_for_inputs`](Self::wait_for_inputs) waits for the regions that the pipelines it reads have not completed,
    /// and a release hands out the part they decide.
    ///
    /// # Panics
    ///
    /// When `reader`'s queue has closed: every pipeline it reads has finished.
    pub(crate) fn queue_for(&self, reader: PipelineId, guard: &TileGuard) {
        self.queue_in_current(reader, guard, false);
    }

    /// [`queue_for`](Self::queue_for) for a loop's round: the row of a nested loop's store, which
    /// follows the pipelines inside the cycle around it ([`follow`](Self::follow)), or a row the
    /// closing round has every inner pipeline read again. A reader that
    /// waits for inputs takes the row again whatever it took before, and only once the pipelines it reads
    /// have completed all of it, the row's end with its rows ([`WaitingInput`]).
    pub(crate) fn queue_round(&self, reader: PipelineId, guard: &TileGuard) {
        self.queue_in_current(reader, guard, true);
    }

    fn queue_in_current(&self, reader: PipelineId, guard: &TileGuard, round: bool) {
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
    pub(crate) fn is_source(&self, pipeline: PipelineId) -> bool {
        self.infos[pipeline.0].reads.is_empty()
    }

    /// Order `reader`'s rounds after `read`'s, a pipeline it reads, in a loop's scope: `reader`
    /// takes no push of `read`'s, and takes a package only once `read` is quiescent
    /// ([`quiescent`](Self::quiescent)), having run the round. A scope's planner orders two edges
    /// so, where a pipeline cannot wait for input completion: a nested loop's scope after the pipelines its rounds pull,
    /// and a reader after a nested loop's scope, which pushes its store only once it is terminal.
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

    /// Have every push of `read` to `reader`, which takes arrivals and waits for inputs
    /// ([`take_arrivals`](Self::take_arrivals), [`wait_for_inputs`](Self::wait_for_inputs)),
    /// bring the rows it names: `read`'s pushes arrive as `reader`'s own keys, as an arm of a
    /// concatenation, and no arrival names them.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`, takes no arrivals, or does not wait for inputs, where a push
    /// brings no row.
    pub fn queue_pushes_of(&mut self, reader: PipelineId, read: PipelineId) {
        let info = &mut self.infos[reader.0];
        assert!(
            info.reads.contains(&read.0) && info.arrivals && info.waits_for_inputs,
            "pipeline {} takes arrivals, waits for inputs, and reads pipeline {}, whose pushes it \
             queues",
            reader.0,
            read.0
        );
        info.pushed_rows.push(read.0);
    }

    /// Mark `pipeline`, which reads pipelines, as also taking the arrivals of live sources: it is
    /// notified and closed as a source is ([`notify`](Self::notify), [`close`](Self::close)), and
    /// its queue closes once both its close and the finishes of the pipelines it reads have
    /// happened. It takes an arrival once those pipelines have completed it ([`wait_for_inputs`](Self::wait_for_inputs)) or
    /// are quiescent ([`follow`](Self::follow)).
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline or takes arrivals already, and when a source has been
    /// notified or closed already.
    pub fn take_arrivals(&mut self, pipeline: PipelineId) {
        self.mark_arrivals(pipeline);
    }

    /// Park `pipeline`'s arrivals until the pipelines it reads have completed them: a notify of a
    /// region they have not all completed keeps its morsels out of the queue, and the complete push
    /// that covers a morsel appends it to the pipeline's queue
    /// ([`record_complete`](Self::record_complete)). A loop's scope or a transaction store, whose
    /// steps pull the pipelines it reads, takes each delivery so once what it pulls is final
    /// (`src/interpreter/design-dispatcher.md`, "Waiting for input completion").
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline, and when a source has been notified or closed already.
    pub fn wait_for_inputs(&mut self, pipeline: PipelineId) {
        let p = pipeline.0;
        assert!(
            self.states.iter().all(|pipeline| {
                pipeline.queue.reserved() == 0
                    && !pipeline
                        .queue
                        .state
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .arrivals_closed
            }),
            "pipeline {p} is configured to wait for inputs before any notify or close"
        );
        assert!(
            !self.infos[p].reads.is_empty(),
            "pipeline {p} waits for arrivals from the pipelines it reads"
        );
        self.infos[p].waits_for_inputs = true;
    }

    /// Mark `pipeline` as a store's seed input, which the store's other pipelines read: a store
    /// opens before it steps, so once `pipeline` has consumed a package, the seeds are read and
    /// the store is open, and each of its readers records it wholly complete at its finish, which
    /// makes their waiting inputs ready ([`wait_for_inputs`](Self::wait_for_inputs)). A writer's pipeline that
    /// reads its input whole takes it only once that record covers it, and one over a live source
    /// holds each delivery until then.
    ///
    /// # Panics
    ///
    /// When `pipeline` is read by no pipeline.
    pub fn opens_before(&mut self, pipeline: PipelineId) {
        assert!(
            !self.infos[pipeline.0].readers.is_empty(),
            "a store's seed input {} is read by the store's other pipelines",
            pipeline.0
        );
        self.infos[pipeline.0].opens = true;
    }

    /// Record that `read`, a pipeline `reader` reads, completes `reader`'s input only once it is
    /// whole: one path from it completes only part of what a row depends on, and another passes a
    /// complete region on ([`Routes::completing_part`]), so the union of what they pass names rows
    /// the other path has not completed. A complete push of it that is not whole records nothing.
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`.
    pub fn completes_whole_only(&mut self, reader: PipelineId, read: PipelineId) {
        let info = &mut self.infos[reader.0];
        let at = info
            .reads
            .iter()
            .position(|&r| r == read.0)
            .unwrap_or_else(|| panic!("pipeline {} reads pipeline {}", reader.0, read.0));
        if info.whole_only.len() < info.reads.len() {
            info.whole_only.resize(info.reads.len(), false);
        }
        info.whole_only[at] = true;
    }

    /// Record that the pushes of `read`, a pipeline `reader` reads, reach `region` of its input
    /// along routes that keep their keys, and no more of it: a row outside `region` does not depend
    /// on `read`, so it waits for nothing of it ([`wait_for_inputs`](Self::wait_for_inputs)). A read with no such record
    /// reaches all of the input, as one along a route that widens, or one read by pull, does.
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
    /// complete: per read, the rows it reaches that it has completed, and the rows it does not reach
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

    /// The complete part of a region that may split, or the whole region once complete otherwise.
    /// A round's row waits for its end as well as its values before it can be queued.
    fn ready_part(&self, reader: usize, guard: &TileGuard, splits: bool) -> TileGuard {
        match splits {
            true => self.complete_part(reader, guard),
            false if self.reads_complete(reader, guard) => guard.clone(),
            false => guard_minus(guard, guard),
        }
    }

    /// Queue `guard`, rows a push or the dispatcher's caller brings `reader`, which waits for inputs, where
    /// every pipeline it reads has completed them, and wait for the rest ([`wait_for_inputs`](Self::wait_for_inputs)). Of a
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

    /// Append the waiting morsels whose inputs are now complete to the reader’s
    /// queue ([`wait_for_inputs`](Self::wait_for_inputs)). A complete push lands before the pushing pipeline counts its
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
        let appended = match self.infos[reader].arrivals {
            true => {
                let morsels: Vec<TileGuard> =
                    released.into_iter().map(|(morsel, _)| morsel).collect();
                queue.append_locked(&mut queue_state, reader, &morsels)
            }
            // A round's row is read again whole ([`WaitingInput`]).
            false => released.iter().all(|(morsel, again)| match *again {
                true => queue.append_again_locked(&mut queue_state, morsel),
                false => queue.append_unqueued_locked(&mut queue_state, morsel),
            }),
        };
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

    fn mark_arrivals(&mut self, pipeline: PipelineId) {
        let p = pipeline.0;
        assert!(
            self.states.iter().all(|pipeline| {
                pipeline.queue.reserved() == 0
                    && !pipeline
                        .queue
                        .state
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .arrivals_closed
            }),
            "pipeline {p} takes arrivals before any notify or close"
        );
        let info = &mut self.infos[p];
        assert!(
            !info.reads.is_empty() && !info.arrivals,
            "pipeline {p} takes arrivals beside the pipelines it reads, once"
        );
        info.arrivals = true;
        // The progress was made before the mark, so its count gains the close of the arrivals.
        self.states[p].unfinished.fetch_add(1, Ordering::AcqRel);
    }

    /// Whether `pipeline` is notified and closed: a source, or a pipeline that takes arrivals
    /// beside the pipelines it reads ([`take_arrivals`](Self::take_arrivals)).
    fn takes_arrivals(&self, pipeline: usize) -> bool {
        self.infos[pipeline].reads.is_empty() || self.infos[pipeline].arrivals
    }

    /// End the arrivals of `pipeline`, which takes arrivals: a source's queue closes, and a
    /// pipeline that also reads pipelines counts the end toward its close
    /// ([`count_toward_close`](Self::count_toward_close)).
    fn end_arrivals(&self, pipeline: usize) {
        match self.infos[pipeline].reads.is_empty() {
            true => {
                self.states[pipeline].queue.close();
            }
            false => self.count_toward_close(pipeline),
        }
    }

    /// Count one feed of `reader`'s queue finished: a pipeline it reads, or the end of
    /// its arrivals. The last of them closes the queue.
    ///
    /// # Panics
    ///
    /// When the queue was closed already.
    fn count_toward_close(&self, reader: usize) {
        // The decrement orders the appends of every earlier event before the close.
        let unfinished = self.states[reader]
            .unfinished
            .fetch_sub(1, Ordering::AcqRel);
        debug_assert!(
            unfinished > 0,
            "pipeline {reader} counts each event its queue waits for once"
        );
        if unfinished != 1 {
            return;
        }
        let closed = self.states[reader].queue.close();
        self.ensure(closed, || {
            format!("pipeline {reader} receives packages once")
        });
    }

    /// Grow what `source` has completed of `reader`'s input by `guard`, or record it whole where
    /// `guard` is `None`. `source` is a pipeline `reader` reads, whose record every pipeline it
    /// reads that shares `source`'s breaker shares, since a store's pipelines push one store's
    /// complete region ([`share_pushes`](Self::share_pushes)); or `reader` itself, for the ranges
    /// in its own chain.
    fn record_complete(&self, reader: usize, source: usize, guard: Option<&TileGuard>) {
        let reads = &self.infos[reader].reads;
        // A store's complete push reaches its own pipelines around its recurrence, which is no
        // read: a pipeline of a store reads a sibling only for its seed input's consume
        // ([`opens_before`](Self::opens_before)), which records it whole.
        if guard.is_some()
            && source != reader
            && self.infos[source].pushes_with == self.infos[reader].pushes_with
        {
            return;
        }
        self.ensure(source == reader || reads.contains(&source), || {
            format!(
                "pipeline {source} pushes a complete region to pipeline {reader}, which reads it"
            )
        });
        let mut complete = self.states[reader]
            .complete
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if complete.len() <= reads.len() {
            complete.resize(reads.len() + 1, Completion::Nothing);
        }
        let slots: Vec<usize> = match source == reader {
            true => vec![reads.len()],
            false => (0..reads.len())
                .filter(|&at| self.infos[reads[at]].pushes_with == self.infos[source].pushes_with)
                .collect(),
        };
        let whole_only = &self.infos[reader].whole_only;
        for at in slots {
            if guard.is_some() && whole_only.get(at).copied().unwrap_or(false) {
                continue;
            }
            let before = std::mem::take(&mut complete[at]);
            complete[at] = match guard {
                Some(guard) => before.grown(guard),
                None => Completion::Whole,
            };
        }
        drop(complete);
        if self.infos[reader].waits_for_inputs {
            self.queue_ready_inputs(reader);
        }
    }

    /// Whether a claim may take `pipeline`'s packages: once every pipeline it follows
    /// ([`follow`](Self::follow)) is quiescent ([`quiescent`](Self::quiescent)).
    fn takes_from(&self, pipeline: usize) -> bool {
        let follows = &self.infos[pipeline].follows;
        follows.is_empty()
            || (!self.states[pipeline].followers_held.load(Ordering::SeqCst)
                && follows.iter().all(|&read| self.quiescent(read)))
    }

    /// The serial coordinator changes these holds between claims, after settling held pushes.
    /// A hold does not revoke a claim or wait for a worker already consuming a package.
    ///
    /// Hold the given pipelines that follow others ([`follow`](Self::follow)) from taking a
    /// package, or release them. A loop's round holds them while the pipelines they follow push
    /// what they complete. A breaker that pushes only what `push_held` asks it to, as `MapAggregate`,
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

    /// Mark `pipeline`, which reads a pipeline, as consuming its breaker's input whole, `input`
    /// cut one package per morsel ([`seed`]), in place of what the pipelines it reads push: the
    /// morsels are waiting for inputs from the start, and the complete push that leaves every pipeline it reads
    /// having completed them queues them ([`wait_for_inputs`](Self::wait_for_inputs)). A planner does so where no push
    /// reaches the reader restated in its keys, where two pipelines it reads can push one key, or
    /// where a pipeline it reads takes no push and names no region the planner could queue for the
    /// reader at the start (`run_program`). It takes no push ([`Landing::queue`]).
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
        assert!(
            self.states.iter().all(|pipeline| {
                pipeline.queue.reserved() == 0
                    && !pipeline
                        .queue
                        .state
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .arrivals_closed
            }),
            "pipeline {} reads its input whole from before any notify or close",
            pipeline.0
        );
        let info = &mut self.infos[pipeline.0];
        info.whole = true;
        info.waits_for_inputs = true;
        let mut state = self.states[pipeline.0]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        for guard in seed(input, self.morsel_rows) {
            state.wait_for_inputs(WaitingInput {
                guard,
                splits: true,
            });
        }
    }

    pub(crate) fn require_final_keys(
        &mut self,
        reader: PipelineId,
        source: PipelineId,
        keys: Vec<Value>,
    ) {
        let info = &mut self.infos[reader.0];
        let at = info
            .reads
            .iter()
            .position(|read| *read == source.0)
            .expect("a completion belongs to a read pipeline");
        info.required_keys.resize_with(info.reads.len(), Vec::new);
        info.required_keys[at] = keys;
        info.whole_only.resize(info.reads.len(), false);
        info.whole_only[at] = true;
    }

    fn land_completed_keys(&self, source: usize, keys: &[Value]) {
        if keys.is_empty() {
            return;
        }
        for &reader in &self.infos[source].readers {
            let info = &self.infos[reader];
            let required: Vec<&Value> = info
                .reads
                .iter()
                .enumerate()
                .filter(|(_, read)| {
                    self.infos[**read].pushes_with == self.infos[source].pushes_with
                })
                .flat_map(|(at, _)| info.required_keys.get(at).into_iter().flatten())
                .collect();
            if !required.is_empty() && required.iter().all(|key| keys.contains(key)) {
                self.record_complete(reader, source, None);
            }
        }
    }

    /// Mark `pipeline` as consuming its morsels one at a time, in the order they were queued, then
    /// its finish. Its breaker's state advances through them in order, as a loop's store completes
    /// its positions ascending.
    pub fn order(&mut self, pipeline: PipelineId) {
        self.infos[pipeline.0].ordered = true;
    }

    /// Mark `pipelines` as the pipelines of one breaker, each consuming an input of its own: their
    /// pushes read and grow one record of what the breaker pushed, the first pipeline's, so a
    /// region one of them pushed is pushed by none of the others.
    ///
    /// # Panics
    ///
    /// When `pipelines` is empty, or one of them shares another breaker's pushes already.
    pub fn share_pushes(&mut self, pipelines: &[PipelineId]) {
        let first = pipelines
            .first()
            .expect("a breaker's pushes are shared by its pipelines, of which it has one at least")
            .0;
        for pipeline in pipelines {
            let info = &mut self.infos[pipeline.0];
            assert_eq!(
                info.pushes_with, pipeline.0,
                "pipeline {} already shares the pushes of another breaker's pipelines",
                pipeline.0
            );
            info.pushes_with = first;
        }
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
            completed_keys: Vec::new(),
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

    /// Queue a source pipeline's input and close the source: `input`, the
    /// tiling its breaker's input answers, less `released`, what the breaker's input has already
    /// released, as one package per morsel ([`seed`]). A run's first start passes nothing
    /// released; a run after a pause or a reload starts over a breaker that consumed, and queues
    /// it nothing it has finished with. It queues as [`notify`](Self::notify) would, without
    /// waiting for any limit, then [`close`](Self::close)s the source.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline, or is closed, and where the guard algebra has no exact
    /// difference of a morsel and `released` ([`guard_minus`]).
    pub fn start_source(&self, pipeline: PipelineId, input: &Tiling, released: &TileGuard) {
        self.ensure(self.infos[pipeline.0].reads.is_empty(), || {
            format!(
                "pipeline {} starts whole only as a source, which reads no pipeline",
                pipeline.0
            )
        });
        let left = guard_minus(&input.universal_guard(), released).closed_over(input);
        let morsels: Vec<TileGuard> = seed(input, self.morsel_rows)
            .iter()
            .map(|morsel| guard_minus(morsel, released).closed_over(input))
            .filter(|morsel| !morsel.is_empty())
            .collect();
        debug_assert!(
            partition_gap(&left, &morsels).is_none(),
            "the morsels of a source's unreleased input partition it: {}",
            partition_gap(&left, &morsels).unwrap_or_default()
        );
        self.append_to_source(pipeline, &morsels);
        self.close(pipeline);
    }

    /// Queue `guard`, a region of a source pipeline's input that has arrived, as one package per
    /// morsel: every `morsel_rows` positions, where `guard` names finite runs of positions
    /// (`Value::UInt` keys), and whole otherwise. The workers claim them as they are queued.
    ///
    /// A source [limited](Self::limit) to as many packages outstanding as it has waits until one
    /// is acknowledged, so the thread that notifies is held back by the workers. After a failure
    /// it returns at once, having queued nothing.
    ///
    /// # Panics
    ///
    /// When `pipeline` takes no arrivals ([`take_arrivals`](Self::take_arrivals))
    /// or is closed; in a debug build, when `guard` meets a region queued for a source before.
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
        let info = &self.infos[pipeline.0];
        debug_assert!(
            info.waits_for_inputs || info.reads.iter().all(|read| info.follows.contains(read)),
            "pipeline {} does not wait for input completion, so it takes one only once every pipeline it reads is \
             quiescent, which it follows",
            pipeline.0
        );
        // A limit is a source's alone (`limit`), whose every package its notifies queue.
        if info.limit != usize::MAX && self.state(pipeline).outstanding() >= info.limit {
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

    /// Refuse `pipeline` unless it takes arrivals: a source, one that reads no pipeline, or one
    /// that takes arrivals beside the pipelines it reads ([`take_arrivals`](Self::take_arrivals)).
    fn ensure_source(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.takes_arrivals(p), || {
            format!(
                "pipeline {p} is queued arrivals only as a source, which reads no pipeline, or \
                 as a pipeline that takes arrivals beside the pipelines it reads"
            )
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
        let ready;
        let morsels = if self.infos[p].waits_for_inputs {
            let (complete, incomplete): (Vec<TileGuard>, Vec<TileGuard>) = morsels
                .iter()
                .cloned()
                .partition(|morsel| self.reads_complete(p, morsel));
            for guard in incomplete {
                admission.wait_for_inputs(WaitingInput {
                    guard,
                    splits: false,
                });
            }
            ready = complete;
            &ready[..]
        } else {
            morsels
        };
        if morsels.is_empty() {
            return;
        }
        let appended = queue.append_locked(&mut admission, p, morsels);
        self.ensure(appended, || {
            format!("pipeline {p} is queued nothing once it is closed")
        });
        self.advance();
    }

    /// Close a pipeline that takes arrivals: nothing more of its input arrives. A source's queue
    /// closes; one that takes arrivals beside the pipelines it reads counts the close toward its
    /// queue's close. A claim never finishes a source before its close, so workers may claim
    /// before the sources start; they wait until then.
    ///
    /// # Panics
    ///
    /// When `pipeline` takes no arrivals ([`take_arrivals`](Self::take_arrivals)), or is closed
    /// already.
    pub fn close(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        let state = self.state(pipeline);
        self.ensure(self.takes_arrivals(p), || {
            format!(
                "pipeline {p} closes its arrivals only as a source, which reads no pipeline, or as \
                 a pipeline that takes arrivals beside the pipelines it reads"
            )
        });
        let mut admission = state
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        self.ensure(!admission.arrivals_closed, || {
            format!("pipeline {p} closes its queue once")
        });
        admission.arrivals_closed = true;
        self.end_arrivals(p);
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
        self.land_completed_keys(p, &pushes.completed_keys);
        if morsels.is_empty() {
            return;
        }
        self.ensure(self.states[p].phase.load() != Phase::Finished, || {
            format!("pipeline {p} lands its pushes before it finishes")
        });
        self.land_in(p, &morsels, pushes.to.as_ref());
        self.advance();
    }

    /// Push `complete`, the region of its keys `pipeline`'s breaker has completed, through `to`, its
    /// breaker's consumer, which restates it as each operator on the way completes
    /// ([`Landing::is_complete`]), and record what reaches each reader's entry
    /// ([`complete_of`](Self::complete_of)).
    ///
    /// Where `complete` is every key, each reader the push reached no entry of reads `pipeline` by
    /// pull, as a loop's rounds pull a sum its body reads from outside the loop's cycle, which
    /// reads all of it: it records `pipeline` whole.
    /// `pipeline` is the pushing pipeline, or, for a range in its own chain, the pipeline itself.
    fn land_complete(
        &self,
        pipeline: usize,
        complete: Option<&Projection>,
        to: Option<&SharedConsumer>,
    ) {
        self.land_complete_from(pipeline, complete, to, true);
    }

    /// Push `complete`, the region of its keys a range in `pipeline`'s chain has completed, through
    /// `to`, the range's consumer, and record what reaches each pipeline's entry as complete by the
    /// ranges in that pipeline's own chain ([`complete_of`](Self::complete_of)): a range can reach
    /// the entry of a pipeline beside its own, as the rows of a store per row reach the reader of
    /// the store.
    pub(crate) fn land_range_complete(
        &self,
        pipeline: PipelineId,
        complete: &Projection,
        to: &SharedConsumer,
    ) {
        self.land_complete_from(pipeline.0, Some(complete), Some(to), false);
    }

    /// [`land_complete`](Self::land_complete), applying its rule for readers a push reaches no
    /// entry of only where `pulled` says the push is a breaker's, which its readers read.
    fn land_complete_from(
        &self,
        pipeline: usize,
        complete: Option<&Projection>,
        to: Option<&SharedConsumer>,
        pulled: bool,
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
                range: !pulled,
            },
            from: pipeline,
            widened: false,
        };
        to.borrow_mut().notify(complete, &mut landing);
        let Target::Completion { reached, .. } = landing.target else {
            unreachable!("a complete landing stays one");
        };
        if whole && pulled {
            for &reader in &self.infos[pipeline].readers {
                if !reached.contains(&reader) {
                    self.record_complete(reader, pipeline, None);
                }
            }
        }
    }

    /// What `source` has completed of `reader`'s breaker's input: a pipeline `reader` reads, or
    /// `reader` itself for the ranges in its own chain, as the end-of-run check reads it.
    ///
    /// # Panics
    ///
    /// When `source` is neither `reader` nor a pipeline it reads.
    #[cfg(debug_assertions)]
    pub(crate) fn complete_of(&self, reader: PipelineId, source: PipelineId) -> Completion {
        let reads = &self.infos[reader.0].reads;
        let at = match source.0 == reader.0 {
            true => reads.len(),
            false => reads
                .iter()
                .position(|&r| r == source.0)
                .unwrap_or_else(|| panic!("pipeline {} reads pipeline {}", reader.0, source.0)),
        };
        self.states[reader.0]
            .complete
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(at)
            .cloned()
            .unwrap_or_default()
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
                    to.borrow_mut().notify(&region, &mut landing);
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
    /// begun to finish; and where the pipeline finishes with rows waiting for inputs.
    pub fn finish(&self, mut pushes: Pushes<'_>) {
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
        self.land_complete(p, complete.as_ref(), pushes.to.as_ref());
        self.land_completed_keys(p, &pushes.completed_keys);
        // At its finish every pipeline it reads has completed all of what it reaches (the
        // planner's end-of-run check), so nothing stays waiting for inputs.
        {
            let queue_state = self.states[p]
                .queue
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            self.ensure(queue_state.waiting_for_inputs.is_empty(), || {
                format!(
                    "pipeline {p} finishes with rows waiting for inputs that the pipelines it reads never \
                     complete: {:?}",
                    queue_state.waiting_for_inputs
                )
            });
        }
        // The store's own pipelines wait for its seed input's consume; a reader of the store
        // reads that pipeline too, but waits for what the store completes.
        if self.infos[p].opens {
            for &reader in &self.infos[p].readers {
                if self.infos[reader].pushes_with == self.infos[p].pushes_with {
                    self.record_complete(reader, p, None);
                }
            }
        }
        self.land_in(p, &morsels, pushes.to.as_ref());
        for &reader in &self.infos[p].readers {
            self.count_toward_close(reader);
        }
        self.unfinished.fetch_sub(1, Ordering::AcqRel);
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

    /// Finish `pipeline` as a claim does, with `push` in place of the breaker: begin the finish,
    /// let `push` push, and mark the pipeline finished. A source pipeline is closed first,
    /// whatever was queued for it.
    #[cfg(test)]
    pub(crate) fn finish_by_hand(&self, pipeline: PipelineId, push: impl FnOnce(&mut Pushes<'_>)) {
        if self.takes_arrivals(pipeline.0)
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

/// `guard`, `None` where it is empty.
fn nonempty(guard: TileGuard) -> Option<TileGuard> {
    (!guard.is_empty()).then_some(guard)
}

/// Grow `region` by `guard`.
fn grow(region: &mut Option<TileGuard>, guard: &TileGuard) {
    *region = Some(match region.take() {
        None => guard.clone(),
        Some(region) => region.union(guard),
    });
}

/// The rows of `rows`, a guard of `input`, that `released` does not name, closed over `input`
/// (`TileGuard::closed_over`): where a row's level is a finite range of positions, what the input
/// released through the row's last position covers its paths past it. `None` for none.
///
/// # Panics
///
/// Where the guard algebra has no exact difference of the two ([`guard_minus`]).
fn unreleased(rows: &TileGuard, released: &TileGuard, input: &Tiling) -> Option<TileGuard> {
    if released.is_universal() {
        return None;
    }
    nonempty(guard_minus(rows, released).closed_over(input))
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
/// ([`Consumer::notify`]), each operator on the way restates it in its own keys, and the [`Entry`] of
/// each breaker it reaches queues it for that breaker's pipeline.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    pipeline: usize,
    morsels: Vec<TileGuard>,
    /// The region of its keys the breaker has completed, as a projection, which climbs the
    /// consumer chain beside the morsels ([`Landing::is_complete`]); `None` where it pushed none.
    complete: Option<Projection>,
    completed_keys: Vec<Value>,
    /// The consumer the morsels climb, the pushing breaker's.
    to: Option<SharedConsumer>,
}

impl Pushes<'_> {
    /// Push what `breaker` has completed and the pipeline has not pushed before, its final guard
    /// less the region pushed, for the pipelines that read it: one package per morsel the breaker
    /// cuts it into, in the breaker's order. A push of nothing new pushes nothing, and so does a
    /// breaker no pipeline reads. The difference and the region's growth are one step under the
    /// region's lock, so two pushes of one pipeline from two threads push disjoint regions, and a
    /// finish pushes only what no consume pushed.
    ///
    /// # Panics
    ///
    /// Where the guard algebra has no exact difference of the two ([`guard_minus`]); in a debug
    /// build, when the morsels do not partition what is pushed ([`partition_gap`]).
    pub fn push_final<B: BreakingProducer + ?Sized>(&mut self, breaker: &B) {
        if self.dispatcher.infos[self.pipeline].readers.is_empty() {
            return;
        }
        self.completed_keys = breaker.completed_keys().to_vec();
        let to = breaker.base().downstream.clone();
        self.dispatcher.ensure(to.is_some(), || {
            format!(
                "{}, which pipeline {} reads, pushes to a consumer",
                breaker.name(),
                self.pipeline
            )
        });
        self.to = to;
        // The complete region is the breaker's statement of it, released or not: a released key
        // stays complete. A region no projection spells is pushed as nothing complete, which
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
        let mut pushed = self.dispatcher.states[self.dispatcher.infos[self.pipeline].pushes_with]
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
    /// Records each, for a planner that probes which region of a reader's input a pipeline's push
    /// names; which edges keep keys the planner reads off [`Routes`].
    Probe(Vec<Arrival>),
    /// Records each, as `Probe` does, for a push restated as a wholly complete region is: the
    /// region of a reader's input a pipeline can ever decide ([`Dispatcher::reaches`]).
    ProbeCompletion(Vec<Arrival>),
    /// Grows, for each, what the pushing pipeline has completed of the reader's input
    /// ([`Dispatcher::complete_of`]), and queues nothing. `whole` says the pushing pipeline is
    /// wholly complete, and `reached` lists the readers whose entry the push reached.
    Completion {
        dispatcher: &'d Dispatcher,
        whole: bool,
        reached: Vec<usize>,
        /// Whether a range pushes it, which counts as a range in the chain of each pipeline whose
        /// entry it reaches.
        range: bool,
    },
}

/// A region a probing push brought to an [`Entry`].
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
            Target::Probe(_) | Target::ProbeCompletion(_) => true,
        }
    }

    pub(crate) fn is_delivery(&self) -> bool {
        matches!(
            self.target,
            Target::Queue { .. } | Target::Completion { .. }
        )
    }

    /// A landing that records where `from`'s push arrives, and queues nothing.
    pub(crate) fn probe(from: PipelineId) -> Landing<'static> {
        Landing {
            target: Target::Probe(Vec::new()),
            from: from.0,
            widened: false,
        }
    }

    /// A landing that records where `from`'s push of a wholly complete region arrives, and queues
    /// nothing.
    pub(crate) fn probe_complete(from: PipelineId) -> Landing<'static> {
        Landing {
            target: Target::ProbeCompletion(Vec::new()),
            from: from.0,
            widened: false,
        }
    }

    /// What a probing landing recorded.
    pub(crate) fn arrivals(self) -> Vec<Arrival> {
        match self.target {
            Target::Probe(arrivals) | Target::ProbeCompletion(arrivals) => arrivals,
            Target::Queue { .. } | Target::Completion { .. } => {
                panic!("only a probing landing records arrivals")
            }
        }
    }

    /// Whether the region climbing is a complete region rather than a change: an operator restates
    /// a complete region by keeping what it names where it keeps the keys, and where it widens them
    /// by naming nothing until the region is every key, since each of its keys depends on every
    /// key of its input.
    pub fn is_complete(&self) -> bool {
        matches!(
            self.target,
            Target::Completion { .. } | Target::ProbeCompletion(_)
        )
    }

    /// Whether the region climbing is a complete region of a source that is wholly complete: an
    /// operator that widens its input's keys passes it as every key, since what that source
    /// contributes to each of the operator's keys is complete, and the reader intersects what its
    /// other sources complete.
    pub fn is_wholly_complete(&self) -> bool {
        matches!(
            self.target,
            Target::Completion { whole: true, .. } | Target::ProbeCompletion(_)
        )
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader`, less
    /// what is queued for it already: a push that reaches a breaker along two
    /// paths, as a filter reads one memo for its values and its predicate, is queued once. A
    /// reader that reads its input whole ([`Dispatcher::read_whole`]) takes no push, widened or
    /// not, and nor does one that follows the pipeline that pushed ([`Dispatcher::follow`]). A
    /// reader configured by [`Dispatcher::wait_for_inputs`] queues the rows a push brings once their inputs complete,
    /// and nothing for a widened push or one to a reader that takes arrivals, but for a push of a
    /// pipeline whose rows arrive as the reader's own keys ([`Dispatcher::queue_pushes_of`]).
    ///
    /// # Panics
    ///
    /// When `reader` does not read the pipeline that pushed, or has begun to finish;
    /// when the push was widened on its way to a reader that neither waits for inputs nor reads its input
    /// whole; and where the
    /// guard algebra has no exact difference of `guard` and what is queued ([`guard_minus`]).
    pub fn queue(&mut self, reader: PipelineId, guard: &TileGuard) {
        let dispatcher = match &mut self.target {
            Target::Queue { dispatcher } => *dispatcher,
            Target::Probe(arrivals) | Target::ProbeCompletion(arrivals) => {
                arrivals.push(Arrival {
                    pipeline: reader,
                    guard: guard.clone(),
                });
                return;
            }
            Target::Completion {
                dispatcher,
                whole,
                reached,
                range,
            } => {
                reached.push(reader.0);
                let source = match range {
                    true => reader.0,
                    false => self.from,
                };
                // A region that names the entry's input whole is the source wholly complete,
                // whatever the entry's tiling: a store's seed entry is one value in front of a
                // pipeline whose input is the loop's positions. A wholly complete source is, along
                // whatever its push was restated to on the way, as an arm of a union restates it
                // under its tag.
                let guard = (!(*whole || guard.is_universal())).then_some(guard);
                return dispatcher.record_complete(reader.0, source, guard);
            }
        };
        let (from, r) = (self.from, reader.0);
        dispatcher.state(reader);
        dispatcher.ensure(dispatcher.infos[r].reads.contains(&from), || {
            format!("pipeline {from} pushes to pipeline {r}, which reads it")
        });
        let info = &dispatcher.infos[r];
        // A reader that reads its input whole takes no push, and a nested loop's scope, or a
        // reader that waits for one, takes its rows in rounds.
        if info.whole || info.follows.contains(&from) {
            return;
        }
        let queue = &dispatcher.states[r];
        dispatcher.ensure(queue.phase.load() == Phase::Running, || {
            format!("pipeline {r} receives packages before it finishes")
        });
        // A reader that waits for inputs reads each row once, when every pipeline it reads has completed it:
        // a push brings the rows it names, widened or not, less what a push brought before, and
        // the complete pushes release them ([`Dispatcher::wait_for_inputs`]).
        if info.waits_for_inputs {
            if !info.arrivals || (!self.widened && info.pushed_rows.contains(&from)) {
                dispatcher.queue_or_wait_for_inputs(r, guard, false);
            }
            return;
        }
        dispatcher.ensure(!self.widened, || {
            format!(
                "a push of pipeline {from} is widened to `Everything` on its way to pipeline {r}, \
                 which neither waits for inputs nor reads its input whole"
            )
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
            Target::Queue { dispatcher, .. } | Target::Completion { dispatcher, .. } => {
                dispatcher.ensure(false, || message)
            }
            Target::Probe(_) | Target::ProbeCompletion(_) => panic!("{message}"),
        }
    }
}

/// The entries a push of one pipeline's keys reaches, and whether each path keeps those keys, as
/// the consumers on the way declare ([`Consumer::route`]). Nothing is pushed: each consumer states
/// how it passes any push on.
pub struct Routes {
    widened: bool,
    completes_part: bool,
    final_key: Option<Value>,
    reached: Vec<Route>,
}

/// One path of a push to the entry of a pipeline ([`Routes`]).
pub(crate) struct Route {
    /// The pipeline whose entry the path reaches.
    pub(crate) pipeline: PipelineId,
    /// Whether every operator on the path keeps the pushing pipeline's keys, restated as its own
    /// or under a tag, so that a push of some keys reaches the entry as those keys.
    pub(crate) keeps_keys: bool,
    /// Whether the complete region the path passes on names only part of what a row it reaches
    /// depends on ([`Routes::completing_part`]).
    pub(crate) completes_part: bool,
    pub(crate) final_key: Option<Value>,
}

impl Routes {
    /// No path walked yet.
    pub(crate) fn new() -> Self {
        Routes {
            widened: false,
            completes_part: false,
            final_key: None,
            reached: Vec::new(),
        }
    }

    /// The paths walked, each to the entry it reaches.
    pub(crate) fn reached(self) -> Vec<Route> {
        self.reached
    }

    /// Record that the path walked reaches the entry of `pipeline`.
    pub fn reach(&mut self, pipeline: PipelineId) {
        self.reached.push(Route {
            pipeline,
            keeps_keys: !self.widened,
            completes_part: self.completes_part,
            final_key: self.final_key.clone(),
        });
    }

    pub(crate) fn requiring_final_key(&mut self, key: &Value, route: impl FnOnce(&mut Self)) {
        let was = self.final_key.replace(key.clone());
        route(self);
        self.final_key = was;
    }

    /// Walk on through `route` as widened: the operator declares that it reads its input's keys
    /// as none of its own, so a push of some of them reaches it as `Everything`. A sibling path
    /// walked after `route` returns is not widened by this one.
    pub fn widened(&mut self, route: impl FnOnce(&mut Self)) {
        let was = std::mem::replace(&mut self.widened, true);
        route(self);
        self.widened = was;
    }

    /// Walk on through `route` as a path whose complete region names only part of what a row it
    /// reaches depends on: a widening passes a region that is not whole on as nothing complete,
    /// and a lookup's operand names the rows that read a complete key, whatever their input holds.
    pub fn completing_part(&mut self, route: impl FnOnce(&mut Self)) {
        let was = std::mem::replace(&mut self.completes_part, true);
        route(self);
        self.completes_part = was;
    }

    /// Refuse the walk: it re-entered a consumer it is passing through, so its chain is a cycle,
    /// which only a store closes.
    pub fn reentered(&mut self) {
        panic!("a push's route re-enters a consumer it is passing through");
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
    inline: Option<Box<dyn Consumer>>,
    input: Tiling,
    /// Where an unplaced entry still records a complete push ([`CompletionTarget`]).
    completes: CompletionTarget,
}

/// The pipeline an unplaced [`Entry`] records a complete push at, and that pipeline's input, which
/// the entry's input keys name the same rows of: a loop's drive reads its source by pull, so the
/// entry in front of the source queues nothing, but the positions the drive emits are the
/// source's keys, so what the source completes of its keys the scope's input has completed of its
/// positions. `None` where nothing records it, as in front of any other pulled input.
// shared-state-ok: the drive and the entry in front of its source both hold it, the planner
// writes it before the run, and what crosses it is a pipeline's index and a tiling, never a tile.
pub type CompletionTarget = Rc<RefCell<Option<(PipelineId, Tiling)>>>;

/// The pipeline an [`Entry`] queues for, which a planner sets once it has put the entry's breaker
/// in one: `None` before, as in a run that only pulls, where the entry queues nothing.
// shared-state-ok: the breaker and the entry at its input both hold it, the planner writes it
// before the run, and what crosses it is a pipeline's index, never a tile.
pub type Placement = Rc<Cell<Option<PipelineId>>>;

impl Entry {
    /// The entry of `pipeline`, whose breaker reads `input`, in front of `inner`.
    #[cfg(test)]
    pub fn new(pipeline: PipelineId, input: Tiling) -> Self {
        Entry {
            pipeline: Rc::new(Cell::new(Some(pipeline))),
            input,
            completes: CompletionTarget::default(),
            inline: None,
        }
    }

    /// The entry of a breaker that reads `input`, in front of `inner`, and its placement, which
    /// the breaker keeps for a planner to set ([`ProducerBase::placement`]).
    ///
    /// [`ProducerBase::placement`]: crate::interpreter::tile_operators::ProducerBase
    pub fn unplaced(input: Tiling) -> (Self, Placement) {
        let pipeline: Placement = Rc::new(Cell::new(None));
        let entry = Entry {
            pipeline: pipeline.clone(),
            input,
            completes: CompletionTarget::default(),
            inline: None,
        };
        (entry, pipeline)
    }

    pub(crate) fn inline_through(mut self, consumer: Box<dyn Consumer>) -> Self {
        self.inline = Some(consumer);
        self
    }

    /// The target this entry records a complete push at while it is unplaced, which the holder
    /// keeps for a planner to set ([`CompletionTarget`]).
    pub fn complete_target(&self) -> CompletionTarget {
        self.completes.clone()
    }
}

// Whether this thread is in a compiled program's dispatched run (`run_program`), which a debug
// build checks no cache invalidation is delivered in.
//
// shared-state-ok: a debug check's one bit. Nothing crosses it between operators; the run sets it
// and the consumers a notification passes read it.
thread_local! {
    // shared-state-ok: the flag itself, for the reason on the macro above. The checker's upward
    // scan stops at `thread_local! {`, so the note above does not reach this line.
    static IN_A_RUN: Cell<bool> = const { Cell::new(false) };
}

/// Execute `run` within a dispatched pipeline's evaluation context.
pub(crate) fn in_a_run<R>(run: impl FnOnce() -> R) -> R {
    struct Leave(bool);
    impl Drop for Leave {
        fn drop(&mut self) {
            IN_A_RUN.with(|in_a_run| in_a_run.set(self.0));
        }
    }
    let _leave = Leave(IN_A_RUN.with(|in_a_run| in_a_run.replace(true)));
    run()
}

/// Whether this thread is inside a compiled program's dispatched run ([`in_a_run`]).
pub(crate) fn is_in_a_run() -> bool {
    IN_A_RUN.with(Cell::get)
}

impl Consumer for Entry {
    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        if let Some(pipeline) = self.pipeline.get()
            && landing.accepts_entry(pipeline)
        {
            if let Some(guard) = pushed_guard(region, &self.input) {
                landing.queue(pipeline, &guard);
            }
            return;
        }
        if self.pipeline.get().is_none() && landing.is_delivery() && !landing.is_complete() {
            if let Some(inline) = &mut self.inline {
                inline.notify(region, landing);
            }
            return;
        }
        if !landing.is_complete() {
            return;
        }
        if let Some((pipeline, input)) = &*self.completes.borrow()
            && let Some(guard) = pushed_guard(region, input)
        {
            // The drive's positions are its source's keys, so a region of the source's keys is
            // one of the store's input.
            debug_assert!(
                guard.check_from(input),
                "a drive's source completes positions of its store's input: {region:?}"
            );
            landing.queue(*pipeline, &guard);
        }
    }
    fn route(&mut self, routes: &mut Routes) {
        if let Some(pipeline) = self.pipeline.get() {
            routes.reach(pipeline);
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

/// `held`, a breaker's complete region of its output `tiling`, as a projection: every key where it
/// names every position of the finite range of positions the output's outermost keys range over,
/// as a store or an aggregate under a loop of positions `0..n` states the positions it completed,
/// which `TileGuard::closed_over` leaves as they are. `None` where no projection spells it.
fn complete_projection(held: TileGuard, tiling: &Tiling) -> Option<Projection> {
    if let (
        Some(Extent::UIntRange(positions)),
        TileGuard::Function(FunctionGuard::Domain(region @ Predicate::Intervals(_))),
    ) = (tiling.domain_extent(), &held)
    {
        let covered = region.covers_positions(&positions);
        if covered {
            return Some(Projection::Everything);
        }
    }
    Projection::of(&held).ok()
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
/// closed. The driver consumes the package of the lowest pipeline that has one; when no pipeline
/// has one, it finishes the lowest pipeline that may finish. It stops when every pipeline has
/// finished. Every breaker initializes its per-run state before the first package.
///
/// # Panics
///
/// When a pipeline cannot finish though nothing is queued, which an acyclic graph rules out; in a
/// debug build, when a package's guard is not a guard of the tiling its breaker's input answers,
/// when a pipeline consumes a region it consumed before, or when a breaker's morsels do not
/// partition its final guard; and at any of the invariants [`finish_pipeline`] asserts.
pub fn run(dispatcher: &Dispatcher, breakers: &[BreakerHandle]) {
    in_a_run(|| {
        for breaker in breakers {
            breaker.borrow_mut().begin_run();
        }
        assert_eq!(
            breakers.len(),
            dispatcher.infos.len(),
            "one breaker per pipeline"
        );
        drive(dispatcher, &mut handles(breakers));
    });
}

/// Execute a component operation as one dispatched unit command.
#[cfg(any(test, feature = "test-helpers"))]
pub(crate) fn in_pipeline_for_test<R>(work: impl FnOnce() -> R) -> R {
    if is_in_a_run() {
        return work();
    }
    struct Command<F, R> {
        work: Option<F>,
        result: Option<R>,
    }
    impl<F: FnOnce() -> R, R> Breaker for Command<F, R> {
        fn as_producer(&self) -> Option<&dyn BreakingProducer> {
            None
        }
        fn consume_impl(&mut self, _: InputId, _: TileGuard) {
            self.result = Some(self.work.take().expect("one command")());
        }
        fn input_tiling(&self, _: InputId) -> Tiling {
            Tiling::Scalar(Extent::Base(crate::interpreter::BaseType::Unit))
        }
        fn input_released(&self, _: InputId) -> TileGuard {
            TileGuard::Scalar(if self.work.is_none() {
                Predicate::True
            } else {
                Predicate::False
            })
        }
    }
    let mut command = Command {
        work: Some(work),
        result: None,
    };
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    in_a_run(|| {
        drive(&dispatcher, &mut |_, call| {
            call(&mut command, InputId::ONLY)
        })
    });
    command.result.expect("the dispatcher consumes the command")
}

/// Evaluate a component query inside one dispatched unit command, for protocol fixtures.
#[cfg(any(test, feature = "test-helpers"))]
pub fn read_for_test<P: crate::interpreter::tile_operators::TileProducer + ?Sized>(
    producer: &mut P,
    guard: TileGuard,
) -> crate::interpreter::Tile {
    in_pipeline_for_test(|| producer.get(guard))
}

#[cfg(test)]
pub(crate) fn notify_for_test<C: Consumer + ?Sized>(consumer: &mut C, region: &Projection) {
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    let mut landing = Landing {
        target: Target::Queue {
            dispatcher: &dispatcher,
        },
        from: 0,
        widened: false,
    };
    consumer.notify(region, &mut landing);
}

/// Each pipeline's breaker, reached for one call at a time: through a handle ([`handles`]), or by
/// walking a compiled program's producer chains (`run_program`).
type Reach<'r> = dyn FnMut(PipelineId, &mut Call<'_>) + 'r;

/// One call on a pipeline's breaker, which a [`Reach`] makes, with the input of the breaker the
/// pipeline consumes.
type Call<'c> = dyn FnMut(&mut dyn Breaker, InputId) + 'c;

/// The breakers `breakers` holds, by pipeline, each borrowed for one call.
fn handles(breakers: &[BreakerHandle]) -> impl FnMut(PipelineId, &mut Call<'_>) {
    move |pipeline, call| {
        let mut breaker = breakers[pipeline.0].borrow_mut();
        debug_assert!(
            breaker.as_producer().is_some(),
            "{} answers itself as a producer, so its pushes reach its readers",
            breaker.name()
        );
        call(&mut *breaker, InputId::ONLY)
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
            reach(PipelineId(pipeline), &mut |breaker, at| {
                input = Some(breaker.input_tiling(at));
            });
            let input = input.expect("a reach calls the breaker it reaches");
            // A run with no live source has no boundary to pause at, so it starts over breakers
            // that have consumed nothing.
            dispatcher.start_source(PipelineId(pipeline), &input, &input.empty_guard());
        }
    }
}

/// Hand `package` to its pipeline's breaker, land what the breaker complete since its last push
/// ([`Pushes::push_final`]) where the breaker is a producer ([`Breaker::as_producer`]) that
/// pushes while consuming ([`BreakingProducer::pushes_while_consuming`]), then acknowledge the
/// package. The push lands before the acknowledgement, which may let the pipeline finish.
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
    reach(package.pipeline, &mut |breaker, input| {
        let tiling = breaker.input_tiling(input);
        // A package carries a guard of the tiling of the pipeline that pushed it, or of this
        // breaker's own input for a source or a pipeline that reads it whole, so it fits only a
        // breaker whose input answers that tiling.
        debug_assert!(
            package.guard.check_from(&tiling),
            "pipeline {p} consumes a guard of the tiling its breaker's input answers: {:?}",
            package.guard
        );
        breaker.consume_impl(input, package.guard.clone());
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
        if dispatcher.states[pipeline.0].phase.load() == Phase::Finished {
            continue;
        }
        let mut landed = None;
        reach(pipeline, &mut |breaker, _| {
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

/// Finish `pipeline`, after checking what a finish rests on.
///
/// # Panics
///
/// When the pipeline has begun to finish already, its queue is not closed or not empty, a package
/// claimed for it is in flight, a pipeline it reads has not finished, or its breaker's input has
/// not released every guard the pipeline consumed. Also where the guard algebra has no exact
/// difference of a consumed guard and the guard the input released ([`guard_minus`]).
pub fn finish_pipeline(dispatcher: &Dispatcher, breakers: &[BreakerHandle], pipeline: PipelineId) {
    let consumed = dispatcher.begin_finish(pipeline);
    finish_with(dispatcher, &mut handles(breakers), pipeline, consumed);
}

/// Finish `pipeline`, which has begun after consuming `consumed`: push what it completed and no
/// consume pushed, through the breaker's [`finish`][Breaker::finish], then mark it finished.
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
    reach(pipeline, &mut |breaker, input| {
        let consumed = consumed
            .take()
            .expect("a reach calls the breaker it reaches once");
        let released = breaker.input_released(input);
        dispatcher.ensure(
            consumed.is_none_or(|consumed| {
                unreleased(&consumed, &released, &breaker.input_tiling(input)).is_none()
            }),
            || {
                format!(
                    "pipeline {p} finishes after its input has released every guard the \
                     pipeline consumed"
                )
            },
        );
        let mut pushes = dispatcher.pushes(pipeline);
        breaker.finish(input, &mut pushes);
        finished = Some(pushes);
    });
    dispatcher.finish(finished.expect("a reach calls the breaker it reaches"));
}

#[cfg(test)]
mod tests {
    #[cfg(debug_assertions)]
    #[test]
    fn final_read_completion_depends_on_its_required_keys() {
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0], vec![0]], 1);
        let a = Value::String("a".into());
        let b = Value::String("b".into());
        dispatcher.require_final_keys(PipelineId(1), PipelineId(0), vec![a.clone()]);
        dispatcher.require_final_keys(PipelineId(2), PipelineId(0), vec![a.clone(), b.clone()]);
        dispatcher.land_completed_keys(0, std::slice::from_ref(&a));
        assert!(matches!(
            dispatcher.complete_of(PipelineId(1), PipelineId(0)),
            Completion::Whole
        ));
        assert!(matches!(
            dispatcher.complete_of(PipelineId(2), PipelineId(0)),
            Completion::Nothing
        ));
        dispatcher.land_completed_keys(0, &[a, b]);
        assert!(matches!(
            dispatcher.complete_of(PipelineId(2), PipelineId(0)),
            Completion::Whole
        ));
    }

    use intervalsets::{Interval, IntervalSet};

    use super::*;
    use crate::interpreter::BaseType;

    fn retained_package_guards(queue: &Queue) -> usize {
        let state = queue.state.lock().unwrap();
        state.ready.len() + state.in_flight.len()
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

    #[rstest::rstest]
    fn an_admitted_arrival_precedes_concurrent_close(
        #[values(false, true)] waits_for_inputs: bool,
    ) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::sync::{Arc, Barrier};

        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1).unrecorded();
        let reader = PipelineId(1);
        dispatcher.take_arrivals(reader);
        if waits_for_inputs {
            dispatcher.wait_for_inputs(reader);
        } else {
            dispatcher.follow(reader, PipelineId(0));
        }
        let admitted = Arc::new(Barrier::new(2));
        let resume = Arc::new(Barrier::new(2));
        let (seen, go) = (admitted.clone(), resume.clone());
        *dispatcher.transition_hooks[0]
            .get_or_init(|| Mutex::new(None))
            .lock()
            .unwrap() = Some(Box::new(move || {
            seen.wait();
            go.wait();
        }));
        let guard = keys_between(0, 0);
        thread::scope(|scope| {
            let notify = scope.spawn(|| dispatcher.notify(reader, &guard));
            admitted.wait();
            // Closure must acquire the same lock as an admission not yet published to the queue.
            assert!(matches!(
                dispatcher.states[1].queue.state.try_lock(),
                Err(std::sync::TryLockError::WouldBlock)
            ));
            let close = scope.spawn(|| dispatcher.close(reader));
            resume.wait();
            notify.join().unwrap();
            close.join().unwrap();
        });
        assert_eq!(
            dispatcher.states[1]
                .queue
                .state
                .lock()
                .unwrap()
                .waiting_for_inputs
                .len(),
            usize::from(waits_for_inputs)
        );
        dispatcher.record_complete(1, 0, None);
        let package = dispatcher
            .claim_of(reader)
            .expect("the admitted arrival survives closure");
        assert_eq!(package.guard, guard);
        dispatcher.acknowledge(package);
        dispatcher.close(PipelineId(0));
        dispatcher.begin_finish(PipelineId(0));
        dispatcher.finish(dispatcher.pushes(PipelineId(0)));
        dispatcher.begin_finish(reader);
        dispatcher.finish(dispatcher.pushes(reader));
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }

    #[rstest::rstest]
    fn a_closed_arrival_feed_rejects_both_queued_and_waiting_for_inputs_input(
        #[values(false, true)] complete: bool,
    ) {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
        let reader = PipelineId(1);
        dispatcher.take_arrivals(reader);
        dispatcher.wait_for_inputs(reader);
        if complete {
            dispatcher.record_complete(1, 0, None);
        }
        dispatcher.close(reader);
        assert!(!dispatcher.states[1].queue.is_closed());
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                dispatcher.notify(reader, &keys_between(0, 0));
            }))
            .is_err()
        );
        assert_eq!(dispatcher.states[1].queue.reserved(), 0);
        assert!(
            dispatcher.states[1]
                .queue
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .waiting_for_inputs
                .is_empty()
        );
        assert!(matches!(dispatcher.try_claim(None), Next::Failed));
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
mod in_a_run_tests {
    use super::*;
    use crate::interpreter::tile_operators::Arrivals;

    /// A run that panics leaves the thread outside a run, so a later notification passes.
    #[test]
    fn a_run_that_panics_leaves_the_thread_outside_a_run() {
        let unwound = std::panic::catch_unwind(|| in_a_run(|| panic!("the run fails")));
        assert!(unwound.is_err());
        assert!(!is_in_a_run());
        let _consumer = Arrivals::new().consumer(Box::new(|| {}));
    }
}

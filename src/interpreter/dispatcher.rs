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
//! that can end a sleep wakes the sleepers. The dispatcher holds no breaker. The single-threaded
//! driver, [`run`], reaches the breakers through
//! the handles its caller passes, indexed by pipeline. Nothing outside unit tests calls it, and
//! only unit tests drive the dispatcher from several threads. See
//! `src/interpreter/design-dispatcher.md`, "The dispatcher".

use std::cell::Cell;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
#[cfg(test)]
use std::sync::OnceLock;
use std::sync::RwLock;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, PoisonError};
use std::thread;

use intervalsets::Bounding;

use crate::interpreter::tile_operators::{
    Breaker, BreakingProducer, FunctionGuard, Tiling, cut_before, guard_covers, guard_minus,
    partition_gap, spelled_part,
};
use crate::interpreter::tile_operators::{InputId, closed_keeping_row_ends};
use crate::interpreter::{
    Consumer, Extent, Predicate, Projection, SharedConsumer, TileGuard, Value,
};

pub(crate) mod loop_scope;
pub use loop_scope::{Offered, Offers};
mod plan;
mod scope;
pub(crate) mod transaction_scope;
mod workers;

pub use plan::{
    Ended, Planned, Refused, Run, RunObserver, Targets, run_program, run_program_into,
    run_program_polling, run_program_with_workers,
};
#[cfg(test)]
pub(crate) use plan::{default_workers, run_program_polling_with_workers};

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

impl WorkPackage {
    fn consume<'b>(
        &self,
        breaker: &'b dyn Breaker,
        input: InputId,
        pushes: &mut Pushes<'_>,
    ) -> Option<&'b dyn BreakingProducer> {
        debug_assert!(
            self.guard.check_from(&breaker.input_tiling(input)),
            "pipeline {} consumes a guard of the tiling its breaker's input answers: {:?}",
            self.pipeline.0,
            self.guard
        );
        breaker.consume_for_dispatch(input, self.guard.clone(), pushes)
    }
}

/// What a source's notify did with a region ([`Dispatcher::try_notify`]).
pub enum Admission {
    /// The region is queued, or names nothing.
    Queued,
    /// The source has as many packages outstanding as its [limit](Dispatcher::limit); nothing is
    /// queued.
    Full,
    /// The run's claims have stopped or the run has failed, so no claim takes a package; nothing
    /// is queued.
    Stopped,
}

/// What a worker does next, as [`Dispatcher::try_claim`] answers.
#[cfg_attr(test, derive(Debug))]
pub enum Next {
    /// Hand the package to its pipeline's breaker, then [`acknowledge`](Dispatcher::acknowledge)
    /// it.
    Package(WorkPackage),
    /// Finish the pipeline, which the claim moved to finishing, then
    /// [`finish`](Dispatcher::finish) it: push what it completed and no consume pushed, through the
    /// breaker's [`finish`][Breaker::finish], its last call.
    ///
    /// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
    Finish { pipeline: PipelineId },
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

/// A scope body's follower hold, read before a publication pass ([`Dispatcher::followers_hold`]).
pub(crate) struct FollowersHold(u64);

/// One scope body's follower hold: its inner pipelines and step, which a hold stops from taking
/// a package while the round's pushes settle ([`Dispatcher::add_hold_group`]).
#[derive(Clone, Copy)]
pub(crate) struct HoldGroup(usize);

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
}

impl Queue {
    fn new() -> Self {
        Queue {
            state: Mutex::new(QueueState::default()),
            reserved: AtomicUsize::new(0),
        }
    }

    /// Append each of `morsels` as a package. An empty morsel is no package. A closed queue takes
    /// nothing.
    fn append_locked(&self, state: &mut QueueState, morsels: &[TileGuard]) -> bool {
        let morsels: Vec<&TileGuard> = morsels.iter().filter(|morsel| !morsel.is_empty()).collect();
        if morsels.is_empty() {
            return !self.is_closed();
        }
        let Some(first) = self.reserve(morsels.len()) else {
            return false;
        };
        for (index, morsel) in (first..).zip(morsels) {
            state.ready.push_back((index, morsel.clone()));
        }
        true
    }

    /// [`append_locked`](Self::append_locked) under the queue's lock.
    fn append(&self, morsels: &[TileGuard]) -> bool {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        self.append_locked(&mut state, morsels)
    }

    /// Move the oldest ready package to in-flight while its dependencies permit the claim and it
    /// names no region a package in flight names.
    fn claim<R>(
        &self,
        pipeline: usize,
        ordered: bool,
        reserve: impl FnOnce() -> Option<R>,
    ) -> Option<(WorkPackage, R)> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        // A pipeline can be notified of a region again before its package for the region is
        // acknowledged, as a reader keyed by one row is at each push of what it reads. Two
        // packages naming one region would read it at once, and the first to finish releases what
        // the other still reads, so the later one waits, and the packages behind it with it.
        let overlaps = |state: &QueueState| {
            state.ready.front().is_some_and(|(_, next)| {
                state
                    .in_flight
                    .values()
                    .any(|running| !next.intersect(running).is_empty())
            })
        };
        // An append publishes prerequisite work before queuing this package. Inspect dependencies
        // after observing it under the lock; the check reads counters and takes no queue lock.
        if state.ready.is_empty() || (ordered && !state.in_flight.is_empty()) || overlaps(&state) {
            return None;
        }
        let reservation = reserve()?;
        let (index, guard) = state.ready.pop_front()?;
        state.in_flight.insert(index, guard.clone());
        Some((
            WorkPackage {
                pipeline: PipelineId(pipeline),
                guard,
                index,
            },
            reservation,
        ))
    }

    /// Remove a matching claim, and answer whether it was one: `None` where no claim matches, and
    /// otherwise whether the package at the head of the queue met the removed one, which
    /// [`claim`](Self::claim) holds back while they overlap. Monotonic indices distinguish
    /// repeated reads of the same guard.
    fn acknowledge(&self, package: &WorkPackage, on_ack: impl FnOnce()) -> Option<bool> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if state.in_flight.get(&package.index) != Some(&package.guard) {
            return None;
        }
        on_ack();
        state.in_flight.remove(&package.index);
        let freed_head = state
            .ready
            .front()
            .is_some_and(|(_, next)| !next.intersect(&package.guard).is_empty());
        Some(freed_head)
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
    /// The tiling of the breaker input the pipeline consumes, where a planner set it
    /// ([`consumes_input`](Dispatcher::consumes_input)). An entry of another of the breaker's
    /// inputs, as a loop's seed is, or beneath a chain that reshapes this one lands regions of
    /// another tiling, which [`rows_named`](Dispatcher::rows_named) restates as rows of this one.
    input: Option<Tiling>,
    ingress: Option<std::ops::Range<usize>>,
    /// The pipelines it reads whose pushes the planner walked, each with whether the walk reached
    /// this pipeline's entry ([`plan_route`](Dispatcher::plan_route)).
    walked: Vec<(usize, bool)>,
    /// The follower hold of the scope body it is in, inner pipeline or step
    /// ([`add_hold_group`](Dispatcher::add_hold_group)); `None` outside a body.
    hold: Option<HoldGroup>,
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
    /// How many of the pipeline's packages have been acknowledged.
    acknowledged: AtomicUsize,
    /// The union of the guards of the packages acknowledged, which a finish checks its breaker's
    /// input has released ([`finish_with`]).
    // shared-state-ok: a debug build's record of what was acknowledged, grown under the queue's
    // lock at each acknowledgement and read at the finish; what crosses it is a guard, never a
    // tile.
    #[cfg(debug_assertions)]
    consumed: Mutex<Option<TileGuard>>,
}

impl PipelineState {
    fn new(reads: usize) -> Self {
        Self {
            queue: Queue::new(),
            phase: AtomicPhase::new(Phase::Running),
            unfinished: AtomicUsize::new(reads),
            pushed: Mutex::new(None),
            acknowledged: AtomicUsize::new(0),
            #[cfg(debug_assertions)]
            consumed: Mutex::new(None),
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

#[cfg(test)]
type StepProbe = Arc<dyn Fn(PipelineId) + Sync + Send>;
#[cfg(test)]
thread_local! {
    // Test runs copy their own probe into the dispatcher before starting workers.
    static STEP_PROBE: std::cell::RefCell<Option<StepProbe>> = const { std::cell::RefCell::new(None) };
}

/// The graph of pipelines, the work packages queued for each pipeline, and what each has consumed.
pub struct Dispatcher {
    /// The held rows a cut of a work package targets, where its shape supports cutting.
    morsel_rows: usize,
    /// What each pipeline is, fixed before the dispatcher is shared.
    infos: Vec<PipelineInfo>,
    /// What each pipeline has done, which the workers change.
    states: Vec<PipelineState>,
    /// Per scope body ([`HoldGroup`]), whether its pipelines wait for the round to settle before
    /// following their reads, in the low bit, and how many holds it has taken, in the bits above:
    /// a release that read the count before a later hold fails
    /// ([`release_followers_if`](Self::release_followers_if)).
    holds: Vec<AtomicU64>,
    /// How many pipelines have not finished. The finish that brings it to zero ends the run.
    unfinished: AtomicUsize,
    /// Set by [`Dispatcher::fail`], and by every refusal before it panics ([`Dispatcher::ensure`]).
    failed: AtomicBool,
    /// Set by [`Dispatcher::stop_claims`]: every claim answers [`Next::Done`].
    stopped: AtomicBool,
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
    scope_step_probe: Option<StepProbe>,
    #[cfg(test)]
    transition_hooks: [OnceLock<Mutex<Option<TransitionHook>>>; 2],
    /// How many pipelines quiescence checks have read the counts of.
    #[cfg(test)]
    quiescence_reads: AtomicUsize,
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
    /// Crate-private: a run executes the one dispatcher it builds, and a package is acknowledged
    /// through the dispatcher that issued it, so no caller holds two.
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
    pub(crate) fn new(reads: Vec<Vec<usize>>, morsel_rows: usize) -> Self {
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
                follows: Vec::new(),
                limit: usize::MAX,
                pushes_with: pipeline,
                arrivals: false,
                input: None,
                ingress: None,
                walked: Vec::new(),
                hold: None,
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
            holds: Vec::new(),
            failed: AtomicBool::new(false),
            stopped: AtomicBool::new(false),
            generation: AtomicU64::new(0),
            sleepers: AtomicUsize::new(0),
            sleep: Mutex::new(()),
            wake: Condvar::new(),
            #[cfg(test)]
            events: Mutex::new(Vec::new()),
            #[cfg(test)]
            recording: true,
            #[cfg(test)]
            scope_step_probe: STEP_PROBE.with_borrow(Clone::clone),
            #[cfg(test)]
            transition_hooks: std::array::from_fn(|_| OnceLock::new()),
            #[cfg(test)]
            quiescence_reads: AtomicUsize::new(0),
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
        assert!(
            graph.holds.is_empty(),
            "a body's hold is added once it is appended to the run's dispatcher"
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
            info.pushes_with += offset;
            for (read, _) in &mut info.walked {
                *read += offset;
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
            follows: Vec::new(),
            limit: usize::MAX,
            pushes_with: pipeline,
            arrivals: false,
            input: None,
            ingress: None,
            walked: Vec::new(),
            hold: None,
        });
        *self.unfinished.get_mut() += 1;
        PipelineId(pipeline)
    }

    /// Add one follower hold over `pipelines`, a scope body's inner pipelines and step, before
    /// execution starts: [`hold_followers`](Self::hold_followers) stops every one of them from
    /// taking a package that follows its reads, and a release lets every one go.
    ///
    /// # Panics
    ///
    /// When a pipeline is in another hold already.
    pub(crate) fn add_hold_group(
        &mut self,
        pipelines: impl IntoIterator<Item = PipelineId>,
    ) -> HoldGroup {
        let group = HoldGroup(self.holds.len());
        self.holds.push(AtomicU64::new(0));
        for pipeline in pipelines {
            let hold = &mut self.infos[pipeline.0].hold;
            assert!(
                hold.is_none(),
                "pipeline {} is in one scope body's hold",
                pipeline.0
            );
            *hold = Some(group);
        }
        group
    }

    /// Accept pushes at this entry only from the configured input graph.
    pub(crate) fn restrict_ingress(&mut self, pipeline: PipelineId, from: std::ops::Range<usize>) {
        assert!(
            from.start <= from.end && from.end <= self.infos.len(),
            "an ingress range names planned pipelines"
        );
        self.infos[pipeline.0].ingress = Some(from);
    }

    /// The count of the dispatcher's changes so far ([`Generation`]): an equal count read twice
    /// says nothing was queued, consumed or finished between.
    pub(crate) fn changes(&self) -> u64 {
        self.generation.load(Ordering::SeqCst)
    }

    /// Whether every pipeline of `pipelines` has consumed every package queued for it, and every
    /// pipeline it reads is quiescent too: no package of theirs is outstanding. A breaker that
    /// pushes only what `try_push_held` asks of it, as `MapAggregate`, can be quiescent before its
    /// readers took what it completed, which is why a loop's round holds its followers until its
    /// pushes settle ([`hold_followers`](Self::hold_followers)).
    ///
    /// One check reads each pipeline it reaches once, however many paths of reads reach it.
    fn quiescent(&self, pipelines: impl IntoIterator<Item = usize>) -> bool {
        let mut quiescent = vec![false; self.infos.len()];
        pipelines
            .into_iter()
            .all(|pipeline| self.quiescent_in(pipeline, &mut quiescent))
    }

    /// [`quiescent`](Self::quiescent) for one check, `found` marking the pipelines the check has
    /// found quiescent. A check stops at the first pipeline it finds otherwise, so a pipeline
    /// not marked has not been read.
    fn quiescent_in(&self, pipeline: usize, found: &mut [bool]) -> bool {
        if found[pipeline] {
            return true;
        }
        #[cfg(test)]
        self.quiescence_reads.fetch_add(1, Ordering::Relaxed);
        // The pipelines it reads first: a push lands before the acknowledgement of the package
        // that made it, so a read found quiescent has queued all it pushed before this pipeline's
        // counts are read, and a package in flight on another thread is seen. A read marked
        // found had its counts read earlier in this check, which is before this pipeline's too.
        if !self.infos[pipeline]
            .reads
            .iter()
            .all(|&read| self.quiescent_in(read, found))
        {
            return false;
        }
        // Acknowledged before reserved: the count only grows and never passes the reservations,
        // so the two equal says no package of the pipeline was outstanding when the second was
        // read.
        let state = &self.states[pipeline];
        let acknowledged = state.acknowledged.load(Ordering::SeqCst);
        found[pipeline] = acknowledged == state.queue.reserved.load(Ordering::SeqCst) & !CLOSED;
        found[pipeline]
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader`: at the
    /// start, what a range brings that no push names ([`run_program`]), and a loop's round's row.
    ///
    /// # Panics
    ///
    /// When `reader`'s queue has closed: every pipeline it reads has finished.
    pub(crate) fn queue_for(&self, reader: PipelineId, guard: &TileGuard) {
        self.queue_in_current(reader, guard);
    }

    fn queue_in_current(&self, reader: PipelineId, guard: &TileGuard) {
        let _publisher = self.publisher();
        let queue = &self.states[reader.0].queue;
        let appended = queue.append(std::slice::from_ref(guard));
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

    /// Record that the planner walked the pushes of `read`, a pipeline `reader` reads, and whether
    /// the walk reached `reader`'s entry. Where it did not, the planner reads `read` by pull, so a
    /// push of `read` that reaches `reader` took a path the walk did not, and fails the run where
    /// it is queued ([`Landing::queue`]).
    ///
    /// # Panics
    ///
    /// When `reader` does not read `read`, or the walk of `read` is already recorded.
    pub(crate) fn plan_route(&mut self, reader: PipelineId, read: PipelineId, reached: bool) {
        let info = &mut self.infos[reader.0];
        assert!(
            info.reads.contains(&read.0),
            "pipeline {} walks the routes of pipeline {}, which it reads",
            reader.0,
            read.0
        );
        assert!(
            info.walked.iter().all(|&(walked, _)| walked != read.0),
            "the routes of pipeline {} to pipeline {} are walked once",
            read.0,
            reader.0
        );
        info.walked.push((read.0, reached));
    }

    /// Mark `pipeline`, which reads pipelines, as also taking the arrivals of live sources: it is
    /// notified and closed as a source is ([`notify`](Self::notify), [`close`](Self::close)), and
    /// its queue closes once both its close and the finishes of the pipelines it reads have
    /// happened. It takes an arrival as it arrives, or once those pipelines are quiescent where it
    /// follows them ([`follow`](Self::follow)).
    ///
    /// # Panics
    ///
    /// When `pipeline` reads no pipeline or takes arrivals already, and when a source has been
    /// notified or closed already.
    pub fn take_arrivals(&mut self, pipeline: PipelineId) {
        self.mark_arrivals(pipeline);
    }

    fn mark_arrivals(&mut self, pipeline: PipelineId) {
        let p = pipeline.0;
        let state = &self.states[p];
        // Composed scope graphs may already contain their initial queued inputs.
        // This newly configured entry must itself have received nothing yet.
        assert!(
            state.queue.reserved() == 0
                && !state
                    .queue
                    .state
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .arrivals_closed
                && state.phase.load() == Phase::Running,
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

    /// Whether the end of `pipeline`'s arrivals is the last feed its queue waits for: every
    /// pipeline it reads has finished and landed its final pushes. A scope that closes its intake
    /// after its reads checks this on each admission ([`Body::intake`](loop_scope::Body::intake)).
    fn only_arrivals_remain(&self, pipeline: PipelineId) -> bool {
        debug_assert!(
            self.infos[pipeline.0].arrivals,
            "pipeline {} takes arrivals beside its reads",
            pipeline.0
        );
        self.states[pipeline.0].unfinished.load(Ordering::Acquire) == 1
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

    /// Whether a claim may take `pipeline`'s packages: once every pipeline it follows
    /// ([`follow`](Self::follow)) is quiescent ([`quiescent`](Self::quiescent)) and its followers
    /// are not held.
    ///
    /// Quiescence is read before the hold. A worker holds a body's followers before it
    /// acknowledges the body's package (`WorkerPool::consume`), so a quiescence that sees the
    /// acknowledgement also sees the hold. Read the other way round, a hold taken between the two
    /// reads goes unseen.
    fn takes_from(&self, pipeline: usize) -> bool {
        let info = &self.infos[pipeline];
        info.follows.is_empty()
            || (self.quiescent(info.follows.iter().copied())
                && info
                    .hold
                    .is_none_or(|group| self.holds[group.0].load(Ordering::SeqCst) & 1 == 0))
    }

    /// Claimants release these holds after settling held pushes.
    /// A hold does not revoke a claim or wait for a worker already consuming a package.
    ///
    /// Hold the pipelines of `group`, a scope body's, from taking a package that follows its
    /// reads ([`follow`](Self::follow)). A loop's round holds them while the pipelines they follow
    /// push what they complete. A breaker that pushes only what `try_push_held` asks it to, as
    /// `MapAggregate`, is quiescent before its readers have taken what it completed. Each hold is
    /// counted, so a release that read the hold before this one fails
    /// ([`release_followers_if`](Self::release_followers_if)). See
    /// `src/interpreter/design-dispatcher.md`, "A loop in rounds".
    pub(crate) fn hold_followers(&self, group: HoldGroup) {
        let _ = self.holds[group.0].fetch_update(Ordering::SeqCst, Ordering::SeqCst, |hold| {
            Some((((hold >> 1) + 1) << 1) | 1)
        });
        self.advance();
    }

    /// `group`'s follower hold as it stands, for a later
    /// [`release_followers_if`](Self::release_followers_if).
    pub(crate) fn followers_hold(&self, group: HoldGroup) -> FollowersHold {
        FollowersHold(self.holds[group.0].load(Ordering::SeqCst))
    }

    /// Release `group` where its hold is still `read`: held, and held by no hold taken since. A
    /// worker that consumes a package of a loop's or transaction writer's body holds the body
    /// again before it acknowledges the package, so a release decided before that consume
    /// published fails, and the round's step waits for the next publication. Whether it released
    /// the group. One compare-and-swap of the group's hold releases every pipeline of it at once.
    pub(crate) fn release_followers_if(&self, group: HoldGroup, read: FollowersHold) -> bool {
        if read.0 & 1 == 0 {
            return false;
        }
        let released = self.holds[group.0]
            .compare_exchange(read.0, read.0 & !1, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok();
        self.advance();
        released
    }

    /// Record that `pipeline` consumes a breaker input of `input`'s tiling.
    pub(crate) fn consumes_input(&mut self, pipeline: PipelineId, input: Tiling) {
        self.infos[pipeline.0].input = Some(input);
    }

    /// `guard`, a region an entry of `reader` lands, as rows of the input `reader` consumes. A
    /// region of another tiling, as of a loop's seed or of an input a chain reshapes, is no region
    /// of those rows, and a change of it changes every row ([`rows_named_in`]).
    fn rows_named(&self, reader: usize, guard: &TileGuard) -> TileGuard {
        match &self.infos[reader].input {
            Some(input) => rows_named_in(input, guard),
            None => guard.clone(),
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
    /// until then, and [`try_notify`](Self::try_notify) answers [`Admission::Full`]. A notify
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
            pending: Vec::new(),
            unspelled: false,
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

    /// Queue a source pipeline's input and close the source: `input`, the
    /// tiling its breaker's input answers, less `released`, what the breaker's input has already
    /// released, as one package per morsel ([`seed_within`]). A run's first start passes nothing
    /// released; a run after a pause or a reload starts over a breaker that consumed, and queues
    /// it nothing it has finished with. The cut visits only the positions left, so a source
    /// released whole is closed with nothing queued. It queues as [`notify`](Self::notify) would,
    /// without waiting for any limit, then [`close`](Self::close)s the source.
    ///
    /// # Panics
    ///
    /// When `pipeline` reads a pipeline, or is closed, and where the guard algebra has no exact
    /// difference of the input and `released` ([`guard_minus`]).
    pub fn start_source(&self, pipeline: PipelineId, input: &Tiling, released: &TileGuard) {
        let _publisher = self.publisher();
        self.ensure(self.infos[pipeline.0].reads.is_empty(), || {
            format!(
                "pipeline {} starts whole only as a source, which reads no pipeline",
                pipeline.0
            )
        });
        let left = guard_minus(&input.universal_guard(), released).closed_over(input);
        let morsels = match left.is_empty() {
            true => Vec::new(),
            false => seed_within(input, &left, self.morsel_rows),
        };
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
    /// is acknowledged, so the thread that notifies is held back by the workers. A notify that
    /// checks after the run's claims stop ([`stop_claims`](Self::stop_claims)) or the run fails
    /// returns at once with [`Admission::Stopped`] and queues nothing, a notify already waiting
    /// for credit included. A notify that checks just before a stop may still queue, which no
    /// claim then takes. It answers [`Admission::Queued`] or [`Admission::Stopped`].
    ///
    /// # Panics
    ///
    /// When `pipeline` takes no arrivals ([`take_arrivals`](Self::take_arrivals))
    /// or is closed; in a debug build, when `guard` meets a region queued for a source before.
    pub fn notify(&self, pipeline: PipelineId, guard: &TileGuard) -> Admission {
        loop {
            // Read before the check: an acknowledgement or a stop the check misses advances the
            // generation past this one, so the wait returns at once.
            let generation = self.generation.load(Ordering::SeqCst);
            match self.try_notify(pipeline, guard) {
                Admission::Full => self.wait(Generation(generation)),
                admitted => return admitted,
            }
        }
    }

    /// [`notify`](Self::notify) without waiting: [`Admission::Full`] while the source has as many
    /// packages outstanding as its [limit](Self::limit), and [`Admission::Stopped`] where it
    /// checks after the run's claims stop or the run fails, since no claim will take a package.
    /// Neither queues anything.
    ///
    /// # Panics
    ///
    /// As [`notify`](Self::notify).
    pub fn try_notify(&self, pipeline: PipelineId, guard: &TileGuard) -> Admission {
        let _publisher = self.publisher();
        if self.failed.load(Ordering::SeqCst) {
            return Admission::Stopped;
        }
        self.ensure_source(pipeline);
        if self.stopped.load(Ordering::SeqCst) {
            return Admission::Stopped;
        }
        if guard.is_empty() {
            return Admission::Queued;
        }
        let info = &self.infos[pipeline.0];
        // A limit is a source's alone (`limit`), whose every package its notifies queue.
        if info.limit != usize::MAX && self.state(pipeline).outstanding() >= info.limit {
            return Admission::Full;
        }
        let morsels = cut_positions(guard, self.morsel_rows);
        debug_assert!(
            partition_gap(guard, &morsels).is_none(),
            "the morsels of a notified guard partition it: {}",
            partition_gap(guard, &morsels).unwrap_or_default()
        );
        self.append_to_source(pipeline, &morsels);
        Admission::Queued
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
        if morsels.is_empty() {
            return;
        }
        let appended = queue.append_locked(&mut admission, morsels);
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
        let _publisher = self.publisher();
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
    /// one after observing its dependencies' progress. An ordered pipeline has at most one package
    /// in flight.
    fn claim_from<R>(
        &self,
        pipeline: usize,
        reserve: impl FnOnce() -> Option<R>,
    ) -> Option<(WorkPackage, R)> {
        let state = &self.states[pipeline];
        state
            .queue
            .claim(pipeline, self.infos[pipeline].ordered, || {
                if self.takes_from(pipeline) {
                    reserve()
                } else {
                    None
                }
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
        state.phase.load() == Phase::Running
            && reserved & CLOSED != 0
            && state.acknowledged.load(Ordering::Acquire) == reserved & !CLOSED
    }

    /// Claim the finish only from a closed queue's final reservation count.
    fn try_begin_finish<R>(
        &self,
        pipeline: usize,
        reserve: impl FnOnce() -> Option<R>,
    ) -> Option<R> {
        if !self.ready_to_finish(pipeline) {
            return None;
        }
        let reservation = reserve()?;
        self.states[pipeline]
            .phase
            .moved(Phase::Running, Phase::Finishing)
            .then_some(reservation)
    }

    /// What to do next, without blocking. A claim takes the package at the front of `preferred`'s
    /// queue where it may, and otherwise of the lowest pipeline whose queue it may take from; an
    /// ordered pipeline is skipped while a package of it is in flight. With no package to claim,
    /// it moves the lowest pipeline that may finish to finishing and hands its finish out, so
    /// exactly one claim does so for each pipeline. Otherwise it answers [`Next::Done`] once every
    /// pipeline has finished, and [`Next::Wait`] before. After a failure it answers
    /// [`Next::Failed`].
    pub fn try_claim(&self, preferred: Option<PipelineId>) -> Next {
        self.try_claim_with(preferred, &|_| true, &|_| Some(())).0
    }

    /// A successful reservation stays with its claim. A losing finish drops its reservation
    /// before the scan tries another pipeline.
    fn try_claim_with<R: Default>(
        &self,
        preferred: Option<PipelineId>,
        admits: &dyn Fn(PipelineId) -> bool,
        reserve: &dyn Fn(PipelineId) -> Option<R>,
    ) -> (Next, R) {
        // Read before the scan: a change the scan misses advances the generation past this one,
        // so a wait on it returns at once.
        let generation = self.generation.load(Ordering::SeqCst);
        if self.failed.load(Ordering::SeqCst) {
            return (Next::Failed, R::default());
        }
        if self.stopped.load(Ordering::SeqCst) {
            return (Next::Done, R::default());
        }
        let count = self.infos.len();
        if let Some(preferred) = preferred {
            self.state(preferred);
        }
        let scan = preferred.map(|p| p.0).into_iter().chain(0..count);
        if let Some((package, reservation)) = scan
            .filter(|&p| admits(PipelineId(p)))
            .find_map(|p| self.claim_from(p, || reserve(PipelineId(p))))
        {
            return (Next::Package(package), reservation);
        }
        for p in (0..count).filter(|&p| admits(PipelineId(p))) {
            if let Some(reservation) = self.try_begin_finish(p, || reserve(PipelineId(p))) {
                return (
                    Next::Finish {
                        pipeline: PipelineId(p),
                    },
                    reservation,
                );
            }
        }
        if self.unfinished.load(Ordering::Acquire) == 0 {
            return (Next::Done, R::default());
        }
        (Next::Wait(Generation(generation)), R::default())
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

    /// Whether a package of a pipeline `takes` admits is in flight, or claimable now: a claimant
    /// restricted to those pipelines may still change the run. Read before
    /// [`changed_since`](Self::changed_since), it misses no package: one that becomes claimable
    /// after it advances the generation. A package held back because its region meets one in
    /// flight becomes claimable at that package's acknowledgement, which advances the generation
    /// ([`acknowledge`](Self::acknowledge)).
    pub(crate) fn may_claim_where(&self, takes: &dyn Fn(PipelineId) -> bool) -> bool {
        (0..self.infos.len())
            .filter(|&p| takes(PipelineId(p)))
            .any(|p| self.may_claim_from(p))
    }

    fn may_claim_from(&self, p: usize) -> bool {
        if self.states[p].outstanding() == 0 {
            return false;
        }
        let queue = self.states[p]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        // A follower with only queued work may be waiting for its body's publication.
        !queue.in_flight.is_empty() || (!queue.ready.is_empty() && self.takes_from(p))
    }

    /// Whether a new package can start on an ordered pipeline. A retained scope request
    /// occupies its pipeline across several steps, even if another request is queued.
    fn may_start_ordered_package(&self, pipeline: PipelineId) -> bool {
        let p = pipeline.0;
        debug_assert!(self.infos[p].ordered);
        if self.outstanding(pipeline) == 0 {
            return false;
        }
        let queue = self.states[p]
            .queue
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        queue.in_flight.is_empty() && !queue.ready.is_empty() && self.takes_from(p)
    }

    /// A worker registers activity before claiming a finish. A request already
    /// finishing can be waiting for its body and needs another settlement pass.
    pub(crate) fn may_finish_where(&self, finishes: &dyn Fn(PipelineId) -> bool) -> bool {
        (0..self.infos.len())
            .filter(|&p| finishes(PipelineId(p)))
            .any(|p| self.ready_to_finish(p))
    }

    /// Whether the generation has advanced past `generation`: something changed that can make a
    /// claim succeed.
    pub(crate) fn changed_since(&self, generation: &Generation) -> bool {
        self.changes() != generation.0
    }

    /// Wake every thread asleep in [`wait`](Self::wait), as a change that can make a claim succeed
    /// does: a claimant that waited for a package in flight learns that it was acknowledged.
    pub(crate) fn wake_claimants(&self) {
        self.advance();
    }

    /// Whether the run has failed ([`fail`](Self::fail)).
    pub(crate) fn has_failed(&self) -> bool {
        self.failed.load(Ordering::SeqCst)
    }

    /// End the run's claims at a drained boundary: every claim from now answers [`Next::Done`],
    /// every notify that checks from now [`Admission::Stopped`], and every waiter wakes, so a
    /// worker of the pool stops before the run returns and a publisher waiting for credit returns.
    pub(crate) fn stop_claims(&self) {
        self.stopped.store(true, Ordering::SeqCst);
        self.advance();
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
        let freed_head = state.queue.acknowledge(&package, || {
            // Record consumption before unlocking the next ordered claim or publishing finish.
            #[cfg(test)]
            self.record(Event::Consume {
                pipeline: package.pipeline,
                guard: package.guard.clone(),
            });
            #[cfg(debug_assertions)]
            {
                let mut consumed = state
                    .consumed
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner);
                *consumed = Some(match consumed.take() {
                    Some(before) => before.union(&package.guard),
                    None => package.guard.clone(),
                });
            }
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
        self.ensure(freed_head.is_some(), refused);
        // An acknowledgement frees an ordered pipeline's next package or a package that waited
        // on the acknowledged one's region, may let the pipeline finish or a pipeline that follows
        // it claim, and returns credit to a limited source's notify. A claimant asleep on the
        // generation wakes only where it advances.
        if self.infos[p].ordered
            || self.infos[p].limit != usize::MAX
            || freed_head == Some(true)
            || acknowledged == state.queue.reserved()
        {
            self.advance();
        }
    }

    /// Move `pipeline` to finishing, outside a claim.
    ///
    /// # Panics
    ///
    /// When the pipeline has begun to finish already, a package queued for it has not been
    /// acknowledged, a pipeline it reads has not finished, its queue is not closed, or it is held.
    pub fn begin_finish(&self, pipeline: PipelineId) {
        let p = pipeline.0;
        self.state(pipeline);
        self.ensure(self.try_begin_finish(p, || Some(())).is_some(), || {
            format!("pipeline {p} finishes once, after its queue is closed and consumed and its hold is released")
        });
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
        let pending = std::mem::take(&mut pushes.pending);
        if self.failed.load(Ordering::SeqCst) {
            return;
        }
        if pending.is_empty() {
            return;
        }
        self.ensure(self.states[p].phase.load() != Phase::Finished, || {
            format!("pipeline {p} lands its pushes before it finishes")
        });
        self.land_in(p, &pending, pushes.to.as_ref());
        self.advance();
    }

    /// Push `pending`, pushed by `pipeline`: each morsel through `to`, its breaker's consumer, as
    /// one region of the breaker's keys, a projection at any level, and each reader's completion
    /// through the subscription it names. Each reader's queue stays open until the last pipeline it
    /// reads finishes.
    fn land_in(&self, pipeline: usize, pending: &[Push], to: Option<&SharedConsumer>) {
        let mut landing = Landing::push(self, PipelineId(pipeline));
        for push in pending {
            match (push, to) {
                (Push::Reader(reader, region), _) => {
                    crate::interpreter::notifications::notify_shared(reader, region, &mut landing);
                }
                (Push::Morsel(morsel), Some(to)) => {
                    let region = Projection::of(morsel).unwrap_or_else(|why| {
                        self.refuse(format!(
                            "pipeline {pipeline} pushes regions of its keys: {why}"
                        ))
                    });
                    crate::interpreter::notifications::notify_shared(to, &region, &mut landing);
                }
                // A test's push ([`Pushes::push`]) names no consumer and lands in each reader as
                // it is.
                #[cfg(test)]
                (Push::Morsel(morsel), None) => {
                    for &reader in &self.infos[pipeline].readers {
                        landing.queue(PipelineId(reader), morsel);
                    }
                }
                #[cfg(not(test))]
                (Push::Morsel(_), None) => {
                    unreachable!("a breaker's push names the consumer it climbs")
                }
            }
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
        let pending = std::mem::take(&mut pushes.pending);
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
        self.land_in(p, &pending, pushes.to.as_ref());
        for &reader in &self.infos[p].readers {
            self.count_toward_close(reader);
        }
        self.unfinished.fetch_sub(1, Ordering::AcqRel);
        self.advance();
    }

    /// Every pipeline with a claim in flight, and what the claim took: a package no acknowledgement
    /// has completed, or the pipeline's finish, which moved it to finishing and which
    /// [`finish`](Self::finish) has not completed.
    #[cfg(debug_assertions)]
    fn in_flight(&self) -> Vec<(usize, &'static str)> {
        let mut in_flight = Vec::new();
        for (pipeline, state) in self.states.iter().enumerate() {
            let queue = state
                .queue
                .state
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if !queue.in_flight.is_empty() {
                in_flight.push((pipeline, "a claimed package"));
            }
            if state.phase.load() == Phase::Finishing {
                in_flight.push((pipeline, "its claimed finish"));
            }
        }
        in_flight
    }

    /// How many of `pipeline`'s packages are queued and not acknowledged.
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
        (0..self.infos.len()).find_map(|p| self.claim_of(PipelineId(p)))
    }

    /// The package at the front of `pipeline`'s queue, claimed, where a claim may take one.
    #[cfg(test)]
    pub(crate) fn claim_of(&self, pipeline: PipelineId) -> Option<WorkPackage> {
        self.claim_from(pipeline.0, || Some(()))
            .map(|(package, ())| package)
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
    // Of a finite range of outermost positions, a region past the last names no row, nor any
    // part of a row's values beneath it.
    let rows = match input.domain_extent() {
        Some(Extent::UIntRange(positions)) if !rows.is_universal() => {
            let held = TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
                intervalsets::IntervalSet::from_iter(positions.intervals().iter().filter_map(
                    |run| {
                        Some(intervalsets::Interval::closed(
                            Value::UInt(*run.lval()?),
                            Value::UInt(*run.rval()?),
                        ))
                    },
                )),
            )));
            match Projection::of(rows) {
                Ok(
                    region @ (Projection::Keys { .. }
                    | Projection::Within { .. }
                    | Projection::Or(_)),
                ) => {
                    let Ok(held) = Projection::of(&held) else {
                        unreachable!("a range of positions is keys")
                    };
                    region.intersect(&held).guard(input)
                }
                _ => rows.clone(),
            }
        }
        _ => rows.clone(),
    };
    nonempty(guard_minus(&rows, released).closed_over(input))
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
/// ([`Consumer::notify`]), each operator on the way restates it in its own keys, and the [`Entry`] of
/// each breaker it reaches queues it for that breaker's pipeline.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    pipeline: usize,
    pending: Vec<Push>,
    /// The consumer the morsels climb, the pushing breaker's.
    to: Option<SharedConsumer>,
    /// Whether the breaker completed a region no projection spells, which no push names yet
    /// ([`push_final`](Self::push_final)). A finish leaves none.
    unspelled: bool,
}

/// One push a [`Pushes`] holds until it lands.
enum Push {
    /// A region of the breaker's keys, which climbs the breaker's consumer.
    Morsel(TileGuard),
    /// A region one subscription takes as complete apart from the breaker's clock, as a closed
    /// transaction key's readers do ([`Pushes::push_to`]).
    Reader(SharedConsumer, Projection),
}

impl Pushes<'_> {
    /// Push `region` to `reader` alone, through its usual notification path once the breaker has
    /// released its borrow. The breaker's other readers keep their own frontier.
    pub(crate) fn push_to(&mut self, reader: SharedConsumer, region: Projection) {
        if self.has_readers() {
            self.pending.push(Push::Reader(reader, region));
        }
    }

    pub(crate) fn has_readers(&self) -> bool {
        !self.dispatcher.infos[self.pipeline].readers.is_empty()
    }

    pub(crate) fn morsel_rows(&self) -> usize {
        self.dispatcher.morsel_rows
    }

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
        if !self.has_readers() {
            return;
        }
        // A push names a projection of the breaker's keys, so it pushes the part of the final
        // guard a projection spells. The rest, such as a record whose collection field is
        // complete through some rows, is pushed once a projection spells what it has grown to, at
        // the latest once it is whole, which a finish checks.
        let complete = breaker.final_guard();
        let spelled = spelled_part(&complete).unwrap_or_else(|| breaker.tiling().empty_guard());
        self.unspelled = Projection::of(&complete).is_err() && !complete.is_empty();
        self.push_region(breaker, &spelled, |guard, rows| {
            breaker.morsels(guard, rows)
        });
    }

    /// Record a publishable region once across all claimants, then cut only its new part.
    pub(crate) fn push_region<B: BreakingProducer + ?Sized>(
        &mut self,
        breaker: &B,
        region: &TileGuard,
        cut: impl FnOnce(&TileGuard, usize) -> Vec<TileGuard>,
    ) {
        let to = breaker.base().downstream.clone();
        self.dispatcher.ensure(to.is_some(), || {
            format!(
                "{}, which pipeline {} reads, pushes to a consumer",
                breaker.name(),
                self.pipeline
            )
        });
        self.to = to;
        let guard = self.record(|pushed| match pushed {
            Some(pushed) => guard_minus(region, pushed),
            None => region.clone(),
        });
        self.cut(&guard, cut);
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
        self.pending.extend(morsels.into_iter().map(Push::Morsel));
    }
}

impl Drop for Pushes<'_> {
    /// Refuses to drop pushes that never landed, which would lose the reader's packages.
    fn drop(&mut self) {
        if !thread::panicking() {
            let landed = self.pending.is_empty();
            self.dispatcher.ensure(landed, || {
                format!(
                    "pipeline {} lands its pushes through Dispatcher::land or \
                         Dispatcher::finish",
                    self.pipeline
                )
            });
        }
    }
}

/// Where a push lands: its target, which queues it or, in a planner's probe or route walk, records
/// it; and the pipeline that pushed it.
pub struct Landing<'d> {
    target: Target<'d>,
    from: usize,
    /// Per shared consumer this landing has notified, by address, the region it passed on
    /// ([`unjoined`](Self::unjoined)).
    joined: Vec<(usize, Projection)>,
}

/// What a [`Landing`] does with the regions that reach an [`Entry`].
enum Target<'d> {
    /// Queues each in the reader's queue. A region that reaches the pushing pipeline's own entry,
    /// pushed by a range in that pipeline's chain, is collected in `own` for the pipeline to queue
    /// once it has dropped what its input released ([`Landing::push`]).
    Queue {
        dispatcher: &'d Dispatcher,
        own: Vec<TileGuard>,
    },
    /// Records each, for a planner that probes which region of a reader's input a pipeline's push
    /// names; which edges keep keys the planner reads off a route walk ([`Landing::route`]).
    Probe(Vec<Arrival>),
    /// Records each entry the push reaches, for a planner that reads a pusher's routes
    /// ([`Landing::route`]).
    Route { routes: Vec<Route> },
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
            Target::Queue { dispatcher, .. } => {
                pipeline.0 == self.from
                    || dispatcher.infos[pipeline.0]
                        .ingress
                        .as_ref()
                        .is_none_or(|from| from.contains(&self.from))
            }
            Target::Probe(_) | Target::Route { .. } => true,
        }
    }

    /// Whether this landing queues what reaches an entry: a delivery, not a planner's probe or
    /// route walk.
    pub(crate) fn is_delivery(&self) -> bool {
        matches!(self.target, Target::Queue { .. })
    }

    fn new(target: Target<'_>, from: usize) -> Landing<'_> {
        Landing {
            target,
            from,
            joined: Vec::new(),
        }
    }

    /// The part of `region` that the shared consumer at address `join` has not passed on in this
    /// landing, recorded as passed on; `None` where that part is empty. A push that fans out and
    /// meets again at one shared consumer reaches it once per path, and a reader reads its
    /// package only once the landing has ended, so a region repeated within one landing names
    /// nothing new. A landing that queues nothing passes every region on: a planner's probe or
    /// route walk reads every path.
    pub(crate) fn unjoined(&mut self, join: usize, region: &Projection) -> Option<Projection> {
        if !self.is_delivery() {
            return Some(region.clone());
        }
        let Some((_, passed)) = self.joined.iter_mut().find(|(at, _)| *at == join) else {
            self.joined.push((join, region.clone()));
            return Some(region.clone());
        };
        let new = region.minus(passed);
        if new == Projection::Nothing {
            return None;
        }
        *passed = passed.union(region);
        Some(new)
    }

    /// A landing that records where `from`'s push arrives, and queues nothing.
    pub(crate) fn probe(from: PipelineId) -> Landing<'static> {
        Landing::new(Target::Probe(Vec::new()), from.0)
    }

    /// A landing for a push of `from`: a breaker's, or the keys a range in `from`'s chain has newly
    /// yielded. What reaches another pipeline's entry is queued there; what reaches `from`'s own
    /// entry is collected ([`own_arrivals`](Self::own_arrivals)).
    pub(crate) fn push(dispatcher: &Dispatcher, from: PipelineId) -> Landing<'_> {
        Landing::new(
            Target::Queue {
                dispatcher,
                own: Vec::new(),
            },
            from.0,
        )
    }

    /// What a [`push`](Self::push) brought to its own pipeline's entry.
    pub(crate) fn own_arrivals(self) -> Vec<TileGuard> {
        match self.target {
            Target::Queue { own, .. } => own,
            _ => panic!("only a queueing landing collects its own pipeline's arrivals"),
        }
    }

    /// A landing that records the routes a push takes: each entry it reaches. A planner walks a
    /// pusher's consumer with it ([`Consumer::notify`]), so the routes it plans are the paths a
    /// push takes.
    pub(crate) fn route() -> Landing<'static> {
        Landing::new(Target::Route { routes: Vec::new() }, usize::MAX)
    }

    /// What a probing landing recorded.
    pub(crate) fn arrivals(self) -> Vec<Arrival> {
        match self.target {
            Target::Probe(arrivals) => arrivals,
            Target::Queue { .. } | Target::Route { .. } => {
                panic!("only a probing landing records arrivals")
            }
        }
    }

    /// What a routing landing recorded.
    pub(crate) fn routes(self) -> Vec<Route> {
        match self.target {
            Target::Route { routes, .. } => routes,
            _ => panic!("only a routing landing records routes"),
        }
    }

    /// Queue `guard`, a guard of the input of `reader`'s breaker, as a package of `reader`, named as
    /// the rows of that input ([`Dispatcher::rows_named`]). A push that reaches the pushing
    /// pipeline's own entry is kept for it to queue once it has dropped what its input released. A
    /// reader that follows the pipeline that pushed ([`Dispatcher::follow`]) takes no push: a loop's
    /// round queues its rows. A probe and a routing landing record the arrival and queue nothing.
    ///
    /// # Panics
    ///
    /// When `reader` does not read the pipeline that pushed, has begun to finish, or has a closed
    /// queue.
    pub fn queue(&mut self, reader: PipelineId, guard: &TileGuard) {
        let dispatcher = match &mut self.target {
            Target::Queue { own, .. } if reader.0 == self.from => {
                own.push(guard.clone());
                return;
            }
            Target::Queue { dispatcher, .. } => *dispatcher,
            Target::Probe(arrivals) => {
                arrivals.push(Arrival {
                    pipeline: reader,
                    guard: guard.clone(),
                });
                return;
            }
            Target::Route { routes, .. } => {
                routes.push(Route { pipeline: reader });
                return;
            }
        };
        let (from, r) = (self.from, reader.0);
        let guard = &dispatcher.rows_named(r, guard);
        dispatcher.state(reader);
        dispatcher.ensure(dispatcher.infos[r].reads.contains(&from), || {
            format!("pipeline {from} pushes to pipeline {r}, which reads it")
        });
        let info = &dispatcher.infos[r];
        // A nested loop's scope, and a reader that waits for one, takes its rows in rounds.
        if info.follows.contains(&from) {
            return;
        }
        dispatcher.ensure(!info.walked.contains(&(from, false)), || {
            format!(
                "a push of pipeline {from} reaches pipeline {r} along a path its planner's \
                     route walk did not take"
            )
        });
        let queue = &dispatcher.states[r];
        dispatcher.ensure(queue.phase.load() == Phase::Running, || {
            format!("pipeline {r} receives packages before it finishes")
        });
        dispatcher.ensure(queue.queue.append(std::slice::from_ref(guard)), || {
            format!("pipeline {r} receives packages before the last pipeline it reads finishes")
        });
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
            Target::Probe(_) | Target::Route { .. } => {
                panic!("{message}")
            }
        }
    }
}

/// One path of a push to the entry of a pipeline, as a route walk records it ([`Landing::route`]).
pub(crate) struct Route {
    /// The pipeline whose entry the path reaches.
    pub(crate) pipeline: PipelineId,
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
    /// The scope an unplaced entry offers a push to ([`CompletionTarget`]).
    completes: CompletionTarget,
}

/// The scope an unplaced [`Entry`] offers a push to, and the scope's input, which the entry's input
/// keys name the same rows of: a scope's drive reads its source by pull, so the entry in front of
/// the source queues nothing, but the positions or items the drive emits are the source's keys,
/// so what the source pushes of its keys is what the scope's input can take. `None` where nothing
/// is offered, as in front of any other pulled input.
// shared-state-ok: the drive and the entry in front of its source both hold it, the planner
// writes it before the run, and what crosses it is a scope's intake and a tiling, never a tile.
pub type CompletionTarget = Arc<RwLock<Option<(Offers, Tiling)>>>;

/// The pipeline an [`Entry`] queues for, which a planner sets once it has put the entry's breaker
/// in one: `None` before, as in a run that only pulls, where the entry queues nothing.
#[derive(Clone, Default)]
pub struct Placement {
    // shared-state-ok: the breaker and the entry at its input both hold it, the planner writes it
    // before the run, and what crosses it is a pipeline's index, never a tile.
    pipeline: Arc<RwLock<Option<PipelineId>>>,
    /// The intake of the scope whose body or store the entry sits in, which a push the entry's
    /// pipeline does not take wakes ([`Entry::wake`]); `None` outside a scope.
    // shared-state-ok: the scope's run sets it and clears it at the run's end, and what crosses it
    // is the scope's intake of guards of its input, never a tile.
    scope: Arc<RwLock<Option<Offers>>>,
}

impl Placement {
    pub fn get(&self) -> Option<PipelineId> {
        *self.pipeline.read().unwrap_or_else(PoisonError::into_inner)
    }

    pub fn set(&self, pipeline: Option<PipelineId>) {
        *self
            .pipeline
            .write()
            .unwrap_or_else(PoisonError::into_inner) = pipeline;
    }

    /// Record `scope`, the intake of the scope the entry sits in ([`Entry::wake`]).
    pub(crate) fn set_scope(&self, scope: Option<Offers>) {
        let mut held = self.scope.write().unwrap_or_else(PoisonError::into_inner);
        debug_assert!(
            match (&*held, &scope) {
                (Some(before), Some(after)) => Arc::ptr_eq(before, after),
                _ => true,
            },
            "an entry belongs to one scope's run at a time: the run's cleanup clears the scope it \
             set"
        );
        *held = scope;
    }

    fn scope(&self) -> Option<Offers> {
        self.scope
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

impl Entry {
    /// The entry of `pipeline`, whose breaker reads `input`.
    #[cfg(test)]
    pub fn new(pipeline: PipelineId, input: Tiling) -> Self {
        let placement = Placement::default();
        placement.set(Some(pipeline));
        Entry {
            pipeline: placement,
            input,
            completes: CompletionTarget::default(),
            inline: None,
        }
    }

    /// The entry of a breaker that reads `input`, and its placement, which
    /// the breaker keeps for a planner to set ([`ProducerBase::placement`]).
    ///
    /// [`ProducerBase::placement`]: crate::interpreter::tile_operators::ProducerBase
    pub fn unplaced(input: Tiling) -> (Self, Placement) {
        let pipeline = Placement::default();
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

    /// The scope this entry offers a push to while it is unplaced, which the holder keeps for a
    /// planner to set ([`CompletionTarget`]).
    pub fn complete_target(&self) -> CompletionTarget {
        self.completes.clone()
    }

    /// Offer the scope the entry sits in its positions waiting for inputs, for a push no pipeline
    /// here takes: something the scope's body reads has grown, so a request may now decide them.
    /// The region pushed names what grew, not which waiting positions it decides, so all of them
    /// become eligible together. A further wake is remembered for the next decision to park.
    ///
    /// A placed entry records what reached it (`Offered::grown`), whether or not positions wait, so
    /// its pipeline reads it with the next round or attempt: a push that arrives while a round or
    /// attempt runs is read by the one after it.
    fn wake(&self, region: &Projection) {
        let Some(scope) = self.pipeline.scope() else {
            return;
        };
        let mut offered = scope.lock().unwrap_or_else(PoisonError::into_inner);
        offered.wake();
        if let (Some(pipeline), Some(guard)) =
            (self.pipeline.get(), pushed_guard(region, &self.input))
        {
            match offered.grown.iter_mut().find(|(at, _)| at.0 == pipeline.0) {
                Some((_, before)) => *before = before.union(&guard),
                None => offered.grown.push((pipeline, guard)),
            }
        }
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
#[cfg(any(test, feature = "test-helpers"))]
pub(crate) fn is_in_a_run() -> bool {
    IN_A_RUN.with(Cell::get)
}

impl Consumer for Entry {
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        if let Some(pipeline) = self.pipeline.get()
            && landing.accepts_entry(pipeline)
        {
            if let Some(guard) = pushed_guard(region, &self.input) {
                landing.queue(pipeline, &guard);
            }
            return;
        }
        if landing.is_delivery() {
            self.wake(region);
        }
        if self.pipeline.get().is_some() {
            return;
        }
        // In front of a drive's source, a push offers its keys to the scope the drive runs in.
        if landing.is_delivery()
            && let Some((offers, input)) = &*self
                .completes
                .read()
                .unwrap_or_else(PoisonError::into_inner)
            && let Some(guard) = pushed_guard(region, input)
        {
            let mut offered = offers.lock().unwrap_or_else(PoisonError::into_inner);
            offered.offer(guard);
        }
        if landing.is_delivery()
            && let Some(inline) = &self.inline
        {
            inline.notify(region, landing);
        }
    }
}

/// `guard`, a region an entry lands, as rows of `input`, the breaker input its pipeline consumes
/// ([`Dispatcher::rows_named`]): itself where it is a guard of `input`, and every row where it is a
/// region of another tiling, as of another of the breaker's inputs or of an input a chain
/// reshapes.
pub(crate) fn rows_named_in(input: &Tiling, guard: &TileGuard) -> TileGuard {
    match guard.check_from(input) {
        true => guard.clone(),
        false => input.universal_guard(),
    }
}

/// The guard of `input` a push of `region` names at a pipeline's entry, and `None` where it names
/// nothing. It is closed over `input`, so a region under every tag of a tagged union is the
/// universal guard, as a pull of every arm is.
pub(crate) fn pushed_guard(region: &Projection, input: &Tiling) -> Option<TileGuard> {
    match region {
        Projection::Within { .. } | Projection::Or(_) => {
            Some(region.guard(input).closed_over(input))
        }
        Projection::Nothing => None,
        Projection::Everything => Some(input.universal_guard()),
        // A push of a row's remainder lands as itself: it states the row's end.
        Projection::Keys { .. } => Some(closed_keeping_row_ends(region.guard(input), input)),
        // Each field is closed over its own tiling, as a push of that field alone would be.
        Projection::Fields { .. } => {
            let Tiling::Record(fields) = input else {
                panic!("{region:?} names the fields of a record, and {input} is none")
            };
            Some(TileGuard::Record(
                fields
                    .iter()
                    .map(|(name, field)| {
                        let part = pushed_guard(&region.field(name), field)
                            .unwrap_or_else(|| field.empty_guard());
                        (name.clone(), part)
                    })
                    .collect(),
            ))
        }
    }
}

/// `input`'s universal guard cut as [`seed_within`] cuts a region: every `rows` keys where the
/// input's tiling states a finite range of positions for its outermost keys, and one morsel
/// otherwise.
#[cfg(test)]
fn seed(input: &Tiling, rows: usize) -> Vec<TileGuard> {
    seed_within(input, &input.universal_guard(), rows)
}

/// `region`, a guard of `input`, cut into morsels: every `rows` of the
/// positions both the range and `region` hold, where `input` states a finite range of positions
/// and `region` names runs of them, and whole otherwise. Only the positions `region` holds are
/// counted, so a region of a few positions of a large range is cut in as many steps.
fn seed_within(input: &Tiling, region: &TileGuard, rows: usize) -> Vec<TileGuard> {
    let Some(domain) = input.domain_extent() else {
        return vec![region.clone()];
    };
    let (Extent::UIntRange(positions), TileGuard::Function(FunctionGuard::Domain(keys))) =
        (&domain, region)
    else {
        return vec![region.clone()];
    };
    let Some(range) = closed_runs(positions, |at| Some(u128::from(*at)), None) else {
        return vec![region.clone()];
    };
    let runs = match keys {
        Predicate::True => range,
        Predicate::Intervals(held) => {
            // An unbounded end of a run of keys is the first or last `u64`.
            let Some(held) = closed_runs(held, uint_position, Some((0, u128::from(u64::MAX))))
            else {
                return vec![region.clone()];
            };
            intersect_runs(&range, &held)
        }
        _ => return vec![region.clone()],
    };
    let morsels = cut_before(keys, &cuts_every(runs, rows), &domain);
    #[cfg(test)]
    MORSELS_SEEDED.with(|seeded| seeded.set(seeded.get() + morsels.len()));
    morsels
}

// shared-state-ok: a test's count of the morsels this thread's seeds cut. Nothing crosses it
// between operators.
#[cfg(test)]
thread_local! {
    // shared-state-ok: the count itself, for the reason on the macro above. The checker's upward
    // scan stops at `thread_local! {`, so the note above does not reach this line.
    static MORSELS_SEEDED: Cell<usize> = const { Cell::new(0) };
}

/// The positions both `a` and `b` hold, each a list of closed runs in ascending order.
fn intersect_runs(a: &[(u128, u128)], b: &[(u128, u128)]) -> Vec<(u128, u128)> {
    let (mut i, mut j, mut both) = (0, 0, Vec::new());
    while i < a.len() && j < b.len() {
        let (first, last) = (a[i].0.max(b[j].0), a[i].1.min(b[j].1));
        if first <= last {
            both.push((first, last));
        }
        if a[i].1 < b[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    both
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
pub type BreakerHandle = Arc<RwLock<dyn BreakingProducer>>;

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
/// pipeline, starts with its breaker's input whole, as one package per morsel ([`seed_within`]),
/// and is closed. The driver consumes the package of the lowest pipeline that has one; when no
/// pipeline has one, it finishes the lowest pipeline that may finish. It stops when every pipeline
/// has finished. Every breaker initializes its per-run state before the first package.
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
            breaker
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .begin_run();
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
        work: std::cell::RefCell<Option<F>>,
        result: std::cell::RefCell<Option<R>>,
    }
    impl<F: FnOnce() -> R, R> Breaker for Command<F, R> {
        fn as_producer(&self) -> Option<&dyn BreakingProducer> {
            None
        }
        fn consume_impl(&self, _: InputId, _: TileGuard) {
            *self.result.borrow_mut() = Some(self.work.borrow_mut().take().expect("one command")());
        }
        fn input_tiling(&self, _: InputId) -> Tiling {
            Tiling::Scalar(Extent::Base(crate::interpreter::BaseType::Unit))
        }
        fn input_released(&self, _: InputId) -> TileGuard {
            TileGuard::Scalar(if self.work.borrow().is_none() {
                Predicate::True
            } else {
                Predicate::False
            })
        }
    }
    let mut command = Command {
        work: std::cell::RefCell::new(Some(work)),
        result: std::cell::RefCell::new(None),
    };
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    in_a_run(|| {
        drive(&dispatcher, &mut |_, call| {
            call(&mut command, InputId::ONLY)
        })
    });
    command
        .result
        .into_inner()
        .expect("the dispatcher consumes the command")
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
pub(crate) fn notify_for_test<C: Consumer + ?Sized>(consumer: &C, region: &Projection) {
    let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
    let mut landing = Landing::new(
        Target::Queue {
            dispatcher: &dispatcher,
            own: Vec::new(),
        },
        0,
    );
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
        let mut breaker = breakers[pipeline.0]
            .write()
            .unwrap_or_else(PoisonError::into_inner);
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
            Next::Finish { pipeline } => finish_with(dispatcher, reach, pipeline),
            Next::Wait(_) => {
                panic!("an acyclic graph with nothing queued has a pipeline that may finish")
            }
            Next::Done => return,
            Next::Failed => panic!("a run on one thread fails only by panicking on it"),
        }
    }
}

/// Queue each source pipeline's input whole, as one package per morsel ([`seed_within`]), and
/// close it. [`run`] starts here.
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
    let mut pushes = dispatcher.pushes(package.pipeline);
    reach(package.pipeline, &mut |breaker, input| {
        if let Some(producer) = package.consume(breaker, input, &mut pushes) {
            pushes.push_final(producer);
        }
    });
    if !pushes.pending.is_empty() {
        dispatcher.land(pushes);
    }
    dispatcher.acknowledge(package);
}

enum Publication {
    Busy,
    Published,
    Settled,
}

/// Only a complete pass that published nothing can release a body's follower hold.
fn try_push_held(
    dispatcher: &Dispatcher,
    pipelines: impl IntoIterator<Item = PipelineId>,
    mut reach: impl FnMut(PipelineId, &mut Call<'_>) -> bool,
) -> Publication {
    let mut published = false;
    for pipeline in pipelines {
        if dispatcher.states[pipeline.0].phase.load() == Phase::Finished {
            continue;
        }
        let mut landed = None;
        let reached = reach(pipeline, &mut |breaker, _| {
            if let Some(producer) = breaker.as_producer() {
                let mut pushes = dispatcher.pushes(pipeline);
                pushes.push_final(producer);
                landed = Some(pushes);
            }
        });
        if !reached {
            return if published {
                Publication::Published
            } else {
                Publication::Busy
            };
        }
        if let Some(pushes) = landed {
            published |= !pushes.pending.is_empty();
            dispatcher.land(pushes);
        }
    }
    if published {
        Publication::Published
    } else {
        Publication::Settled
    }
}

/// Finish `pipeline`, after checking what a finish rests on.
///
/// # Panics
///
/// When the pipeline has begun to finish already, its queue is not closed or not empty, a package
/// claimed for it is in flight, or a pipeline it reads has not finished. In a debug build, also
/// when its breaker's input has not released every guard the pipeline acknowledged
/// ([`Breaker::input_released`]), and where the guard algebra has no exact difference of the
/// acknowledged guards and the guard the input released ([`guard_minus`]).
pub fn finish_pipeline(dispatcher: &Dispatcher, breakers: &[BreakerHandle], pipeline: PipelineId) {
    dispatcher.begin_finish(pipeline);
    finish_with(dispatcher, &mut handles(breakers), pipeline);
}

/// Finish `pipeline`, which has begun: in a debug build check that its breaker's input has
/// released every guard the pipeline acknowledged ([`Breaker::input_released`]), push what it
/// completed and no consume pushed, through the breaker's [`finish`][Breaker::finish], then mark
/// it finished.
///
/// [Breaker::finish]: crate::interpreter::tile_operators::Breaker::finish
fn finish_with(dispatcher: &Dispatcher, reach: &mut Reach<'_>, pipeline: PipelineId) {
    let p = pipeline.0;
    // As in `consume_with`, the pushes land once the reach has returned.
    let mut finished = None;
    reach(pipeline, &mut |breaker, input| {
        #[cfg(debug_assertions)]
        {
            let consumed = dispatcher.states[p]
                .consumed
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            let released = breaker.input_released(input);
            let left = consumed.and_then(|consumed| {
                unreleased(&consumed, &released, &breaker.input_tiling(input))
            });
            dispatcher.ensure(left.is_none(), || {
                format!(
                    "pipeline {p} finishes after its input has released every guard the \
                     pipeline acknowledged: {left:?} is not released"
                )
            });
        }
        let mut pushes = dispatcher.pushes(pipeline);
        breaker.finish(input, &mut pushes);
        dispatcher.ensure(!pushes.unspelled, || {
            format!(
                "pipeline {p} finishes having pushed all it completed: a region no projection \
                 spells would reach no reader"
            )
        });
        finished = Some(pushes);
    });
    dispatcher.finish(finished.expect("a reach calls the breaker it reaches"));
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_read_counts_as_finished_for_intake_only_after_its_last_push_lands() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        struct LastPush {
            reader: PipelineId,
        }
        impl Consumer for LastPush {
            fn notify(&self, _: &Projection, landing: &mut Landing<'_>) {
                let Target::Queue { dispatcher, .. } = &landing.target else {
                    unreachable!()
                };
                assert!(
                    dispatcher.infos[self.reader.0]
                        .reads
                        .iter()
                        .all(|&p| dispatcher.states[p].phase.load() == Phase::Finished)
                );
                assert!(!dispatcher.only_arrivals_remain(self.reader));
                landing.queue(self.reader, &keys_between(0, 0));
            }
        }

        let mut dispatcher = Dispatcher::new(vec![vec![], vec![], vec![0, 1]], 1);
        let reader = PipelineId(2);
        dispatcher.take_arrivals(reader);
        for p in [PipelineId(0), PipelineId(1)] {
            dispatcher.close(p);
            dispatcher.begin_finish(p);
        }
        dispatcher.finish(dispatcher.pushes(PipelineId(0)));
        let mut pushes = dispatcher.pushes(PipelineId(1));
        pushes.push(&keys_between(0, 0), |guard, _| vec![guard.clone()]);
        pushes.to = Some(Arc::new(LastPush { reader }));
        dispatcher.finish(pushes);
        assert!(dispatcher.only_arrivals_remain(reader));
        dispatcher.close(reader);
        let package = dispatcher
            .claim_of(reader)
            .expect("the last push is claimable");
        assert!(!dispatcher.ready_to_finish(reader.0));
        dispatcher.acknowledge(package);
        assert!(dispatcher.ready_to_finish(reader.0));
    }

    /// A chain of diamonds: each layer's two pipelines read the one below, and the pipeline
    /// above reads both. A path of reads to the bottom doubles at each layer, and a quiescence
    /// check of the top reads each pipeline once.
    #[test]
    fn a_quiescence_check_reads_each_pipeline_once() {
        const LAYERS: usize = 16;
        let mut reads = vec![vec![]];
        for _ in 0..LAYERS {
            let below = reads.len() - 1;
            reads.push(vec![below]);
            reads.push(vec![below]);
            reads.push(vec![below + 1, below + 2]);
        }
        let top = reads.len() - 1;
        let pipelines = reads.len();
        let dispatcher = Dispatcher::new(reads, 1).unrecorded();
        assert!(dispatcher.quiescent([top]), "nothing is queued");
        assert_eq!(
            dispatcher.quiescence_reads.load(Ordering::Relaxed),
            pipelines
        );
    }

    /// A release decided against the hold read before a publication pass fails where a hold was
    /// taken since, as a worker's after a claim of the body, and leaves the body held. It succeeds
    /// against the hold as it stands; a released hold is not released twice.
    #[test]
    fn a_release_fails_after_a_hold_taken_since_it_read_the_hold() {
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        let (body, step) = (PipelineId(0), PipelineId(1));
        let group = dispatcher.add_hold_group([body, step]);
        let held = || dispatcher.followers_hold(group).0 & 1 == 1;
        dispatcher.hold_followers(group);
        let read = dispatcher.followers_hold(group);
        dispatcher.hold_followers(group);
        assert!(!dispatcher.release_followers_if(group, read));
        assert!(held(), "a failed release releases nothing");
        let read = dispatcher.followers_hold(group);
        assert!(dispatcher.release_followers_if(group, read));
        assert!(!held());
        let read = dispatcher.followers_hold(group);
        assert!(!dispatcher.release_followers_if(group, read));
    }

    /// The placements a planning pass sets are cleared when a probe in the pass unwinds.
    #[test]
    fn placements_a_pass_sets_are_cleared_when_it_unwinds() {
        let placements: Vec<Vec<Placement>> = vec![
            vec![Placement::default()],
            Vec::new(),
            vec![Placement::default(), Placement::default()],
        ];
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _placed = plan::ClearsPlacements(&placements);
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

            fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
                self.tiling().empty_tile()
            }

            fn release_impl(&self, _obsolete_guard: TileGuard) {}
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
            let inputs = super::super::plan::visit_inputs_checked(
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
            super::super::plan::visit_inputs_checked(
                &mut two_inputs(Walk::Swapped),
                &mut |_, _| {},
            );
        }

        /// A mutable walk that visits each input under the other's role keeps the producers and
        /// the count and panics.
        #[test]
        #[should_panic(expected = "under `b` mutably as its input 0, where it lists")]
        fn a_walk_that_swaps_two_roles_panics() {
            super::super::plan::visit_inputs_checked(
                &mut two_inputs(Walk::RolesSwapped),
                &mut |_, _| {},
            );
        }

        /// A mutable walk that visits one input twice keeps the count and panics.
        #[test]
        #[should_panic(expected = "mutably as its input 1, where it lists")]
        fn a_walk_that_repeats_an_input_panics() {
            super::super::plan::visit_inputs_checked(
                &mut two_inputs(Walk::FirstTwice),
                &mut |_, _| {},
            );
        }
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

    /// A package whose region meets one in flight waits for that package's acknowledgement, and the
    /// packages behind it wait with it; a package disjoint from every one in flight claims at once.
    #[test]
    fn a_package_waits_for_an_overlapping_one_in_flight() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let dispatcher = Dispatcher::new(vec![vec![]], 1 << 20).unrecorded();
        let source = PipelineId(0);
        dispatcher.notify(source, &keys_between(0, 9));
        let first = dispatcher
            .claim_of(source)
            .expect("the first package claims");
        dispatcher.notify(source, &keys_between(20, 29));
        let disjoint = dispatcher
            .claim_of(source)
            .expect("a package disjoint from the one in flight claims");
        assert_eq!(disjoint.guard, keys_between(20, 29));
        dispatcher.notify(source, &keys_between(5, 14));
        dispatcher.notify(source, &keys_between(40, 49));
        assert!(
            dispatcher.claim_of(source).is_none(),
            "a package meeting one in flight waits, and the package behind it waits with it"
        );
        dispatcher.acknowledge(first);
        let overlapping = dispatcher
            .claim_of(source)
            .expect("the acknowledgement frees the overlapping package");
        assert_eq!(overlapping.guard, keys_between(5, 14));
        for package in [disjoint, overlapping] {
            dispatcher.acknowledge(package);
        }
    }

    #[test]
    fn disjoint_fields_can_be_claimed_on_the_same_row() {
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Record([("a".into(), scalar.clone()), ("b".into(), scalar)].into()),
        );
        let field = |key, name| {
            Projection::within(
                crate::interpreter::CurryLevel::OUTERMOST,
                Predicate::point(Value::UInt(key)),
                Projection::of_field(name, Projection::Everything),
            )
            .guard(&tiling)
        };
        let first = field(0, "a");
        let other = field(1, "b");
        let same = field(0, "b");
        assert!(first.intersect(&same).is_empty());
        let queue = Queue::new();
        let guards = [first, other, same];
        queue.append(&guards);
        for guard in guards {
            let (package, ()) = queue.claim(0, false, || Some(())).expect("disjoint field");
            assert_eq!(package.guard, guard);
        }
    }

    /// The acknowledgement that frees a package waiting on an overlapping one wakes a claimant
    /// asleep on the pipeline, with no other change to the dispatcher. The claimant is asleep in
    /// [`Dispatcher::wait`] before the acknowledgement, and must return within a bounded wait.
    #[test]
    fn acknowledging_an_overlap_wakes_a_sleeping_claimant() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::time::{Duration, Instant};
        let dispatcher = Dispatcher::new(vec![vec![]], 1 << 20).unrecorded();
        let source = PipelineId(0);
        dispatcher.notify(source, &keys_between(0, 9));
        let first = dispatcher
            .claim_of(source)
            .expect("the first package claims");
        dispatcher.notify(source, &keys_between(5, 14));
        let (claimed, woke) = std::sync::mpsc::channel();
        thread::scope(|scope| {
            scope.spawn(|| {
                let next = dispatcher.claim(None);
                claimed.send(next).expect("the test waits for the claim");
            });
            // The claimant finds only the overlapping package and sleeps.
            let deadline = Instant::now() + Duration::from_secs(10);
            while dispatcher.sleepers.load(Ordering::SeqCst) == 0 {
                assert!(Instant::now() < deadline, "the claimant never slept");
                thread::sleep(Duration::from_millis(1));
            }
            dispatcher.acknowledge(first);
            let next = woke.recv_timeout(Duration::from_secs(5));
            if next.is_err() {
                // Release the claimant so the scope can end, then report the missed wake.
                dispatcher.fail();
            }
            let Ok(Next::Package(package)) = next else {
                panic!("the acknowledgement left the claimant asleep: {next:?}")
            };
            assert_eq!(package.guard, keys_between(5, 14));
            dispatcher.acknowledge(package);
        });
    }

    /// A notify after the run's claims stop queues nothing: no claim will take it.
    #[test]
    fn a_notify_after_claims_stop_queues_nothing() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        let mut dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let source = PipelineId(0);
        dispatcher.limit(source, 1);
        dispatcher.stop_claims();
        for keys in [keys_between(0, 0), keys_between(1, 1)] {
            assert!(matches!(
                dispatcher.try_notify(source, &keys),
                Admission::Stopped
            ));
        }
        assert_eq!(
            dispatcher.outstanding(source),
            0,
            "a stopped run queues nothing"
        );
    }

    /// A publisher waiting for credit on a limited source returns once the run's claims stop,
    /// since no claim will acknowledge a package to give it credit. It is asleep in
    /// [`Dispatcher::wait`] before the stop, and must return within a bounded wait.
    #[test]
    fn a_publisher_waiting_for_credit_returns_when_claims_stop() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use std::time::{Duration, Instant};
        let mut dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let source = PipelineId(0);
        dispatcher.limit(source, 1);
        let _ = dispatcher.notify(source, &keys_between(0, 0));
        let (returned, done) = std::sync::mpsc::channel();
        thread::scope(|scope| {
            scope.spawn(|| {
                let admitted = dispatcher.notify(source, &keys_between(1, 1));
                returned
                    .send(matches!(admitted, Admission::Stopped))
                    .expect("the test waits for the publisher");
            });
            // The publisher finds no credit and sleeps.
            let deadline = Instant::now() + Duration::from_secs(10);
            while dispatcher.sleepers.load(Ordering::SeqCst) == 0 {
                assert!(Instant::now() < deadline, "the publisher never slept");
                thread::sleep(Duration::from_millis(1));
            }
            dispatcher.stop_claims();
            let outcome = done.recv_timeout(Duration::from_secs(5));
            if outcome.is_err() {
                // Release the publisher so the scope can end, then report that it stayed blocked.
                dispatcher.fail();
            }
            assert_eq!(
                outcome.ok(),
                Some(true),
                "the publisher returns stopped once the claims stop"
            );
        });
        assert_eq!(
            dispatcher.outstanding(source),
            1,
            "the stop admitted nothing more"
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

    /// A package claimed and not acknowledged, and a finish claimed and not completed, are each in
    /// flight; nothing is once each completes.
    #[test]
    #[cfg(debug_assertions)]
    fn a_claim_is_in_flight_until_it_completes() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;

        let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX).unrecorded();
        let source = PipelineId(0);
        dispatcher.notify(source, &keys_between(0, 0));
        let package = dispatcher.claim_of(source).expect("the delivered package");
        assert_eq!(dispatcher.in_flight(), [(0, "a claimed package")]);
        dispatcher.acknowledge(package);
        assert_eq!(dispatcher.in_flight(), []);
        dispatcher.close(source);
        let Next::Finish { pipeline, .. } = dispatcher.try_claim(None) else {
            panic!("the drained source finishes")
        };
        assert_eq!(dispatcher.in_flight(), [(0, "its claimed finish")]);
        dispatcher.finish(dispatcher.pushes(pipeline));
        assert_eq!(dispatcher.in_flight(), []);
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

    /// A source over a million positions with all but its last two released is cut into the
    /// morsels of those two, and one released whole is closed with none: the cut visits only the
    /// positions left, not the range's.
    #[test]
    fn a_source_started_after_its_release_cuts_only_what_is_left() {
        use crate::interpreter::tile_operators::Predicate;
        let input = Tiling::data_function(
            Extent::UIntRange(IntervalSet::from(Interval::closed(0, 999_999))),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let released = |through: u64| {
            TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
                through,
            ))))
        };
        let seeded = || MORSELS_SEEDED.with(Cell::get);
        let dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let before = seeded();
        dispatcher.start_source(PipelineId(0), &input, &released(999_997));
        assert_eq!(
            seeded() - before,
            2,
            "the cut visits the two positions left"
        );
        assert_eq!(dispatcher.outstanding(PipelineId(0)), 2);

        let dispatcher = Dispatcher::new(vec![vec![]], 1).unrecorded();
        let before = seeded();
        dispatcher.start_source(PipelineId(0), &input, &input.universal_guard());
        assert_eq!(seeded() - before, 0, "nothing is left to cut");
        assert_eq!(dispatcher.outstanding(PipelineId(0)), 0);
    }

    /// A region of several runs is cut every `rows` of the positions it and the range both hold.
    #[test]
    fn a_seed_within_a_region_counts_only_its_positions() {
        let input = Tiling::data_function(
            Extent::UIntRange(IntervalSet::from(Interval::closed(0, 9))),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let region = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            IntervalSet::new(vec![
                Interval::closed(Value::UInt(2), Value::UInt(4)),
                Interval::closed(Value::UInt(8), Value::UInt(20)),
            ]),
        )));
        let morsels = seed_within(&input, &region, 2);
        assert_eq!(partition_gap(&region, &morsels), None);
        let held: Vec<Vec<u64>> = morsels
            .iter()
            .map(|morsel| {
                let TileGuard::Function(FunctionGuard::Domain(keys)) = morsel else {
                    panic!("a morsel of keys")
                };
                (0..=9)
                    .filter(|key| keys.contains(&Value::UInt(*key)))
                    .collect()
            })
            .collect();
        assert_eq!(held, vec![vec![2, 3], vec![4, 8], vec![9]]);
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

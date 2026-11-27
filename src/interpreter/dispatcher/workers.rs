//! Shared native breaker execution: worker threads that claim the packages of admitted pipelines
//! from the run's dispatcher. See `src/interpreter/design-dispatcher.md`, "Shared native pipeline
//! execution".
use super::scope::{ScopePipeline, ScopeSteps};
use super::transaction_scope::ReservedSeed;
use super::*;
#[cfg(test)]
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::thread::{Scope, ScopedJoinHandle};

/// The breaker a worker consumes with: a chain's, which pushes what it produces, or a sink's at
/// the root of the run, which hands each package's answer to its sink and pushes nothing.
pub(super) enum WorkerBreaker {
    Chain(BreakerHandle),
    // shared-state-ok: as `BreakerHandle`, the workers' handle on a sink breaker they call; no tile
    // passes between operators through it.
    Sink(Arc<RwLock<crate::interpreter::tile_operators::SinkBreaker>>),
}

impl WorkerBreaker {
    /// `f` on the breaker, held exclusively.
    fn write<R>(&self, f: impl FnOnce(&mut dyn Breaker) -> R) -> R {
        match self {
            WorkerBreaker::Chain(handle) => {
                f(&mut *handle.write().unwrap_or_else(PoisonError::into_inner))
            }
            WorkerBreaker::Sink(sink) => {
                f(&mut *sink.write().unwrap_or_else(PoisonError::into_inner))
            }
        }
    }
}

/// A breaker the workers can run and whether they may consume its packages concurrently.
pub(super) struct WorkerTarget {
    pub(super) handle: WorkerBreaker,
    /// Whether packages run beside each other: the breaker consumes concurrently over keyed input.
    pub(super) concurrent: bool,
}

/// An admitted pipeline's breaker and whether its packages run beside each other.
struct Spec {
    target: WorkerBreaker,
    /// Whether its packages run beside each other ([`WorkerTarget::concurrent`]); otherwise they
    /// are consumed one at a time, in queue order.
    concurrent: bool,
    /// For a pipeline of a loop's or transaction writer's body, the body's follower hold, which a
    /// claim holds again before it is acknowledged.
    body: Option<HoldGroup>,
}

enum WorkerPipeline {
    Breaker(Spec),
    Scope(ScopePipeline),
}

/// What each pipeline's claims did on the pool, for the tests below ([`WorkerPool::report`]).
#[cfg(test)]
#[derive(Default)]
struct Stats {
    claims: AtomicUsize,
    /// One bit per worker that consumed a claim of the pipeline.
    used: AtomicU64,
    incremental: AtomicUsize,
}

/// Count execution until the worker has published and polled. A scope request
/// may stay in the dispatcher's finishing phase after this claim returns.
pub(super) struct ActiveClaim<'a> {
    busy: &'a AtomicUsize,
    dispatcher: &'a Dispatcher,
}

impl Drop for ActiveClaim<'_> {
    fn drop(&mut self) {
        self.busy.fetch_sub(1, Ordering::SeqCst);
        self.dispatcher.wake_claimants();
    }
}

/// One drain between source polls. Claimants share the last quiet generation so a
/// worker's completed publication pass also answers the caller's quiescence check.
#[derive(Default)]
enum Drain {
    #[default]
    Inactive,
    Replay,
    Active {
        live: bool,
        settled_at: Option<u64>,
    },
}

/// The run's worker threads, and which pipelines they claim from.
pub(super) struct WorkerPool {
    /// How many workers the run has; with one, the coordinator claims everything and no thread
    /// starts.
    count: usize,
    scope_steps: ScopeSteps,
    // shared-state-ok: serializes idle publication and records when live source polling may resume.
    drain: Mutex<Drain>,
    /// Per pipeline, its breaker and whether its packages run beside each other, where the
    /// pipeline is admitted.
    pipelines: Vec<Option<WorkerPipeline>>,
    /// Set where the system refused every worker thread: the coordinator claims everything.
    unstarted: AtomicBool,
    /// How many claims, packages and finishes, workers hold and have not ended with a wake. A
    /// claim changes the dispatcher's state before it advances the generation: an
    /// acknowledgement clears its package from the queue first, and a finish marks its pipeline
    /// finished first. Between the two the state alone shows a coordinator no claim that can
    /// still change the run.
    busy: AtomicUsize,
    #[cfg(test)]
    stats: Vec<Stats>,
    /// The test counters the worker threads counted: a transaction driver's reissued attempts
    /// (`RETRIES`) and its stalled requests (`STALLS`). The coordinator adds them to its own
    /// ([`hand_over_counters`](Self::hand_over_counters)), so a test that runs a program reads
    /// every thread's counts on its own thread.
    #[cfg(test)]
    counters: Mutex<[usize; 2]>,
}

impl WorkerPool {
    pub(super) fn new(
        count: usize,
        targets: Vec<Option<WorkerTarget>>,
        bodies: Vec<Option<HoldGroup>>,
        actions: Vec<Option<ScopePipeline>>,
        scope_steps: ScopeSteps,
    ) -> Self {
        assert!(count > 0, "a run has at least one worker");
        debug_assert_eq!(
            targets.len(),
            bodies.len(),
            "the targets and the bodies name the same pipelines"
        );
        debug_assert_eq!(targets.len(), actions.len());
        let pipelines: Vec<_> = targets
            .into_iter()
            .zip(bodies)
            .zip(actions)
            .map(|((target, body), action)| {
                if let Some(action) = action {
                    debug_assert!(target.is_none());
                    return Some(WorkerPipeline::Scope(action));
                }
                let WorkerTarget { handle, concurrent } = target?;
                Some(WorkerPipeline::Breaker(Spec {
                    target: handle,
                    concurrent,
                    body,
                }))
            })
            .collect();
        Self {
            count: if pipelines.iter().any(Option::is_some) {
                count
            } else {
                1
            },
            scope_steps,
            drain: Mutex::default(),
            #[cfg(test)]
            stats: (0..pipelines.len()).map(|_| Stats::default()).collect(),
            #[cfg(test)]
            counters: Mutex::new([0; 2]),
            pipelines,
            unstarted: AtomicBool::new(false),
            busy: AtomicUsize::new(0),
        }
    }

    /// Whether the run starts worker threads: more than one worker, and a pipeline for them.
    fn threaded(&self) -> bool {
        self.count > 1
    }

    /// Whether `pipeline`'s packages are the workers' to claim.
    pub(super) fn admits(&self, pipeline: PipelineId) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && self.pipelines[pipeline.0].is_some()
    }

    /// The admitted pipelines whose packages do not run beside each other, which the run orders
    /// so that one package of each is in flight at a time. None where the run starts no worker.
    pub(super) fn serial(&self) -> Vec<PipelineId> {
        if !self.threaded() {
            return Vec::new();
        }
        self.pipelines
            .iter()
            .enumerate()
            .filter(|(_, p)| match p {
                Some(WorkerPipeline::Scope(_)) => true,
                Some(WorkerPipeline::Breaker(spec)) => !spec.concurrent,
                None => false,
            })
            .map(|(pipeline, _)| PipelineId(pipeline))
            .collect()
    }

    /// Start the workers in `scope`. Each claims until the run is done, has failed, or its claims
    /// are stopped. [`join`](Self::join) takes the handles.
    pub(super) fn spawn<'scope, 'env>(
        &'env self,
        scope: &'scope Scope<'scope, 'env>,
        dispatcher: &'env Dispatcher,
        replay: bool,
    ) -> Vec<ScopedJoinHandle<'scope, ()>> {
        if replay {
            *self.drain.lock().unwrap_or_else(PoisonError::into_inner) = Drain::Replay;
        }
        if !self.threaded() {
            return Vec::new();
        }
        // A thread the system refuses leaves the run with the workers it has. Panicking instead
        // would leave the workers already started asleep, and the scope waiting for them.
        let mut handles = Vec::new();
        // The coordinator claims as one of the run's workers (`WorkerPool::next`), so the run
        // starts one thread fewer than it has workers.
        for worker in 1..self.count {
            match thread::Builder::new().spawn_scoped(scope, move || self.work(dispatcher, worker))
            {
                Ok(handle) => handles.push(handle),
                Err(_) => break,
            }
        }
        if handles.is_empty() {
            self.unstarted.store(true, Ordering::SeqCst);
        }
        handles
    }

    /// Reserve a seed's store only after its package or finish is ready. A busy
    /// store leaves the work available and the claimant continues scanning.
    fn reserve_seed(&self, id: PipelineId) -> Result<Option<ReservedSeed<'_>>, ()> {
        match &self.pipelines[id.0] {
            Some(WorkerPipeline::Scope(ScopePipeline::Seed(store, input))) => {
                Ok(Some(ReservedSeed {
                    store: store.try_write()?,
                    input: *input,
                }))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn next<'a>(
        &'a self,
        dispatcher: &'a Dispatcher,
        preferred: Option<PipelineId>,
        admits: &dyn Fn(PipelineId) -> bool,
    ) -> (Next, (Option<ReservedSeed<'a>>, Option<ActiveClaim<'a>>)) {
        dispatcher.try_claim_with(preferred, admits, &|p| {
            let seed = self.reserve_seed(p).ok()?;
            Some((seed, self.threaded().then(|| self.active_claim(dispatcher))))
        })
    }

    fn active_claim<'a>(&'a self, dispatcher: &'a Dispatcher) -> ActiveClaim<'a> {
        self.busy.fetch_add(1, Ordering::SeqCst);
        ActiveClaim {
            busy: &self.busy,
            dispatcher,
        }
    }

    /// One worker's claims: consume, publish and acknowledge each package of an admitted pipeline.
    fn work(&self, dispatcher: &Dispatcher, worker: usize) {
        #[cfg(not(test))]
        let _ = worker;
        in_a_run(|| {
            // A panic fails the run, so no claimant waits for what this worker held.
            let _worker = dispatcher.worker();
            self.replay_before_sources(dispatcher);
            let mut preferred = None;
            loop {
                let (next, (mut reserved, _activity)) =
                    self.next(dispatcher, preferred, &|p| self.admits(p));
                let mut reach_seed = |_: PipelineId, call: &mut Call<'_>| {
                    reserved
                        .take()
                        .expect("a seed claim reserves its store")
                        .reach(call);
                };
                match next {
                    Next::Package(package) => {
                        preferred = Some(package.pipeline);
                        #[cfg(test)]
                        self.count_claim(dispatcher, &package, worker);
                        self.consume(dispatcher, package, &mut reach_seed);
                        while self.scope_steps.poll(dispatcher) {}
                        #[cfg(test)]
                        self.collect_counters();
                    }
                    Next::Finish { pipeline } => {
                        self.finish(dispatcher, pipeline, &mut reach_seed);
                        while self.scope_steps.poll(dispatcher) {}
                    }
                    Next::Done | Next::Failed => break,
                    Next::Wait(generation) => {
                        if !self.help_active_claim(dispatcher)
                            && !self.try_settle(dispatcher, &generation)
                        {
                            dispatcher.wait(generation);
                        }
                    }
                }
            }
        });
        #[cfg(test)]
        self.collect_counters();
    }

    /// A handler can be inside a transition while another scope becomes runnable. Borrow its
    /// activity count while checking, so the coordinator cannot report idle during publication.
    pub(super) fn help_active_claim(&self, dispatcher: &Dispatcher) -> bool {
        if self
            .busy
            .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |busy| {
                (busy != 0).then_some(busy + 1)
            })
            .is_err()
        {
            return false;
        }
        let advanced = self.scope_steps.poll(dispatcher);
        if self.busy.fetch_sub(1, Ordering::SeqCst) == 1 {
            dispatcher.wake_claimants();
        }
        advanced
    }

    #[cfg(test)]
    fn collect_counters(&self) {
        let mut counters = self.counters.lock().unwrap_or_else(PoisonError::into_inner);
        counters[0] += crate::interpreter::commit_operator::RETRIES.with(|c| c.replace(0));
        counters[1] += transaction_scope::STALLS.with(|c| c.replace(0));
    }

    /// The first claimant republishes output carried over from the previous run. Both the
    /// live driver and the workers wait for that publication before touching their inputs.
    pub(super) fn replay_before_sources(&self, dispatcher: &Dispatcher) {
        let mut drain = self.drain.lock().unwrap_or_else(PoisonError::into_inner);
        if matches!(*drain, Drain::Replay) {
            self.publish_held(dispatcher);
            *drain = Drain::Inactive;
        }
    }

    pub(super) fn begin_drain(&self, dispatcher: &Dispatcher, live: bool) {
        *self.drain.lock().unwrap_or_else(PoisonError::into_inner) = Drain::Active {
            live,
            settled_at: None,
        };
        dispatcher.wake_claimants();
    }

    pub(super) fn end_drain(&self) {
        *self.drain.lock().unwrap_or_else(PoisonError::into_inner) = Drain::Inactive;
    }

    /// Workers skip a pass another claimant owns and return to the package queues.
    fn try_settle(&self, dispatcher: &Dispatcher, generation: &Generation) -> bool {
        let Ok(mut slot) = self.drain.try_lock() else {
            return false;
        };
        self.settle(dispatcher, generation, &mut slot)
    }

    /// Synchronize with the last publisher before the driver can poll live sources again.
    pub(super) fn drained(&self, dispatcher: &Dispatcher, generation: &Generation) -> bool {
        let mut slot = self.drain.lock().unwrap_or_else(PoisonError::into_inner);
        self.settle(dispatcher, generation, &mut slot);
        let quiet = matches!(*slot, Drain::Active {settled_at: Some(at), ..} if at == generation.0)
            && !self.may_progress(dispatcher)
            && !dispatcher.changed_since(generation);
        if quiet {
            *slot = Drain::Inactive;
        }
        quiet
    }

    fn settle(&self, dispatcher: &Dispatcher, generation: &Generation, drain: &mut Drain) -> bool {
        let Drain::Active { live, settled_at } = drain else {
            return false;
        };
        if *settled_at == Some(generation.0)
            || dispatcher.changed_since(generation)
            || self.busy.load(Ordering::SeqCst) != 0
        {
            return false;
        }
        if self.scope_steps.poll(dispatcher) || (*live && self.publish_held(dispatcher)) {
            return true;
        }
        *settled_at = Some(generation.0);
        false
    }

    fn publish_held(&self, dispatcher: &Dispatcher) -> bool {
        let published = try_push_held(
            dispatcher,
            (0..self.pipelines.len())
                .filter(|&id| !dispatcher.infos[id].readers.is_empty())
                .map(PipelineId),
            |id, call| {
                match &self.pipelines[id.0] {
                    Some(WorkerPipeline::Breaker(spec)) => {
                        spec.target.write(|breaker| call(breaker, InputId::ONLY))
                    }
                    Some(WorkerPipeline::Scope(ScopePipeline::Request(scope)))
                        if !scope.has_request() =>
                    {
                        scope.reach(call)
                    }
                    Some(WorkerPipeline::Scope(ScopePipeline::Seed(store, input))) => {
                        ReservedSeed {
                            store: store.write(),
                            input: *input,
                        }
                        .reach(call);
                    }
                    _ => {}
                }
                true
            },
        );
        matches!(published, Publication::Published)
    }

    /// Add the counters the worker threads counted to this thread's, once they have joined.
    #[cfg(test)]
    pub(super) fn hand_over_counters(&self) {
        let counters =
            std::mem::take(&mut *self.counters.lock().unwrap_or_else(PoisonError::into_inner));
        crate::interpreter::commit_operator::RETRIES.with(|c| c.set(c.get() + counters[0]));
        transaction_scope::STALLS.with(|c| c.set(c.get() + counters[1]));
    }

    /// [`consume`](Self::consume) on the coordinator, which claims as worker 0. It wakes the
    /// claimants after, as a worker thread does, so a claimant that waits on the pool's busy count
    /// sees the claim end.
    pub(super) fn consume_on_coordinator(
        &self,
        dispatcher: &Dispatcher,
        package: WorkPackage,
        reach: &mut Reach<'_>,
    ) {
        #[cfg(test)]
        self.count_claim(dispatcher, &package, 0);
        dispatcher.wake_claimants();
        self.consume(dispatcher, package, reach);
    }

    /// Offers from the upstream breaker have landed. A scope with other reads
    /// still running keeps its offers until those reads publish or settlement retries.
    fn admit_readers(&self, dispatcher: &Dispatcher, pipeline: PipelineId) {
        for &reader in &dispatcher.infos[pipeline.0].readers {
            if let Some(WorkerPipeline::Scope(ScopePipeline::Request(scope))) =
                &self.pipelines[reader]
            {
                scope.try_queue_requests(dispatcher);
            }
        }
    }

    /// Consume the package, publish any incremental output, then acknowledge the claim.
    fn consume(&self, dispatcher: &Dispatcher, package: WorkPackage, reach: &mut Reach<'_>) {
        let pipeline = package.pipeline;
        let spec = match self.pipelines[pipeline.0]
            .as_ref()
            .expect("an admitted pipeline")
        {
            WorkerPipeline::Scope(action) => return action.consume(dispatcher, package, reach),
            WorkerPipeline::Breaker(spec) => spec,
        };
        let mut pushes = dispatcher.pushes(pipeline);
        if spec.concurrent {
            debug_assert!(
                Projection::of(&package.guard).is_ok(),
                "pipeline {} runs a package beside others that names no projection: {:?}",
                pipeline.0,
                package.guard
            );
            match &spec.target {
                WorkerBreaker::Sink(sink) => {
                    package.consume(
                        &*sink.read().unwrap_or_else(PoisonError::into_inner),
                        InputId::ONLY,
                        &mut pushes,
                    );
                }
                WorkerBreaker::Chain(handle) => {
                    let needs_snapshot = {
                        let breaker = handle.read().unwrap_or_else(PoisonError::into_inner);
                        package
                            .consume(&*breaker, InputId::ONLY, &mut pushes)
                            .is_some()
                    };
                    if needs_snapshot {
                        let breaker = handle.write().unwrap_or_else(PoisonError::into_inner);
                        pushes.push_final(&*breaker);
                    }
                }
            }
        } else {
            spec.target.write(|breaker| {
                if let Some(producer) = package.consume(breaker, InputId::ONLY, &mut pushes) {
                    pushes.push_final(producer);
                }
            });
        }
        if !pushes.pending.is_empty() {
            dispatcher.land(pushes);
        }
        // Before the acknowledgement that can leave the body quiescent: the round's step waits
        // for a claimant to publish what this consume left held.
        if let Some(body) = &spec.body {
            dispatcher.hold_followers(*body);
        }
        dispatcher.acknowledge(package);
        self.admit_readers(dispatcher, pipeline);
    }

    /// Finish `pipeline`, whose finish this worker claimed: release a parallel input whole, then
    /// push what the breaker completed and mark the pipeline finished (`finish_with`).
    pub(super) fn finish(
        &self,
        dispatcher: &Dispatcher,
        pipeline: PipelineId,
        reach: &mut Reach<'_>,
    ) {
        let spec = match &self.pipelines[pipeline.0] {
            Some(WorkerPipeline::Breaker(spec)) => spec,
            Some(WorkerPipeline::Scope(scope)) => {
                if let Some(published) = scope.finish(dispatcher, pipeline, reach) {
                    self.admit_readers(dispatcher, published);
                }
                return;
            }
            None => unreachable!("a worker finishes an admitted pipeline"),
        };
        let mut reach = |reached: PipelineId, call: &mut Call<'_>| {
            debug_assert_eq!(
                reached.0, pipeline.0,
                "a worker's finish reaches its own breaker"
            );
            spec.target.write(|breaker| call(breaker, InputId::ONLY))
        };
        if spec.concurrent {
            reach(pipeline, &mut |breaker, _| breaker.finish_parallel_input());
        }
        // No follower hold, unlike a consume: the finish lands everything the breaker completed,
        // and a hold taken once the scope's body is inactive is never released.
        finish_with(dispatcher, &mut reach, pipeline);
        self.admit_readers(dispatcher, pipeline);
    }

    /// Join the workers, and resume a worker's panic on this thread.
    pub(super) fn join(handles: Vec<ScopedJoinHandle<'_, ()>>) {
        let mut panicked = None;
        for handle in handles {
            if let Err(payload) = handle.join() {
                panicked.get_or_insert(payload);
            }
        }
        if let Some(payload) = panicked {
            std::panic::resume_unwind(payload);
        }
    }

    /// Whether a worker holds or can claim a package: the coordinator waits for the workers rather
    /// than deciding the run is stalled.
    pub(super) fn may_progress(&self, dispatcher: &Dispatcher) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && (dispatcher.may_claim_where(&|pipeline| {
                matches!(self.pipelines[pipeline.0], Some(WorkerPipeline::Breaker(_)))
            }) || dispatcher.may_finish_where(&|pipeline| self.admits(pipeline))
                || self.busy.load(Ordering::SeqCst) > 0)
    }

    /// Before the coordinator finishes an admitted pipeline, release its input whole.
    pub(super) fn finishing(&self, p: PipelineId, reach: &mut Reach<'_>) {
        if matches!(&self.pipelines[p.0], Some(WorkerPipeline::Breaker(spec)) if spec.concurrent) {
            reach(p, &mut |breaker, _| breaker.finish_parallel_input());
        }
    }

    #[cfg(test)]
    fn count_claim(&self, dispatcher: &Dispatcher, package: &WorkPackage, worker: usize) {
        let stats = &self.stats[package.pipeline.0];
        stats.claims.fetch_add(1, Ordering::Relaxed);
        stats.used.fetch_or(1 << (worker % 64), Ordering::Relaxed);
        if dispatcher.infos[package.pipeline.0]
            .reads
            .iter()
            .any(|p| dispatcher.states[*p].phase.load() != Phase::Finished)
        {
            stats.incremental.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Report each pipeline's claims in `planned`, a pipeline of a scope's body under the
    /// program's pipeline `owners` names for it.
    #[cfg(test)]
    pub(super) fn report(&self, planned: &mut [Planned], owners: &[usize]) {
        let mut used = vec![0u64; planned.len()];
        for (p, stats) in self.stats.iter().enumerate() {
            let planned = &mut planned[owners[p]];
            planned.worker_claims += stats.claims.load(Ordering::Relaxed);
            planned.incremental_claims += stats.incremental.load(Ordering::Relaxed);
            used[owners[p]] |= stats.used.load(Ordering::Relaxed);
        }
        for (planned, used) in planned.iter_mut().zip(used) {
            planned.workers_used = used.count_ones() as usize;
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::formatdoc;

    use super::super::run_program_with_workers;
    use crate::ccl::{
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    };
    use crate::interpreter::{Tile, TileGuard, Tiling};

    fn evaluate(source: &str, dop: usize) -> super::super::Run {
        let mut context = GlobalContext::default();
        let mut program =
            compile_program(&mut context, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        run_program_with_workers(&mut program, 8, dop).unwrap()
    }
    enum TestBreaker {
        Sink,
        MapAggregate,
        FlatMemo,
        NestedMemo,
        NestedMemoReleasing,
        NestedMemoClosingEmpty,
        NestedMemoClosingAncestors,
        RecordMemoReleasing,
        RecordMemoDiscarded,
    }

    #[rstest_log::rstest]
    #[case::sink(TestBreaker::Sink)]
    #[case::map_aggregate(TestBreaker::MapAggregate)]
    #[case::flat_memo(TestBreaker::FlatMemo)]
    #[case::nested_memo(TestBreaker::NestedMemo)]
    #[case::nested_memo_releasing(TestBreaker::NestedMemoReleasing)]
    #[case::close_without_payload_while_peer_releases(TestBreaker::NestedMemoClosingEmpty)]
    #[case::absent_leaf_closes_two_ancestors_before_peer_releases(
        TestBreaker::NestedMemoClosingAncestors
    )]
    #[case::record_memo_releasing(TestBreaker::RecordMemoReleasing)]
    #[case::release_output_while_input_release_is_paused(TestBreaker::RecordMemoDiscarded)]
    fn acknowledges_while_a_peer_is_still_consuming(#[case] target: TestBreaker) {
        use super::*;
        use crate::ccl::AggregateKind;
        use crate::interpreter::{
            DataSink, Tile,
            tile_operators::{
                MemoProducer, ProducerBase, SinkBreaker, TileProducer,
                growing::{Input, KEYS, NestedInput, source},
                guard_covers, map_aggregate_over,
                test_helpers::{
                    ProjectionSpy, int_entries, keys_between, paths_guard, two_levels_of_ints,
                },
            },
            types::BaseType,
        };
        use std::sync::mpsc;
        use std::time::Duration;

        struct PausedInput {
            inner: Box<dyn TileProducer>,
            paused: TileGuard,
            pause_on_release: bool,
            entered: mpsc::Sender<()>,
            resume: Mutex<mpsc::Receiver<()>>,
        }
        impl PausedInput {
            fn pause(&self, guard: &TileGuard, releasing: bool) {
                if releasing == self.pause_on_release && *guard == self.paused {
                    self.entered.send(()).unwrap();
                    self.resume
                        .lock()
                        .unwrap()
                        .recv_timeout(Duration::from_secs(15))
                        .unwrap();
                }
            }
        }
        impl TileProducer for PausedInput {
            fn base(&self) -> &ProducerBase {
                self.inner.base()
            }
            fn base_mut(&mut self) -> &mut ProducerBase {
                self.inner.base_mut()
            }
            fn restates(&self) -> crate::interpreter::Restates {
                self.inner.restates()
            }
            fn get_impl(&self, guard: TileGuard) -> Tile {
                self.pause(&guard, false);
                self.inner.get_impl(guard)
            }
            fn release_impl(&self, guard: TileGuard) {
                self.pause(&guard, true);
                self.inner.release_impl(guard);
            }
        }
        struct Sink(mpsc::Sender<Tile>);
        impl DataSink for Sink {
            fn process(&self, tile: &Tile) {
                self.0.send(tile.clone()).unwrap();
            }
        }

        // Both nested claims contribute to row 0 of a two-row collection. Finishing
        // the merge closes only row 0, leaving row 1 open.
        let discard_output = matches!(target, TestBreaker::RecordMemoDiscarded);
        let record = matches!(target, TestBreaker::RecordMemoReleasing) || discard_output;
        let field = |key| if key == 0 { "left" } else { "right" };
        let record_tiling = Tiling::Record(
            [
                ("left".into(), Tiling::Scalar(Extent::Base(BaseType::Int))),
                ("right".into(), two_levels_of_ints().1),
            ]
            .into(),
        );
        let ancestors = matches!(target, TestBreaker::NestedMemoClosingAncestors);
        let empty_close = matches!(target, TestBreaker::NestedMemoClosingEmpty) || ancestors;
        let releasing = matches!(target, TestBreaker::NestedMemoReleasing) || empty_close;
        let nested = matches!(target, TestBreaker::NestedMemo) || releasing;
        let point = |key| Predicate::point(Value::UInt(key));
        let claim = |key| {
            if record {
                let part = if key == 0 {
                    Projection::Everything
                } else {
                    Projection::keys_at(
                        crate::interpreter::CurryLevel::new(1),
                        Predicate::qualified(point(1), point(2)),
                    )
                };
                Projection::of_field(field(key), part).guard(&record_tiling)
            } else if nested {
                let inner = if key == 0 {
                    point(0).union(&point(1))
                } else {
                    point(2)
                };
                if ancestors {
                    crate::interpreter::CurryLevel::new(2).wrap_guard(TileGuard::Function(
                        FunctionGuard::Domain(Predicate::qualified(
                            Predicate::exactly(&[Value::UInt(0), Value::UInt(0)]),
                            inner,
                        )),
                    ))
                } else {
                    paths_guard(Predicate::qualified(point(0), inner))
                }
            } else {
                keys_between(key, key)
            }
        };
        let (entered, pulling) = mpsc::channel();
        let (release, resume) = mpsc::channel();
        let input = Box::new(PausedInput {
            inner: match target {
                TestBreaker::RecordMemoReleasing | TestBreaker::RecordMemoDiscarded => {
                    let tile = Tile::record(
                        [
                            (
                                "left".into(),
                                Tile::Scalar(crate::interpreter::ColumnValue::Ints(vec![11])),
                            ),
                            ("right".into(), two_levels_of_ints().0),
                        ]
                        .into(),
                    );
                    Box::new(ProjectionSpy::new(tile, record_tiling.clone()).0)
                }
                TestBreaker::NestedMemoClosingAncestors => {
                    // Row 0 has one group and row 1 is still open in the memo. The
                    // second worker learns only that the group's third item is absent.
                    let (mut tile, ty) = two_levels_of_ints();
                    let Tile::DataFunction { codomain, .. } = &mut tile else {
                        unreachable!()
                    };
                    **codomain = Tile::grouped(
                        vec![0, 1],
                        crate::interpreter::ColumnValue::UInts(vec![0, 0]),
                        codomain.clone(),
                        Predicate::True,
                        Default::default(),
                    );
                    let ty = Tiling::data_function(
                        Extent::uint_range(2),
                        Tiling::data_function(
                            Extent::uint_range(1),
                            ty.values_at(crate::interpreter::CurryLevel::new(1)).clone(),
                        ),
                    );
                    tile.remove_guarded(claim(1));
                    tile.compact();
                    Box::new(ProjectionSpy::new(tile, ty).0)
                }
                TestBreaker::FlatMemo => Box::new(Input::over(&source(0..2))),
                TestBreaker::NestedMemo
                | TestBreaker::NestedMemoReleasing
                | TestBreaker::NestedMemoClosingEmpty => {
                    let (mut tile, tiling) = two_levels_of_ints();
                    if empty_close {
                        tile.remove_guarded(claim(1));
                        tile.compact();
                    }
                    Box::new(ProjectionSpy::new(tile, tiling).0)
                }
                _ => Box::new(NestedInput::over(&source(0..2))),
            },
            paused: claim(0),
            pause_on_release: releasing || record,
            entered,
            resume: Mutex::new(resume),
        });
        let (delivered, tiles) = mpsc::channel();
        let reader = PipelineId(1);
        let mut memo = None;
        let handle = match target {
            TestBreaker::FlatMemo
            | TestBreaker::NestedMemo
            | TestBreaker::NestedMemoReleasing
            | TestBreaker::NestedMemoClosingEmpty
            | TestBreaker::NestedMemoClosingAncestors
            | TestBreaker::RecordMemoReleasing
            | TestBreaker::RecordMemoDiscarded => {
                let tiling = input.tiling().clone();
                let mut producer = MemoProducer::over(input, &tiling);
                producer.base_mut().downstream = Some(Arc::new(Entry::new(reader, tiling)));
                let chain: BreakerHandle = Arc::new(RwLock::new(producer));
                memo = Some(chain.clone());
                WorkerBreaker::Chain(chain)
            }
            TestBreaker::MapAggregate => {
                let output = Tiling::data_function(
                    Extent::uint_range(KEYS),
                    Tiling::Aggregation {
                        kind: AggregateKind::Sum,
                        accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
                    },
                );
                let chain = map_aggregate_over(input, &output, AggregateKind::Sum);
                chain.write().unwrap().base_mut().downstream =
                    Some(Arc::new(Entry::new(reader, output)));
                WorkerBreaker::Chain(chain)
            }
            TestBreaker::Sink => {
                let sink = SinkBreaker::new(
                    Arc::new(RwLock::new(Some(input))),
                    Arc::new(Sink(delivered)),
                );
                WorkerBreaker::Sink(Arc::new(RwLock::new(sink)))
            }
        };
        let workers = WorkerPool::new(
            2,
            vec![
                Some(WorkerTarget {
                    handle,
                    concurrent: true,
                }),
                None,
            ],
            vec![None; 2],
            vec![None, None],
            ScopeSteps::default(),
        );
        let dispatcher = Dispatcher::new(
            if !matches!(target, TestBreaker::Sink) {
                vec![vec![], vec![0]]
            } else {
                vec![vec![], vec![]]
            },
            1,
        );
        let pipeline = PipelineId(0);
        for key in 0..2 {
            dispatcher.queue_for(pipeline, &claim(key));
        }
        dispatcher.close(pipeline);
        let consume = || {
            let Next::Package(package) = dispatcher.try_claim(None) else {
                panic!("expected a disjoint package");
            };
            workers.consume(&dispatcher, package, &mut |_, _| unreachable!());
        };
        let read_key = |memo: &BreakerHandle, key: u64| {
            let Next::Package(package) = dispatcher.try_claim(Some(reader)) else {
                panic!("the reader must receive key {key}");
            };
            assert_eq!(package.pipeline, reader);
            let memo = memo.read().unwrap();
            let tile = in_a_run(|| memo.get(package.guard.clone()));
            if record {
                assert_eq!(package.guard, claim(key));
                let Tile::Record { fields, .. } = tile else {
                    panic!("expected a record")
                };
                assert_eq!(
                    fields[field(key)].deepest_values(),
                    &Tile::Scalar(crate::interpreter::ColumnValue::Ints(vec![if key == 0 {
                        11
                    } else {
                        12
                    }])),
                );
                assert!(fields[field(1 - key)].is_empty());
            } else if nested {
                let row = keys_between(0, 0);
                let closing_claim = if releasing { 1 } else { 0 };
                let expected = if key == closing_claim {
                    guard_minus(&row, &claim(1 - key))
                } else {
                    claim(key)
                };
                assert!(
                    guard_covers(&expected, &package.guard)
                        && guard_covers(&package.guard, &expected)
                );
                assert_eq!(guard_covers(&memo.complete(), &row), key == 0 || releasing);
                assert!(!guard_covers(&memo.complete(), &keys_between(1, 1)));
                let values = if key == 0 {
                    vec![0, 1]
                } else if empty_close {
                    vec![]
                } else {
                    vec![2]
                };
                assert_eq!(
                    tile.deepest_values(),
                    &Tile::Scalar(crate::interpreter::ColumnValue::Ints(values))
                );
            } else {
                assert_eq!(package.guard, claim(key));
                assert_eq!(int_entries(&tile), vec![(key, key as i64 * 10)]);
            }
            dispatcher.acknowledge(package);
        };
        let timeout = Duration::from_secs(5);
        thread::scope(|threads| {
            threads.spawn(consume);
            pulling.recv_timeout(timeout).unwrap();
            let (done, acknowledged) = mpsc::channel();
            threads.spawn(move || {
                consume();
                let _ = done.send(());
            });
            let completed = acknowledged.recv_timeout(timeout);
            if completed.is_ok()
                && let Some(memo) = &memo
            {
                read_key(memo, 1);
            }
            let outstanding = dispatcher.outstanding(pipeline);
            let waiting = matches!(dispatcher.try_claim(None), Next::Wait(_));
            if discard_output {
                let memo = memo.as_ref().unwrap();
                threads.spawn(|| {
                    memo.read()
                        .unwrap()
                        .release(record_tiling.universal_guard())
                });
                // The reader can abandon its subscription while the writer releases its
                // input. Its release promise is recorded before physical reclamation waits.
                let deadline = std::time::Instant::now() + timeout;
                while !memo.read().unwrap().obsolete_guard().is_universal() {
                    assert!(std::time::Instant::now() < deadline);
                    thread::yield_now();
                }
            }
            release.send(()).unwrap();
            completed.expect("the second package can acknowledge while its peer is paused");
            assert_eq!(outstanding, 1);
            assert!(waiting, "finish still waits for the first package");
        });
        if !discard_output && let Some(memo) = &memo {
            read_key(memo, 0);
        }
        assert_eq!(dispatcher.outstanding(reader), 0, "no extra packages");
        let Next::Finish { pipeline } = dispatcher.try_claim(None) else {
            panic!("both packages acknowledged");
        };
        workers.finish(&dispatcher, pipeline, &mut |_, _| unreachable!());
        if nested {
            while let Next::Package(package) = dispatcher.try_claim(Some(reader)) {
                assert!(
                    package.guard.intersect(&keys_between(0, 0)).is_empty(),
                    "finish must not publish any of row 0 again: {:?}",
                    package.guard
                );
                dispatcher.acknowledge(package);
            }
        }
        if matches!(target, TestBreaker::MapAggregate) {
            assert!(
                dispatcher.outstanding(reader) > 0,
                "finish publishes the held groups"
            );
        } else if matches!(target, TestBreaker::Sink) {
            assert_eq!(tiles.try_iter().count(), 2, "one delivery per key");
        }
    }

    /// Both packages read row 7. Pause A during its pull or during release after its merge. B must
    /// publish, reach the sink and release just its field before A can return.
    #[rstest_log::rstest]
    #[case::during_read(false)]
    #[case::during_release(true)]
    fn cached_memo_delivers_a_sibling_field_while_the_first_worker_is_paused(
        #[case] on_release: bool,
    ) {
        use super::*;
        use crate::interpreter::{ColumnValue, CurryLevel, Tile, types::BaseType};
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        let tiling = Tiling::data_function(
            Extent::uint_range(16),
            Tiling::Record([("a".into(), scalar.clone()), ("b".into(), scalar)].into()),
        );
        let record = Tile::record(
            [
                ("a".into(), Tile::Scalar(ColumnValue::Ints(vec![17]))),
                ("b".into(), Tile::Scalar(ColumnValue::Ints(vec![29]))),
            ]
            .into(),
        );
        let row = Tile::data_function(
            ColumnValue::UInts(vec![7]),
            Box::new(record),
            Predicate::False,
            Default::default(),
        );
        let field = |name| {
            Projection::within(
                CurryLevel::OUTERMOST,
                Predicate::point(Value::UInt(7)),
                Projection::of_field(name, Projection::Everything),
            )
            .guard(&tiling)
        };
        let (mut first, second, remaining) =
            deliver_sibling_packages(&row, &tiling, [field("a"), field("b")], on_release);
        first.merge(second);
        assert_eq!(first, row);
        assert!(
            remaining.is_empty(),
            "releasing both fields reclaims the row"
        );
    }

    #[rstest_log::rstest]
    #[case::during_read(false)]
    #[case::during_release(true)]
    fn cached_memo_delivers_item_four_while_item_two_is_paused(#[case] on_release: bool) {
        use super::*;
        use crate::interpreter::{ColumnValue, CurryLevel, Tile};
        let tiling = customer_tiling();
        let customers = customers_with_history();
        let field = |item| customer_history_item(&tiling, item);
        let (first, second, remaining) =
            deliver_sibling_packages(&customers, &tiling, [field(2), field(4)], on_release);
        for (tile, item, value) in [(first, 4, 74), (second, 2, 72)] {
            assert_eq!(tile.paths_at(CurryLevel::OUTERMOST), [vec![Value::UInt(7)]]);
            let Tile::Record { fields, .. } = tile.deepest_values() else {
                panic!("expected customer record")
            };
            assert!(fields["id"].is_empty());
            assert_eq!(fields["profile"].cell_count(), 0);
            assert_eq!(
                fields["history"].paths_at(CurryLevel::new(1)),
                [vec![Value::UInt(3), Value::UInt(item)]]
            );
            assert_eq!(
                fields["history"].deepest_values(),
                &Tile::Scalar(ColumnValue::Ints(vec![value]))
            );
        }
        assert!(!remaining.contains_guarded(&field(2)));
        assert!(!remaining.contains_guarded(&field(4)));
    }

    #[rstest_log::rstest]
    #[case::during_read(false)]
    #[case::during_release(true)]
    fn cached_memo_delivers_the_nested_profile_while_a_history_item_is_paused(
        #[case] on_release: bool,
    ) {
        use super::*;
        use crate::interpreter::{ColumnValue, CurryLevel, Tile};
        let tiling = customer_tiling();
        let profile = Projection::within(
            CurryLevel::OUTERMOST,
            Predicate::point(Value::UInt(7)),
            Projection::of_field("profile", Projection::Everything),
        )
        .guard(&tiling);
        let (first, _, _) = deliver_sibling_packages(
            &customers_with_history(),
            &tiling,
            [customer_history_item(&tiling, 2), profile],
            on_release,
        );
        let Tile::Record { fields, .. } = first.deepest_values() else {
            panic!("customer")
        };
        let Tile::Record {
            fields: profile, ..
        } = &fields["profile"]
        else {
            panic!("profile")
        };
        assert_eq!(profile["rank"], Tile::Scalar(ColumnValue::Ints(vec![1])));
        assert_eq!(
            profile["visits"].deepest_values(),
            &Tile::Scalar(ColumnValue::Ints(vec![1]))
        );
        assert!(fields["history"].is_empty());
    }

    #[test]
    fn a_mixed_memo_package_keeps_each_customers_projection() {
        use super::*;
        use crate::interpreter::CurryLevel;
        let tiling = customer_tiling();
        let customer_eight = Projection::within(
            CurryLevel::OUTERMOST,
            Predicate::point(Value::UInt(8)),
            Projection::of_field(
                "profile",
                Projection::of_field("rank", Projection::Everything),
            ),
        )
        .guard(&tiling);
        let mixed = customer_eight.union(&customer_history_item(&tiling, 4));
        let (first, _, _) = deliver_sibling_packages(
            &customers_with_history(),
            &tiling,
            [customer_history_item(&tiling, 2), mixed.clone()],
            false,
        );
        assert_eq!(first.to_guard(), mixed);
        assert_eq!(
            first.cell_count(),
            6,
            "two customer keys, a rank and one day/item/value"
        );
    }

    // Two independently seeded stores and two snapshots of running sums, one per customer.
    fn customers_with_state(finished: [bool; 2], totals: [i64; 2]) -> (Tiling, Tile) {
        use super::*;
        use crate::{
            ccl::AggregateKind,
            interpreter::{ColumnValue, StoreClosures, types::BaseType},
        };
        let int = Tiling::Scalar(Extent::Base(BaseType::Int));
        let store = Tiling::Store {
            domain: Extent::uint_range(16),
            codomain: Box::new(Tiling::Record([("balance".into(), int.clone())].into())),
        };
        let one = |value, terminal| {
            let mut t = store.empty_tile();
            let Tile::Store { seed, closures, .. } = &mut t else {
                unreachable!()
            };
            **seed = Tile::record(
                [(
                    "balance".into(),
                    Tile::Scalar(ColumnValue::Ints(vec![value])),
                )]
                .into(),
            );
            *closures = StoreClosures::uniform(terminal);
            t
        };
        let mut accounts = one(13, finished[0]);
        accounts.merge_rows(one(29, finished[1]));
        let tiling = Tiling::data_function(
            Extent::uint_range(16),
            Tiling::Record(
                [
                    ("account".into(), store),
                    (
                        "total".into(),
                        Tiling::Aggregation {
                            kind: AggregateKind::Sum,
                            accumulator: Box::new(int.clone()),
                        },
                    ),
                    ("id".into(), int),
                ]
                .into(),
            ),
        );
        let rows = Tile::grouped(
            vec![0],
            ColumnValue::UInts(vec![7, 8]),
            Box::new(Tile::record(
                [
                    ("account".into(), accounts),
                    (
                        "total".into(),
                        Tile::Aggregation {
                            kind: AggregateKind::Sum,
                            accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(totals.into()))),
                            terminal: ColumnValue::Bools(finished.into()),
                        },
                    ),
                    ("id".into(), Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                ]
                .into(),
            )),
            Predicate::False,
            Default::default(),
        );
        (tiling, rows)
    }

    fn state_field(tiling: &Tiling, row: u64, name: &str) -> TileGuard {
        use super::*;
        use crate::interpreter::CurryLevel;
        Projection::within(
            CurryLevel::OUTERMOST,
            Predicate::point(Value::UInt(row)),
            Projection::of_field(name, Projection::Everything),
        )
        .guard(tiling)
    }

    #[rstest_log::rstest]
    fn a_finished_store_and_sum_reach_the_sink_independently(
        #[values(false, true)] on_release: bool,
    ) {
        use crate::interpreter::ColumnValue;
        let (ty, rows) = customers_with_state([true, true], [3, 9]);
        let (first, second, _) = deliver_sibling_packages(
            &rows,
            &ty,
            [state_field(&ty, 7, "total"), state_field(&ty, 7, "account")],
            on_release,
        );
        let Tile::Record { fields, .. } = first.deepest_values() else {
            unreachable!()
        };
        let Tile::Store { seed, closures, .. } = &fields["account"] else {
            unreachable!()
        };
        assert!(closures.at(0).terminal);
        let Tile::Record { fields, .. } = &**seed else {
            unreachable!()
        };
        assert_eq!(fields["balance"], Tile::Scalar(ColumnValue::Ints(vec![13])));
        let Tile::Record { fields, .. } = second.deepest_values() else {
            unreachable!()
        };
        let Tile::Aggregation { accumulator, .. } = &fields["total"] else {
            unreachable!()
        };
        assert_eq!(**accumulator, Tile::Scalar(ColumnValue::Ints(vec![3])));
    }

    #[test]
    fn a_memo_retains_unfinished_state_at_the_input_until_its_customer_closes() {
        use super::*;
        use crate::interpreter::{
            ColumnValue,
            tile_operators::{
                MemoProducer, TileProducer,
                test_helpers::{ConsumeInPipeline, ProjectionSpy},
            },
        };
        let (ty, rows) = customers_with_state([true, false], [3, 4]);
        let (spy, script) = ProjectionSpy::scripted(rows, ty.clone());
        let releases = spy.released.clone();
        let mut memo = MemoProducer::over(Box::new(spy), &ty);
        memo.consume_in_pipeline(InputId::ONLY, ty.universal_guard());
        let sum = state_field(&ty, 8, "total");
        let account = state_field(&ty, 8, "account");
        let first = releases.read().unwrap()[0].clone();
        assert!(first.subsumes(&state_field(&ty, 7, "total")));
        assert!(first.subsumes(&state_field(&ty, 7, "account")));
        assert!(first.intersect(&sum.union(&account)).is_empty());
        let absent = in_a_run(|| memo.get(sum.clone()));
        assert!(absent.to_guard().is_empty());
        *script.write().unwrap() = customers_with_state([true, true], [3, 11]).1;
        memo.consume_in_pipeline(InputId::ONLY, ty.universal_guard());
        let last = releases.read().unwrap().last().unwrap().clone();
        assert!(last.subsumes(&sum.union(&account)));
        assert!(last.intersect(&first).is_empty());
        let ready = in_a_run(|| memo.get(sum));
        let Tile::Record { fields, .. } = ready.deepest_values() else {
            unreachable!()
        };
        let Tile::Aggregation { accumulator, .. } = &fields["total"] else {
            unreachable!()
        };
        assert_eq!(**accumulator, Tile::Scalar(ColumnValue::Ints(vec![11])));
        let store = in_a_run(|| memo.get(account));
        let Tile::Record { fields, .. } = store.deepest_values() else {
            unreachable!()
        };
        let Tile::Store { seed, .. } = &fields["account"] else {
            unreachable!()
        };
        let Tile::Record { fields, .. } = &**seed else {
            unreachable!()
        };
        assert_eq!(fields["balance"], Tile::Scalar(ColumnValue::Ints(vec![29])));
    }

    fn customers_with_history() -> Tile {
        use crate::interpreter::{ColumnValue, Predicate, Tile};
        // The same item keys occur on another day and under another customer.
        let group = |starts, keys, values| {
            Tile::grouped(
                starts,
                ColumnValue::UInts(keys),
                Box::new(values),
                Predicate::False,
                Default::default(),
            )
        };
        let history = group(
            vec![0, 2],
            vec![3, 5, 3],
            group(
                vec![0, 2, 3],
                vec![2, 4, 4, 4],
                Tile::Scalar(ColumnValue::Ints(vec![72, 74, 75, 84])),
            ),
        );
        let mut customers = group(
            vec![0],
            vec![7, 8],
            Tile::record(
                [
                    ("id".into(), Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                    (
                        "profile".into(),
                        Tile::record(
                            [
                                ("rank".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
                                (
                                    "visits".into(),
                                    group(
                                        vec![0, 1],
                                        vec![0, 1],
                                        Tile::Scalar(ColumnValue::Ints(vec![1, 3])),
                                    ),
                                ),
                            ]
                            .into(),
                        ),
                    ),
                    ("history".into(), history),
                ]
                .into(),
            ),
        );
        // A closed cache must only restate the requested leaf.
        if let Tile::DataFunction {
            domain_predicate, ..
        } = &mut customers
        {
            *domain_predicate = Predicate::True;
        }
        customers
    }

    fn customer_tiling() -> Tiling {
        use super::*;
        use crate::interpreter::types::BaseType;
        let collection = |values| Tiling::data_function(Extent::uint_range(16), values);
        let scalar = Tiling::Scalar(Extent::Base(BaseType::Int));
        collection(Tiling::Record(
            [
                ("id".into(), scalar.clone()),
                (
                    "profile".into(),
                    Tiling::Record(
                        [
                            ("rank".into(), scalar.clone()),
                            ("visits".into(), collection(scalar.clone())),
                        ]
                        .into(),
                    ),
                ),
                ("history".into(), collection(collection(scalar))),
            ]
            .into(),
        ))
    }

    fn customer_history_item(tiling: &Tiling, item: u64) -> TileGuard {
        use super::*;
        use crate::interpreter::CurryLevel;
        Projection::within(
            CurryLevel::OUTERMOST,
            Predicate::point(Value::UInt(7)),
            Projection::of_field(
                "history",
                Projection::of_path(&[Value::UInt(3), Value::UInt(item)]),
            ),
        )
        .guard(tiling)
    }

    #[test]
    fn a_whole_customer_read_serializes_with_each_history_item() {
        use super::*;
        let tiling = customer_tiling();
        let whole = Projection::admitting(Predicate::point(Value::UInt(7))).guard(&tiling);
        let two = customer_history_item(&tiling, 2);
        let four = customer_history_item(&tiling, 4);
        let queue = Queue::new();
        queue.append(&[
            two.clone(),
            four.clone(),
            whole.clone(),
            whole.clone(),
            two.clone(),
        ]);
        let claim = || {
            queue
                .claim(0, false, || Some(()))
                .map(|(package, ())| package)
        };
        let a = claim().unwrap();
        let b = claim().unwrap();
        assert_eq!((&a.guard, &b.guard), (&two, &four));
        assert!(claim().is_none());
        queue.acknowledge(&b, || {}).unwrap();
        assert!(claim().is_none());
        queue.acknowledge(&a, || {}).unwrap();
        let first_row = claim().unwrap();
        assert_eq!(first_row.guard, whole);
        assert!(claim().is_none(), "two whole-row reads must serialize");
        queue.acknowledge(&first_row, || {}).unwrap();
        let second_row = claim().unwrap();
        assert_eq!(second_row.guard, whole);
        assert!(
            claim().is_none(),
            "a leaf also waits behind a whole-row read"
        );
        queue.acknowledge(&second_row, || {}).unwrap();
        let leaf = claim().unwrap();
        assert_eq!(leaf.guard, two);
        queue.acknowledge(&leaf, || {}).unwrap();
    }

    fn deliver_sibling_packages(
        row: &Tile,
        tiling: &Tiling,
        [paused_field, ready_field]: [TileGuard; 2],
        on_release: bool,
    ) -> (Tile, Tile, Tile) {
        use super::*;
        use crate::interpreter::{
            DataSink, Tile,
            tile_operators::{
                MemoProducer, ProducerBase, SinkBreaker, TileProducer, share_breaker,
                test_helpers::{ConsumeInPipeline, ProjectionSpy, first_breaker},
            },
        };
        use std::{sync::mpsc, time::Duration};

        struct PausedField {
            input: Box<dyn TileProducer>,
            field: TileGuard,
            on_release: bool,
            paused: mpsc::Sender<()>,
            resume: Mutex<Option<mpsc::Receiver<()>>>,
        }
        impl PausedField {
            fn pause(&self, guard: &TileGuard, releasing: bool) {
                if self.on_release == releasing
                    && *guard == self.field
                    && let Some(resume) = self.resume.lock().unwrap().take()
                {
                    self.paused.send(()).unwrap();
                    resume.recv_timeout(Duration::from_secs(15)).unwrap();
                }
            }
        }
        impl TileProducer for PausedField {
            fn base(&self) -> &ProducerBase {
                self.input.base()
            }
            fn base_mut(&mut self) -> &mut ProducerBase {
                self.input.base_mut()
            }
            fn get(&self, guard: TileGuard) -> Tile {
                let answer = self.input.get(guard.clone());
                self.pause(&guard, false);
                answer
            }
            fn get_impl(&self, _: TileGuard) -> Tile {
                unreachable!()
            }
            fn release_impl(&self, guard: TileGuard) {
                self.pause(&guard, true);
                self.input.release_impl(guard);
            }
        }
        struct Output(mpsc::Sender<Tile>);
        impl DataSink for Output {
            fn process(&self, tile: &Tile) {
                self.0.send(tile.clone()).unwrap();
            }
        }

        let (spy, _, _) = ProjectionSpy::new(row.clone(), tiling.clone());
        let mut cache = MemoProducer::over(Box::new(spy), tiling);
        cache.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        let (paused, entered) = mpsc::channel();
        let (resume, resume_rx) = mpsc::channel();
        let cached_reader = share_breaker(cache);
        let original = first_breaker(&*cached_reader).unwrap();
        let input = PausedField {
            input: cached_reader,
            field: paused_field.clone(),
            on_release,
            paused,
            resume: Mutex::new(Some(resume_rx)),
        };
        let (source, sink) = (PipelineId(0), PipelineId(1));
        let mut memo = MemoProducer::over(Box::new(input), tiling);
        memo.base_mut().downstream = Some(Arc::new(Entry::new(sink, tiling.clone())));
        let reader = share_breaker(memo);
        let chain = first_breaker(&*reader).unwrap();
        let (sent, tiles) = mpsc::channel();
        let output = Arc::new(RwLock::new(SinkBreaker::new(
            Arc::new(RwLock::new(Some(reader))),
            Arc::new(Output(sent)),
        )));
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 16);
        let execution = plan::Execution::new(&[None, None], &mut dispatcher);
        let workers = execution.worker_pool(&mut dispatcher, 2, |id| {
            Some(if id == source.0 {
                WorkerBreaker::Chain(chain.clone())
            } else {
                WorkerBreaker::Sink(output.clone())
            })
        });
        for guard in [&paused_field, &ready_field] {
            dispatcher.queue_for(source, guard);
        }
        let consume = |pipeline, expected: TileGuard| {
            let package = dispatcher
                .claim_of(pipeline)
                .expect("independent field ready");
            assert_eq!(package.guard, expected);
            workers.consume(&dispatcher, package, &mut |_, _| unreachable!());
        };
        let timeout = Duration::from_secs(5);
        let delivered = thread::scope(|threads| {
            let worker_a = threads.spawn(|| consume(source, paused_field.clone()));
            entered.recv_timeout(timeout).expect("first worker paused");
            threads.spawn(|| {
                consume(source, ready_field.clone());
                consume(sink, ready_field.clone());
            });
            let first = tiles.recv_timeout(timeout);
            let released = chain.read().unwrap().obsolete_guard();
            resume.send(()).unwrap();
            worker_a.join().unwrap();
            let first =
                first.expect("the ready package reached the sink while its sibling was paused");
            assert_eq!(released, ready_field);
            assert_eq!(first.to_guard(), ready_field);
            consume(sink, paused_field.clone());
            let second = tiles.recv_timeout(timeout).unwrap();
            assert_eq!(second.to_guard(), paused_field);
            (first, second)
        });
        assert_eq!(dispatcher.outstanding(sink), 0);
        assert!(tiles.try_recv().is_err());
        let remaining = in_a_run(|| chain.read().unwrap().get(tiling.universal_guard()));
        // Check physical reclamation in the original memo too. The other day and
        // customer have the same item key and must retain their cells.
        let mut expected = row.clone();
        expected.remove_guarded(paused_field.union(&ready_field));
        expected.compact();
        let cached = in_a_run(|| original.read().unwrap().get(tiling.universal_guard()));
        assert_eq!(cached, expected);
        (delivered.0, delivered.1, remaining)
    }

    #[test]
    fn flat_memo_publishes_partial_answers_and_later_absences_once() {
        use super::*;
        use crate::interpreter::tile_operators::{
            MemoProducer,
            growing::{Input, growing_source, ints},
            test_helpers::{keys_between, push_to},
        };

        let source = growing_source([0, 2, 4]);
        let mut memo = MemoProducer::over(Box::new(Input::over(&source)), &ints());
        push_to(&mut memo, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 2);
        let requested = keys_between(0, 5);
        let consume = |guard| {
            let mut pushes = dispatcher.pushes(PipelineId(0));
            let snapshot = memo.consume_for_dispatch(InputId::ONLY, guard, &mut pushes);
            assert!(
                snapshot.is_none(),
                "each package publishes its own completion"
            );
            dispatcher.land(pushes);
            let mut received = Vec::new();
            while let Next::Package(package) = dispatcher.try_claim(Some(PipelineId(1))) {
                received.push(package.guard.clone());
                dispatcher.acknowledge(package);
            }
            received
        };
        let point = |k| keys_between(k, k);
        assert_eq!(
            consume(requested.clone()),
            vec![point(0).union(&point(2)), point(4)]
        );
        assert!(consume(requested.clone()).is_empty());
        source.write().unwrap().closed = true;
        let absent = point(1).union(&point(3)).union(&point(5));
        assert_eq!(consume(requested.clone()), vec![absent]);
        // Completing the remaining positions closes the whole finite collection.
        let rest = guard_minus(&ints().universal_guard(), &requested);
        assert_eq!(consume(keys_between(6, 11)), vec![rest]);
    }

    /// The first handler holds its schedule and its store until a distinct worker enters the
    /// second one and advances it another round without waiting for the first.
    #[rstest_log::rstest]
    fn independent_scope_steps_overlap(#[values(false, true)] transactions: bool) {
        use super::super::{PipelineId, STEP_PROBE};
        use std::sync::{Arc, Condvar, Mutex};
        use std::time::Duration;

        let source = if transactions {
            indoc::indoc! {"
                a: Mut(Int, Txn) := 0
                b: Mut(Int, Txn) := 0
                for x in [1, 2, 3]:
                    with begin():
                        a := a + x
                for y in [4, 5]:
                    with begin():
                        b := b + y
                await_final(a) + await_final(b)
            "}
        } else {
            indoc::indoc! {"
                a := 0
                b := 0
                for x in [1, 2, 3]:
                    a += x
                for y in [4, 5]:
                    b += y
                a + b
            "}
        };
        let expected = evaluate(source, 1).main.expect("a serial result");
        let entered = Arc::new((Mutex::new(Vec::new()), Condvar::new()));
        let observed = entered.clone();
        let probe = Arc::new(move |pipeline: PipelineId| {
            let (entries, changed) = &*observed;
            let mut entries = entries.lock().unwrap();
            if entries.len() == 3 {
                return;
            }
            entries.push((pipeline.0, std::thread::current().id()));
            changed.notify_all();
            if entries.len() > 1 {
                return;
            }
            let (entries, _) = changed
                .wait_timeout_while(entries, Duration::from_secs(5), |e| e.len() < 3)
                .unwrap();
            assert_eq!(
                entries.len(),
                3,
                "an independent scope must step twice before this handler exits"
            );
        });
        STEP_PROBE.set(Some(probe));
        let run = evaluate(source, 2);
        STEP_PROBE.set(None);
        assert_eq!(run.main, Some(expected));
        let entries = entered.0.lock().unwrap();
        assert_eq!(entries.len(), 3);
        assert_eq!(entries[1].0, entries[2].0);
        assert_ne!(entries[0].0, entries[1].0);
        assert_ne!(entries[0].1, entries[1].1);
    }

    #[test]
    fn compiled_programs_use_shared_native_breakers_at_each_dop() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        for tail in [
            "[y + 1 for y in ys]",
            "max(ys)",
            "sum(ys)",
            "max([max(g) for g in groupby(ys, \\x -> x - (x // 8) * 8)])",
        ] {
            let source = format!("xs = [{values}]\nys = [x * 2 for x in xs]\n{tail}");
            let inline = evaluate(&source, 1);
            assert!(
                inline.planned.iter().all(|p| p.worker_claims == 0),
                "one worker consumes on the coordinator: {tail}"
            );
            let expected = inline.main.map(crate::interpreter::sort_function_by_domain);
            for dop in [2, 4] {
                let run = evaluate(&source, dop);
                assert_eq!(
                    run.main.map(crate::interpreter::sort_function_by_domain),
                    expected,
                    "DOP {dop}: {tail}"
                );
                assert!(
                    run.planned.iter().any(|p| p.worker_claims > 0),
                    "no native worker: {tail}"
                );
            }
        }
    }
    #[test]
    fn native_pipelines_publish_before_dependencies_close() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let run = evaluate(
            &format!("xs = [{values}]\nys = [x * 2 for x in xs]\n[y + 1 for y in ys]"),
            4,
        );
        assert!(
            run.planned.iter().any(|p| p.workers_used > 1),
            "{:#?}",
            run.planned
        );
        assert!(
            run.planned.iter().any(|p| p.incremental_claims > 0),
            "{:#?}",
            run.planned
        );
    }
    /// A `:=` loop over a collection the workers build answers at more than one worker what it
    /// answers at one: its source can run on the workers between rounds.
    #[test]
    fn a_loop_answers_at_each_dop_what_it_answers_at_one() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            ys = [x * 2 for x in xs]
            total := 0
            for y in ys:
                total += y
            total
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            let run = evaluate(&source, dop);
            assert_eq!(run.main, expected, "DOP {dop}");
            assert!(
                run.planned.iter().any(|p| p.worker_claims > 0),
                "DOP {dop}: the source of the loop runs on the workers"
            );
        }
    }

    /// A `:=` loop whose body holds breakers the workers run, a materialized comprehension and a
    /// `max` over it, answers at more than one worker what it answers at one: each round's work
    /// is queued once the scope releases its store, and the step waits for what the round's
    /// consumes left held.
    #[test]
    fn a_loop_body_on_the_workers_answers_what_it_answers_at_one() {
        let values = (0..256)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            total := 0
            for x in xs:
                total += max([x * k for k in [1, 2, 3]])
            total
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            for _ in 0..4 {
                let run = evaluate(&source, dop);
                assert_eq!(run.main, expected, "DOP {dop}");
                // Each of the 256 rounds gives the body's breakers a package each, counted under
                // the loop's request pipeline.
                let body: usize = run
                    .planned
                    .iter()
                    .filter(|planned| planned.name.starts_with("InductionRequest"))
                    .map(|planned| planned.worker_claims)
                    .sum();
                assert!(
                    body >= 256,
                    "DOP {dop}: the body runs on the workers: {:?}",
                    run.planned
                );
            }
        }
    }

    #[test]
    fn a_worker_seed_opens_a_transaction_after_its_input_loop_finishes() {
        use crate::interpreter::{ColumnValue, tiling::Tile};
        let source = indoc::indoc! {"
            initial := 0
            for x in [1, 2, 3, 4]:
                initial += x
            total: Mut(Int, Txn) := initial
            for r in [1, 2]:
                with begin():
                    total := total - r
            await_final(total)
        "};
        for dop in [1, 2, 4] {
            let run = evaluate(source, dop);
            assert_eq!(run.main, Some(Tile::Scalar(ColumnValue::Ints(vec![7]))));
            let seed = run
                .planned
                .iter()
                .find(|p| p.name.starts_with("Commit") && p.rounds.is_empty())
                .expect("the transaction seed has its own pipeline");
            assert_eq!(seed.worker_claims > 0, dop > 1);
        }
    }

    /// A transaction writer whose body holds breakers the workers run answers at more than one
    /// worker what it answers at one: each attempt's work is queued once the writer releases its
    /// store, and the commit waits for what the attempt's consumes left held.
    #[test]
    fn a_transaction_body_on_the_workers_answers_what_it_answers_at_one() {
        let values = (0..128)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            t: Mut(Int, Txn) := 0
            for x in xs:
                with begin():
                    t := t + max([x * k for k in [1, 2, 3]])
            await_final(t)
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            for _ in 0..4 {
                let run = evaluate(&source, dop);
                assert_eq!(run.main, expected, "DOP {dop}");
                // Each of the 128 attempts gives the body's breaker a package, counted under the
                // writer's pipeline.
                let body: usize = run
                    .planned
                    .iter()
                    .filter(|planned| planned.name.starts_with("Commit"))
                    .map(|planned| planned.worker_claims)
                    .sum();
                assert!(
                    body >= 128,
                    "DOP {dop}: the body runs on the workers: {:?}",
                    run.planned
                );
            }
        }
    }

    /// A panic in a claim a worker consumes ends the run with that panic on the calling thread,
    /// and the pool it unwinds through joins its workers: a later run on the thread completes.
    #[test]
    fn a_worker_panic_ends_the_run_with_that_panic() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let failed = std::panic::catch_unwind(|| {
            evaluate(
                &formatdoc! {"
                    xs = [{values}]
                    ys = [x // (x - x) for x in xs]
                    [y + 1 for y in ys]
                "},
                4,
            )
        })
        .err()
        .expect("a division by zero in a worker's claim fails the run");
        assert_eq!(
            failed.downcast_ref::<&str>().copied(),
            Some("attempt to divide by zero")
        );
        let run = evaluate(
            &formatdoc! {"
                xs = [{values}]
                ys = [x * 2 for x in xs]
                max(ys)
            "},
            4,
        );
        assert!(run.planned.iter().any(|p| p.worker_claims > 0));
    }
}

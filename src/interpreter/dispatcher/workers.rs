//! Shared native breaker execution: worker threads that claim the packages of admitted pipelines
//! from the run's dispatcher. See `src/interpreter/design-dispatcher.md`, "Shared native pipeline
//! execution".
use super::*;
use crate::interpreter::CurryLevel;
#[cfg(test)]
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::thread::{Scope, ScopedJoinHandle};

/// The breaker a worker consumes with: a chain's, which pushes what it produces, or a sink's at
/// the root of the run, which hands each package's answer to its sink and pushes nothing.
pub(super) enum WorkerBreaker {
    Chain(BreakerHandle),
    Sink(Arc<RwLock<crate::interpreter::tile_operators::SinkBreaker>>),
}

impl WorkerBreaker {
    /// `f` on the breaker, held shared.
    fn read<R>(&self, f: impl FnOnce(&dyn Breaker) -> R) -> R {
        match self {
            WorkerBreaker::Chain(handle) => {
                f(&*handle.read().unwrap_or_else(PoisonError::into_inner))
            }
            WorkerBreaker::Sink(sink) => f(&*sink.read().unwrap_or_else(PoisonError::into_inner)),
        }
    }

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

/// A pipeline the workers may run: its breaker, how its claims split, and whether a worker runs
/// its finish.
pub(super) struct WorkerTarget {
    pub(super) handle: WorkerBreaker,
    /// The deepest level whose keys the chain beneath the breaker restates, where the breaker's
    /// consume runs concurrently: a package naming keys at or above it runs beside others.
    pub(super) restated: Option<CurryLevel>,
    /// Whether the workers consume the pipeline although it has no parallel level, one package at
    /// a time, and run its finish: no scope's pipeline reads it, so no consume or finish of it
    /// offers a scope requests.
    pub(super) serial: bool,
}

/// An admitted pipeline's breaker and the level its claims partition.
struct Spec {
    target: WorkerBreaker,
    /// The deepest level whose keys its chain restates ([`WorkerTarget::restated`]); `None` for a
    /// pipeline whose packages are consumed one at a time, in queue order.
    restated: Option<CurryLevel>,
    /// Whether a worker runs the pipeline's finish.
    finishes: bool,
    /// For a pipeline of a loop's or transaction writer's body, the body's follower hold, which a
    /// claim holds again before it is acknowledged.
    body: Option<HoldGroup>,
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

/// The run's worker threads, and which pipelines they claim from.
pub(super) struct WorkerPool {
    /// How many workers the run has; with one, the coordinator claims everything and no thread
    /// starts.
    count: usize,
    /// Per pipeline, its breaker and level where the pipeline is admitted.
    specs: Vec<Option<Spec>>,
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
}

impl WorkerPool {
    pub(super) fn new(
        count: usize,
        targets: Vec<Option<WorkerTarget>>,
        bodies: Vec<Option<HoldGroup>>,
    ) -> Self {
        assert!(count > 0, "a run has at least one worker");
        debug_assert_eq!(
            targets.len(),
            bodies.len(),
            "the targets and the bodies name the same pipelines"
        );
        let specs: Vec<_> = targets
            .into_iter()
            .zip(bodies)
            .map(|(target, body)| {
                let WorkerTarget {
                    handle,
                    restated,
                    serial,
                } = target?;
                (restated.is_some() || serial).then_some(Spec {
                    target: handle,
                    restated,
                    finishes: serial,
                    body,
                })
            })
            .collect();
        Self {
            count,
            #[cfg(test)]
            stats: (0..specs.len()).map(|_| Stats::default()).collect(),
            specs,
            unstarted: AtomicBool::new(false),
            busy: AtomicUsize::new(0),
        }
    }

    /// Whether the run starts worker threads: more than one worker, and a pipeline for them.
    fn threaded(&self) -> bool {
        self.count > 1 && self.specs.iter().any(Option::is_some)
    }

    /// Whether `pipeline`'s packages are the workers' to claim.
    pub(super) fn admits(&self, pipeline: PipelineId) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && self.specs.get(pipeline.0).is_some_and(Option::is_some)
    }

    /// Whether `pipeline`'s finish is the workers' to claim.
    pub(super) fn finishes(&self, pipeline: PipelineId) -> bool {
        self.admits(pipeline)
            && self.specs[pipeline.0]
                .as_ref()
                .is_some_and(|spec| spec.finishes)
    }

    /// The admitted pipelines with no parallel level, which the run orders so that one package of
    /// each is in flight at a time. None where the run starts no worker.
    pub(super) fn serial(&self) -> Vec<PipelineId> {
        if !self.threaded() {
            return Vec::new();
        }
        self.specs
            .iter()
            .enumerate()
            .filter(|(_, spec)| spec.as_ref().is_some_and(|spec| spec.restated.is_none()))
            .map(|(pipeline, _)| PipelineId(pipeline))
            .collect()
    }

    /// The admitted pipelines whose packages run at once, with the deepest level their chains
    /// restate. None where the run starts no worker.
    pub(super) fn restated(&self) -> Vec<(PipelineId, CurryLevel)> {
        if !self.threaded() {
            return Vec::new();
        }
        self.specs
            .iter()
            .enumerate()
            .filter_map(|(pipeline, spec)| Some((PipelineId(pipeline), spec.as_ref()?.restated?)))
            .collect()
    }

    /// Start the workers in `scope`. Each claims until the run is done, has failed, or its claims
    /// are stopped. [`join`](Self::join) takes the handles.
    pub(super) fn spawn<'scope, 'env>(
        &'env self,
        scope: &'scope Scope<'scope, 'env>,
        dispatcher: &'env Dispatcher,
    ) -> Vec<ScopedJoinHandle<'scope, ()>> {
        if !self.threaded() {
            return Vec::new();
        }
        // A thread the system refuses leaves the run with the workers it has. Panicking instead
        // would leave the workers already started asleep, and the scope waiting for them.
        let mut handles = Vec::new();
        // The coordinator claims as one of the run's workers ([`next`](Self::next)), so the run
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

    /// One worker's claims: consume, publish and acknowledge each package of an admitted pipeline.
    fn work(&self, dispatcher: &Dispatcher, worker: usize) {
        #[cfg(not(test))]
        let _ = worker;
        in_a_run(|| {
            // A panic fails the run, so no claimant waits for what this worker held.
            let _worker = dispatcher.worker();
            let mut preferred = None;
            loop {
                match dispatcher.claim_where(
                    preferred,
                    &|pipeline| self.admits(pipeline),
                    &|pipeline| self.finishes(pipeline),
                ) {
                    // Counted once the claim has returned. Until then the claim's own state
                    // shows it: the package is in flight, or the pipeline finishing, and
                    // `may_progress` reads both.
                    Next::Package(package) => {
                        self.busy.fetch_add(1, Ordering::SeqCst);
                        preferred = Some(package.pipeline);
                        #[cfg(test)]
                        self.count_claim(dispatcher, &package, worker);
                        self.consume(dispatcher, package);
                        // A coordinator asleep because this package was in flight wakes to see the
                        // claim ended, whether or not the acknowledgement advanced the generation.
                        self.busy.fetch_sub(1, Ordering::SeqCst);
                        dispatcher.wake_claimants();
                    }
                    Next::Finish { pipeline } => {
                        self.busy.fetch_add(1, Ordering::SeqCst);
                        self.finish(dispatcher, pipeline);
                        self.busy.fetch_sub(1, Ordering::SeqCst);
                        dispatcher.wake_claimants();
                    }
                    Next::Done | Next::Failed => return,
                    Next::Wait(_) => unreachable!("a worker's claim blocks while it waits"),
                }
            }
        });
    }

    /// [`consume`](Self::consume) on the coordinator, which claims as worker 0. It wakes the
    /// claimants after, as a worker thread does, so a claimant that waits on the pool's busy count
    /// sees the claim end.
    pub(super) fn consume_on_coordinator(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        #[cfg(test)]
        self.count_claim(dispatcher, &package, 0);
        self.consume(dispatcher, package);
        dispatcher.wake_claimants();
    }

    /// [`finish`](Self::finish) on the coordinator, waking the claimants after as a worker
    /// thread does.
    pub(super) fn finish_on_coordinator(&self, dispatcher: &Dispatcher, pipeline: PipelineId) {
        self.finish(dispatcher, pipeline);
        dispatcher.wake_claimants();
    }

    /// Consume `package` under the breaker's handle held shared, publish the pipeline under it
    /// held exclusively, land the pushes with no handle held, and acknowledge the package.
    fn consume(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        let pipeline = package.pipeline;
        let spec = self.specs[pipeline.0]
            .as_ref()
            .expect("a worker claims only admitted pipelines");
        let target = &spec.target;
        if spec.restated.is_none() {
            // One package at a time, under the handle held exclusively, as on the coordinator
            // (`consume_with`).
            let pushes = target.write(|breaker| {
                debug_assert!(
                    package
                        .guard
                        .check_from(&breaker.input_tiling(InputId::ONLY)),
                    "pipeline {} consumes a guard of the tiling its breaker's input answers: {:?}",
                    pipeline.0,
                    package.guard
                );
                breaker.consume_impl(InputId::ONLY, package.guard.clone());
                breaker
                    .as_producer()
                    .filter(|producer| producer.pushes_while_consuming())
                    .map(|producer| {
                        let mut pushes = dispatcher.pushes(pipeline);
                        pushes.push_final(producer);
                        pushes
                    })
            });
            if let Some(pushes) = pushes {
                dispatcher.land(pushes);
            }
            if let Some(body) = &spec.body {
                dispatcher.hold_followers(*body);
            }
            dispatcher.acknowledge(package);
            return;
        }
        target.read(|breaker| {
            debug_assert!(
                package
                    .guard
                    .check_from(&breaker.input_tiling(InputId::ONLY)),
                "pipeline {} consumes a guard of the tiling its breaker's input answers: {:?}",
                pipeline.0,
                package.guard
            );
            breaker.consume_impl(InputId::ONLY, package.guard.clone());
        });
        // Exclusive, so the push sees no consume between the merge of its rows and the release of
        // its input, which the readers it wakes rely on. A breaker that publishes only at its
        // finish or in the resume pass pushes nothing here, as on the coordinator
        // (`consume_with`).
        let pushes = target.write(|breaker| {
            breaker
                .as_producer()
                .filter(|producer| producer.pushes_while_consuming())
                .map(|producer| {
                    let mut pushes = dispatcher.pushes(pipeline);
                    pushes.push_final(producer);
                    pushes
                })
        });
        if let Some(pushes) = pushes {
            dispatcher.land(pushes);
        }
        // Before the acknowledgement that can leave the body quiescent: the round's step waits
        // for the coordinator to publish what this consume left held, as it does after a claim
        // of its own (`Execution::consume`).
        if let Some(body) = &spec.body {
            dispatcher.hold_followers(*body);
        }
        dispatcher.acknowledge(package);
    }

    /// Finish `pipeline`, whose finish this worker claimed: release a parallel input whole, then
    /// push what the breaker completed and mark the pipeline finished (`finish_with`).
    fn finish(&self, dispatcher: &Dispatcher, pipeline: PipelineId) {
        let spec = self.specs[pipeline.0]
            .as_ref()
            .expect("a worker finishes only admitted pipelines");
        let mut reach = |reached: PipelineId, call: &mut Call<'_>| {
            debug_assert_eq!(
                reached.0, pipeline.0,
                "a worker's finish reaches its own breaker"
            );
            spec.target.write(|breaker| call(breaker, InputId::ONLY))
        };
        if spec.restated.is_some() {
            reach(pipeline, &mut |breaker, _| breaker.finish_parallel_input());
        }
        // No follower hold, unlike a consume: the finish lands everything the breaker completed,
        // and a hold taken once the scope's body is inactive is never released.
        finish_with(dispatcher, &mut reach, pipeline);
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

    /// The coordinator's next claim: any package and any finish, since the coordinator is one of
    /// the run's workers. A claim of a pipeline the workers admit runs as a worker's would
    /// ([`consume`](Self::consume), [`finish`](Self::finish)); any other runs through the
    /// coordinator's handlers.
    pub(super) fn next(&self, dispatcher: &Dispatcher) -> Next {
        dispatcher.try_claim_where(None, &|_| true, &|_| true)
    }

    /// Whether a worker holds or can claim a package: the coordinator waits for the workers rather
    /// than deciding the run is stalled.
    pub(super) fn may_progress(&self, dispatcher: &Dispatcher) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && (self.busy.load(Ordering::SeqCst) > 0
                || dispatcher.may_claim_where(&|pipeline| self.admits(pipeline))
                || dispatcher.may_finish_where(&|pipeline| self.finishes(pipeline)))
    }

    /// Before the coordinator finishes an admitted pipeline, release its input whole.
    pub(super) fn finishing(&self, p: PipelineId, reach: &mut Reach<'_>) {
        if self
            .specs
            .get(p.0)
            .and_then(Option::as_ref)
            .is_some_and(|spec| spec.restated.is_some())
        {
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

    fn evaluate(source: &str, dop: usize) -> super::super::Run {
        let mut context = GlobalContext::default();
        let mut program =
            compile_program(&mut context, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        run_program_with_workers(&mut program, 8, dop).unwrap()
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
    /// answers at one: its body runs on the coordinator, and its source on the workers.
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

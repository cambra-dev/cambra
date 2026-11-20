//! Shared native breaker execution: worker threads that claim every package and every finish from
//! the run's dispatcher, beside the coordinator. See `src/interpreter/design-dispatcher.md`,
//! "Shared native pipeline execution".
use super::plan::Execution;
use super::*;
use crate::interpreter::CurryLevel;
#[cfg(test)]
use std::sync::atomic::{AtomicU64, AtomicUsize};
use std::thread::{Scope, ScopedJoinHandle};

/// A partitioned pipeline's breaker and the level its claims partition.
struct Spec {
    target: BreakerHandle,
    level: CurryLevel,
    /// For a pipeline of a loop's or transaction writer's body, the body's pipelines and step,
    /// whose followers a claim holds again before it is acknowledged.
    body: Option<Vec<PipelineId>>,
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

/// What a thread's claim did ([`WorkerPool::run_next`]).
pub(super) enum Claimed {
    /// It ran a package or a finish.
    Ran,
    /// Nothing was claimable since the generation.
    Wait(Generation),
    Done,
    Failed,
}

/// The run's worker threads, and which pipelines several of them consume at once.
pub(super) struct WorkerPool {
    /// How many threads the run has, the coordinator included: it starts one fewer worker thread.
    /// With one, the coordinator claims everything and no thread starts.
    count: usize,
    /// Per pipeline, its breaker and level where several claims consume it at once.
    specs: Vec<Option<Spec>>,
    /// Per pipeline, the exclusion domain its serial work belongs to: a package of a pipeline that
    /// is not partitioned, and every pipeline's finish ([`ExclusionDomains`]).
    domain_of: Vec<usize>,
    /// Per exclusion domain, its pipelines.
    domains: Vec<Vec<PipelineId>>,
    /// Per exclusion domain, whether a thread holds it: one claim of its serial work, or the
    /// coordinator's control ([`control`](Self::control)).
    // shared-state-ok: one flag per domain, set by compare-and-swap; the holder alone clears it.
    busy: Vec<AtomicBool>,
    /// Per exclusion domain, whether a thread found it held since its holder took it: the holder
    /// wakes the claimants as it releases it, so one that skipped the domain sees it free.
    // shared-state-ok: a flag a thread sets and the domain's holder clears as it releases it.
    contended: Vec<AtomicBool>,
    /// Set while the coordinator takes or holds every domain for the run's control: no serial
    /// claim starts, so the coordinator is not starved of a domain a worker takes again.
    controlling: AtomicBool,
    /// Set where the system refused every worker thread: the coordinator claims everything.
    unstarted: AtomicBool,
    #[cfg(test)]
    stats: Vec<Stats>,
}

impl WorkerPool {
    pub(super) fn new(
        count: usize,
        targets: Vec<Option<BreakerHandle>>,
        bodies: Vec<Option<Vec<PipelineId>>>,
        mut domains: Joining,
        reads: &[Vec<usize>],
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
                let target = target?;
                let level = target
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .parallel_level()?;
                Some(Spec {
                    target,
                    level,
                    body,
                })
            })
            .collect();
        // A pipeline that is not partitioned shares a domain with every pipeline it reads: its
        // consume reads what their claims are still changing, and its release counts on none of
        // them running beside it. A partitioned pipeline's packages hold no domain, and its finish
        // waits for every pipeline it reads to finish.
        for (pipeline, spec) in specs.iter().enumerate() {
            if spec.is_none() {
                for &read in &reads[pipeline] {
                    domains.join(pipeline, read);
                }
            }
        }
        let domains = domains.done();
        debug_assert_eq!(
            domains.domain_of.len(),
            specs.len(),
            "every pipeline belongs to one exclusion domain"
        );
        let mut members = vec![Vec::new(); domains.count];
        for (pipeline, &domain) in domains.domain_of.iter().enumerate() {
            members[domain].push(PipelineId(pipeline));
        }
        Self {
            count,
            #[cfg(test)]
            stats: (0..specs.len()).map(|_| Stats::default()).collect(),
            specs,
            domain_of: domains.domain_of,
            busy: (0..members.len()).map(|_| AtomicBool::new(false)).collect(),
            contended: (0..members.len()).map(|_| AtomicBool::new(false)).collect(),
            domains: members,
            controlling: AtomicBool::new(false),
            unstarted: AtomicBool::new(false),
        }
    }

    /// Whether the run starts worker threads: more than one worker, and a partitioned pipeline.
    /// Without one, every claim is serial work, which another thread would only wait to run.
    fn threaded(&self) -> bool {
        self.count > 1 && self.specs.iter().any(Option::is_some)
    }

    /// Whether several claims of `pipeline` consume it at once, outside its exclusion domain. With
    /// one thread every package is serial work.
    fn partitioned(&self, pipeline: PipelineId) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && self.specs.get(pipeline.0).is_some_and(Option::is_some)
    }

    /// Take `domain` where no thread holds it. A thread that finds it held marks it contended
    /// and tries once more, so a holder that released it in between is not missed: either this
    /// try takes it, or the holder saw the mark and woke the claimants.
    fn try_hold(&self, domain: usize) -> bool {
        let take = || {
            self.busy[domain]
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
        };
        if take() {
            return true;
        }
        self.contended[domain].store(true, Ordering::SeqCst);
        take()
    }

    /// Release `domain`, and wake the claimants where a thread found it held: it skipped the
    /// domain, or the coordinator waits to take it.
    fn release(&self, dispatcher: &Dispatcher, domain: usize) {
        self.busy[domain].store(false, Ordering::SeqCst);
        if self.contended[domain].swap(false, Ordering::SeqCst) {
            dispatcher.wake_claimants();
        }
    }

    /// Take every exclusion domain for the run's control: source starts, range landings, the
    /// resume pass, live polling and the stall check. No serial claim runs until the guard drops;
    /// partitioned claims go on. The coordinator alone takes it, so no two threads wait for each
    /// other's domains.
    pub(super) fn control<'a>(&'a self, dispatcher: &'a Dispatcher) -> Control<'a> {
        self.controlling.store(true, Ordering::SeqCst);
        let mut control = Control {
            pool: self,
            dispatcher,
            held: 0,
        };
        while control.held < self.domains.len() {
            let generation = dispatcher.generation();
            if self.try_hold(control.held) {
                control.held += 1;
            } else if dispatcher.has_failed() {
                // A failed run's claims stop, and a holder that panicked never releases.
                break;
            } else {
                dispatcher.wait(generation);
            }
        }
        control
    }

    /// Claim and run the next package or finish: a package of a partitioned pipeline, with no
    /// domain held, then serial work of the first exclusion domain that has some and that this
    /// thread takes. [`Claimed::Wait`] answers a generation taken before either claim, so a wait
    /// on it misses nothing that became claimable since, nor a domain released since.
    pub(super) fn run_next(
        &self,
        dispatcher: &Dispatcher,
        execution: &Execution,
        reach: &mut Reach<'_>,
        preferred: &mut Option<PipelineId>,
        #[cfg_attr(not(test), allow(unused_variables))] worker: usize,
    ) -> Claimed {
        let generation =
            match dispatcher.try_claim_where(*preferred, &|p| self.partitioned(p), &|_| false) {
                Next::Package(package) => {
                    *preferred = Some(package.pipeline);
                    #[cfg(test)]
                    self.count_claim(dispatcher, &package, worker);
                    self.consume(dispatcher, package);
                    return Claimed::Ran;
                }
                Next::Wait(generation) => generation,
                Next::Done => return Claimed::Done,
                Next::Failed => return Claimed::Failed,
                Next::Finish { .. } => unreachable!("a claim without finishes answers none"),
            };
        if self.controlling.load(Ordering::SeqCst) {
            // The control's release advances the generation.
            return Claimed::Wait(generation);
        }
        for (domain, pipelines) in self.domains.iter().enumerate() {
            if !dispatcher.may_hand_out(pipelines) || !self.try_hold(domain) {
                continue;
            }
            let ran = match dispatcher.try_claim_where(
                None,
                &|p| self.domain_of[p.0] == domain && !self.partitioned(p),
                &|p| self.domain_of[p.0] == domain,
            ) {
                Next::Package(package) => {
                    execution.consume(dispatcher, reach, package);
                    Claimed::Ran
                }
                Next::Finish { pipeline, consumed } => {
                    self.finishing(pipeline, reach);
                    execution.finish(dispatcher, reach, pipeline, consumed);
                    Claimed::Ran
                }
                Next::Wait(_) => {
                    self.release(dispatcher, domain);
                    continue;
                }
                Next::Done => Claimed::Done,
                Next::Failed => Claimed::Failed,
            };
            self.release(dispatcher, domain);
            // The coordinator, deciding under its control whether the run is stalled, sees this
            // claim's progress in the generation.
            dispatcher.wake_claimants();
            return ran;
        }
        Claimed::Wait(generation)
    }

    /// Start the workers in `scope`. Each claims until the run is done, has failed, or its claims
    /// are stopped, and reaches breakers through `root` as the coordinator does.
    /// [`join`](Self::join) takes the handles.
    pub(super) fn spawn<'scope, 'env>(
        &'env self,
        scope: &'scope Scope<'scope, 'env>,
        dispatcher: &'env Dispatcher,
        execution: &'env Execution,
        root: &'env SharedReach<'env>,
    ) -> Vec<ScopedJoinHandle<'scope, ()>> {
        if !self.threaded() {
            return Vec::new();
        }
        // A thread the system refuses leaves the run with the workers it has. Panicking instead
        // would leave the workers already started asleep, and the scope waiting for them.
        let mut handles = Vec::new();
        for worker in 0..self.count - 1 {
            match thread::Builder::new().spawn_scoped(scope, move || {
                self.work(dispatcher, execution, root, worker)
            }) {
                Ok(handle) => handles.push(handle),
                Err(_) => break,
            }
        }
        if handles.is_empty() {
            self.unstarted.store(true, Ordering::SeqCst);
        }
        handles
    }

    /// One worker's claims: every package and every finish, until the run ends.
    fn work(
        &self,
        dispatcher: &Dispatcher,
        execution: &Execution,
        root: &SharedReach<'_>,
        worker: usize,
    ) {
        in_a_run(|| {
            // A panic fails the run, so no claimant waits for what this worker held.
            let _worker = dispatcher.worker();
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                execution.reach(pipeline, root, call);
            };
            let mut preferred = None;
            loop {
                match self.run_next(dispatcher, execution, &mut reach, &mut preferred, worker) {
                    Claimed::Ran => {}
                    Claimed::Wait(generation) => dispatcher.wait(generation),
                    Claimed::Done | Claimed::Failed => return,
                }
            }
        });
    }

    /// Consume `package` under the breaker's handle held shared, publish the pipeline under it
    /// held exclusively, land the pushes with no handle held, and acknowledge the package.
    fn consume(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        let pipeline = package.pipeline;
        let spec = self.specs[pipeline.0]
            .as_ref()
            .expect("a claim outside an exclusion domain is of a partitioned pipeline");
        let target = &spec.target;
        {
            let breaker = target.read().unwrap_or_else(PoisonError::into_inner);
            debug_assert!(
                package
                    .guard
                    .check_from(&breaker.input_tiling(InputId::ONLY)),
                "pipeline {} consumes a guard of the tiling its breaker's input answers: {:?}",
                pipeline.0,
                package.guard
            );
            breaker.consume_impl(InputId::ONLY, package.guard.clone());
        }
        // Exclusive, so the push sees no consume between the merge of its rows and the release of
        // its input, which the readers it wakes rely on. A breaker that publishes only at its
        // finish or in the resume pass pushes nothing here, as in serial work
        // (`consume_with`).
        let pushes = {
            let breaker = target.write().unwrap_or_else(PoisonError::into_inner);
            breaker
                .as_producer()
                .filter(|producer| producer.pushes_while_consuming())
                .map(|producer| {
                    let mut pushes = dispatcher.pushes(pipeline);
                    pushes.push_final(producer);
                    pushes
                })
        };
        if let Some(pushes) = pushes {
            dispatcher.land(pushes);
        }
        // Before the acknowledgement that can leave the body quiescent: the round's step waits
        // for the coordinator to publish what this consume left held, as it does after a claim
        // of its own (`Execution::consume`).
        if let Some(body) = &spec.body {
            dispatcher.hold_followers(body.iter().copied(), true);
        }
        dispatcher.acknowledge(package);
        // An acknowledgement advances the generation only where it frees or completes a queue; a
        // coordinator asleep because this package was in flight wakes to see it acknowledged.
        dispatcher.wake_claimants();
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

    /// The index [`run_next`](Self::run_next) counts the coordinator's claims under, after the
    /// worker threads'.
    pub(super) fn coordinator(&self) -> usize {
        self.count - 1
    }

    /// Whether a package of a partitioned pipeline is in flight or claimable: the coordinator,
    /// finding nothing to claim, waits for it rather than deciding the run is stalled. Asked
    /// under [`control`](Self::control), where no serial claim is running, it misses no running
    /// claim; one that ends wakes the claimants ([`consume`](Self::consume)).
    pub(super) fn may_progress(&self, dispatcher: &Dispatcher, _control: &Control<'_>) -> bool {
        self.threaded()
            && !self.unstarted.load(Ordering::SeqCst)
            && dispatcher.may_claim_where(&|pipeline| self.partitioned(pipeline))
    }

    pub(super) fn start_source(
        &self,
        dispatcher: &Dispatcher,
        p: PipelineId,
        input: &Tiling,
        released: &TileGuard,
    ) {
        if self
            .specs
            .get(p.0)
            .and_then(Option::as_ref)
            .is_some_and(|s| s.level == CurryLevel::new(1))
        {
            let Tiling::DataFunction { codomain, .. } = input else {
                unreachable!("a source admitted at level 1 reads a collection")
            };
            let guards = seed(codomain, dispatcher.morsel_rows)
                .into_iter()
                .map(|g| {
                    let TileGuard::Function(FunctionGuard::Domain(keys)) = g else {
                        unreachable!("a seed of a collection's keys is a domain guard")
                    };
                    guard_minus(
                        &Projection::keys_at(CurryLevel::new(1), keys).guard(input),
                        released,
                    )
                })
                .filter(|g| !g.is_empty())
                .collect::<Vec<_>>();
            dispatcher.append_to_source(p, &guards);
            dispatcher.close(p);
        } else {
            dispatcher.start_source(p, input, released);
        }
    }

    /// Before a partitioned pipeline finishes, release its input whole.
    pub(super) fn finishing(&self, p: PipelineId, reach: &mut Reach<'_>) {
        if self.specs.get(p.0).is_some_and(Option::is_some) {
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

/// The coordinator's hold of every exclusion domain ([`WorkerPool::control`]). Dropping it
/// releases them and lets serial claims start again.
pub(super) struct Control<'a> {
    pool: &'a WorkerPool,
    dispatcher: &'a Dispatcher,
    /// The domains taken, from the first: every one, unless the run failed while it waited.
    held: usize,
}

impl Drop for Control<'_> {
    fn drop(&mut self) {
        let pool = self.pool;
        pool.controlling.store(false, Ordering::SeqCst);
        for domain in 0..self.held {
            pool.busy[domain].store(false, Ordering::SeqCst);
            pool.contended[domain].store(false, Ordering::SeqCst);
        }
        // A claimant that found the run under control waits on a generation from before.
        self.dispatcher.wake_claimants();
    }
}

/// The run's pipelines partitioned into exclusion domains: at most one claim of a domain's serial
/// work runs at a time, and the domains' serial work runs concurrently. A domain holds the
/// pipelines whose serial claims share state no other lock orders: a scope's request, step and
/// body, the scopes of one store, and a pipeline queued reads again with every pipeline it reads.
/// See `src/interpreter/design-dispatcher.md`, "Exclusion domains".
pub(super) struct ExclusionDomains {
    /// Per pipeline, its domain, numbered from 0.
    domain_of: Vec<usize>,
    count: usize,
}

impl ExclusionDomains {
    /// `pipelines` domains of one pipeline each, which [`join`](Self::join) merges.
    pub(super) fn singletons(pipelines: usize) -> Joining {
        Joining {
            parent: (0..pipelines).collect(),
        }
    }
}

/// [`ExclusionDomains`] while planning merges them: a union-find over the pipelines.
pub(super) struct Joining {
    parent: Vec<usize>,
}

impl Joining {
    fn root(&mut self, mut pipeline: usize) -> usize {
        while self.parent[pipeline] != pipeline {
            self.parent[pipeline] = self.parent[self.parent[pipeline]];
            pipeline = self.parent[pipeline];
        }
        pipeline
    }

    /// Put `a` and `b` in one domain.
    pub(super) fn join(&mut self, a: usize, b: usize) {
        let (a, b) = (self.root(a), self.root(b));
        self.parent[a.max(b)] = a.min(b);
    }

    pub(super) fn done(mut self) -> ExclusionDomains {
        let mut number = vec![usize::MAX; self.parent.len()];
        let mut count = 0;
        let domain_of = (0..self.parent.len())
            .map(|pipeline| {
                let root = self.root(pipeline);
                if number[root] == usize::MAX {
                    number[root] = count;
                    count += 1;
                }
                number[root]
            })
            .collect();
        ExclusionDomains { domain_of, count }
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
    /// answers at one: its body runs as serial work, and its source's packages are partitioned.
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

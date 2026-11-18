//! Shared native breaker execution. The dispatcher owns claims and completion accounting.
use super::*;
use crate::interpreter::CurryLevel;
#[cfg(test)]
use std::collections::HashSet;
use std::sync::atomic::AtomicBool;
use std::sync::mpsc;

struct Completion {
    worker: usize,
    /// The claims the worker consumed, or `None` where it stopped before consuming them all
    /// because another worker panicked.
    result: thread::Result<Option<Vec<WorkPackage>>>,
}
enum Job {
    Consume(Vec<WorkPackage>),
    Stop,
}
/// A thread of the pool and the channel its claims reach it on. Distinct from
/// [`super::Worker`], a thread that claims from the dispatcher itself.
struct WorkerThread {
    jobs: mpsc::Sender<Job>,
    thread: Option<thread::JoinHandle<()>>,
    idle: bool,
}
struct Spec {
    target: BreakerHandle,
    level: CurryLevel,
}
/// What each pipeline's claims did on the pool, for the tests below ([`WorkerPool::report`]).
#[cfg(test)]
#[derive(Default)]
struct Stats {
    claims: usize,
    used: HashSet<usize>,
    incremental: usize,
}
pub(super) struct WorkerPool {
    workers: Vec<WorkerThread>,
    completions: mpsc::Receiver<Completion>,
    specs: Vec<Option<Spec>>,
    #[cfg(test)]
    stats: Vec<Stats>,
    busy: usize,
    pending: Option<Next>,
    preferred: Option<PipelineId>,
}
impl WorkerPool {
    pub(super) fn new(count: usize, targets: Vec<Option<BreakerHandle>>) -> Self {
        assert!(count > 0, "a run has at least one worker");
        let specs: Vec<_> = targets
            .into_iter()
            .map(|target| {
                let target = target?;
                let level = target
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .parallel_level()?;
                Some(Spec { target, level })
            })
            .collect();
        let (outgoing, completions) = mpsc::channel();
        let mut workers = Vec::new();
        // One worker is the coordinator: it consumes every claim itself, on no other thread.
        if count > 1 && specs.iter().any(Option::is_some) {
            // Set by the worker that panics. The state it was integrating into is half updated,
            // so the others consume no further claim against it.
            let stop = Arc::new(AtomicBool::new(false));
            for worker in 0..count {
                let stop = stop.clone();
                let targets: Vec<_> = specs
                    .iter()
                    .map(|s| s.as_ref().map(|s| s.target.clone()))
                    .collect();
                let outgoing = outgoing.clone();
                let (jobs, incoming) = mpsc::channel();
                let thread = thread::spawn(move || {
                    while let Ok(Job::Consume(claims)) = incoming.recv() {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            in_a_run(|| {
                                let target = targets[claims[0].pipeline.0]
                                    .as_ref()
                                    .expect("an admitted pipeline");
                                for claim in &claims {
                                    if stop.load(Ordering::SeqCst) {
                                        return None;
                                    }
                                    // Held for one claim: the coordinator's push of another
                                    // worker's completion takes the breaker exclusively, and
                                    // waits for a claim rather than for the batch.
                                    target
                                        .read()
                                        .unwrap_or_else(PoisonError::into_inner)
                                        .consume_impl(InputId::ONLY, claim.guard.clone());
                                }
                                Some(claims)
                            })
                        }));
                        let failed = result.is_err();
                        if failed {
                            stop.store(true, Ordering::SeqCst);
                        }
                        if outgoing.send(Completion { worker, result }).is_err() || failed {
                            break;
                        }
                    }
                });
                workers.push(WorkerThread {
                    jobs,
                    thread: Some(thread),
                    idle: true,
                });
            }
        }
        Self {
            #[cfg(test)]
            stats: (0..specs.len()).map(|_| Stats::default()).collect(),
            specs,
            workers,
            completions,
            busy: 0,
            pending: None,
            preferred: None,
        }
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
                unreachable!()
            };
            let guards = seed(codomain, dispatcher.morsel_rows)
                .into_iter()
                .map(|g| {
                    let TileGuard::Function(FunctionGuard::Domain(keys)) = g else {
                        unreachable!()
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
    pub(super) fn next(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> Next {
        while let Ok(completion) = self.completions.try_recv() {
            self.complete(dispatcher, reach, completion);
        }
        self.pending
            .take()
            .unwrap_or_else(|| dispatcher.try_claim(self.preferred.take()))
    }
    pub(super) fn submit(
        &mut self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        package: WorkPackage,
    ) -> Result<(), WorkPackage> {
        if self.workers.is_empty()
            || self
                .specs
                .get(package.pipeline.0)
                .is_none_or(Option::is_none)
        {
            return Err(package);
        }
        while self.workers.iter().all(|w| !w.idle) {
            self.wait(dispatcher, reach);
        }
        let pipeline = package.pipeline;
        let mut claims = vec![package];
        // Bound the batch so completed work becomes visible before upstream closure.
        if self.pending.is_none() {
            while claims.len() < 4 {
                match dispatcher.try_claim(Some(pipeline)) {
                    Next::Package(p) if p.pipeline.0 == pipeline.0 => claims.push(p),
                    next @ (Next::Package(_) | Next::Finish { .. }) => {
                        self.pending = Some(next);
                        break;
                    }
                    _ => break,
                }
            }
        }
        #[cfg(test)]
        if dispatcher.infos[pipeline.0]
            .reads
            .iter()
            .any(|p| dispatcher.states[*p].phase.load() != Phase::Finished)
        {
            self.stats[pipeline.0].incremental += claims.len();
        }
        let worker = self
            .workers
            .iter_mut()
            .find(|w| w.idle)
            .expect("a free worker");
        worker.idle = false;
        self.busy += 1;
        worker
            .jobs
            .send(Job::Consume(claims))
            .expect("a worker accepts its claim");
        Ok(())
    }
    pub(super) fn wait(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        if self.busy == 0 {
            return false;
        }
        let completion = self.completions.recv().expect("an active worker answers");
        self.complete(dispatcher, reach, completion);
        true
    }
    fn complete(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>, completion: Completion) {
        self.workers[completion.worker].idle = true;
        self.busy -= 1;
        let fail = |failure| -> ! {
            dispatcher.fail();
            std::panic::resume_unwind(failure)
        };
        let claims = match completion.result {
            Ok(Some(claims)) => claims,
            // A worker stops only after another has panicked, and that one answers with its
            // panic. The claims this one left stay in flight: the run ends with them.
            Ok(None) => loop {
                let failed = self
                    .completions
                    .recv()
                    .expect("the worker that panicked answers");
                if let Err(failure) = failed.result {
                    fail(failure)
                }
            },
            Err(failure) => fail(failure),
        };
        let p = claims[0].pipeline;
        #[cfg(test)]
        {
            self.stats[p.0].claims += claims.len();
            self.stats[p.0].used.insert(completion.worker);
        }
        // The push reaches the breaker exclusively, so it sees no claim between the merge of its
        // rows and the release of its input, which the readers it wakes rely on.
        push_held(dispatcher, reach, [p]);
        for claim in claims {
            dispatcher.acknowledge(claim);
        }
        self.preferred = Some(PipelineId((p.0 + 1) % dispatcher.infos.len()));
    }
    pub(super) fn finishing(&mut self, p: PipelineId, reach: &mut Reach<'_>) {
        if self.specs.get(p.0).is_some_and(Option::is_some) {
            reach(p, &mut |breaker, _| breaker.finish_parallel_input());
        }
    }
    #[cfg(test)]
    pub(super) fn report(&self, planned: &mut [Planned]) {
        for (p, planned) in planned.iter_mut().enumerate() {
            planned.worker_claims = self.stats[p].claims;
            planned.workers_used = self.stats[p].used.len();
            planned.incremental_claims = self.stats[p].incremental;
        }
    }
}
impl Drop for WorkerThread {
    fn drop(&mut self) {
        let _ = self.jobs.send(Job::Stop);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}
impl Drop for WorkerPool {
    fn drop(&mut self) {
        // Every active reader exits before the run returns its operator graph.
        for worker in &self.workers {
            let _ = worker.jobs.send(Job::Stop);
        }
        self.workers.clear();
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

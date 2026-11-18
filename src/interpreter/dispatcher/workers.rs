//! Shared native breaker execution. The dispatcher owns claims and completion accounting.
use super::*;
use crate::interpreter::CurryLevel;
use std::collections::HashSet;
use std::sync::mpsc;

struct Completion {
    worker: usize,
    result: thread::Result<Vec<WorkPackage>>,
}
enum Job {
    Consume(Vec<WorkPackage>),
    Stop,
}
struct Worker {
    jobs: mpsc::Sender<Job>,
    thread: Option<thread::JoinHandle<()>>,
    idle: bool,
}
struct Spec {
    target: BreakerHandle,
    level: CurryLevel,
}
#[derive(Default)]
struct Stats {
    claims: usize,
    used: HashSet<usize>,
    incremental: usize,
}
pub(super) struct WorkerPool {
    workers: Vec<Worker>,
    completions: mpsc::Receiver<Completion>,
    specs: Vec<Option<Spec>>,
    stats: Vec<Stats>,
    busy: usize,
    pending: Option<Next>,
    preferred: Option<PipelineId>,
}
impl WorkerPool {
    pub(super) fn new(
        count: usize,
        targets: Vec<Option<BreakerHandle>>,
        dispatcher: &mut Dispatcher,
        reach: &mut Reach<'_>,
    ) -> Self {
        assert!(count > 0, "a run has at least one worker");
        // Checked arithmetic and order-sensitive control retain dependency order.
        let mut ordered = Vec::new();
        for p in 0..targets.len() {
            reach(PipelineId(p), &mut |breaker, _| {
                if breaker.requires_ordered_input() {
                    ordered.push(p);
                }
            });
        }
        let mut seen = HashSet::new();
        while let Some(p) = ordered.pop() {
            if seen.insert(p) {
                dispatcher.order(PipelineId(p));
                ordered.extend(dispatcher.infos[p].reads.iter().copied());
            }
        }
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
        if specs.iter().any(Option::is_some) {
            for worker in 0..count {
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
                                let target = target.read().unwrap_or_else(PoisonError::into_inner);
                                for claim in &claims {
                                    target.consume_impl(InputId::ONLY, claim.guard.clone());
                                }
                                claims
                            })
                        }));
                        let failed = result.is_err();
                        if outgoing.send(Completion { worker, result }).is_err() || failed {
                            break;
                        }
                    }
                });
                workers.push(Worker {
                    jobs,
                    thread: Some(thread),
                    idle: true,
                });
            }
        }
        Self {
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
        if self
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
        let claims = completion.result.unwrap_or_else(|failure| {
            dispatcher.fail();
            std::panic::resume_unwind(failure)
        });
        let p = claims[0].pipeline;
        self.stats[p.0].claims += claims.len();
        self.stats[p.0].used.insert(completion.worker);
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
    pub(super) fn report(&self, planned: &mut [Planned]) {
        for (p, planned) in planned.iter_mut().enumerate() {
            planned.worker_claims = self.stats[p].claims;
            planned.workers_used = self.stats[p].used.len();
            planned.incremental_claims = self.stats[p].incremental;
        }
    }
}
impl Drop for Worker {
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
            let expected = evaluate(&source, 1)
                .main
                .map(crate::interpreter::sort_function_by_domain);
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
}

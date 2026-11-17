//! Worker execution for the production plan. The dispatcher remains the sole work queue;
//! workers own reusable subscriptions and integrate into the plan's native shared breakers.
use super::*;
use crate::ccl::provenance::NodeId;
use crate::interpreter::tile_operators::pipeline_worker::PipelineWorker;
use crate::interpreter::tile_operators::{SinkBreaker, TileOperator, WorkerPlan};
use crate::interpreter::{CurryLevel, SubscribeContext};
use std::collections::{HashMap, HashSet};
use std::sync::mpsc;

#[derive(Clone)]
pub(super) enum Target {
    Chain(BreakerHandle),
    Sink(Arc<RwLock<SinkBreaker>>),
}
impl Target {
    fn apply(&self, delta: crate::interpreter::tile_operators::WorkerDelta) {
        match self {
            Self::Chain(handle) => handle.write().apply_worker(delta),
            Self::Sink(handle) => handle.write().apply_worker(delta),
        }
    }
}
struct Spec {
    plan: WorkerPlan,
    target: Target,
    level: CurryLevel,
    pinned: bool,
}
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
pub(super) struct WorkerPool {
    workers: Vec<Worker>,
    completions: mpsc::Receiver<Completion>,
    specs: Vec<Option<Spec>>,
    next: Option<Next>,
    preferred: Option<PipelineId>,
    busy: usize,
    stats: Vec<Stats>,
}
#[derive(Default)]
struct Stats {
    claims: usize,
    flushes: usize,
    used: HashSet<usize>,
    incremental: usize,
}

fn partitions(
    op: &dyn TileOperator,
    level: CurryLevel,
    boundaries: &HashSet<NodeId>,
    visiting: &mut HashSet<NodeId>,
) -> bool {
    if op.operator_id().is_some_and(|id| boundaries.contains(&id)) {
        return true;
    }
    if !op.partitions_at(level) {
        return false;
    }
    if let Some(id) = op.operator_id() {
        if !visiting.insert(id) {
            return false;
        }
    }
    let mut supported = true;
    let input_level = op.partition_input_level(level);
    op.visit_inputs(&mut |input| {
        supported &= partitions(input.target, input_level, boundaries, visiting);
    });
    if let Some(id) = op.operator_id() {
        visiting.remove(&id);
    }
    supported
}

impl WorkerPool {
    pub(super) fn new(
        count: usize,
        targets: Vec<Option<Target>>,
        bindings: HashMap<NodeId, BreakerHandle>,
    ) -> Self {
        assert!(count > 0, "a run has at least one worker");
        let boundaries: HashSet<_> = bindings.keys().copied().collect();
        let mut specs: Vec<_> = targets.into_iter().map(|target| {
            let target = target?;
            let plan = match &target {
                Target::Chain(handle) => handle.read().worker_plan(),
                Target::Sink(handle) => handle.read().worker_plan(),
            }?;
            let shape = plan.input.tiling();
            let inner = !matches!(shape.domain_extent(), Some(Extent::UIntRange(_)))
                && matches!(shape, Tiling::DataFunction { codomain, .. }
                    if matches!(&**codomain, Tiling::DataFunction { domain: Extent::UIntRange(_), .. }));
            // Materialized nested collections retain native whole-row execution.
            // Only grouped folds have a delta protocol for inner-position claims.
            if inner && !matches!(plan.fold,
                crate::interpreter::tile_operators::pipeline_worker::WorkerFold::Groups { .. }) {
                return None;
            }
            let level = if inner { CurryLevel::new(1) } else { CurryLevel::OUTERMOST };
            partitions(&*plan.input, level, &boundaries, &mut HashSet::new())
                .then_some(Spec { plan, target, level, pinned: false })
        }).collect();
        let (completion_tx, completions) = mpsc::channel();
        let mut workers = Vec::new();
        if specs.iter().any(Option::is_some) {
            for worker in 0..count {
                // Register every subscription before admitting work. No worker constructs
                // graph wiring or readers while another executes it.
                let mut states: Vec<_> = specs
                    .iter()
                    .map(|spec| {
                        spec.as_ref().map(|spec| {
                            let mut context = SubscribeContext::new();
                            context.breakers = bindings.clone();
                            (
                                PipelineWorker::new(&spec.plan, context),
                                spec.target.clone(),
                            )
                        })
                    })
                    .collect();
                let (jobs, incoming) = mpsc::channel();
                let outgoing = completion_tx.clone();
                let thread = thread::spawn(move || {
                    while let Ok(Job::Consume(claims)) = incoming.recv() {
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            in_a_run(|| {
                                let (state, target) = states[claims[0].pipeline.0]
                                    .as_mut()
                                    .expect("only admitted pipelines execute on workers");
                                let delta =
                                    state.execute(claims.iter().map(|claim| claim.guard.clone()));
                                target.apply(delta);
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
        for spec in specs.iter_mut().flatten() {
            if let Target::Chain(handle) = &spec.target {
                handle.write().pin_worker_inputs();
                spec.pinned = true;
            }
        }
        let stats = (0..specs.len()).map(|_| Stats::default()).collect();
        Self {
            workers,
            completions,
            specs,
            next: None,
            preferred: None,
            busy: 0,
            stats,
        }
    }

    pub(super) fn configure(&self, dispatcher: &mut Dispatcher) {
        for (p, spec) in self.specs.iter().enumerate() {
            if let Some(Spec {
                target: Target::Sink(sink),
                ..
            }) = spec
            {
                if sink.read().may_reorder() {
                    dispatcher.infos[p].ordered = false;
                }
            }
        }
    }
    pub(super) fn finishing(&mut self, pipeline: PipelineId, reach: &mut Reach<'_>) {
        if let Some(Some(spec)) = self.specs.get_mut(pipeline.0) {
            if spec.pinned {
                if let Target::Chain(handle) = &spec.target {
                    handle.write().unpin_worker_inputs();
                }
                spec.pinned = false;
            }
            reach(pipeline, &mut |breaker, _| breaker.finish_worker_input());
        }
    }
    pub(super) fn report(&self, planned: &mut [Planned]) {
        for (p, planned) in planned.iter_mut().enumerate() {
            planned.worker_claims = self.stats[p].claims;
            planned.workers_used = self.stats[p].used.len();
            planned.delta_flushes = self.stats[p].flushes;
            planned.incremental_claims = self.stats[p].incremental;
            planned.worker_instances = if self.specs[p].is_some() {
                self.workers.len()
            } else {
                0
            };
        }
    }

    pub(super) fn start_source(
        &self,
        dispatcher: &Dispatcher,
        pipeline: PipelineId,
        input: &Tiling,
        released: &TileGuard,
    ) {
        if self
            .specs
            .get(pipeline.0)
            .and_then(Option::as_ref)
            .is_some_and(|spec| spec.level == CurryLevel::new(1))
        {
            let Tiling::DataFunction { codomain, .. } = input else {
                unreachable!()
            };
            let guards = seed(codomain, dispatcher.morsel_rows)
                .into_iter()
                .map(|guard| {
                    let TileGuard::Function(FunctionGuard::Domain(keys)) = guard else {
                        unreachable!()
                    };
                    let guard = Projection::keys_at(CurryLevel::new(1), keys).guard(input);
                    guard_minus(&guard, released)
                })
                .filter(|guard| !guard.is_empty())
                .collect::<Vec<_>>();
            dispatcher.append_to_source(pipeline, &guards);
            dispatcher.close(pipeline);
        } else {
            dispatcher.start_source(pipeline, input, released);
        }
    }

    pub(super) fn next(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> Next {
        while let Ok(completion) = self.completions.try_recv() {
            self.complete(dispatcher, reach, completion);
        }
        self.next
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
        while self.workers.iter().all(|worker| !worker.idle) {
            self.wait(dispatcher, reach);
        }
        let pipeline = package.pipeline;
        let mut claims = vec![package];
        // A bounded batch reuses the worker's group map over several claims and publishes
        // its delta promptly. Ordered pipelines naturally admit just one claim.
        if self.next.is_none() {
            while claims.len() < 4 {
                match dispatcher.try_claim(Some(pipeline)) {
                    Next::Package(package) if package.pipeline.0 == pipeline.0 => {
                        claims.push(package)
                    }
                    other @ (Next::Package(_) | Next::Finish { .. }) => {
                        self.next = Some(other);
                        break;
                    }
                    _ => break,
                }
            }
        }
        if dispatcher.infos[pipeline.0]
            .reads
            .iter()
            .any(|read| dispatcher.states[*read].phase.load() != Phase::Finished)
        {
            self.stats[pipeline.0].incremental += claims.len();
        }
        let worker = self.workers.iter_mut().find(|worker| worker.idle).unwrap();
        worker.idle = false;
        self.busy += 1;
        worker
            .jobs
            .send(Job::Consume(claims))
            .expect("workers remain alive until joined");
        Ok(())
    }
    pub(super) fn wait(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        if self.busy == 0 {
            return false;
        }
        let completion = self
            .completions
            .recv()
            .expect("an active worker answers its claim");
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
        let pipeline = claims[0].pipeline;
        self.stats[pipeline.0].claims += claims.len();
        self.stats[pipeline.0].flushes += 1;
        self.stats[pipeline.0].used.insert(completion.worker);
        // Workers integrated their contributions under the shared breaker's lock.
        // Publication and acknowledgement stay in the control plane.
        push_held(dispatcher, reach, [pipeline]);
        for claim in claims {
            dispatcher.acknowledge(claim);
        }
        self.preferred = Some(PipelineId((pipeline.0 + 1) % dispatcher.infos.len()));
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
        for worker in &self.workers {
            let _ = worker.jobs.send(Job::Stop);
        }
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                let _ = thread.join();
            }
        }
        for spec in self.specs.iter_mut().flatten() {
            if spec.pinned {
                if let Target::Chain(handle) = &spec.target {
                    handle.write().unpin_worker_inputs();
                }
                spec.pinned = false;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::BaseType;
    use crate::interpreter::dispatcher::run_program_with_workers;

    fn evaluate(source: &str, workers: usize) -> Run {
        let mut context = GlobalContext::default();
        let mut program =
            compile_program(&mut context, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        run_program_with_workers(&mut program, 1, workers).unwrap()
    }

    #[test]
    fn external_named_sink_delivery_retains_its_input_order() {
        let values = (0..128)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = format!(
            "out = test_sink()\nxs = [{values}]\nys = [x * 2 for x in xs]\nout << [y + 1 for y in ys]"
        );
        let run = |dop| {
            let mut context = GlobalContext::default();
            let sink = context.register_test_sink("out");
            let mut program =
                compile_program(&mut context, &LoadedProgram::test(&source), Box::new(|| {}))
                    .unwrap();
            run_program_with_workers(&mut program, 1, dop).unwrap();
            sink.value().unwrap()
        };
        let expected = run(1);
        for _ in 0..4 {
            assert_eq!(run(4), expected);
        }
    }

    #[test]
    fn live_main_delivery_retains_its_input_order_through_shared_breakers() {
        use crate::interpreter::TestDataSource;
        let run = |dop| {
            let mut context = GlobalContext::default();
            let source = TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            );
            source.write().add_data(
                &(0..128)
                    .map(|x| (Value::UInt(x), Value::Int(x as i64)))
                    .collect::<Vec<_>>(),
            );
            source.write().set_yield_predicate(Predicate::True);
            context.register_source(source);
            let mut program = compile_program(
                &mut context,
                &LoadedProgram::test(
                    "xs = source1()\nys = [x * 2 for x in xs]\n[y + 1 for y in ys]",
                ),
                Box::new(|| {}),
            )
            .unwrap();
            run_program_with_workers(&mut program, 1, dop).unwrap().main
        };
        let expected = run(1);
        for _ in 0..4 {
            assert_eq!(run(4), expected);
        }
    }

    #[test]
    fn restoring_position_order_preserves_deleted_rows() {
        use crate::interpreter::{ColumnValue, Tile};
        let mut tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 1]))),
            Predicate::True,
            [0].into_iter().collect(),
        );
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        crate::interpreter::tile_operators::order_positions(&mut tile, &tiling);
        tile.compact();
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            unreachable!()
        };
        assert_eq!(domain, ColumnValue::UInts(vec![0]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Ints(vec![1])));
    }

    #[test]
    fn native_shared_breakers_use_multiple_workers_and_publish_incrementally() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = format!("xs = [{values}]\nys = [x * 2 for x in xs]\n[y + 1 for y in ys]");
        let expected = evaluate(&source, 1).main;
        let run = evaluate(&source, 4);
        assert_eq!(run.main, expected);
        assert!(
            run.planned.iter().any(|p| p.workers_used > 1),
            "{:?}",
            run.planned
        );
        assert!(
            run.planned
                .iter()
                .any(|p| p.worker_claims > p.worker_instances * 4)
        );
        assert!(run.planned.iter().any(|p| p.incremental_claims > 0));
    }

    #[test]
    fn checked_sum_preserves_its_producing_dependency_order() {
        let source = format!(
            "xs = [-{}, 0, 0, 0, {}, 1, 0, 0]\nys = [x for x in xs]\nsum(ys)",
            i64::MAX,
            i64::MAX
        );
        let expected = evaluate(&source, 1).main;
        for workers in [2, 4] {
            assert_eq!(evaluate(&source, workers).main, expected);
        }
    }

    #[test]
    #[ignore = "manual benchmark; compilation is outside measured execution"]
    fn benchmark_unified_dispatcher() {
        let values = (0..4096)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        for (name, source) in [
            ("map", format!("xs = [{values}]\n[x * 3 + 1 for x in xs]")),
            (
                "groups",
                format!("max([max(g) for g in groupby([{values}], \\x -> x - (x // 64) * 64)])"),
            ),
        ] {
            let mut expected = None;
            for dop in [1, 2, 4] {
                let mut times = Vec::new();
                for _ in 0..3 {
                    let mut context = GlobalContext::default();
                    let mut program = compile_program(
                        &mut context,
                        &LoadedProgram::test(&source),
                        Box::new(|| {}),
                    )
                    .unwrap();
                    let start = std::time::Instant::now();
                    let run = run_program_with_workers(&mut program, 128, dop).unwrap();
                    times.push(start.elapsed().as_secs_f64() * 1000.0);
                    if let Some(expected) = &expected {
                        assert_eq!(&run.main, expected);
                    } else {
                        expected = Some(run.main);
                    }
                    eprintln!(
                        "{name} dop={dop} claims={} workers={} incremental={} flushes={}",
                        run.planned.iter().map(|p| p.worker_claims).sum::<usize>(),
                        run.planned
                            .iter()
                            .map(|p| p.workers_used)
                            .max()
                            .unwrap_or(0),
                        run.planned
                            .iter()
                            .map(|p| p.incremental_claims)
                            .sum::<usize>(),
                        run.planned.iter().map(|p| p.delta_flushes).sum::<usize>()
                    );
                }
                times.sort_by(f64::total_cmp);
                eprintln!("BENCH {name} dop={dop} median_ms={:.3}", times[1]);
            }
        }
    }

    #[test]
    fn compiled_native_programs_match_at_each_dop() {
        for source in [
            "1 + 2",
            "[x * 2 + 1 for x in [1, 2, 3, 4, 5, 6]]",
            "max([x * 2 for x in [1, 2, 3, 4]])",
            "xs = [1, 2, 3, 4, 5, 6]\n[x * 3 for x in xs if x > 2]",
            "[x * 2 for x in [1, 2, 3] if x > 10]",
            "[[7, 8] for x in [1, 2, 3]]",
            "(answer=7, rows=[1, 2, 3])",
            "max([max(g) for g in groupby([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], \\x -> x - (x // 3) * 3)])",
        ] {
            let expected = evaluate(source, 1).main;
            for workers in [2, 4] {
                assert_eq!(
                    evaluate(source, workers).main,
                    expected,
                    "{source}; DOP {workers}"
                );
            }
        }
    }
}

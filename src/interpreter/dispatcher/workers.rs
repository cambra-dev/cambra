//! Worker execution for the production plan. The dispatcher remains the sole work queue;
//! workers own reusable subscriptions and integrate into the plan's native shared breakers.
use super::*;
use crate::ccl::provenance::NodeId;
use crate::interpreter::CurryLevel;
#[cfg(test)]
use crate::interpreter::SubscribeContext;
use crate::interpreter::tile_operators::pipeline_worker::PipelineWorker;
use crate::interpreter::tile_operators::{InputReleases, SinkBreaker, TileOperator, WorkerPlan};
#[cfg(test)]
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::mpsc;

#[derive(Clone)]
pub(super) enum Target {
    Chain(BreakerHandle),
    Sink(Arc<RwLock<SinkBreaker>>),
}
impl Target {
    fn execute(
        &self,
        state: &mut PipelineWorker,
        guards: impl Iterator<Item = TileGuard>,
    ) -> InputReleases {
        match self {
            Self::Chain(handle) => state.execute(
                &*handle.read().unwrap_or_else(PoisonError::into_inner),
                guards,
            ),
            Self::Sink(handle) => state.execute(
                &*handle.read().unwrap_or_else(PoisonError::into_inner),
                guards,
            ),
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
    result: thread::Result<(Vec<WorkPackage>, InputReleases)>,
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
    if let Some(id) = op.operator_id()
        && !visiting.insert(id)
    {
        return false;
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
        boundaries: HashSet<NodeId>,
        graphs: &[crate::interpreter::operator_graph::OperatorGraph],
    ) -> Self {
        assert!(count > 0, "a run has at least one worker");
        let mut specs: Vec<_> = targets.into_iter().map(|target| {
            let target = target?;
            let plan = match &target {
                Target::Chain(handle) => handle.read().unwrap_or_else(PoisonError::into_inner).worker_plan(graphs),
                Target::Sink(handle) => handle.read().unwrap_or_else(PoisonError::into_inner).worker_plan(graphs),
            }?;
            let shape = plan.input.tiling();
            // Nested values retain the native whole-row publication contract.
            // They need a separate delta contract before materialization can be partitioned.
            let flat = match shape {
                Tiling::DataFunction { codomain, .. } => !codomain.holds_a_level(),
                _ => !shape.holds_a_level(),
            };
            if plan.whole_rows && !flat { return None; }

            let inner = !matches!(shape.domain_extent(), Some(Extent::UIntRange(_)))
                && matches!(shape, Tiling::DataFunction { codomain, .. }
                    if matches!(&**codomain, Tiling::DataFunction { domain: Extent::UIntRange(_), .. }));
            // Materialized nested collections retain native whole-row execution.
            // Only grouped folds have a delta protocol for inner-position claims.
            if inner && !plan.inner_positions {
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
                // Wire every worker's local state and shared breaker inputs before admitting work.
                let mut states: Vec<_> = specs
                    .iter()
                    .map(|spec| {
                        spec.as_ref()
                            .map(|spec| (PipelineWorker::new(&spec.plan), spec.target.clone()))
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
                                let released = target
                                    .execute(state, claims.iter().map(|claim| claim.guard.clone()));
                                (claims, released)
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
                handle
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .pin_worker_inputs();
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
                && sink
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .may_reorder()
            {
                dispatcher.infos[p].ordered = false;
            }
        }
    }
    pub(super) fn finishing(&mut self, pipeline: PipelineId, reach: &mut Reach<'_>) {
        if let Some(Some(spec)) = self.specs.get_mut(pipeline.0) {
            if std::mem::take(&mut spec.pinned)
                && let Target::Chain(handle) = &spec.target
            {
                handle
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .unpin_worker_inputs();
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
        let (claims, released) = completion.result.unwrap_or_else(|failure| {
            dispatcher.fail();
            std::panic::resume_unwind(failure)
        });
        let pipeline = claims[0].pipeline;
        self.stats[pipeline.0].claims += claims.len();
        self.stats[pipeline.0].flushes += 1;
        self.stats[pipeline.0].used.insert(completion.worker);
        // Native consume/flush published output before canonical reclamation and notification.
        reach(pipeline, &mut |breaker, _| {
            breaker.release_worker_input(released.clone())
        });
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
        let unwinding = thread::panicking();
        let mut failure = None;
        for spec in self.specs.iter_mut().flatten() {
            if std::mem::take(&mut spec.pinned)
                && let Target::Chain(handle) = &spec.target
            {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    handle
                        .write()
                        .unwrap_or_else(PoisonError::into_inner)
                        .unpin_worker_inputs();
                }));
                if failure.is_none() {
                    failure = result.err();
                }
            }
        }
        if !unwinding && let Some(failure) = failure {
            std::panic::resume_unwind(failure);
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
    fn a_blocked_transaction_retains_its_filter_inputs() {
        for filter in [
            "sum([z2 for z2 in [1, 2, 3] if z2 > r])",
            "sum([z2 * r for z2 in [1, 2, 3] if z2 > r])",
        ] {
            let source = format!(
                "out = test_sink()\npool: Mut(Int, Txn) := 100\nlog: Mut(Int, Txn) := 0\nfor r in [1, 2, 3]:\n    try:\n        with begin():\n            pool := pool - r\n            if {filter} > 2:\n                raise r\n        with begin():\n            log := log + r\n    except Int:\n        pass\nout << await_final(log)"
            );
            for dop in [1, 4] {
                let mut context = GlobalContext::default();
                let sink = context.register_test_sink("out");
                let mut program =
                    compile_program(&mut context, &LoadedProgram::test(&source), Box::new(|| {}))
                        .unwrap();
                run_program_with_workers(&mut program, 1, dop).unwrap();
                assert_eq!(
                    sink.value().unwrap(),
                    Value::Function(vec![crate::interpreter::FuncBinding {
                        input: Value::Unit,
                        output: Value::Int(3),
                    }])
                );
            }
        }
    }

    #[test]
    fn restoring_progress_registers_all_aliases_before_releasing_shared_input() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use crate::interpreter::tile_operators::{Constant, FanOut, MakeRecord, WorkerPlan};
        use crate::interpreter::{ColumnValue, Tile};
        let shape = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::True,
            Default::default(),
        );
        let fan = FanOut::new(Arc::new(Constant::collection(values, shape)));
        // MakeRecord subscribes its inputs in order: the released alias MUST be
        // first, so eager restoration would reclaim key 0 before sibling b exists.
        let op = Arc::new(MakeRecord::new_named(vec![
            ("a".into(), fan.slot()),
            ("b".into(), fan.slot()),
        ]));
        let mut canonical = op.clone().subscribe(
            op.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let Tiling::Record(fields) = op.tiling() else {
            unreachable!()
        };
        canonical.release(TileGuard::Record(HashMap::from([
            ("a".into(), keys_between(0, 0)),
            ("b".into(), fields["b"].empty_guard()),
        ])));
        let canonical = crate::interpreter::tile_operators::pipeline_worker::share_input(canonical);
        let plan = WorkerPlan::new(
            &*canonical,
            &[crate::interpreter::tile_operators::pipeline_worker::test_graph(op.clone())],
        )
        .unwrap();
        let mut worker = plan.reader();
        let mut tile = in_a_run(|| worker.get(op.tiling().universal_guard()));
        tile.compact();
        let Tile::Record { fields, .. } = tile else {
            unreachable!()
        };
        let Tile::DataFunction {
            domain, codomain, ..
        } = &fields["b"]
        else {
            unreachable!()
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![0, 1]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::Ints(vec![10, 20])));
    }

    #[test]
    fn repeated_subscriptions_of_one_definition_keep_distinct_progress() {
        use crate::interpreter::tile_operators::{Constant, FanOut, WorkerPlan, Zip};
        use crate::interpreter::{ColumnValue, Tile};
        for fan_slot in [false, true] {
            let shape = Tiling::data_function(
                Extent::uint_range(2),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            );
            let values = Tile::data_function(
                ColumnValue::UInts(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
                Predicate::True,
                Default::default(),
            );
            let constant: Arc<dyn TileOperator> = Arc::new(Constant::collection(values, shape));
            let input = if fan_slot {
                FanOut::new(constant).slot()
            } else {
                constant
            };
            let op = Arc::new(Zip::new_at(
                vec!["a".into(), "b".into()],
                vec![input.clone(), input],
                CurryLevel::new(1),
            ));
            let canonical = op.clone().subscribe(
                op.tiling().universal_guard(),
                Box::new(|| {}),
                &mut SubscribeContext::new(),
            );
            let canonical =
                crate::interpreter::tile_operators::pipeline_worker::share_input(canonical);
            assert!(
                WorkerPlan::new(
                    &*canonical,
                    &[crate::interpreter::tile_operators::pipeline_worker::test_graph(op.clone())]
                )
                .is_some(),
                "distinct subscriptions retain their own existing state, fan={fan_slot}"
            );
        }
    }

    #[test]
    fn partially_released_zip_history_stays_with_its_canonical_producer() {
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use crate::interpreter::tile_operators::{Constant, WorkerPlan, Zip};
        use crate::interpreter::{ColumnValue, Tile};
        let input = || {
            let shape = Tiling::data_function(
                Extent::uint_range(2),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            );
            Arc::new(Constant::collection(
                Tile::data_function(
                    ColumnValue::UInts(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
                    Predicate::True,
                    Default::default(),
                ),
                shape,
            )) as Arc<dyn TileOperator>
        };
        let op = Arc::new(Zip::new_at(
            vec!["a".into(), "b".into()],
            vec![input(), input()],
            CurryLevel::new(1),
        ));
        let mut canonical = op.clone().subscribe(
            op.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        in_a_run(|| {
            canonical.get(keys_between(0, 0));
        });
        let release = CurryLevel::new(1).wrap_guard(TileGuard::Record(HashMap::from([
            (
                "a".into(),
                TileGuard::Scalar(Predicate::qualified(
                    Predicate::point(Value::UInt(0)),
                    Predicate::True,
                )),
            ),
            ("b".into(), TileGuard::Scalar(Predicate::False)),
        ])));
        canonical.release(release);
        let mut canonical =
            crate::interpreter::tile_operators::pipeline_worker::share_input(canonical);
        assert!(
            WorkerPlan::new(
                &*canonical,
                &[crate::interpreter::tile_operators::pipeline_worker::test_graph(op.clone())]
            )
            .is_some()
        );
        let remaining = in_a_run(|| canonical.get(keys_between(0, 0)));
        let Tile::DataFunction {
            domain, codomain, ..
        } = remaining
        else {
            unreachable!()
        };
        assert_eq!(domain, ColumnValue::UInts(vec![0]));
        let Tile::Record { fields, .. } = *codomain else {
            unreachable!()
        };
        assert_eq!(fields["b"], Tile::Scalar(ColumnValue::Ints(vec![1])));
    }
    #[test]
    fn output_release_keeps_a_workers_function_operand_alive_until_its_reads_finish() {
        use crate::interpreter::operator_graph::{InputEdgeSpec, value};
        use crate::interpreter::tile_operators::{
            Constant, MapResult, Memo, OperatorBase, ProducerBase, TileProducer,
            impl_operator_base, impl_producer_base,
        };
        use crate::interpreter::{ColumnValue, Tile};
        struct PausingArgs {
            base: OperatorBase,
            input: Arc<dyn TileOperator>,
            entered: mpsc::Sender<()>,
            resume: Mutex<mpsc::Receiver<()>>,
        }
        impl TileOperator for PausingArgs {
            impl_operator_base!();
            fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
                visit(value("input", &*self.input));
            }
            fn partitions_at(&self, _: CurryLevel) -> bool {
                true
            }
            fn subscribe(
                self: Arc<Self>,
                guard: TileGuard,
                consumer: Box<dyn Consumer>,
                cx: &mut SubscribeContext,
            ) -> Box<dyn TileProducer> {
                Box::new(PausingProducer {
                    base: ProducerBase::new(
                        PausingProducer::alloc_id(),
                        self.tiling(),
                        self.clone(),
                        cx,
                    ),
                    input: self.input.clone().subscribe(guard, consumer, cx),
                    operator: self,
                    paused: AtomicBool::new(false),
                })
            }
        }
        struct PausingProducer {
            base: ProducerBase,
            input: Box<dyn TileProducer>,
            operator: Arc<PausingArgs>,
            paused: AtomicBool,
        }
        impl TileProducer for PausingProducer {
            impl_producer_base!();
            fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
                visit("input", &*self.input);
            }
            fn shared_execution(&self) -> bool {
                true
            }
            fn get_impl(
                &self,
                cx: &mut crate::interpreter::tile_operators::ExecutionContext,
                guard: TileGuard,
            ) -> Tile {
                let arguments = cx.get(&*self.input, guard);
                if !self.paused.swap(true, Ordering::SeqCst) {
                    self.operator.entered.send(()).unwrap();
                    self.operator
                        .resume
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .recv()
                        .unwrap();
                }
                arguments
            }
            fn release_impl(&mut self, guard: TileGuard) {
                self.input.release(guard);
            }
        }
        fn bindings(producer: &dyn TileProducer, out: &mut HashMap<NodeId, BreakerHandle>) {
            if let (Some(id), Some(handle)) = (
                producer.base().node_id,
                producer
                    .base()
                    .breaker_handle
                    .as_ref()
                    .and_then(std::sync::Weak::upgrade),
            ) {
                out.insert(id, handle);
            }
            producer.visit_input_producers(&mut |_, input| bindings(input, out));
        }
        let uints = Tiling::data_function(
            Extent::uint_range(1),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let ints = Tiling::data_function(
            Extent::uint_range(1),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let table = |values| {
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::Scalar(values)),
                Predicate::True,
                Default::default(),
            )
        };
        let function = Arc::new(Memo::new(Arc::new(Constant::collection(
            table(ColumnValue::Ints(vec![10])),
            ints,
        ))));
        let function_id = function.operator_id().unwrap();
        let (entered_tx, entered_rx) = mpsc::channel();
        let (resume_tx, resume_rx) = mpsc::channel();
        let arguments = Arc::new(PausingArgs {
            base: OperatorBase::new(uints.clone()),
            input: Arc::new(Constant::collection(
                table(ColumnValue::UInts(vec![0])),
                uints,
            )),
            entered: entered_tx,
            resume: Mutex::new(resume_rx),
        });
        let output = Arc::new(Memo::new(Arc::new(MapResult::new_at(
            arguments,
            function,
            CurryLevel::new(1),
        ))));
        let output_id = output.operator_id().unwrap();
        let graphs =
            [crate::interpreter::tile_operators::pipeline_worker::test_graph(output.clone())];
        let reader = output.clone().subscribe(
            output.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let mut shared = HashMap::new();
        bindings(&*reader, &mut shared);
        let function = shared[&function_id].clone();
        let output = shared[&output_id].clone();
        in_a_run(|| {
            let mut function = function.write().unwrap_or_else(PoisonError::into_inner);
            let whole = function.input_tiling(InputId::ONLY).universal_guard();
            function.consume(InputId::ONLY, whole);
            function
                .base()
                .placement
                .as_ref()
                .unwrap()
                .set(Some(PipelineId(1)));
        });
        output
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .pin_worker_inputs();
        let plan = output
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .worker_plan(&graphs)
            .unwrap();
        let mut worker = PipelineWorker::new(&plan);
        let target = Target::Chain(output.clone());
        let guard = plan.input.tiling().universal_guard();
        let job =
            thread::spawn(move || in_a_run(|| target.execute(&mut worker, std::iter::once(guard))));
        entered_rx
            .recv_timeout(std::time::Duration::from_secs(5))
            .unwrap();
        let whole = output
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .tiling()
            .universal_guard();
        let releasing = output.clone();
        let release = thread::spawn(move || {
            releasing
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .release(whole);
        });
        // Shared claims exclude canonical mutation until their input reads finish.
        assert!(output.try_write().is_err());
        assert!(
            function
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .obsolete_guard()
                .is_empty()
        );
        resume_tx.send(()).unwrap();
        let released = job
            .join()
            .expect("the function remains available after arguments are read");
        release
            .join()
            .expect("output release follows the active shared claim");
        output
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release_worker_input(released);
        output
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .unpin_worker_inputs();
        assert!(
            function
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .obsolete_guard()
                .is_universal()
        );
    }

    #[test]
    fn deferred_release_panics_do_not_repeat_unpin_or_abort_unwind() {
        use crate::interpreter::Tile;
        use crate::interpreter::tile_operators::{
            Constant, MemoProducer, ProducerBase, TileProducer, impl_producer_base,
        };
        use std::sync::atomic::{AtomicUsize, Ordering};
        struct FailingRelease {
            base: ProducerBase,
            calls: Arc<AtomicUsize>,
        }
        impl TileProducer for FailingRelease {
            impl_producer_base!();
            fn get_exclusive_impl(&mut self, _: TileGuard) -> Tile {
                self.tiling().empty_tile()
            }
            fn release_impl(&mut self, _: TileGuard) {
                self.calls.fetch_add(1, Ordering::SeqCst);
                panic!("injected release failure");
            }
        }
        for unwinding in [false, true] {
            let calls = Arc::new(AtomicUsize::new(0));
            let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
            let mut base = ProducerBase::unowned(0, &tiling);
            base.definition = Some(Arc::new(Constant::new(
                Value::Int(1),
                Extent::Base(BaseType::Int),
            )));
            let graphs = [
                crate::interpreter::tile_operators::pipeline_worker::test_graph(
                    base.definition.as_ref().unwrap().clone(),
                ),
            ];
            let target: BreakerHandle = Arc::new(RwLock::new(MemoProducer::over(
                Box::new(FailingRelease {
                    base,
                    calls: calls.clone(),
                }),
                &tiling,
            )));
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut pool = WorkerPool::new(
                    1,
                    vec![Some(Target::Chain(target.clone()))],
                    HashSet::new(),
                    &graphs,
                );
                target
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .release(tiling.universal_guard());
                if unwinding {
                    panic!("original worker failure");
                }
                pool.finishing(PipelineId(0), &mut |_, call| {
                    call(
                        &mut *target.write().unwrap_or_else(PoisonError::into_inner),
                        InputId::ONLY,
                    )
                });
            }));
            let error = result.expect_err("the original failure propagates");
            assert_eq!(
                error.downcast_ref::<&str>().copied(),
                Some(if unwinding {
                    "original worker failure"
                } else {
                    "injected release failure"
                })
            );
            assert_eq!(calls.load(Ordering::SeqCst), 1);
        }
    }

    #[test]
    fn worker_probe_readings_survive_the_pool_and_retire_with_the_canonical_subscription() {
        use crate::interpreter::operator_graph::GraphNode;
        let mut context = GlobalContext::default();
        let mut program = compile_program(
            &mut context,
            &LoadedProgram::test("xs = [1, 2, 3, 4, 5, 6, 7, 8]\n[x * 2 for x in xs]"),
            Box::new(|| {}),
        )
        .unwrap();
        drop(context.take_operator_map());
        context.subscribe_context().probes().enable();
        let operators = program
            .operator_graph
            .nodes()
            .iter()
            .filter_map(|node| match node {
                GraphNode::Operator {
                    id,
                    kind: "MapResult",
                    ..
                } => Some(*id),
                _ => None,
            })
            .collect::<HashSet<_>>();
        assert!(!operators.is_empty());
        let run = run_program_with_workers(&mut program, 1, 4).unwrap();
        assert!(run.planned.iter().any(|p| p.worker_claims > 0));
        let probed = context
            .subscribe_context()
            .probes()
            .with_table(|table| {
                table
                    .probe_keys()
                    .filter_map(|(node, _)| node)
                    .collect::<HashSet<_>>()
            })
            .unwrap();
        assert!(
            operators.iter().all(|node| probed.contains(node)),
            "{operators:?} vs {probed:?}"
        );
        drop(program);
        let retained = context
            .subscribe_context()
            .probes()
            .with_table(|table| {
                table
                    .probe_keys()
                    .filter_map(|(node, _)| node)
                    .collect::<HashSet<_>>()
            })
            .unwrap();
        assert!(
            operators.is_disjoint(&retained),
            "retired subscriptions left probes behind"
        );
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
            source
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .add_data(
                    &(0..128)
                        .map(|x| (Value::UInt(x), Value::Int(x as i64)))
                        .collect::<Vec<_>>(),
                );
            source
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .set_yield_predicate(Predicate::True);
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
    fn compiled_native_programs_match_at_each_dop() {
        for source in [
            "1 + 2",
            "[x * 2 + 1 for x in [1, 2, 3, 4, 5, 6]]",
            "max([x * 2 for x in [1, 2, 3, 4]])",
            "xs = [1, 2, 3, 4, 5, 6]\n[x * 3 for x in xs if x > 2]",
            "[x * 2 for x in [1, 2, 3] if x > 10]",
            "[[7, 8] for x in [1, 2, 3]]",
            "(answer=7, rows=[1, 2, 3])",
            "[x + y for x in ['a', 'b'] for y in ['c', 'd', 'e']]",
            "a = [1, 2]; b = [10, 20]; [(x, y) for x in a for y in b]",
            "x = [1, 2]; y = x ++ x ++ x; y",
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

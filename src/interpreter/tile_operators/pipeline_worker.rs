//! Shared canonical pipeline inputs and execution-local read progress.
use super::*;
use std::collections::HashSet;

pub(crate) type SharedInputHandle = Arc<RwLock<Box<dyn TileProducer>>>;

#[derive(Default)]
struct ReadProgress {
    released: Option<TileGuard>,
    last: Option<Tile>,
}

/// Per-execution cursors, validation snapshots and releases awaiting output integration.
#[doc(hidden)]
#[derive(Default)]
pub struct ExecutionContext {
    worker: bool,
    progress: HashMap<usize, ReadProgress>,
    pending: HashMap<usize, TileGuard>,
}
fn address<P: TileProducer + ?Sized>(producer: &P) -> usize {
    std::ptr::from_ref(producer).cast::<()>() as usize
}
impl ExecutionContext {
    pub(crate) fn obsolete<P: TileProducer + ?Sized>(&self, producer: &P) -> TileGuard {
        self.progress
            .get(&address(producer))
            .and_then(|p| p.released.as_ref())
            .map_or_else(
                || producer.obsolete_guard().clone(),
                |released| producer.obsolete_guard().union(released),
            )
    }
    pub(crate) fn get<P: TileProducer + ?Sized>(&mut self, producer: &P, guard: TileGuard) -> Tile {
        #[cfg(debug_assertions)]
        let _pull = {
            pull_levels::check_input_level(
                pull_levels::address_of(producer),
                || producer.name(),
                &guard,
            );
            pull_levels::PullFrame::enter(producer, &guard)
        };
        let projection = Projection::of(&guard).ok();
        if let Some(level) = projection.as_ref().and_then(Projection::level) {
            assert!(
                !producer.restates().refuses(level),
                "{} cannot restate {level}",
                producer.name()
            );
        }
        let mut result = producer.get_impl(self, guard);
        let obsolete = self.obsolete(producer);
        result.remove_guarded(obsolete.clone());
        assert!(
            result.check_from(producer.tiling()),
            "{} produced a tile outside its tiling",
            producer.name()
        );
        debug_assert!(validate_tile(&result));
        if let Some(projection) = &projection {
            debug_assert!(result.within_over(projection, producer.tiling()).is_ok());
        }
        let progress = self.progress.entry(address(producer)).or_default();
        if cfg!(debug_assertions) {
            if let Some(last) = &progress.last {
                let mut last = last.clone();
                if let Some(projection) = &projection {
                    last.restrict_to(projection, producer.tiling());
                }
                assert!(
                    completeness_violation(&producer.name(), &last, &result, &obsolete).is_none()
                );
            }
            progress.last = Some(match (&projection, progress.last.take()) {
                (Some(Projection::Nothing), Some(last)) => last,
                (Some(region @ Projection::Keys { .. }), Some(mut last)) => {
                    last.restrict_to(&Projection::Everything.minus(region), producer.tiling());
                    last.remove_guarded(obsolete.clone());
                    last.compact();
                    let mut answered = result.clone();
                    answered.restrict_to(region, producer.tiling());
                    last.merge(answered);
                    last
                }
                _ => result.clone(),
            });
        }
        let base = producer.base();
        base.probes.observe_named(
            base.node_id,
            base.id,
            || producer.name(),
            &result,
            &obsolete,
        );
        result
    }
    pub(crate) fn release<P: TileProducer + ?Sized>(&mut self, producer: &P, guard: TileGuard) {
        assert!(guard.check_from(producer.tiling()));
        let id = address(producer);
        let released = self
            .obsolete(producer)
            .union(&guard)
            .closed_over(producer.tiling());
        self.progress.entry(id).or_default().released = Some(released);
        self.pending
            .entry(id)
            .and_modify(|before| *before = before.union(&guard))
            .or_insert(guard);
    }
    pub(super) fn apply<P: TileProducer + ?Sized>(&mut self, producer: &mut P) {
        if !self.pending.is_empty() {
            apply_releases(producer, &std::mem::take(&mut self.pending));
        }
    }
}

/// Retention metadata only; workers have already integrated their output before reporting it.
#[doc(hidden)]
#[derive(Clone)]
pub struct InputReleases {
    pub(crate) guard: TileGuard,
    pub(super) nodes: HashMap<usize, TileGuard>,
}
pub(super) fn apply_releases<P: TileProducer + ?Sized>(
    producer: &mut P,
    releases: &HashMap<usize, TileGuard>,
) {
    fn walk<P: TileProducer + ?Sized>(
        producer: &mut P,
        releases: &HashMap<usize, TileGuard>,
        visited: &mut HashSet<usize>,
    ) {
        if !visited.insert(address(producer)) {
            return;
        }
        if let Some(guard) = releases.get(&address(producer)) {
            producer.release(guard.clone());
        }
        if producer.worker_breaker().is_none() {
            producer.visit_input_producers_mut(&mut |_, input| walk(input, releases, visited));
        }
    }
    walk(producer, releases, &mut Default::default());
}

/// Stateless supported operands are already safe to read through the containing shared chain.
/// Exclusive operands keep one cell for canonical execution; worker admission rejects them.
pub(crate) fn shared_operand(input: Box<dyn TileProducer>) -> Box<dyn TileProducer> {
    if input.shared_execution() {
        input
    } else {
        share_input(input)
    }
}

/// Retain the existing input chain once, shared by its canonical reader and every worker.
pub(crate) fn share_input(input: Box<dyn TileProducer>) -> Box<dyn TileProducer> {
    if input.shared_input().is_some() {
        return input;
    }
    let mut base = ProducerBase::unowned(SharedInput::alloc_id(), input.tiling());
    base.definition = input.base().definition.clone();
    base.obsolete_guard = input.obsolete_guard().clone();
    Box::new(SharedInput {
        base,
        input: Arc::new(RwLock::new(input)),
    })
}
struct SharedInput {
    base: ProducerBase,
    input: SharedInputHandle,
}
impl TileProducer for SharedInput {
    impl_producer_base!();
    fn shared_input(&self) -> Option<SharedInputHandle> {
        Some(self.input.clone())
    }
    fn shared_execution(&self) -> bool {
        true
    }
    fn get_impl(&self, cx: &mut ExecutionContext, guard: TileGuard) -> Tile {
        if self
            .input
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .shared_execution()
        {
            cx.get(
                &**self.input.read().unwrap_or_else(PoisonError::into_inner),
                guard,
            )
        } else {
            assert!(
                !cx.worker,
                "worker admission excludes exclusive input nodes"
            );
            self.input
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .get(guard)
        }
    }

    fn release_impl(&mut self, guard: TileGuard) {
        self.input
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release(guard);
    }
    fn restates(&self) -> Restates {
        self.input
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .restates()
    }
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit(
            "input",
            &**self.input.read().unwrap_or_else(PoisonError::into_inner),
        );
    }
    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit(
            "input",
            &mut **self.input.write().unwrap_or_else(PoisonError::into_inner),
        );
    }
    fn apply_input_releases(&mut self, releases: &InputReleases) {
        apply_releases(
            &mut **self.input.write().unwrap_or_else(PoisonError::into_inner),
            &releases.nodes,
        );
        self.release(releases.guard.clone());
    }
}

/// A reference to the existing input graph, never a recipe for constructing another chain.
#[doc(hidden)]
#[derive(Clone)]
pub struct WorkerPlan {
    pub(crate) input: Arc<dyn TileOperator>,
    pub(crate) whole_rows: bool,
    pub(crate) inner_positions: bool,
    shared: SharedInputHandle,
}
impl WorkerPlan {
    pub(crate) fn new(
        input: &dyn TileProducer,
        _graphs: &[crate::interpreter::operator_graph::OperatorGraph],
    ) -> Option<Self> {
        let shared = input.shared_input()?;
        fn supported(producer: &dyn TileProducer, visited: &mut HashSet<usize>) -> bool {
            if !visited.insert(address(producer)) {
                return true;
            }
            if producer.worker_breaker().is_some() {
                return true;
            }
            if !producer.shared_execution() {
                return false;
            }
            let mut yes = true;
            producer.visit_input_producers(&mut |_, input| yes &= supported(input, visited));
            yes
        }
        if !supported(
            &**shared.read().unwrap_or_else(PoisonError::into_inner),
            &mut Default::default(),
        ) {
            return None;
        }
        Some(Self {
            input: input.base().definition.clone()?,
            whole_rows: true,
            inner_positions: false,
            shared,
        })
    }
    #[cfg(test)]
    pub(crate) fn reader(&self) -> Box<dyn TileProducer> {
        let mut base = ProducerBase::unowned(InputReader::alloc_id(), self.input.tiling());
        base.obsolete_guard = self
            .shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .obsolete_guard()
            .clone();
        Box::new(InputReader {
            base,
            input: self.shared.clone(),
            cx: ExecutionContext {
                worker: true,
                ..Default::default()
            },
        })
    }
}

/// Mutable input execution state supplied to the existing shared breaker instance.
#[doc(hidden)]
pub struct ConsumeState<'a> {
    pub(super) input: &'a mut dyn TileProducer,
    pub(super) local: &'a mut Option<Box<dyn std::any::Any + Send + Sync>>,
    pub(super) worker: bool,
}
impl ConsumeState<'_> {
    pub(super) fn local<T: std::any::Any + Send + Sync>(
        &mut self,
        init: impl FnOnce() -> T,
    ) -> &mut T {
        self.local
            .get_or_insert_with(|| Box::new(init()))
            .downcast_mut()
            .expect("one pipeline retains one native consumer's local state")
    }
}

struct InputReader {
    base: ProducerBase,
    input: SharedInputHandle,
    cx: ExecutionContext,
}
impl TileProducer for InputReader {
    impl_producer_base!();
    fn get(&mut self, guard: TileGuard) -> Tile {
        self.cx.get(
            &**self.input.read().unwrap_or_else(PoisonError::into_inner),
            guard,
        )
    }
    fn get_impl(&self, _cx: &mut ExecutionContext, guard: TileGuard) -> Tile {
        self.get(guard)
    }
    fn release_impl(&mut self, guard: TileGuard) {
        self.cx.release(
            &**self.input.read().unwrap_or_else(PoisonError::into_inner),
            guard,
        );
    }
    fn restates(&self) -> Restates {
        self.input
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .restates()
    }
}
pub(crate) struct PipelineWorker {
    input: InputReader,
    local: Option<Box<dyn std::any::Any + Send + Sync>>,
}
impl PipelineWorker {
    pub(crate) fn new(plan: &WorkerPlan) -> Self {
        let mut base = ProducerBase::unowned(InputReader::alloc_id(), plan.input.tiling());
        base.obsolete_guard = plan
            .shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .obsolete_guard()
            .clone();
        Self {
            input: InputReader {
                base,
                input: plan.shared.clone(),
                cx: ExecutionContext {
                    worker: true,
                    ..Default::default()
                },
            },
            local: None,
        }
    }
    pub(crate) fn execute(
        &mut self,
        breaker: &dyn Breaker,
        guards: impl Iterator<Item = TileGuard>,
    ) -> InputReleases {
        let mut state = ConsumeState {
            input: &mut self.input,
            local: &mut self.local,
            worker: true,
        };
        for guard in guards {
            breaker.consume_impl(&mut state, InputId::ONLY, guard);
        }
        breaker.flush_worker(&mut state);
        InputReleases {
            guard: self.input.obsolete_guard().clone(),
            nodes: std::mem::take(&mut self.input.cx.pending),
        }
    }
}

#[cfg(test)]
pub(crate) fn test_graph(
    operator: Arc<dyn TileOperator>,
) -> crate::interpreter::operator_graph::OperatorGraph {
    crate::interpreter::operator_graph::BoundarySession::install()
        .into_graph(&[("main".into(), operator)])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::dispatcher::in_a_run;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Observed {
        base: OperatorBase,
        subscribed: AtomicUsize,
        reads: Arc<Mutex<HashSet<usize>>>,
        releases: Arc<AtomicUsize>,
    }
    impl TileOperator for Observed {
        impl_operator_base!();
        fn visit_inputs(&self, _: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn subscribe(
            self: Arc<Self>,
            _: TileGuard,
            _: Box<dyn Consumer>,
            cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            self.subscribed.fetch_add(1, Ordering::SeqCst);
            Box::new(ObservedProducer {
                base: ProducerBase::new(
                    ObservedProducer::alloc_id(),
                    self.tiling(),
                    self.clone(),
                    cx,
                ),
                reads: self.reads.clone(),
                releases: self.releases.clone(),
            })
        }
    }
    struct ObservedProducer {
        base: ProducerBase,
        reads: Arc<Mutex<HashSet<usize>>>,
        releases: Arc<AtomicUsize>,
    }
    impl TileProducer for ObservedProducer {
        impl_producer_base!();
        fn shared_execution(&self) -> bool {
            true
        }
        fn get_impl(&self, _: &mut ExecutionContext, _: TileGuard) -> Tile {
            self.reads.lock().unwrap().insert(address(self));
            Tile::Scalar(ColumnValue::Ints(vec![42]))
        }
        fn release_impl(&mut self, _: TileGuard) {
            self.releases.fetch_add(1, Ordering::SeqCst);
        }
    }
    fn source() -> (Arc<Observed>, Box<dyn TileProducer>) {
        let source = Arc::new(Observed {
            base: OperatorBase::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            subscribed: AtomicUsize::new(0),
            reads: Arc::new(Mutex::new(HashSet::new())),
            releases: Arc::new(AtomicUsize::new(0)),
        });
        let canonical = share_input(source.clone().subscribe(
            source.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        ));
        (source, canonical)
    }
    #[test]
    fn workers_read_the_same_subscribed_instance() {
        let (source, canonical) = source();
        let plan = WorkerPlan::new(&*canonical, &[]).unwrap();
        std::thread::scope(|scope| {
            for _ in 0..2 {
                let mut reader = plan.reader();
                let whole = source.tiling().universal_guard();
                scope.spawn(move || {
                    in_a_run(|| {
                        assert_eq!(reader.get(whole), Tile::Scalar(ColumnValue::Ints(vec![42])));
                    })
                });
            }
        });
        assert_eq!(source.subscribed.load(Ordering::SeqCst), 1);
        assert_eq!(source.reads.lock().unwrap().len(), 1);
    }
    #[test]
    fn worker_releases_wait_for_canonical_application() {
        let (source, mut canonical) = source();
        let plan = WorkerPlan::new(&*canonical, &[]).unwrap();
        let mut worker = PipelineWorker::new(&plan);
        let whole = source.tiling().universal_guard();
        in_a_run(|| {
            worker.input.get(whole.clone());
        });
        worker.input.release(whole);
        assert_eq!(source.releases.load(Ordering::SeqCst), 0);
        assert!(canonical.obsolete_guard().is_empty());
        canonical.apply_input_releases(&InputReleases {
            guard: worker.input.obsolete_guard().clone(),
            nodes: std::mem::take(&mut worker.input.cx.pending),
        });
        assert_eq!(source.releases.load(Ordering::SeqCst), 1);
        assert!(canonical.obsolete_guard().is_universal());
    }
}

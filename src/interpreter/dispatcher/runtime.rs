//! Transferable descriptions of finite pure operator chains. Runtime producers and construction
//! cells are created on their owning worker; only immutable descriptions and tile state cross it.

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use crate::ccl::AggregateKind;
use crate::ccl::provenance::NodeId;
use crate::interpreter::tile_operators::{
    MapAggregateKernel, MapAggregateState, OperatorBase, ProducerBase, TileOperator, TileProducer,
};
use crate::interpreter::types::BaseType;
use crate::interpreter::{Extent, Tile, TileGuard, Tiling};
use smol_str::SmolStr;

type BuildOperator = dyn Fn(&RuntimeBase, &RuntimeBuild) -> Box<dyn TileOperator> + Send + Sync;

/// Shared immutable configuration for one operator. Concrete native adapters drop after
/// subscription; inline fan-out owners retain input bridges.
pub struct RuntimeOperator {
    plan: Arc<OperatorPlan>,
    pub(crate) partitionable: bool,
    pub(crate) reads: Vec<usize>,
    pub(crate) region_reads: Vec<usize>,
    pub(crate) sources: Vec<Arc<RuntimeSource>>,
    pub(crate) region_sources: Vec<Arc<RuntimeSource>>,
    pub(crate) inner_partitionable: bool,
}
pub(crate) struct RuntimeSource {
    pub(crate) output: Arc<SharedOutput>,
    pub(crate) universal: TileGuard,
    pub(crate) empty: TileGuard,
}
struct OperatorPlan {
    base: RuntimeBase,
    correlation: Option<Vec<crate::interpreter::tile_operators::TilePathStep>>,
    build: Box<BuildOperator>,
}
impl RuntimeOperator {
    pub(crate) fn new(
        base: RuntimeBase,
        correlation: Option<Vec<crate::interpreter::tile_operators::TilePathStep>>,
        build: impl Fn(&RuntimeBase, &RuntimeBuild) -> Box<dyn TileOperator> + Send + Sync + 'static,
        partitionable: bool,
        reads: Vec<usize>,
    ) -> Self {
        Self {
            plan: Arc::new(OperatorPlan {
                base,
                correlation,
                build: Box::new(build),
            }),
            partitionable,
            reads,
            region_reads: Vec::new(),
            sources: Vec::new(),
            region_sources: Vec::new(),
            inner_partitionable: false,
        }
    }
    pub(crate) fn with_inner_partitions(mut self, supported: bool) -> Self {
        self.inner_partitionable = supported;
        self
    }
    pub(crate) fn with_sources(mut self, sources: Vec<Arc<RuntimeSource>>) -> Self {
        self.sources = sources;
        self
    }
    pub(crate) fn sources<'a>(
        inputs: impl IntoIterator<Item = &'a RuntimeOperator>,
    ) -> Vec<Arc<RuntimeSource>> {
        let mut sources = Vec::new();
        for input in inputs {
            for source in &input.sources {
                if !sources.iter().any(|other| Arc::ptr_eq(source, other)) {
                    sources.push(source.clone());
                }
            }
        }
        sources
    }
    pub(crate) fn with_region_sources(mut self, sources: Vec<Arc<RuntimeSource>>) -> Self {
        self.region_sources = sources;
        self
    }
    pub(crate) fn regional_sources<'a>(
        inputs: impl IntoIterator<Item = &'a RuntimeOperator>,
    ) -> Vec<Arc<RuntimeSource>> {
        let inputs: Vec<_> = inputs.into_iter().collect();
        let mut sources = Vec::new();
        for input in &inputs {
            for source in &input.region_sources {
                if !sources.iter().any(|other| Arc::ptr_eq(source, other)) {
                    sources.push(source.clone());
                }
            }
        }
        sources.retain(|source| {
            inputs.iter().all(|input| {
                !input.sources.iter().any(|other| Arc::ptr_eq(source, other))
                    || input
                        .region_sources
                        .iter()
                        .any(|other| Arc::ptr_eq(source, other))
            })
        });
        sources
    }
    pub(crate) fn with_regions(mut self, reads: Vec<usize>) -> Self {
        self.region_reads = reads;
        self
    }
    pub(crate) fn regions<'a>(inputs: impl IntoIterator<Item = &'a RuntimeOperator>) -> Vec<usize> {
        let inputs: Vec<_> = inputs.into_iter().collect();
        let mut regions: Vec<_> = inputs
            .iter()
            .flat_map(|input| input.region_reads.iter().copied())
            .collect();
        regions.sort_unstable();
        regions.dedup();
        regions.retain(|r| {
            inputs
                .iter()
                .all(|input| !input.reads.contains(r) || input.region_reads.contains(r))
        });
        regions
    }
    pub(crate) fn input(&self, context: &RuntimeBuild) -> Box<dyn TileOperator> {
        Box::new(RuntimeInput {
            plan: self.plan.clone(),
            build: Rc::downgrade(&context.0),
            base: self.plan.base.thaw(),
        })
    }
    pub(crate) fn dependencies<'a>(
        inputs: impl IntoIterator<Item = &'a RuntimeOperator>,
    ) -> Vec<usize> {
        let mut reads: Vec<_> = inputs
            .into_iter()
            .flat_map(|input| input.reads.iter().copied())
            .collect();
        reads.sort_unstable();
        reads.dedup();
        reads
    }
}
impl Clone for RuntimeOperator {
    fn clone(&self) -> Self {
        Self {
            plan: self.plan.clone(),
            partitionable: self.partitionable,
            reads: self.reads.clone(),
            region_reads: self.region_reads.clone(),
            sources: self.sources.clone(),
            region_sources: self.region_sources.clone(),
            inner_partitionable: self.inner_partitionable,
        }
    }
}

struct RuntimeInput {
    plan: Arc<OperatorPlan>,
    // Fan-out construction owners retain input adapters; a strong reference would form a cycle.
    build: std::rc::Weak<BuildState>,
    base: OperatorBase,
}
impl TileOperator for RuntimeInput {
    fn result_correlation(&self) -> Option<Vec<crate::interpreter::tile_operators::TilePathStep>> {
        self.plan.correlation.clone()
    }
    fn tiling(&self) -> &Tiling {
        &self.base.tiling
    }
    fn operator_id(&self) -> Option<NodeId> {
        Some(self.base.id)
    }
    fn visit_inputs(
        &self,
        _: &mut dyn FnMut(crate::interpreter::operator_graph::InputEdgeSpec<'_>),
    ) {
    }
    fn subscribe(
        &mut self,
        intent: TileGuard,
        consumer: Box<dyn crate::interpreter::Consumer>,
        cx: &mut crate::interpreter::SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let build = RuntimeBuild(
            self.build
                .upgrade()
                .expect("a pipeline owns its subscription state"),
        );
        let mut op = (self.plan.build)(&self.plan.base, &build);
        op.subscribe(intent, consumer, cx)
    }
}

/// Construction aliases retained by one pipeline's worker state. Adapters hold weak references.
#[derive(Default)]
pub(crate) struct RuntimeBuild(Rc<BuildState>);
#[derive(Default)]
struct BuildState {
    inline: std::cell::RefCell<HashMap<NodeId, Rc<crate::interpreter::tile_operators::FanOut>>>,
}

/// Private execution state for one worker and one run. Shared plans contain no subscriptions.
#[derive(Default)]
pub(crate) struct WorkerContext {
    pipelines: HashMap<usize, PipelineState>,
}
struct PipelineState {
    input: Box<dyn TileProducer>,
    // Fan-out subscription owners must outlive the producers that reference them.
    _build: RuntimeBuild,
    aggregate: Option<LocalAggregate>,
}
struct LocalAggregate {
    plan: Arc<RuntimeAggregate>,
    state: MapAggregateState,
    shape: Tiling,
}
impl WorkerContext {
    pub(crate) fn consume(
        &mut self,
        pipeline: usize,
        plan: &RuntimeOperator,
        guard: TileGuard,
        output: &SharedOutput,
    ) -> bool {
        let mut initialized = false;
        let state = self.pipelines.entry(pipeline).or_insert_with(|| {
            let build = RuntimeBuild::default();
            let mut op = plan.input(&build);
            let mut cx = crate::interpreter::SubscribeContext::new();
            let input = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut cx);
            initialized = true;
            PipelineState {
                input,
                _build: build,
                aggregate: None,
            }
        });
        let tile = state.input.get(guard);
        let released = tile.to_guard();
        output.apply(tile);
        state.input.release(released);
        initialized
    }
    pub(crate) fn accumulate(
        &mut self,
        pipeline: usize,
        plan: &RuntimeOperator,
        guard: TileGuard,
        aggregate: &Arc<RuntimeAggregate>,
    ) -> bool {
        let mut initialized = false;
        let state = self.pipelines.entry(pipeline).or_insert_with(|| {
            let build = RuntimeBuild::default();
            let mut op = plan.input(&build);
            let input = op.subscribe(
                op.tiling().universal_guard(),
                Box::new(|| {}),
                &mut crate::interpreter::SubscribeContext::new(),
            );
            initialized = true;
            PipelineState {
                input,
                _build: build,
                aggregate: Some(LocalAggregate {
                    plan: aggregate.clone(),
                    state: MapAggregateState::new(aggregate.kernel.clone()),
                    shape: aggregate.group_shape.thaw(),
                }),
            }
        });
        let mut tile = state.input.get(guard);
        let released = tile.to_guard();
        // Native folds consume only live rows; keep the full statement for input release.
        tile.compact();
        let local = state
            .aggregate
            .as_mut()
            .expect("aggregate state belongs to this pipeline");
        let tile = aggregate.wrap(tile);
        local.state.apply(&tile, &local.shape);
        state.input.release(released);
        initialized
    }
    pub(crate) fn flush(&mut self, pipeline: usize, output: &SharedOutput) {
        let state = self
            .pipelines
            .get_mut(&pipeline)
            .expect("a flush has an owning worker");
        let local = state
            .aggregate
            .as_mut()
            .expect("only aggregate state buffers contributions");
        output.apply_delta(local.state.drain(), &local.plan, &local.shape);
    }
    pub(crate) fn finish(&mut self, pipeline: usize) {
        if let Some(mut state) = self.pipelines.remove(&pipeline) {
            if let Some(local) = &state.aggregate {
                assert!(
                    local.state.is_drained(),
                    "finish cannot discard buffered aggregate contributions"
                );
            }
            state.input.release(state.input.tiling().universal_guard());
        }
    }
}

/// One run's operator identities and pipeline descriptions. Breakers export shared held state;
/// inline fan-outs export construction aliases private to each pipeline instance.
#[derive(Default)]
pub struct RuntimeContext {
    shared: HashMap<NodeId, RuntimeOperator>,
    pub(crate) pipelines: Vec<RuntimePipeline>,
}
pub(crate) struct RuntimePipeline {
    pub(crate) input: RuntimeOperator,
    pub(crate) output: Arc<SharedOutput>,
    pub(crate) tiling: Tiling,
    pub(crate) input_tiling: Tiling,
    pub(crate) aggregate: Option<Arc<RuntimeAggregate>>,
}

pub(crate) struct RuntimeAggregate {
    kernel: Arc<MapAggregateKernel>,
    group_shape: Arc<RuntimeTiling>,
    scalar: bool,
    pub(crate) inner_partition: bool,
}
impl RuntimeAggregate {
    fn wrap(&self, tile: Tile) -> Tile {
        if !self.scalar {
            return tile;
        }
        Tile::data_function(
            crate::interpreter::ColumnValue::Units(1),
            Box::new(tile),
            crate::interpreter::Predicate::True,
            Default::default(),
        )
    }
    fn unwrap(&self, tile: Tile) -> Tile {
        if !self.scalar {
            return tile;
        }
        let Tile::DataFunction { codomain, .. } = tile else {
            unreachable!("scalar folds use one synthetic group")
        };
        *codomain
    }
}
impl RuntimePipeline {
    pub(crate) fn seeds(&self, morsel_rows: usize) -> Vec<TileGuard> {
        let guards = if self
            .aggregate
            .as_ref()
            .is_some_and(|agg| agg.inner_partition)
        {
            let Tiling::DataFunction { codomain, .. } = &self.input_tiling else {
                unreachable!()
            };
            let Tiling::DataFunction { domain, .. } = &**codomain else {
                unreachable!()
            };
            let frame =
                Tiling::data_function(domain.clone(), Tiling::Scalar(Extent::Base(BaseType::Unit)));
            super::seed(&frame, morsel_rows)
                .into_iter()
                .map(|guard| {
                    let TileGuard::Function(crate::interpreter::FunctionGuard::Domain(keys)) =
                        guard
                    else {
                        unreachable!()
                    };
                    crate::interpreter::Projection::keys_at(
                        crate::interpreter::CurryLevel::new(1),
                        keys,
                    )
                    .guard(&self.input_tiling)
                })
                .collect()
        } else if self.input.partitionable {
            super::seed(&self.input_tiling, morsel_rows)
        } else {
            vec![self.input_tiling.universal_guard()]
        };
        if guards.is_empty() && self.aggregate.is_some() {
            vec![self.input_tiling.universal_guard()]
        } else {
            guards
        }
    }
    pub(crate) fn reads_regions(&self) -> bool {
        self.aggregate.is_some()
            || matches!(
                self.input_tiling.domain_extent(),
                Some(Extent::UIntRange(_))
            )
    }
    pub(crate) fn publishes_regions(&self) -> bool {
        self.input.partitionable
            && self.tiling.is_data_function()
            && !self
                .aggregate
                .as_ref()
                .is_some_and(|agg| agg.inner_partition)
    }
}

impl RuntimeContext {
    pub(crate) fn get(&self, id: NodeId) -> Option<RuntimeOperator> {
        self.shared.get(&id).cloned()
    }
    pub(crate) fn memo(
        &mut self,
        op: &dyn TileOperator,
        input: impl FnOnce(&mut Self) -> Result<RuntimeOperator, String>,
    ) -> Result<RuntimeOperator, String> {
        let id = op.operator_id().ok_or("a memo has an operator identity")?;
        if let Some(reader) = self.shared.get(&id) {
            return Ok(reader.clone());
        }
        let input = input(self)?;
        self.materialize(op, input)
    }
    pub(crate) fn shared(&mut self, op: &dyn TileOperator) -> Result<RuntimeOperator, String> {
        let id = op
            .operator_id()
            .ok_or("a shared runtime input has an operator identity")?;
        if let Some(reader) = self.shared.get(&id) {
            return Ok(reader.clone());
        }
        let input = op.runtime_operator(self)?;
        if let Some(reader) = self.shared.get(&id) {
            return Ok(reader.clone());
        }
        let partitionable = input.partitionable;
        let reads = input.reads.clone();
        let regions = input.region_reads.clone();
        let sources = input.sources.clone();
        let region_sources = input.region_sources.clone();
        let inner = input.inner_partitionable;
        let base = RuntimeBase {
            id,
            tiling: RuntimeTiling::freeze(op.tiling())?,
        };
        let private = RuntimeOperator::new(
            base,
            op.result_correlation(),
            move |_base, build| {
                let existing = build.0.inline.borrow().get(&id).cloned();
                let fan = existing.unwrap_or_else(|| {
                    let op = input.input(build);
                    let fan = Rc::new(crate::interpreter::tile_operators::FanOut::new(op));
                    build.0.inline.borrow_mut().insert(id, fan.clone());
                    fan
                });
                fan.slot()
            },
            partitionable,
            reads,
        )
        .with_regions(regions)
        .with_sources(sources)
        .with_region_sources(region_sources)
        .with_inner_partitions(inner);
        self.shared.insert(id, private.clone());
        Ok(private)
    }

    pub(crate) fn materialize(
        &mut self,
        op: &dyn TileOperator,
        input: RuntimeOperator,
    ) -> Result<RuntimeOperator, String> {
        self.materialize_input(op, input, op.tiling(), None)
    }
    pub(crate) fn aggregate(
        &mut self,
        op: &dyn TileOperator,
        input: RuntimeOperator,
        input_tiling: &Tiling,
        kind: AggregateKind,
    ) -> Result<RuntimeOperator, String> {
        let scalar = matches!(op.tiling(), Tiling::Aggregation { .. });
        let shape = if scalar {
            Tiling::data_function(Extent::Base(BaseType::Unit), op.tiling().clone())
        } else {
            op.tiling().clone()
        };
        let inner_partition = !scalar
            && input.partitionable
            && input.inner_partitionable
            && !matches!(input_tiling.domain_extent(), Some(Extent::UIntRange(_)))
            && matches!(input_tiling, Tiling::DataFunction {codomain,..} if matches!(&**codomain,Tiling::DataFunction {domain:Extent::UIntRange(_),..}));
        let aggregate = Arc::new(RuntimeAggregate {
            kernel: Arc::new(MapAggregateKernel { kind }),
            group_shape: Arc::new(RuntimeTiling::freeze(&shape)?),
            scalar,
            inner_partition,
        });
        self.materialize_input(op, input, input_tiling, Some(aggregate))
    }
    fn materialize_input(
        &mut self,
        op: &dyn TileOperator,
        input: RuntimeOperator,
        input_tiling: &Tiling,
        aggregate: Option<Arc<RuntimeAggregate>>,
    ) -> Result<RuntimeOperator, String> {
        let id = op
            .operator_id()
            .ok_or("a breaker has an operator identity")?;
        let tiling = op.tiling();
        let correlation = op.result_correlation();
        let shape = RuntimeTiling::freeze(tiling)?;
        let output = Arc::new(SharedOutput::pending());
        let index = self.pipelines.len();
        debug_assert!(
            input.reads.iter().all(|read| *read < index),
            "runtime dependencies precede their reader"
        );
        self.pipelines.push(RuntimePipeline {
            input,
            output: output.clone(),
            tiling: tiling.clone(),
            input_tiling: input_tiling.clone(),
            aggregate,
        });
        let reader = RuntimeOperator::new(
            RuntimeBase { id, tiling: shape },
            correlation,
            move |base, _build| {
                Box::new(SharedReaderOperator {
                    output: output.clone(),
                    base: base.thaw(),
                })
            },
            true,
            vec![index],
        )
        .with_regions(vec![index])
        .with_inner_partitions(true);
        self.shared.insert(id, reader.clone());
        Ok(reader)
    }
    pub(crate) fn main(&mut self, input: RuntimeOperator, tiling: &Tiling) -> usize {
        let index = self.pipelines.len();
        self.pipelines.push(RuntimePipeline {
            input,
            output: Arc::new(SharedOutput::pending()),
            tiling: tiling.clone(),
            input_tiling: tiling.clone(),
            aggregate: None,
        });
        index
    }
}

/// Source-free shape metadata. Dynamic extents require a synchronized runtime source adapter.
pub(crate) enum RuntimeExtent {
    Base(BaseType),
    Function(Box<Self>, Box<Self>),
    Record(HashMap<SmolStr, Self>),
    Union(crate::ccl::TagMap<Self>),
    UIntRange(intervalsets::IntervalSet<u64>),
}
impl RuntimeExtent {
    pub(crate) fn freeze(e: &Extent) -> Result<Self, String> {
        Ok(match e {
            Extent::Base(t) => Self::Base(t.clone()),
            Extent::Function { domain, codomain } => Self::Function(
                Box::new(Self::freeze(domain)?),
                Box::new(Self::freeze(codomain)?),
            ),
            Extent::Record(fields) => Self::Record(
                fields
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), Self::freeze(v)?)))
                    .collect::<Result<_, String>>()?,
            ),
            Extent::Union(arms) => Self::Union(crate::ccl::TagMap::from_arms(
                arms.iter()
                    .map(|(k, e)| Ok((k.clone(), Self::freeze(e)?)))
                    .collect::<Result<_, String>>()?,
            )),
            Extent::UIntRange(range) => Self::UIntRange(range.clone()),
            Extent::DataSourceDomain(_) | Extent::Restricted { .. } => {
                return Err("parallel execution requires a finite source-free extent".into());
            }
        })
    }
    pub(crate) fn finite_iteration(&self) -> bool {
        use intervalsets::Bounding;
        match self {
            Self::Base(BaseType::Unit) => true,
            Self::UIntRange(range) => range
                .intervals()
                .iter()
                .all(|run| run.left().is_some() && run.right().is_some()),
            Self::Record(fields) => fields.values().all(Self::finite_iteration),
            Self::Union(arms) => arms.iter().all(|(_, e)| e.finite_iteration()),
            _ => false,
        }
    }
    pub(crate) fn thaw(&self) -> Extent {
        match self {
            Self::Base(t) => Extent::Base(t.clone()),
            Self::Function(d, c) => Extent::Function {
                domain: Box::new(d.thaw()),
                codomain: Box::new(c.thaw()),
            },
            Self::Record(fields) => {
                Extent::Record(fields.iter().map(|(k, v)| (k.clone(), v.thaw())).collect())
            }
            Self::Union(arms) => Extent::Union(arms.map(|_, e| e.thaw())),
            Self::UIntRange(range) => Extent::UIntRange(range.clone()),
        }
    }
}
pub(crate) enum RuntimeTiling {
    Scalar(RuntimeExtent),
    Record(HashMap<SmolStr, Self>),
    Function(RuntimeExtent, Box<Self>),
    Aggregation(AggregateKind, Box<Self>),
}
impl RuntimeTiling {
    pub(crate) fn freeze(t: &Tiling) -> Result<Self, String> {
        Ok(match t {
            Tiling::Scalar(e) => Self::Scalar(RuntimeExtent::freeze(e)?),
            Tiling::Record(fields) => Self::Record(
                fields
                    .iter()
                    .map(|(k, v)| Ok((k.clone(), Self::freeze(v)?)))
                    .collect::<Result<_, String>>()?,
            ),
            Tiling::DataFunction { domain, codomain } => Self::Function(
                RuntimeExtent::freeze(domain)?,
                Box::new(Self::freeze(codomain)?),
            ),
            Tiling::Aggregation { kind, accumulator } => {
                Self::Aggregation(*kind, Box::new(Self::freeze(accumulator)?))
            }
            Tiling::Store { .. } => return Err("parallel store execution is not enabled".into()),
        })
    }
    pub(crate) fn thaw(&self) -> Tiling {
        match self {
            Self::Scalar(e) => Tiling::Scalar(e.thaw()),
            Self::Record(fields) => {
                Tiling::Record(fields.iter().map(|(k, v)| (k.clone(), v.thaw())).collect())
            }
            Self::Function(domain, codomain) => {
                Tiling::data_function(domain.thaw(), codomain.thaw())
            }
            Self::Aggregation(kind, accumulator) => Tiling::Aggregation {
                kind: *kind,
                accumulator: Box::new(accumulator.thaw()),
            },
        }
    }
}
pub(crate) struct RuntimeBase {
    id: NodeId,
    tiling: RuntimeTiling,
}
impl RuntimeBase {
    pub(crate) fn freeze(base: &OperatorBase) -> Result<Self, String> {
        Ok(Self {
            id: base.id,
            tiling: RuntimeTiling::freeze(&base.tiling)?,
        })
    }
    pub(crate) fn thaw(&self) -> OperatorBase {
        OperatorBase {
            id: self.id,
            tiling: self.tiling.thaw(),
        }
    }
}

/// One immutable constant tile shared by all runtime instances. Each reader tracks its own exact
/// releases. Retention lasts until every worker and description has dropped its handle.
pub(crate) fn constant(
    tile: Tile,
    base: RuntimeBase,
    correlation: Option<Vec<crate::interpreter::tile_operators::TilePathStep>>,
) -> RuntimeOperator {
    let shape = base.tiling.thaw();
    let held = Arc::new(SharedOutput::source(tile));
    let source = Arc::new(RuntimeSource {
        output: held.clone(),
        universal: shape.universal_guard(),
        empty: shape.empty_guard(),
    });
    let region_sources = if shape.is_data_function() {
        vec![source.clone()]
    } else {
        Vec::new()
    };
    RuntimeOperator::new(
        base,
        correlation,
        move |base, _build| {
            Box::new(SharedReaderOperator {
                output: held.clone(),
                base: base.thaw(),
            })
        },
        true,
        Vec::new(),
    )
    .with_sources(vec![source])
    .with_region_sources(region_sources)
    .with_inner_partitions(true)
}

// Callers establish sorted root UInt keys once when immutable or completed state is installed.
fn indexed_tile(tile: &Tile, guard: &TileGuard) -> Option<Tile> {
    let (
        Tile::DataFunction {
            domain: crate::interpreter::ColumnValue::UInts(keys),
            codomain,
            domain_predicate,
            absent_keys,
            ..
        },
        TileGuard::Function(crate::interpreter::FunctionGuard::Domain(
            crate::interpreter::Predicate::Intervals(region),
        )),
    ) = (tile, guard)
    else {
        return None;
    };
    use intervalsets::Bounding;
    let selected: Option<Vec<_>> = region
        .intervals()
        .iter()
        .map(|run| {
            let first = match run.left() {
                None => 0,
                Some(bound) => {
                    let crate::interpreter::Value::UInt(value) = bound.value() else {
                        return None;
                    };
                    keys.partition_point(|key| {
                        if bound.is_closed() {
                            key < value
                        } else {
                            key <= value
                        }
                    })
                }
            };
            let last = match run.right() {
                None => keys.len(),
                Some(bound) => {
                    let crate::interpreter::Value::UInt(value) = bound.value() else {
                        return None;
                    };
                    keys.partition_point(|key| {
                        if bound.is_closed() {
                            key <= value
                        } else {
                            key < value
                        }
                    })
                }
            };
            Some((first..last).collect::<Vec<_>>())
        })
        .collect();
    let rows: Vec<_> = selected?.into_iter().flatten().collect();
    Some(Tile::DataFunction {
        row_starts: vec![0],
        domain: crate::interpreter::ColumnValue::UInts(rows.iter().map(|i| keys[*i]).collect()),
        codomain: Box::new(codomain.select_rows(&rows)),
        domain_predicate: domain_predicate
            .intersect(&crate::interpreter::Predicate::Intervals(region.clone())),
        deleted: Default::default(),
        absent_keys: absent_keys.clone(),
    })
}
/// One breaker's held values and completion are protected by the same mutex. Finite execution
/// retains this data until all pipelines and their private reader instances have drained.
pub(crate) struct SharedOutput(Mutex<Held>);
struct Held {
    tile: Option<Tile>,
    finished: bool,
    indexed: bool,
    readers: HashMap<usize, TileGuard>,
    obsolete: Option<TileGuard>,
    started: bool,
    aggregate: Option<(MapAggregateState, Arc<RuntimeAggregate>)>,
}
impl SharedOutput {
    pub(crate) fn pending() -> Self {
        Self(Mutex::new(Held {
            tile: None,
            finished: false,
            indexed: false,
            readers: HashMap::new(),
            obsolete: None,
            started: false,
            aggregate: None,
        }))
    }
    fn source(tile: Tile) -> Self {
        let output = Self::pending();
        let mut held = output.0.lock().unwrap();
        held.indexed = matches!(&tile,Tile::DataFunction {row_starts,domain:crate::interpreter::ColumnValue::UInts(keys),deleted,..}
            if row_starts.as_slice()==[0] && deleted.is_empty() && keys.windows(2).all(|pair|pair[0]<pair[1]));
        held.tile = Some(tile);
        held.finished = true;
        drop(held);
        output
    }
    pub(crate) fn register(&self, reader: usize, empty: TileGuard) {
        let mut held = self.0.lock().unwrap();
        assert!(!held.started, "readers register before execution");
        held.readers.entry(reader).or_insert(empty);
    }
    pub(crate) fn release(&self, reader: usize, guard: &TileGuard) {
        let mut held = self.0.lock().unwrap();
        let released = held
            .readers
            .get_mut(&reader)
            .expect("a logical reader is registered");
        *released = released.union(guard);
        let agreed = held
            .readers
            .values()
            .cloned()
            .reduce(|a, b| a.intersect(&b))
            .unwrap();
        if let Some((state, _)) = &mut held.aggregate {
            state.release(&agreed);
        }
        if let Some(tile) = &mut held.tile {
            tile.remove_guarded(agreed.clone());
            tile.compact();
        }
        held.obsolete = Some(agreed);
    }
    pub(crate) fn apply(&self, mut tile: Tile) {
        let mut held = self.0.lock().unwrap();
        assert!(
            !held.finished,
            "a completed breaker receives no more contributions"
        );
        held.started = true;
        if let Some(obsolete) = &held.obsolete {
            tile.remove_guarded(obsolete.clone());
            tile.compact();
        }
        held.indexed = false;
        match held.tile.as_mut() {
            Some(previous) => previous.merge(tile),
            None => held.tile = Some(tile),
        }
    }
    fn apply_delta(
        &self,
        mut delta: MapAggregateState,
        plan: &Arc<RuntimeAggregate>,
        shape: &Tiling,
    ) {
        let mut held = self.0.lock().unwrap();
        assert!(!held.finished, "a completed aggregate receives no deltas");
        held.started = true;
        if let Some(obsolete) = &held.obsolete {
            delta.release(obsolete);
        }
        match &mut held.aggregate {
            Some((state, _)) => state.merge(delta),
            None => held.aggregate = Some((delta, plan.clone())),
        }
        let (state, plan) = held.aggregate.as_ref().unwrap();
        let mut tile = plan.unwrap(state.render(shape, !plan.scalar));
        if let Some(obsolete) = &held.obsolete {
            tile.remove_guarded(obsolete.clone());
        }
        held.tile = Some(tile);
        held.indexed = false;
    }
    pub(crate) fn finish(&self, tiling: &Tiling) {
        let mut held = self.0.lock().unwrap();
        assert!(!held.finished, "a shared breaker finishes once");
        if let Some((state, plan)) = &held.aggregate {
            held.tile = Some(plan.unwrap(state.render_finished(&plan.group_shape.thaw())));
        }
        let mut tile = held
            .tile
            .take()
            .unwrap_or_else(|| tiling.empty_tile())
            .closed_over(tiling);
        tile.compact();
        order_positions(&mut tile, tiling);
        held.indexed = matches!(&tile,Tile::DataFunction {row_starts,domain:crate::interpreter::ColumnValue::UInts(keys),deleted,..}
            if row_starts.as_slice()==[0] && deleted.is_empty() && keys.windows(2).all(|pair|pair[0]<pair[1]));
        held.tile = Some(tile);
        held.finished = true;
    }
    fn read(&self, guard: &TileGuard) -> Tile {
        let mut held = self.0.lock().unwrap();
        held.started = true;
        if held.indexed
            && let Some(tile) = indexed_tile(
                held.tile
                    .as_ref()
                    .expect("a completed breaker holds a tile"),
                guard,
            )
        {
            return tile;
        }
        held.tile
            .as_ref()
            .expect("a completed breaker holds a tile")
            .clone()
    }
    pub(crate) fn completed_groups(&self) -> Option<TileGuard> {
        let held = self.0.lock().unwrap();
        held.aggregate
            .as_ref()
            .filter(|(_, plan)| !plan.scalar)
            .map(|(state, _)| state.completed_roots())
    }
    pub(crate) fn is_finished(&self) -> bool {
        self.0.lock().unwrap().finished
    }
    pub(crate) fn snapshot(&self) -> Tile {
        let held = self.0.lock().unwrap();
        assert!(
            held.finished,
            "a scheduled reader observes a completed breaker"
        );
        held.tile
            .as_ref()
            .expect("a completed breaker holds a tile")
            .clone()
    }
}
fn order_positions(tile: &mut Tile, tiling: &Tiling) {
    match (tile, tiling) {
        (
            Tile::DataFunction {
                row_starts,
                domain: crate::interpreter::ColumnValue::UInts(keys),
                codomain,
                ..
            },
            Tiling::DataFunction {
                domain: Extent::UIntRange(_),
                codomain: inner,
            },
        ) => {
            let mut order = Vec::with_capacity(keys.len());
            for (row, &first) in row_starts.iter().enumerate() {
                let last = row_starts.get(row + 1).copied().unwrap_or(keys.len());
                let mut run: Vec<_> = (first..last).collect();
                run.sort_by_key(|i| keys[*i]);
                order.extend(run);
            }
            if order.iter().enumerate().any(|(i, j)| i != *j) {
                **codomain = codomain.select_rows(&order);
                *keys = order.iter().map(|i| keys[*i]).collect();
            }
            order_positions(codomain, inner);
        }
        (
            Tile::DataFunction { codomain, .. },
            Tiling::DataFunction {
                codomain: inner, ..
            },
        ) => order_positions(codomain, inner),
        (Tile::Record { fields, .. }, Tiling::Record(shapes)) => {
            for (name, field) in fields {
                order_positions(field, &shapes[name]);
            }
        }
        (
            Tile::Aggregation { accumulator, .. },
            Tiling::Aggregation {
                accumulator: shape, ..
            },
        ) => order_positions(accumulator, shape),
        _ => {}
    }
}

struct SharedReaderOperator {
    output: Arc<SharedOutput>,
    base: OperatorBase,
}
impl TileOperator for SharedReaderOperator {
    fn tiling(&self) -> &Tiling {
        &self.base.tiling
    }
    fn operator_id(&self) -> Option<NodeId> {
        Some(self.base.id)
    }
    fn visit_inputs(
        &self,
        _: &mut dyn FnMut(crate::interpreter::operator_graph::InputEdgeSpec<'_>),
    ) {
    }
    fn subscribe(
        &mut self,
        _: TileGuard,
        _: Box<dyn crate::interpreter::Consumer>,
        cx: &mut crate::interpreter::SubscribeContext,
    ) -> Box<dyn TileProducer> {
        Box::new(SharedReader {
            output: self.output.clone(),
            base: ProducerBase::new(SharedReader::alloc_id(), self.tiling(), &self.base, cx),
        })
    }
}
struct SharedReader {
    output: Arc<SharedOutput>,
    base: ProducerBase,
}
impl TileProducer for SharedReader {
    fn base(&self) -> &ProducerBase {
        &self.base
    }
    fn base_mut(&mut self) -> &mut ProducerBase {
        &mut self.base
    }
    fn restates(&self) -> crate::interpreter::tiling::Restates {
        crate::interpreter::tiling::Restates::Every
    }
    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        let mut tile = self.output.read(&guard);
        tile.remove_guarded(self.base.obsolete_guard.clone());
        tile.restrict_to(&guard.projection_for(self), self.tiling());
        tile
    }
    fn release_impl(&mut self, _: TileGuard) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::{Constant, test_helpers::keys_between};
    use crate::interpreter::{ColumnValue, Predicate, SubscribeContext};

    #[test]
    fn sole_rejects_duplicate_contributions_from_separate_workers() {
        use crate::interpreter::tile_operators::Aggregate;
        let shape = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let input = Constant::collection(
            Tile::data_function(
                ColumnValue::UInts(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![64, 65]))),
                Predicate::True,
                Default::default(),
            ),
            shape,
        );
        let op = Aggregate::new(Box::new(input), AggregateKind::Sole);
        let mut context = RuntimeContext::default();
        op.runtime_operator(&mut context).unwrap();
        let node = &context.pipelines[0];
        let aggregate = node.aggregate.as_ref().unwrap();
        let mut a = WorkerContext::default();
        let mut b = WorkerContext::default();
        a.accumulate(0, &node.input, keys_between(0, 0), aggregate);
        b.accumulate(0, &node.input, keys_between(1, 1), aggregate);
        a.flush(0, &node.output);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                b.flush(0, &node.output);
            }))
            .is_err(),
            "Sole must reject duplicates even when each local buffer holds one value"
        );
    }

    #[test]
    fn aggregate_flush_applies_deltas_without_replaying_or_premature_finality() {
        use crate::interpreter::tile_operators::Aggregate;
        let input_shape = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let input = Constant::collection(
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![64]))),
                Predicate::True,
                Default::default(),
            ),
            input_shape.clone(),
        );
        let op = Aggregate::new(Box::new(input), AggregateKind::Sole);
        let mut context = RuntimeContext::default();
        op.runtime_operator(&mut context).unwrap();
        let node = &context.pipelines[0];
        let aggregate = node.aggregate.as_ref().unwrap();
        let mut worker = WorkerContext::default();
        worker.accumulate(0, &node.input, keys_between(0, 0), aggregate);
        worker.flush(0, &node.output);
        let partial = node.output.read(&node.tiling.universal_guard());
        assert!(
            !partial.is_terminal(),
            "capturing and releasing input cannot finalize its aggregate"
        );
        worker.accumulate(0, &node.input, keys_between(1, 1), aggregate);
        worker.flush(0, &node.output);
        worker.finish(0);
        node.output.finish(&node.tiling);
        let complete = node.output.snapshot();
        assert!(complete.is_terminal());
        let Tile::Aggregation { accumulator, .. } = complete else {
            panic!("expected aggregate")
        };
        assert_eq!(
            *accumulator,
            Tile::Scalar(ColumnValue::Ints(vec![64])),
            "a later empty delta must not resend the first Sole value"
        );
    }

    #[test]
    fn shared_release_waits_for_all_logical_readers_and_never_resurrects_rows() {
        let shape = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let held = SharedOutput::pending();
        held.register(0, shape.empty_guard());
        held.register(1, shape.empty_guard());
        let rows = |keys: Vec<u64>| {
            Tile::data_function(
                ColumnValue::UInts(keys.clone()),
                Box::new(Tile::Scalar(ColumnValue::Ints(
                    keys.iter().map(|k| *k as i64).collect(),
                ))),
                Predicate::False,
                Default::default(),
            )
        };
        held.apply(rows(vec![0, 1, 2, 3]));
        let prefix = keys_between(0, 1);
        held.release(0, &prefix);
        assert!(
            held.read(&prefix).cell_count() > 0,
            "a pending logical reader still needs these rows"
        );
        held.release(1, &prefix);
        let after = held.read(&prefix);
        assert_eq!(
            after.cell_count(),
            4,
            "released rows are compacted, only rows2,3 remain"
        );
        held.apply(rows(vec![0, 1]));
        assert_eq!(
            held.read(&prefix),
            after,
            "late application cannot resurrect obsolete output"
        );
        assert_eq!(
            held.read(&keys_between(2, 3)).cell_count(),
            4,
            "future regions stay retained"
        );
    }

    #[test]
    fn shared_configuration_drops_native_adapters_and_keeps_worker_state_private() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        struct TrackedOperator {
            input: SharedReaderOperator,
            drops: Arc<AtomicUsize>,
        }
        impl Drop for TrackedOperator {
            fn drop(&mut self) {
                self.drops.fetch_add(1, Ordering::SeqCst);
            }
        }
        impl TileOperator for TrackedOperator {
            fn tiling(&self) -> &Tiling {
                self.input.tiling()
            }
            fn operator_id(&self) -> Option<NodeId> {
                self.input.operator_id()
            }
            fn visit_inputs(
                &self,
                _: &mut dyn FnMut(crate::interpreter::operator_graph::InputEdgeSpec<'_>),
            ) {
            }
            fn subscribe(
                &mut self,
                guard: TileGuard,
                consumer: Box<dyn crate::interpreter::Consumer>,
                cx: &mut SubscribeContext,
            ) -> Box<dyn TileProducer> {
                self.input.subscribe(guard, consumer, cx)
            }
        }
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tile = Arc::new(Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::True,
            Default::default(),
        ));
        let drops = Arc::new(AtomicUsize::new(0));
        let observed = drops.clone();
        let plan = RuntimeOperator::new(
            RuntimeBase::freeze(&OperatorBase::new(tiling.clone())).unwrap(),
            None,
            move |base, _| {
                Box::new(TrackedOperator {
                    drops: observed.clone(),
                    input: SharedReaderOperator {
                        output: Arc::new(SharedOutput::source((*tile).clone())),
                        base: base.thaw(),
                    },
                })
            },
            true,
            Vec::new(),
        );
        let mut a = WorkerContext::default();
        let mut b = WorkerContext::default();
        let output_a = SharedOutput::pending();
        let output_b = SharedOutput::pending();
        assert!(a.consume(0, &plan, keys_between(0, 0), &output_a));
        assert_eq!(
            drops.load(Ordering::SeqCst),
            1,
            "the native construction adapter drops after subscription"
        );
        assert!(!a.consume(0, &plan, keys_between(1, 1), &output_a));
        assert!(b.consume(0, &plan, keys_between(0, 0), &output_b));
        assert!(!b.consume(0, &plan, keys_between(1, 1), &output_b));
        assert_eq!(
            drops.load(Ordering::SeqCst),
            2,
            "subsequent morsels reuse producer state"
        );
        let construction = Rc::downgrade(&a.pipelines[&0]._build.0);
        a.finish(0);
        assert!(
            construction.upgrade().is_none(),
            "finish tears down private construction state"
        );
        b.finish(0);
        output_a.finish(&tiling);
        output_b.finish(&tiling);
        assert_eq!(
            output_a.snapshot(),
            output_b.snapshot(),
            "workers have independent releases"
        );
    }

    #[test]
    fn finishing_private_fan_out_drops_aliases_without_a_context_cycle() {
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let op = Constant::collection(
            Tile::data_function(
                ColumnValue::UInts(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
                Predicate::True,
                Default::default(),
            ),
            tiling,
        );
        let plan = RuntimeContext::default().shared(&op).unwrap();
        let mut worker = WorkerContext::default();
        let output = SharedOutput::pending();
        worker.consume(0, &plan, keys_between(0, 0), &output);
        let construction = Rc::downgrade(&worker.pipelines[&0]._build.0);
        let fan = {
            let aliases = worker.pipelines[&0]._build.0.inline.borrow();
            assert_eq!(aliases.len(), 1);
            Rc::downgrade(aliases.values().next().unwrap())
        };
        worker.finish(0);
        assert!(construction.upgrade().is_none());
        assert!(fan.upgrade().is_none());
    }

    #[test]
    fn indexed_nested_constant_preserves_native_completeness_and_release() {
        let integer = Tiling::Scalar(Extent::Base(BaseType::Int));
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(Extent::uint_range(1), integer),
        );
        let inner = Tile::grouped(
            vec![0, 1],
            ColumnValue::UInts(vec![0, 0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
            Predicate::True,
            Default::default(),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(inner),
            Predicate::True,
            Default::default(),
        );
        let mut native = Constant::collection(tile, tiling.clone());
        let factory = native
            .runtime_operator(&mut RuntimeContext::default())
            .unwrap();
        let build = RuntimeBuild::default();
        let mut runtime = factory.input(&build);
        let mut native = native.subscribe(
            tiling.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let mut runtime = runtime.subscribe(
            tiling.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let guard = keys_between(0, 0);
        let expected = native.get(guard.clone());
        let actual = runtime.get(guard);
        assert_eq!(actual.to_guard(), expected.to_guard());
        assert_eq!(actual, expected);
    }
    #[test]
    fn indexed_reads_remain_exact_after_nonprefix_releases() {
        let tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2, 3]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))),
            Predicate::True,
            Default::default(),
        );
        let mut op = Constant::collection(tile, tiling.clone());
        let factory = op.runtime_operator(&mut RuntimeContext::default()).unwrap();
        let build = RuntimeBuild::default();
        let mut worker = factory.input(&build);
        let mut actual = worker.subscribe(
            tiling.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let mut expected = op.subscribe(
            tiling.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        for key in [2, 0, 3, 1] {
            let guard = keys_between(key, key);
            let want = expected.get(guard.clone());
            let got = actual.get(guard);
            assert_eq!(got, want);
            actual.release(got.to_guard());
            expected.release(want.to_guard());
        }
    }
    #[test]
    fn shared_readers_preserve_projection_correlation() {
        use crate::interpreter::tile_operators::{IterateExtent, Memo};
        use crate::interpreter::{FunctionDef, Value};
        let build = RuntimeBuild::default();
        let op = Memo::new(Box::new(IterateExtent::new(Extent::uint_range(4))));
        let reader = op
            .runtime_operator(&mut RuntimeContext::default())
            .unwrap()
            .input(&build);
        assert_eq!(reader.result_correlation(), op.result_correlation());
        let integer = Extent::Base(BaseType::Int);
        let function = Constant::new(
            Value::ComputableFunction(FunctionDef::RecordField("x".into())),
            Extent::Function {
                domain: Box::new(Extent::Record(
                    [("x".into(), integer.clone())].into_iter().collect(),
                )),
                codomain: Box::new(integer),
            },
        );
        let reader = function
            .runtime_operator(&mut RuntimeContext::default())
            .unwrap()
            .input(&build);
        assert_eq!(reader.result_correlation(), function.result_correlation());
    }
}

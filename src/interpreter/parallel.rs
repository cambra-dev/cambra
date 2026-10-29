//! Morsel-driven execution of a program's `main` pipeline on a pool of worker threads.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use std::{
    collections::{HashMap, HashSet},
    fmt,
    sync::{
        Arc, Condvar, Mutex, OnceLock,
        atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
    },
};

use crate::{
    ccl::{
        AggregateKind,
        context::{CompiledProgram, GlobalContext},
        provenance::NodeId,
    },
    interpreter::{
        Consumer, LockNow, Materialized, PooledRecords, Projection, Scheduler, Tile, TileGuard,
        Tiling,
        operator_graph::{EdgeKind, EdgeRole, GraphNode, OperatorGraph},
        tile_operators::{
            BreakerOutput, Claim, Detached, MorselSource, OperatorBase, ProducerBase, TileOperator,
            TileProducer, impl_producer_base,
        },
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// How many threads run a program's `main` pipeline, and how many rows a morsel holds.
pub struct Config {
    /// Worker threads. One runs the program the way the scheduler loop does.
    pub threads: usize,
    /// Rows per morsel: the row range a work package names, which a worker pulls through its
    /// chain at once.
    pub morsel_rows: u64,
}

impl Config {
    /// The variable naming the worker count.
    pub const THREADS: &str = "CAMBRA_NUM_LOCAL_THREADS";
    /// The variable naming the rows per morsel.
    pub const MORSEL_ROWS: &str = "CAMBRA_MORSEL_ROWS";

    /// Read the configuration from the environment: one thread and 4096 rows unless set.
    ///
    /// A value that does not parse, or a zero, reads as the default.
    pub fn from_env() -> Self {
        fn read<T: std::str::FromStr + PartialOrd + Default>(name: &str, default: T) -> T {
            std::env::var(name)
                .ok()
                .and_then(|value| value.parse().ok())
                .filter(|value| *value > T::default())
                .unwrap_or(default)
        }
        Self {
            threads: read(Self::THREADS, 1),
            morsel_rows: read(Self::MORSEL_ROWS, 4096),
        }
    }
}

/// Why a program's `main` output cannot run on the worker pool: the plan supports one
/// pipeline shape, and this names what the graph has instead.
#[derive(Debug)]
pub struct Unsupported(String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the program's `main` output is not a morsel pipeline: {}",
            self.0
        )
    }
}

/// The pipelines the plan admits, upstream first: the last is the one that ends in `main`.
///
/// A pipeline is a chain of streaming operators, any number of `MapResult`s each applying a
/// `Constant` function operand to its input and `MapResultWithSource`s each reading a source's
/// value at the keys of an `IterateExtent` directly beneath it, from its head to its breaker. A
/// head is an `IterateExtent` over a source ([`Head::Source`]), or a `FanOutSlot` over a `Memo`
/// ([`Head::Breaker`]): the plan cuts the graph at the slot, and the pipeline that feeds the
/// `Memo` ends in a breaker that materializes ([`Breaker::Materialize`]). Every operator in a
/// chain is streaming, so a worker's chain holds no state between morsels. Which rows the source
/// enumerates, and whether it can be cut into morsels, is the source's to say
/// ([`TileOperator::morsel_source`]).
pub struct Plan {
    /// Every pipeline after the ones it streams from.
    pipelines: Vec<PipelinePlan>,
}

impl Plan {
    /// The pipeline that ends in `main`.
    pub(crate) fn main(&self) -> &PipelinePlan {
        self.pipelines.last().expect("a plan holds a pipeline")
    }

    /// What the pipeline that ends in `main` ends in.
    pub fn main_breaker(&self) -> &Breaker {
        &self.main().breaker
    }

    /// How many pipelines the plan holds.
    pub fn pipeline_count(&self) -> usize {
        self.pipelines.len()
    }
}

/// One pipeline of a [`Plan`].
pub(crate) struct PipelinePlan {
    /// What its chain starts from.
    pub(crate) head: Head,
    /// What it ends in.
    pub(crate) breaker: Breaker,
    /// The pipelines, by position in the plan, whose output it reads: the pipeline of the `Memo`
    /// its head slot reads, for a [`Head::Breaker`], and none for a source.
    pub(crate) streams_from: Vec<usize>,
}

/// The breaker a morsel pipeline ends in: what the pool keeps between morsels, and how it
/// answers the `main` output.
pub enum Breaker {
    /// The `main` sink itself: the collection, merged morsel by morsel.
    Collect,
    /// An `Aggregate` read by an `ExtractAggregate` into `main`: a fold the pool keeps as one
    /// accumulator per worker and combines once every morsel is folded.
    Fold {
        kind: AggregateKind,
        /// The accumulator's tiling, which seeds each worker's partial.
        accumulator: Tiling,
    },
    /// The input of a `Memo`: the rows the pipelines that read it stream from.
    Materialize {
        /// The `Memo` the output stands for.
        memo: NodeId,
    },
}

/// The streaming operators the plan admits in a chain.
enum Streaming {
    /// Applies a `Constant` function operand to its input.
    MapResult,
    /// Reads a source's value at the keys of an `IterateExtent` directly beneath it.
    MapResultWithSource,
    /// A unary operator that keeps its input's keys and answers a pull at a guard from the input's
    /// answer at the same guard: `VariantWrap` and `VariantProject`.
    KeepsKeys,
}

/// What the plan does with an operator, by its kind.
enum Class {
    /// A streaming operator the chain passes through.
    Streaming(Streaming),
    /// The head of a pipeline over a source.
    Source,
    /// The head of a pipeline that reads a breaker's output: the plan cuts here.
    Cut,
    /// The `Memo` a slot reads, whose input is the pipeline that feeds it.
    Memo,
    /// The function operand a `MapResult` applies.
    Operand,
    /// The extract over a fold at the top of `main`.
    Extract,
    /// The fold an extract reads.
    Fold,
    /// An operator the plan does not admit, and the reason.
    Refuse(String),
}

/// How the plan classifies an operator by its kind: the one table of the kinds it meets. It ends
/// in an arm that refuses, so an operator the plan has not considered is refused rather than run.
fn classify(kind: &str) -> Class {
    match kind {
        "MapResult" => Class::Streaming(Streaming::MapResult),
        "MapResultWithSource" => Class::Streaming(Streaming::MapResultWithSource),
        "VariantWrap" | "VariantProject" => Class::Streaming(Streaming::KeepsKeys),
        "IterateExtent" => Class::Source,
        "FanOutSlot" => Class::Cut,
        "Memo" => Class::Memo,
        "Constant" => Class::Operand,
        "ExtractAggregate" => Class::Extract,
        "Aggregate" => Class::Fold,
        other => Class::Refuse(format!("`{other}` is not a streaming operator here")),
    }
}

/// Cut `graph` into the plan the pool runs, or say why it cannot.
pub fn plan(graph: &OperatorGraph) -> Result<Plan, Unsupported> {
    let by_id: HashMap<NodeId, &GraphNode> = graph
        .nodes()
        .iter()
        .map(|node| match node {
            GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => (*id, node),
        })
        .collect();
    let mut main = None;
    for node in graph.nodes() {
        if let GraphNode::Sink { name, input, .. } = node {
            if name != "main" {
                return Err(Unsupported(format!(
                    "the program also writes the sink `{name}`"
                )));
            }
            main = Some(input.subscribed);
        }
    }
    let mut at = main.ok_or_else(|| Unsupported("the program has no `main` output".into()))?;
    // The breaker is read off the top of the chain: an extract over a fold, or the sink.
    let mut breaker = Breaker::Collect;
    if let Some(GraphNode::Operator { kind, inputs, .. }) = by_id.get(&at)
        && matches!(classify(kind), Class::Extract)
        && let [edge] = inputs.as_slice()
        && let Some(GraphNode::Operator {
            kind: fold_kind,
            tiling: Tiling::Aggregation { kind, accumulator },
            inputs: fold_inputs,
            ..
        }) = by_id.get(&edge.subscribed)
        && matches!(classify(fold_kind), Class::Fold)
        && let [fold_edge] = fold_inputs.as_slice()
    {
        breaker = Breaker::Fold {
            kind: *kind,
            accumulator: (**accumulator).clone(),
        };
        at = fold_edge.subscribed;
    }
    let mut planner = Planner {
        by_id,
        pipelines: Vec::new(),
        memos: HashSet::new(),
    };
    planner.pipeline(at, breaker)?;
    Ok(Plan {
        pipelines: planner.pipelines,
    })
}

/// The plan under construction: the graph, the pipelines planned so far, and the pipeline planned
/// for each `Memo`, so that every slot that reads one streams from the same pipeline.
struct Planner<'g> {
    by_id: HashMap<NodeId, &'g GraphNode>,
    pipelines: Vec<PipelinePlan>,
    /// The `Memo`s a slot of the plan reads. A chain is linear, so at most one slot reads each;
    /// a second is refused.
    memos: HashSet<NodeId>,
}

impl Planner<'_> {
    /// The kind of the operator `id` names, or why the graph holds none.
    fn kind_of(&self, id: NodeId) -> Option<&'static str> {
        match self.by_id.get(&id) {
            Some(GraphNode::Operator { kind, .. }) => Some(kind),
            Some(GraphNode::Sink { .. }) | None => None,
        }
    }

    /// Plan the pipeline whose chain starts at `top` and ends in `breaker`, after the pipelines
    /// it streams from, and say where it is in the plan.
    fn pipeline(&mut self, top: NodeId, breaker: Breaker) -> Result<usize, Unsupported> {
        let mut at = top;
        let (head, streams_from) = loop {
            let node = self.by_id.get(&at).copied();
            let Some(GraphNode::Operator { kind, inputs, .. }) = node else {
                return Err(Unsupported("the chain reaches no source".into()));
            };
            match classify(kind) {
                Class::Refuse(reason) => return Err(Unsupported(reason)),
                Class::Memo | Class::Operand | Class::Extract | Class::Fold => {
                    return Err(Unsupported(format!(
                        "`{kind}` is not a streaming operator here"
                    )));
                }
                Class::Source => break (Head::Source, Vec::new()),
                Class::Cut => {
                    let [edge] = inputs.as_slice() else {
                        return Err(Unsupported("a `FanOutSlot` without its one input".into()));
                    };
                    let memo = edge.subscribed;
                    let Some(GraphNode::Operator {
                        kind: memo_kind,
                        inputs: memo_inputs,
                        ..
                    }) = self.by_id.get(&memo).copied()
                    else {
                        return Err(Unsupported(
                            "a `FanOutSlot` reads a node that is not a `Memo`".into(),
                        ));
                    };
                    if !matches!(classify(memo_kind), Class::Memo) {
                        return Err(Unsupported(
                            "a `FanOutSlot` reads a node that is not a `Memo`".into(),
                        ));
                    }
                    if !self.memos.insert(memo) {
                        return Err(Unsupported(
                            "a `Memo` is read by more than one slot of the plan".into(),
                        ));
                    }
                    let [upstream] = memo_inputs.as_slice() else {
                        return Err(Unsupported("a `Memo` without its one input".into()));
                    };
                    if !matches!(upstream.kind, EdgeKind::Value { deferred: false }) {
                        return Err(Unsupported(
                            "the chain closes a cycle or reads a shared node".into(),
                        ));
                    }
                    let planned =
                        self.pipeline(upstream.subscribed, Breaker::Materialize { memo })?;
                    break (Head::Breaker, vec![planned]);
                }
                Class::Streaming(Streaming::MapResult) => {
                    let edge = |role: &str| {
                        inputs
                            .iter()
                            .find(|edge| matches!(edge.role, EdgeRole::Named(name) if name == role))
                    };
                    let (Some(data), Some(function)) = (edge("input"), edge("fn")) else {
                        return Err(Unsupported("a `MapResult` without its two inputs".into()));
                    };
                    // The chain is a tree the walk descends once: an edge wired through a
                    // `CycleSlot` closes a cycle, and a `Share` edge reaches a fan, which a
                    // chain reads only at its head, so following only owned edges bounds the walk.
                    for edge in [data, function] {
                        if !matches!(edge.kind, EdgeKind::Value { deferred: false }) {
                            return Err(Unsupported(
                                "the chain closes a cycle or reads a shared node".into(),
                            ));
                        }
                    }
                    match self.kind_of(function.subscribed) {
                        Some(kind) if matches!(classify(kind), Class::Operand) => {}
                        Some(kind) => {
                            return Err(Unsupported(format!(
                                "a `MapResult` applies a `{kind}`, and only a `Constant` is \
                                 streamed"
                            )));
                        }
                        None => {
                            return Err(Unsupported(
                                "a `MapResult` applies something the graph holds no operator for"
                                    .into(),
                            ));
                        }
                    }
                    at = data.subscribed;
                }
                Class::Streaming(Streaming::KeepsKeys) => {
                    at = owned_input(kind, inputs)?.subscribed;
                }
                // Reads a source's value at each key of its input: the keys are the input's, so
                // the chain streams.
                Class::Streaming(Streaming::MapResultWithSource) => {
                    let input = owned_input(kind, inputs)?;
                    // It releases its source by correlating the keys it is released at with the
                    // keys it reads, which only an `IterateExtent` beneath it states: over any
                    // other input it releases the source on a universal guard alone, and the pool
                    // releases morsels.
                    if !self
                        .kind_of(input.subscribed)
                        .is_some_and(|kind| matches!(classify(kind), Class::Source))
                    {
                        return Err(Unsupported(
                            "a `MapResultWithSource` reads a source's value at the keys of an \
                             `IterateExtent` only"
                                .into(),
                        ));
                    }
                    at = input.subscribed;
                }
            }
        };
        self.pipelines.push(PipelinePlan {
            head,
            breaker,
            streams_from,
        });
        Ok(self.pipelines.len() - 1)
    }
}

/// The one input of the operator `kind` when the chain owns the edge: an edge wired through a
/// `CycleSlot` closes a cycle, and a `Share` edge reaches a fan, which a chain reads only at its
/// head.
fn owned_input<'g>(
    kind: &str,
    inputs: &'g [crate::interpreter::operator_graph::InputEdge],
) -> Result<&'g crate::interpreter::operator_graph::InputEdge, Unsupported> {
    let [input] = inputs else {
        return Err(Unsupported(format!("a `{kind}` without its one input")));
    };
    match input.kind {
        EdgeKind::Value { deferred: false } => Ok(input),
        _ => Err(Unsupported(
            "the chain closes a cycle or reads a shared node".into(),
        )),
    }
}

/// Run `program`'s `main` output on `config.threads` workers and return what `main` holds,
/// complete, or say why the program is not one the pool runs.
///
/// Each worker owns one subscription of the chain under the breaker. The chain's source cuts
/// its rows into morsels ([`TileOperator::morsel_source`]) that the [`Dispatcher`] hands to
/// whichever worker asks; a worker pulls its chain at the morsel's guard, hands the tile to the
/// breaker, releases the morsel once the breaker holds its rows, and acknowledges it. A
/// collection is merged into one shared tile, the sink; a fold is accumulated per worker and
/// the partials are combined once every worker has returned: every morsel was acknowledged and
/// every fold worker has handed in its partial.
pub fn run_main(
    ctx: &mut GlobalContext,
    program: &mut CompiledProgram,
    config: &Config,
) -> Result<Tile, Unsupported> {
    run_main_holding(ctx, program, &mut None, config)
}

/// [`run_main`] for a program whose `main` producer is not in its output: a
/// [`LiveProgram`](crate::live_program::LiveProgram) moves it out to drive it, and `main_producer`
/// is where it sits. The pool drops it once the program is accepted, and a refused program keeps
/// it.
pub fn run_main_holding(
    ctx: &mut GlobalContext,
    program: &mut CompiledProgram,
    main_producer: &mut Option<Box<dyn TileProducer>>,
    config: &Config,
) -> Result<Tile, Unsupported> {
    run_main_delivering(ctx, program, main_producer, config, None)
}

/// [`run_main_holding`] for a program over a live source: `delivery` runs on the calling thread
/// while the workers run, and is how the source's arrivals reach the pipeline.
pub(crate) fn run_main_delivering(
    ctx: &mut GlobalContext,
    program: &mut CompiledProgram,
    main_producer: &mut Option<Box<dyn TileProducer>>,
    config: &Config,
    delivery: Option<DeliveringThread<'_>>,
) -> Result<Tile, Unsupported> {
    let plan = plan(&program.operator_graph)?;
    let output = program
        .main_mut()
        .ok_or_else(|| Unsupported("the program has no `main` output".into()))?;
    // Everything the pool can refuse is read before it takes the program: each pipeline's
    // source, the pipelines being cut at the slots that start the ones behind a breaker.
    let source_pipelines = check_pipelines(&*output.op)?;
    if delivery.is_some() && source_pipelines > 1 {
        return Err(Unsupported(
            "the program reads several sources, and a delivery reaches one".into(),
        ));
    }
    // The program is the pool's from here: a program the plan or `source_of` refused still has
    // its producer, and the scheduler loop drives it. The pool owns the pipelines' release
    // records, so the producer `compile_program` subscribed for `main` goes: it registered
    // records that release nothing, which a source would hold its reclaim at. It is in the
    // program's output, or with the caller that moved it out to drive it.
    let dropped = main_producer.take().or_else(|| output.producer.take());
    debug_assert!(
        dropped.is_some(),
        "the pool drops the producer that held the pipeline's record"
    );
    drop(dropped);
    let mut delivery = delivery;
    let mut tiles = None;
    let mut run_chain = |chain: &mut Box<dyn TileOperator>| {
        let mut taken = HashMap::new();
        cut(chain, &mut taken);
        tiles = Some(run_planned(
            ctx,
            &plan,
            chain,
            taken,
            config,
            delivery.take(),
        ));
    };
    // The chain the workers subscribe is the whole output for a collection, and the fold's input
    // for a fold, reached through the extract and the fold the plan saw.
    match plan.main().breaker {
        Breaker::Collect => run_chain(&mut output.op),
        Breaker::Fold { .. } => output.op.visit_inputs_mut(&mut |fold| {
            fold.visit_inputs_mut(&mut |input| run_chain(input));
        }),
        Breaker::Materialize { .. } => unreachable!("`main` is not a memo's input"),
    }
    Ok(tiles
        .expect("the main chain was visited")
        .pop()
        .expect("a run holds a pipeline"))
}

/// The sources of the pipelines of the program whose `main` is `main`, which the plan has
/// already admitted: each pipeline reads one source that is cut into morsels, or starts at a slot
/// that reads a breaker. Returns how many pipelines read a source.
fn check_pipelines(main: &dyn TileOperator) -> Result<usize, Unsupported> {
    struct Walk {
        seen: HashSet<NodeId>,
        sources: usize,
        refusal: Option<Unsupported>,
    }
    fn pipeline(top: &dyn TileOperator, walk: &mut Walk) {
        fn chain(
            op: &dyn TileOperator,
            found: &mut usize,
            ends_at_a_slot: &mut bool,
            walk: &mut Walk,
        ) {
            if matches!(classify(op.kind()), Class::Cut) {
                *ends_at_a_slot = true;
                // The pipeline behind the slot's `Memo` is walked once, however many slots read it.
                op.visit_inputs(&mut |edge| {
                    if let Some(memo) = edge.target.operator_id()
                        && walk.seen.insert(memo)
                    {
                        edge.target
                            .visit_inputs(&mut |upstream| pipeline(upstream.target, walk));
                    }
                });
                return;
            }
            match op.morsel_source() {
                Some(_) => *found += 1,
                None => {
                    op.visit_inputs(&mut |edge| chain(edge.target, found, ends_at_a_slot, walk))
                }
            }
        }
        let (mut found, mut ends_at_a_slot) = (0, false);
        chain(top, &mut found, &mut ends_at_a_slot, walk);
        if !ends_at_a_slot {
            match found {
                1 => walk.sources += 1,
                0 => {
                    walk.refusal.get_or_insert(Unsupported(
                        "the chain reads no source that is cut into morsels".into(),
                    ));
                }
                _ => {
                    walk.refusal.get_or_insert(Unsupported(
                        "the chain reads several sources, and a pipeline is cut at one".into(),
                    ));
                }
            }
        }
    }
    let mut walk = Walk {
        seen: HashSet::new(),
        sources: 0,
        refusal: None,
    };
    pipeline(main, &mut walk);
    match walk.refusal {
        Some(refusal) => Err(refusal),
        None => Ok(walk.sources),
    }
}

/// An upstream pipeline that the cut took out of the graph: the chain that fed a `Memo`, and the
/// output the pipelines that read the `Memo` stream from.
struct Taken {
    chain: Box<dyn TileOperator>,
    output: Arc<Materialized>,
}

/// Cut the graph below `op` at every `FanOutSlot`: the first slot that reads a `Memo` takes the
/// chain that feeds it out of the graph, leaving a [`Detached`] in its place, and every slot is
/// replaced by a [`BreakerOutput`] over the output that chain will fill. The taken chains are cut
/// in turn. The program is the pool's from here, since the cut leaves the graph unusable to the
/// scheduler loop.
fn cut(op: &mut Box<dyn TileOperator>, taken: &mut HashMap<NodeId, Taken>) {
    if !matches!(classify(op.kind()), Class::Cut) {
        op.visit_inputs_mut(&mut |input| cut(input, taken));
        return;
    }
    let mut memo = None;
    op.visit_inputs(&mut |edge| memo = edge.target.operator_id());
    let memo = memo.expect("the plan saw a `Memo`, and an operator has an identity");
    let (tiling, correlation) = (op.tiling().clone(), op.result_correlation());
    // The serial chain the program subscribed when it compiled belongs to the scheduler loop,
    // which the pool replaces: its producer holds release records with the sources beneath it,
    // and the fan-out, which the operator map keeps, would hold it for as long as the program.
    op.drop_serial_subscription();
    let mut upstream = None;
    op.visit_inputs_mut(&mut |shared| {
        shared.visit_inputs_mut(&mut |input| {
            let detached = Box::new(Detached::new(input.tiling().clone()));
            upstream = Some(std::mem::replace(input, detached));
        })
    });
    let mut chain = upstream.expect("a `Memo` has an input");
    let output = Materialized::new(chain.tiling().clone());
    cut(&mut chain, taken);
    *op = Box::new(BreakerOutput::new(
        output.clone(),
        tiling,
        false,
        correlation,
    ));
    let first = taken.insert(memo, Taken { chain, output });
    assert!(first.is_none(), "the plan admits one slot per memo");
}

/// Run the pipelines of `plan` over the chains the cut left: `main_chain` for the pipeline that
/// ends in `main`, and the taken chains for the pipelines that end in a breaker that
/// materializes. The tiles are the pipelines' results, in plan order.
fn run_planned(
    ctx: &mut GlobalContext,
    plan: &Plan,
    main_chain: &mut Box<dyn TileOperator>,
    mut taken: HashMap<NodeId, Taken>,
    config: &Config,
    delivery: Option<DeliveringThread<'_>>,
) -> Vec<Tile> {
    let mut main_chain = Some(main_chain);
    let mut upstream: HashMap<NodeId, &mut Taken> =
        taken.iter_mut().map(|(k, v)| (*k, v)).collect();
    let mut runs = Vec::new();
    for pipeline in &plan.pipelines {
        let (chain, breaker): (&mut dyn TileOperator, PoolBreaker) = match &pipeline.breaker {
            Breaker::Materialize { memo } => {
                let taken = upstream
                    .remove(memo)
                    .expect("the cut took the memo's input");
                (
                    &mut *taken.chain,
                    PoolBreaker::Materialize {
                        output: taken.output.clone(),
                    },
                )
            }
            Breaker::Collect => {
                let chain = main_chain.take().expect("one pipeline ends in `main`");
                let breaker = PoolBreaker::Collect {
                    collector: Mutex::new(chain.tiling().empty_tile()),
                };
                (&mut **chain, breaker)
            }
            Breaker::Fold { kind, accumulator } => {
                let chain = main_chain.take().expect("one pipeline ends in `main`");
                let breaker = PoolBreaker::Fold {
                    kind: *kind,
                    seed: kind.initial_accumulator(accumulator),
                    partials: Arc::new(Mutex::new(Vec::new())),
                    result: None,
                };
                (&mut **chain, breaker)
            }
        };
        let source = source_of(&*chain).expect("the pipeline was checked to read one source");
        runs.push(PipelineRun {
            chain,
            source,
            breaker,
            head: pipeline.head,
            // The plan admits no build side, which would make a pipeline wait on one.
            after: Vec::new(),
            streams_from: pipeline
                .streams_from
                .iter()
                .map(|&i| PipelineId(i))
                .collect(),
        });
    }
    run_pipelines(ctx.scheduler(), runs, config, delivery)
}

/// What delivers a live source's arrivals while the workers run: called once, on the calling
/// thread, with the handle that publishes a region to the pipeline's source and the scheduler the
/// chains were subscribed with. It stands in for the thread that reads the source's input: it
/// writes rows to the source and tells the scheduler, whose `check_for_notifications` polls the
/// source and notifies the consumers registered for it, which reach the pipeline's head. It
/// publishes nothing once it returns, so `run_pipeline` closes the pipeline's source then.
pub(crate) type DeliveringThread<'a> = Box<dyn FnOnce(PipelineHandle, &mut Scheduler) + 'a>;

/// Run the plan's one pipeline: `config.threads` workers each pull their own subscription of
/// `chain_op` at the morsels `source` hands out and feed `breaker`. The result is what the
/// breaker holds once every morsel is acknowledged and every worker has left.
///
/// With a `delivery` the pipeline's head is notified through a [`PipelineConsumer`]: an arrival
/// a notification carries is published to `source` and wakes a parked worker. When `delivery`
/// returns, `run_pipeline` closes the source, and the pipeline finishes once the workers have
/// claimed everything. Without one the source holds every row it will, and it is closed at once.
#[cfg(test)]
fn run_pipeline(
    scheduler: &mut Scheduler,
    chain_op: &mut dyn TileOperator,
    source: Arc<dyn MorselSource>,
    breaker: PoolBreaker,
    config: &Config,
    delivery: Option<DeliveringThread<'_>>,
) -> Tile {
    let run = PipelineRun {
        chain: chain_op,
        source,
        breaker,
        head: Head::Source,
        after: Vec::new(),
        streams_from: Vec::new(),
    };
    let mut tiles = run_pipelines(scheduler, vec![run], config, delivery);
    tiles.pop().expect("one pipeline, one result")
}

/// What a pipeline's chain starts from.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Head {
    /// A data source, whose rows arrive from outside the run: the run publishes what it holds
    /// and closes it, however the pipeline waits on others. The dispatcher keeps the region in
    /// `Early` until the pipeline starts.
    Source,
    /// A breaker's output ([`BreakerOutput`]): the pipeline streams from the pipeline whose
    /// breaker it reads.
    Breaker,
}

/// A pipeline of a run: the chain its workers subscribe, the source they claim from, and the
/// breaker it ends in. The pipelines of a run are numbered by their position, each after the
/// ones it waits on and streams from.
struct PipelineRun<'a> {
    chain: &'a mut dyn TileOperator,
    source: Arc<dyn MorselSource>,
    breaker: PoolBreaker,
    head: Head,
    /// See [`PipelineSpec::after`].
    after: Vec<PipelineId>,
    /// See [`PipelineSpec::streams_from`]. A pipeline with a [`Head::Breaker`] streams from the
    /// pipeline of the breaker it reads, and a [`Head::Source`] pipeline streams from none.
    streams_from: Vec<PipelineId>,
}

/// Run the pipelines of a plan on `config.threads` workers, each of which subscribes every
/// pipeline's chain once and serves whichever pipeline has a morsel. The results are what each
/// pipeline's breaker holds once every pipeline has finished, in plan order.
///
/// A pipeline with a data-source head is published `Everything` when the run starts and closed
/// then, or once `delivery` has returned when it is the first of them and there is one. The head
/// of a pipeline that reads a breaker is notified by the breaker before it, which publishes each
/// morsel's region once it holds the rows ([`Materialized::publish`]), so the pipeline starts at
/// the first morsel and ends when the pipeline before it finishes
/// ([`PipelineSpec::streams_from`]). The first worker's chain of each pipeline carries the
/// consumer that reaches the dispatcher. The breaker's output registers one consumer per reading
/// operator, its first subscription's, so a publish notifies operators and not workers; the other
/// workers' chains carry a consumer that is never notified.
///
/// A chain does not reach another pipeline's operators, and a pipeline that reads a breaker reads
/// the output of a pipeline it streams from; a debug build asserts both, and every build asserts
/// that a source pipeline streams from none and a breaker's pipeline from one. Once the chains
/// are dropped the breakers' readers are retired, so a producer that never released pins no row.
///
/// The result of a pipeline that ends in `Collect` or `Fold` is the answer of `main`. The result
/// of one that ends in `Materialize` is its output once the pipelines that read it have released
/// every row, which is empty and complete: the rows went on to those pipelines.
fn run_pipelines(
    scheduler: &mut Scheduler,
    runs: Vec<PipelineRun<'_>>,
    config: &Config,
    delivery: Option<DeliveringThread<'_>>,
) -> Vec<Tile> {
    // The delivery reaches the first pipeline that reads a data source.
    let delivered = runs.iter().position(|run| run.head == Head::Source);
    let notified = (0..runs.len())
        .map(|pipeline| Some(pipeline) == delivered && delivery.is_some())
        .collect();
    // Without a delivery no row arrives later, so every source closes at the start.
    let close_at_start = (0..runs.len())
        .map(|pipeline| delivery.is_none() || Some(pipeline) != delivered)
        .collect();
    let Prepared {
        dispatcher,
        handles,
        mut chains,
        records,
        breakers,
    } = prepare(scheduler, runs, config, notified, close_at_start);
    // The chains are lent to the workers and dropped here, after the scope, one at a time:
    // a producer's drop detaches its probe with a lock that must not find the probe table
    // held by another worker's `get`.
    // A panic of a worker or of the delivery fails the dispatcher, which stops the other workers,
    // and is raised again here as that panic: a worker's before the delivery's, since a delivery
    // that waits on a failed pool fails because of it.
    let panic = std::thread::scope(|scope| {
        // Armed before the first spawn: a spawn that panics stops the workers already running
        // from claiming further morsels.
        let _fail = FailOnUnwind(&dispatcher);
        let workers: Vec<_> = chains
            .iter_mut()
            .map(|worker_chains| {
                let (dispatcher, breakers) = (&dispatcher, &breakers);
                scope.spawn(move || run_worker(worker_chains, dispatcher, breakers))
            })
            .collect();
        let delivered = delivery.and_then(|delivery| {
            let delivered = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let handle = &handles[delivered.expect("a delivery reaches a source pipeline")];
                delivery(handle.clone(), scheduler);
                handle.close();
            }));
            if delivered.is_err() {
                dispatcher.fail();
            }
            delivered.err()
        });
        // Every worker is joined: one that is not makes the scope panic in its stead.
        let worker_panics: Vec<_> = workers
            .into_iter()
            .filter_map(|worker| worker.join().err())
            .collect();
        worker_panics.into_iter().next().or(delivered)
    });
    // The chains are gone, so no producer reads an output: its readers retire once, here, and a
    // producer that never released pins no row.
    drop(chains);
    for breaker in &breakers {
        if let PoolBreaker::Materialize { output } = breaker {
            output.retire_readers();
        }
    }
    drop(records);
    if let Some(panic) = panic {
        std::panic::resume_unwind(panic);
    }
    debug_assert!(
        dispatcher.all_done(),
        "every worker returned, so every pipeline finished"
    );
    breakers.into_iter().map(PoolBreaker::finish).collect()
}

/// How long a worker in a test may stay parked before the park fails: a worker that waits for a
/// wake-up that never comes fails with a message instead of hanging the suite. Built for the
/// lib's unit tests and for the `it` tests, which build the lib with `test-helpers`.
#[cfg(any(test, feature = "test-helpers"))]
const TEST_PARK_DEADLINE: std::time::Duration = std::time::Duration::from_secs(30);

/// A run's pipelines, subscribed and seeded, before any worker serves them.
struct Prepared {
    dispatcher: Arc<Dispatcher>,
    handles: Vec<PipelineHandle>,
    /// One chain per pipeline per worker, indexed by `PipelineId`.
    chains: Vec<Vec<Box<dyn TileProducer>>>,
    /// The release records the chains registered with the sources, retired when this drops, after
    /// the chains.
    records: PooledRecords,
    breakers: Vec<PoolBreaker>,
}

/// Subscribe every pipeline's chain once per worker and seed the pipelines that read a data
/// source. `notified[pipeline]` says whether the first worker's chain of a data-source pipeline
/// carries the consumer that publishes a notification's region to the dispatcher, and
/// `close_at_start[pipeline]` whether the source closes once it is seeded; a breaker's pipelines
/// always carry the consumer, and the dispatcher closes them.
fn prepare(
    scheduler: &mut Scheduler,
    mut runs: Vec<PipelineRun<'_>>,
    config: &Config,
    notified: Vec<bool>,
    close_at_start: Vec<bool>,
) -> Prepared {
    for (pipeline, run) in runs.iter().enumerate() {
        assert!(
            run.head != Head::Source || run.streams_from.is_empty(),
            "a pipeline over a data source streams from none: {pipeline}"
        );
        assert!(
            run.head != Head::Breaker || !run.streams_from.is_empty(),
            "a pipeline over a breaker's output streams from the pipeline of that breaker: \
             {pipeline}"
        );
    }
    assert_pipelines_are_separate(&runs);
    let tilings: Vec<Tiling> = runs.iter().map(|run| run.chain.tiling().clone()).collect();
    let specs = runs
        .iter()
        .map(|run| {
            let source = run.source.clone();
            PipelineSpec {
                after: run.after.clone(),
                streams_from: run.streams_from.clone(),
                source: Box::new(move || source.clone()),
                finalize: run.breaker.finalize(),
            }
        })
        .collect();
    let dispatcher = Arc::new(Dispatcher::new(specs, config.morsel_rows.max(1)));
    let handles: Vec<PipelineHandle> = (0..runs.len())
        .map(|pipeline| PipelineHandle {
            dispatcher: dispatcher.clone(),
            pipeline: PipelineId(pipeline),
        })
        .collect();
    // One chain per pipeline per worker, indexed by `PipelineId`. Notifications reach the
    // dispatcher through the first worker's chain of each pipeline. Every chain's source
    // registration is notified of the same region, and one consumer publishes it: a second would
    // publish what the source has already claimed. The path from the source to that consumer is
    // region-driven and acyclic (`plan` admits no shared node or recurrence below a head), so no
    // consumer on it drops or widens the region.
    //
    // The chains hold release records with a source, one per source operator and named for the
    // pool: each worker releases the morsels it ran, and a source reclaims what every record
    // releases. The records outlive the chains and retire when `records` drops.
    let (chains, records): (Vec<Vec<Box<dyn TileProducer>>>, _) = scheduler
        .with_pooled_release_records(pool_release_identity(), |scheduler| {
            (0..config.threads.max(1))
                .map(|worker| {
                    runs.iter_mut()
                        .enumerate()
                        .map(|(pipeline, run)| {
                            let head: Box<dyn Consumer> = match (worker, run.head) {
                                (0, Head::Breaker) => {
                                    Box::new(PipelineConsumer(handles[pipeline].clone()))
                                }
                                (0, Head::Source) if notified[pipeline] => {
                                    Box::new(PipelineConsumer(handles[pipeline].clone()))
                                }
                                _ => Box::new(|| {}),
                            };
                            run.chain.subscribe(
                                tilings[pipeline].universal_guard(),
                                head,
                                scheduler,
                            )
                        })
                        .collect()
                })
                .collect()
        });
    let seeded: Vec<usize> = (0..runs.len())
        .filter(|&pipeline| runs[pipeline].head == Head::Source)
        .collect();
    let breakers: Vec<PoolBreaker> = runs.into_iter().map(|run| run.breaker).collect();
    // What a source holds when the pool starts is claimable: nothing notifies of rows that
    // arrived before the chains were subscribed, and a source's own subscription notification
    // reaches only worker 0's head and says nothing of them.
    for &pipeline in &seeded {
        handles[pipeline].publish(&Projection::Everything);
        if close_at_start[pipeline] {
            handles[pipeline].close();
        }
    }
    Prepared {
        dispatcher,
        handles,
        chains,
        records,
        breakers,
    }
}

/// The invariants of a run's pipelines that a debug build checks, which a plan holds and a
/// hand-built run could break: a chain reaches no operator of another pipeline, and a
/// [`Head::Breaker`] pipeline reads the output of a pipeline it streams from.
fn assert_pipelines_are_separate(runs: &[PipelineRun<'_>]) {
    if !cfg!(debug_assertions) {
        return;
    }
    fn visit(op: &dyn TileOperator, pipeline: usize, owner: &mut HashMap<NodeId, usize>) {
        if let Some(id) = op.operator_id() {
            let first = *owner.entry(id).or_insert(pipeline);
            assert_eq!(
                first, pipeline,
                "a chain reaches no operator of another pipeline: {id:?} is in {first} and {pipeline}"
            );
        }
        op.visit_inputs(&mut |edge| visit(edge.target, pipeline, owner));
    }
    let mut owner = HashMap::new();
    for (pipeline, run) in runs.iter().enumerate() {
        visit(&*run.chain, pipeline, &mut owner);
        if run.head == Head::Breaker {
            assert!(
                run.streams_from.iter().any(|upstream| matches!(
                    &runs[upstream.0].breaker,
                    PoolBreaker::Materialize { output } if output.feeds(&run.source)
                )),
                "a pipeline over a breaker's output reads the output of a pipeline it streams from: {pipeline}"
            );
        }
    }
}

/// The name a pool's chains hold their release record under, one per run.
fn pool_release_identity() -> String {
    static RUNS: AtomicU64 = AtomicU64::new(0);
    format!("pool#{}", RUNS.fetch_add(1, Ordering::Relaxed))
}

/// What delivers to one pipeline of a [`Dispatcher`]: a region of arrived keys, and the end of
/// arrivals.
#[derive(Clone)]
pub(crate) struct PipelineHandle {
    dispatcher: Arc<Dispatcher>,
    pipeline: PipelineId,
}

impl PipelineHandle {
    /// The keys `arrived` can be claimed.
    fn publish(&self, arrived: &Projection) {
        self.dispatcher.publish(self.pipeline, arrived);
    }

    /// No further key will arrive.
    fn close(&self) {
        self.dispatcher.close(self.pipeline);
    }
}

/// The consumer at the head of a pipeline: a notification publishes the region it carries to the
/// pipeline's source and never pulls, which is what `region_driven` says.
struct PipelineConsumer(PipelineHandle);

impl Consumer for PipelineConsumer {
    fn notify(&mut self, arrived: &Projection) {
        debug_assert!(
            *arrived != Projection::Nothing,
            "no producer notifies of an empty region"
        );
        // A region of fields names where a change is in a record, and the pipeline's source cuts
        // keys: only everything it has ready is safe to hand out.
        match arrived {
            Projection::Fields(_) => self.0.publish(&Projection::Everything),
            keys => self.0.publish(keys),
        }
    }

    fn region_driven(&self) -> bool {
        true
    }
}

/// The one source under `chain` that cuts its rows into morsels, or why there is none.
///
/// A source is a leaf of the operator tree. The walk descends through each operator's inputs
/// and stops at the first operator that answers [`TileOperator::morsel_source`].
fn source_of(chain: &dyn TileOperator) -> Result<Arc<dyn MorselSource>, Unsupported> {
    fn collect(op: &dyn TileOperator, found: &mut Vec<Arc<dyn MorselSource>>) {
        match op.morsel_source() {
            Some(source) => found.push(source),
            None => op.visit_inputs(&mut |edge| collect(edge.target, found)),
        }
    }
    let mut found = Vec::new();
    collect(chain, &mut found);
    match <[_; 1]>::try_from(found) {
        Ok([source]) => Ok(source),
        Err(found) if found.is_empty() => Err(Unsupported(
            "the chain reads no source that is cut into morsels".into(),
        )),
        Err(_) => Err(Unsupported(
            "the chain reads several sources, and a pipeline is cut at one".into(),
        )),
    }
}

/// The breaker's state while the workers run.
enum PoolBreaker {
    /// The collection, merged morsel by morsel.
    Collect {
        // shared-state-ok: the sink's own state. Every worker merges into it, and no operator
        // reads it: it answers `main` once every worker has returned.
        collector: Mutex<Tile>,
    },
    /// A fold: each worker folds its morsels into a partial of its own and hands the partial
    /// in once, so nothing is shared on the morsel path.
    Fold {
        kind: AggregateKind,
        seed: Tile,
        // shared-state-ok: the breaker's own state, standing where the sink's cell stands for
        // a collection. A worker hands its partial in once, after its last morsel, and no
        // operator reads it: the combine runs after every worker has returned and answers
        // `main`.
        partials: Arc<Mutex<Vec<Tile>>>,
        /// Where an inline run leaves the combined answer when the pipeline finishes, for the
        /// producer that answers `main` to read; a threaded run combines at the end.
        result: Option<Arc<FoldedResult>>,
    },
    /// The rows a pipeline behind this one reads: each worker merges the morsel into the shared
    /// output and publishes its region, and the output is completed when the pipeline finishes.
    Materialize { output: Arc<Materialized> },
}

impl PoolBreaker {
    /// What runs when the pipeline that ends in this breaker finishes, before any pipeline that
    /// waits on it starts or is closed: the output of a breaker that materializes is complete.
    fn finalize(&self) -> Option<Box<dyn Fn() + Send + Sync>> {
        match self {
            PoolBreaker::Materialize { output } => {
                let output = output.clone();
                Some(Box::new(move || output.complete()))
            }
            PoolBreaker::Fold {
                kind,
                seed,
                partials,
                result: Some(result),
            } => {
                let (kind, seed, partials, result) =
                    (*kind, seed.clone(), partials.clone(), result.clone());
                Some(Box::new(move || {
                    result.set(fold_partials(kind, seed.clone(), &partials.lock_wait()))
                }))
            }
            PoolBreaker::Collect { .. } | PoolBreaker::Fold { result: None, .. } => None,
        }
    }

    /// The answer once every worker has returned: complete, since the source answered every row
    /// it has, every package was acknowledged after its rows reached the breaker, and every
    /// fold worker has handed in its partial.
    fn finish(self) -> Tile {
        match self {
            PoolBreaker::Collect { collector } => {
                let mut tile = collector
                    .into_inner()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                // Every worker has returned and every morsel is merged, so the collection is
                // complete at every level, as the universal pull states it.
                tile.complete_every_level();
                tile
            }
            PoolBreaker::Fold {
                kind,
                seed,
                partials,
                ..
            } => fold_partials(kind, seed, &partials.lock_wait()),
            PoolBreaker::Materialize { output } => {
                output.snapshot(&output.tiling().universal_guard())
            }
        }
    }
}

/// The partials of a fold combined into its seed, as `ExtractAggregate` emits them once the fold
/// is terminal.
fn fold_partials(kind: AggregateKind, seed: Tile, partials: &[Tile]) -> Tile {
    let mut total = seed;
    for partial in partials {
        kind.accumulate(&mut total, partial, 0, partial.rows());
    }
    kind.extract(total)
}

/// One pool worker over the plan's pipelines: per pipeline its chain and the breaker the
/// pipeline feeds, and for a fold the partial the worker folds into. `work` and `leave` index
/// them by the package's pipeline.
struct MainWorker<'a> {
    chains: &'a mut [Box<dyn TileProducer>],
    breakers: &'a [PoolBreaker],
    /// Per pipeline, the partial of a fold, borrowed from the run so that a panic in `work` leaves
    /// them where they were.
    partials: &'a mut Vec<Option<Tile>>,
    /// The morsels this worker has run since it was made: a lap makes one, so this counts the
    /// lap's.
    worked: usize,
}

impl PoolWorker for MainWorker<'_> {
    /// Pull the morsel through the package's pipeline, hand the tile to the pipeline's breaker,
    /// release the morsel.
    fn work(&mut self, package: &WorkPackage) {
        let pipeline = package.pipeline.0;
        self.worked += 1;
        let chain = &mut self.chains[pipeline];
        let mut tile = chain.get(package.guard.clone());
        match (&self.breakers[pipeline], &mut self.partials[pipeline]) {
            (PoolBreaker::Collect { collector }, _) => collector.lock_wait().merge(tile),
            (PoolBreaker::Fold { kind, .. }, Some(partial)) => {
                // What `AggregateProducer` folds: the values under the keys, deleted rows
                // compacted away.
                tile.compact();
                let Tile::DataFunction {
                    domain, codomain, ..
                } = tile
                else {
                    panic!("a fold's input is a collection, got {tile:?}");
                };
                // A collection's merge rejects a key answered outside its morsel or twice;
                // a fold would count it silently, so the check is made here.
                debug_assert!(
                    (0..domain.len()).all(|row| package.guard.covers_path(&[domain.index_at(row)])),
                    "a morsel's chain answers keys inside the morsel only, got {domain:?} for {:?}",
                    package.guard
                );
                kind.accumulate(partial, &codomain, 0, codomain.rows());
            }
            (PoolBreaker::Fold { .. }, None) => unreachable!("a fold worker holds a partial"),
            (PoolBreaker::Materialize { output }, _) => {
                // The rows are readable before the region is published, and the region is the
                // morsel's: a key the chain filtered out is in it and has no row.
                tile.compact();
                output.absorb(tile, &package.guard);
                output
                    .publish(&Projection::of(&package.guard).expect("a morsel's guard names keys"));
            }
        }
        // The release is the breaker's acknowledgement: the source may reclaim the morsel
        // only once the collector, the worker's partial or the output holds its rows.
        chain.release(package.guard.clone());
    }

    /// A fold worker hands its partial in once, after its last morsel.
    fn leave(&mut self, pipeline: PipelineId) {
        if let (PoolBreaker::Fold { partials, .. }, Some(partial)) =
            (&self.breakers[pipeline.0], self.partials[pipeline.0].take())
        {
            partials.lock_wait().push(partial);
        }
    }
}

/// One worker's turn on the dispatcher, until every pipeline has finished.
fn run_worker(
    chains: &mut [Box<dyn TileProducer>],
    dispatcher: &Dispatcher,
    breakers: &[PoolBreaker],
) {
    let _fail = FailOnUnwind(dispatcher);
    debug_assert_eq!(
        chains.len(),
        breakers.len(),
        "a worker holds one chain per pipeline"
    );
    let mut partials: Vec<Option<Tile>> = breakers
        .iter()
        .map(|breaker| match breaker {
            PoolBreaker::Collect { .. } | PoolBreaker::Materialize { .. } => None,
            PoolBreaker::Fold { seed, .. } => Some(seed.clone()),
        })
        .collect();
    dispatcher.serve(&mut MainWorker {
        chains,
        breakers,
        partials: &mut partials,
        worked: 0,
    });
}

/// A pipeline of a plan, by its position in the plan.
#[derive(Clone, Copy)]
struct PipelineId(usize);

/// One morsel of one pipeline: the unit a worker takes from the [`Dispatcher`].
///
/// The morsel is named by the guard a worker pulls the pipeline's chain at, never by its
/// rows: the tile is produced by that pull, so data reaches the breaker only through `get`.
struct WorkPackage {
    pipeline: PipelineId,
    guard: TileGuard,
}

/// A pipeline of a plan as the [`Dispatcher`] runs it.
struct PipelineSpec {
    /// Pipelines that finish before this one starts. Each is earlier in the plan, so the
    /// dependencies form no cycle.
    after: Vec<PipelineId>,
    /// Pipelines whose output this one reads as it is produced. The pipeline starts once a
    /// region is published to it, or once every pipeline in `streams_from` has finished with
    /// nothing published, whichever comes first, and it is closed when the last of them
    /// finishes. Each is earlier in the plan, and none is also in `after`.
    streams_from: Vec<PipelineId>,
    /// The source the pipeline's workers claim from, built once every pipeline in `after` has
    /// finished and the stream, if any, has started: a pipeline downstream of a breaker reads
    /// what the breaker produced. Called once, by the thread that releases the last wait. That
    /// can be a thread inside a [`publish`](Dispatcher::publish), an upstream worker in `work` or
    /// `leave` or a consumer's `notify`, so the builder takes no lock the publisher may hold and
    /// does not re-enter the breaker's notification.
    source: Box<dyn Fn() -> Arc<dyn MorselSource> + Send + Sync>,
    /// Called once, by the worker that completes the pipeline, before any pipeline waiting on
    /// it starts: the breaker's combine.
    finalize: Option<Box<dyn Fn() + Send + Sync>>,
}

/// What a worker is told by [`Dispatcher::next`].
enum Next {
    /// A morsel to run.
    Package(WorkPackage),
    /// Nothing is claimable now, and a publish, a close, or a pipeline that finishes or starts may
    /// change that.
    Wait,
    /// Every pipeline has finished, or the dispatcher failed.
    Done,
}

/// What a pool worker does with a morsel and with the state it holds for a pipeline.
trait PoolWorker {
    /// Run `package`'s morsel and release it once the breaker holds its rows.
    fn work(&mut self, package: &WorkPackage);

    /// The worker leaves `pipeline`, whose source is exhausted: hand in what it holds for it.
    fn leave(&mut self, pipeline: PipelineId);
}

/// What hands out the morsels of every pipeline of a plan, starts a pipeline once the pipelines
/// it waits on have finished, and records which pipelines can still produce a morsel.
///
/// A worker claims a morsel from a pipeline's source with [`next`](Self::next) and acknowledges
/// it with [`ack`](Self::ack) once the morsel is released. A pipeline finishes when its source
/// has answered `Exhausted`, every morsel it answered is acknowledged, and every worker that
/// claimed from it has left it. The worker that completes it runs its `finalize` and starts the
/// pipelines waiting on it. A finite source's morsel path takes no lock; a live source's takes
/// its own state lock. The lock that parks idle workers is the only one the dispatcher itself
/// takes on the claim path. See `src/interpreter/design-parallel.md`, "The dispatcher".
struct Dispatcher {
    /// Names this dispatcher in the [`ServeState`]s it mints, so a state of another dispatcher
    /// is recognized whatever its size.
    id: u64,
    /// Per pipeline, by `PipelineId`.
    jobs: Vec<Job>,
    /// Rows a morsel holds, which a worker claims at most.
    morsel_rows: u64,
    /// Pipelines not yet finished.
    unfinished: AtomicUsize,
    /// Set when a worker panics: every `next` answers `Done` from then on, so the other
    /// workers stop claiming morsels of a run whose result is discarded.
    failed: AtomicBool,
    /// Counts the events that can end a wait: a pipeline finishing or exhausting its source, a
    /// publish, a close and a failure.
    epoch: AtomicU64,
    // shared-state-ok: parks idle workers and guards no data; `wake_idle` and `park` state how.
    idle: Mutex<()>,
    wake: Condvar,
    /// How many workers are in `park`, which a test reads to publish only once every worker
    /// waits. It is counted in production builds too, two atomic updates per park, because the
    /// shared-state check cannot read a struct with a `#[cfg(test)]` field.
    parked: AtomicUsize,
}

/// What reached a pipeline before it started: the union of the regions published to it, and
/// whether it was closed.
struct Early {
    region: Projection,
    closed: bool,
}

/// One pipeline's standing in the [`Dispatcher`].
struct Job {
    build: Box<dyn Fn() -> Arc<dyn MorselSource> + Send + Sync>,
    finalize: Option<Box<dyn Fn() + Send + Sync>>,
    /// Pipelines waiting on this one to finish.
    dependents: Vec<usize>,
    /// Pipelines that read this one's output as it is produced.
    stream_readers: Vec<usize>,
    /// What this pipeline still waits on: each pipeline in `after` that has not finished, and
    /// one for the stream when `streams_from` is not empty and nothing has released it.
    waiting: AtomicUsize,
    /// Pipelines in `streams_from` that have not finished.
    streams_open: AtomicUsize,
    /// Whether the stream's count in `waiting` is released, which the first publish to the
    /// pipeline or the finish of its last stream does once.
    stream_released: AtomicBool,
    // shared-state-ok: the pipeline's source, set once when it starts and read by every worker
    // that claims. It answers guards that name morsels and holds no tile.
    source: OnceLock<Arc<dyn MorselSource>>,
    /// What was published to the pipeline before its source was built. `start` hands it to the
    /// source.
    // shared-state-ok: a region and a flag, written by whichever thread delivers an arrival and
    // read once by the thread that starts the pipeline. It holds no tile.
    early: Mutex<Early>,
    /// Whether the source has answered `Exhausted`, which is final.
    exhausted: AtomicBool,
    finished: AtomicBool,
    /// Morsels claimed and not acknowledged, plus claims in flight.
    outstanding: AtomicUsize,
    /// Workers that claimed from the pipeline and have not left it.
    attached: AtomicUsize,
}

impl Dispatcher {
    /// A dispatcher over `pipelines`, in plan order. A pipeline that waits on none starts now.
    fn new(pipelines: Vec<PipelineSpec>, morsel_rows: u64) -> Self {
        let mut dependents = vec![Vec::new(); pipelines.len()];
        let mut stream_readers = vec![Vec::new(); pipelines.len()];
        for (index, spec) in pipelines.iter().enumerate() {
            for (at, earlier) in spec.after.iter().enumerate() {
                assert!(
                    earlier.0 < index,
                    "a pipeline waits on earlier pipelines only, got {} after {}",
                    index,
                    earlier.0
                );
                assert!(
                    !spec.after[..at].iter().any(|a| a.0 == earlier.0),
                    "a pipeline depends on another once, got {} on {}",
                    index,
                    earlier.0
                );
                dependents[earlier.0].push(index);
            }
            for (at, earlier) in spec.streams_from.iter().enumerate() {
                assert!(
                    earlier.0 < index,
                    "a pipeline streams from earlier pipelines only, got {} from {}",
                    index,
                    earlier.0
                );
                assert!(
                    !spec.after.iter().any(|a| a.0 == earlier.0)
                        && !spec.streams_from[..at].iter().any(|s| s.0 == earlier.0),
                    "a pipeline depends on another once, got {} on {}",
                    index,
                    earlier.0
                );
                stream_readers[earlier.0].push(index);
            }
        }
        let jobs: Vec<Job> = pipelines
            .into_iter()
            .zip(dependents.into_iter().zip(stream_readers))
            .map(|(spec, (dependents, stream_readers))| Job {
                waiting: AtomicUsize::new(
                    spec.after.len() + usize::from(!spec.streams_from.is_empty()),
                ),
                streams_open: AtomicUsize::new(spec.streams_from.len()),
                // A pipeline with no stream has none to release.
                stream_released: AtomicBool::new(spec.streams_from.is_empty()),
                stream_readers,
                build: spec.source,
                finalize: spec.finalize,
                dependents,
                source: OnceLock::new(),
                early: Mutex::new(Early {
                    region: Projection::Nothing,
                    closed: false,
                }),
                exhausted: AtomicBool::new(false),
                finished: AtomicBool::new(false),
                outstanding: AtomicUsize::new(0),
                attached: AtomicUsize::new(0),
            })
            .collect();
        static DISPATCHERS: AtomicU64 = AtomicU64::new(0);
        let dispatcher = Self {
            id: DISPATCHERS.fetch_add(1, Ordering::Relaxed),
            unfinished: AtomicUsize::new(jobs.len()),
            jobs,
            morsel_rows,
            failed: AtomicBool::new(false),
            epoch: AtomicU64::new(0),
            idle: Mutex::new(()),
            wake: Condvar::new(),
            parked: AtomicUsize::new(0),
        };
        for index in 0..dispatcher.jobs.len() {
            if dispatcher.jobs[index].waiting.load(Ordering::Relaxed) == 0 {
                dispatcher.start(index);
            }
        }
        dispatcher
    }

    /// Build the pipeline's source, which makes its morsels claimable, and hand it what reached
    /// the pipeline before it started.
    ///
    /// The early state stays locked until the source is set, so a publish either lands in it
    /// before the source reads it or finds the source set.
    fn start(&self, index: usize) {
        let job = &self.jobs[index];
        debug_assert_eq!(
            job.waiting.load(Ordering::Acquire),
            0,
            "a pipeline starts once it waits on nothing"
        );
        let early = job.early.lock_wait();
        let source = (job.build)();
        source.publish(&early.region);
        if early.closed {
            source.close();
        }
        assert!(job.source.set(source).is_ok(), "a pipeline starts once");
    }

    /// Release the wait of pipeline `index` for its stream, once: the first publish to it, or
    /// the finish of the last pipeline it streams from, whichever comes first. The thread that
    /// releases its last wait starts it.
    fn release_stream(&self, index: usize) {
        let job = &self.jobs[index];
        // A pipeline whose stream is released, or that has none, is published to without an
        // atomic update.
        if job.stream_released.load(Ordering::Acquire)
            || job.stream_released.swap(true, Ordering::AcqRel)
        {
            return;
        }
        if job.waiting.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.start(index);
        }
    }

    /// The keys `arrived` have been added to the pipeline's source: unite the region into what
    /// the source can hand out, and wake the workers parked for want of a morsel.
    ///
    /// The caller has written the rows and made their keys ready before it calls, and holds
    /// no lock this call takes: the pipeline's early state, the source's state, the lock the
    /// source's yield-predicate function reads, and the lock that parks idle workers. The source
    /// takes the region under its own lock, and the epoch moves after that, so a worker that finds
    /// no morsel in its claim read the epoch before the move and its park returns at once.
    ///
    /// A publish that releases a pipeline's last wait starts it on the publishing thread: the
    /// pipeline's source builder runs inside this call, under the contract stated at
    /// [`PipelineSpec::source`].
    fn publish(&self, pipeline: PipelineId, arrived: &Projection) {
        let job = &self.jobs[pipeline.0];
        debug_assert!(
            !job.finished.load(Ordering::Acquire),
            "a pipeline is published to before it finishes"
        );
        {
            let mut early = job.early.lock_wait();
            match job.source.get() {
                Some(source) => {
                    drop(early);
                    source.publish(arrived);
                }
                None => early.region = early.region.union(arrived),
            }
        }
        // The region is in the early state before the wait is released, so the source built
        // by the release is handed it.
        self.release_stream(pipeline.0);
        self.wake_idle();
    }

    /// No row will be added to the pipeline's source, which makes its claim `Exhausted` once
    /// every published row is claimed. It follows the last publish, and a second call changes
    /// nothing.
    fn close(&self, pipeline: PipelineId) {
        let job = &self.jobs[pipeline.0];
        {
            let mut early = job.early.lock_wait();
            match job.source.get() {
                Some(source) => {
                    drop(early);
                    source.close();
                }
                None => early.closed = true,
            }
        }
        self.wake_idle();
    }

    /// The next morsel of a started pipeline that has one, trying `prefer` first: a worker
    /// stays on its pipeline while the pipeline has morsels, which keeps its chain, the rows it
    /// reads and its partial in one cache.
    ///
    /// `Wait` when no started pipeline has a morsel and some pipeline has not finished.
    fn next(&self, prefer: Option<PipelineId>) -> Next {
        'scan: loop {
            if self.failed.load(Ordering::Acquire) || self.unfinished.load(Ordering::Acquire) == 0 {
                return Next::Done;
            }
            for index in prefer.map(|p| p.0).into_iter().chain(0..self.jobs.len()) {
                let job = &self.jobs[index];
                let Some(source) = job.source.get() else {
                    continue;
                };
                if job.exhausted.load(Ordering::Acquire) {
                    continue;
                }
                // Counted before the claim, so a thread that finds the source exhausted and no
                // outstanding morsel knows no claim is in flight.
                job.outstanding.fetch_add(1, Ordering::AcqRel);
                match source.claim(self.morsel_rows) {
                    Claim::Morsel(guard) => {
                        return Next::Package(WorkPackage {
                            pipeline: PipelineId(index),
                            guard,
                        });
                    }
                    // A row may still arrive: the pipeline stays open, and a publish or a close
                    // wakes the worker that parks on it.
                    Claim::Idle => {
                        job.outstanding.fetch_sub(1, Ordering::AcqRel);
                        // Another worker's claim can have found the source exhausted while
                        // this one was in flight and counted, and its finish attempt then saw
                        // this claim outstanding. This decrement is the last event that can
                        // complete the pipeline, so the attempt is made here.
                        if job.exhausted.load(Ordering::Acquire) && self.try_finish(index) {
                            continue 'scan;
                        }
                    }
                    Claim::Exhausted => {
                        job.outstanding.fetch_sub(1, Ordering::AcqRel);
                        // A worker parked while attached to this pipeline has to leave it
                        // before it can finish, so the exhaustion wakes it.
                        if !job.exhausted.swap(true, Ordering::AcqRel) {
                            self.wake_idle();
                        }
                        // Finishing may start pipelines, which the scan must see.
                        if self.try_finish(index) {
                            continue 'scan;
                        }
                    }
                }
            }
            return Next::Wait;
        }
    }

    /// Finish the pipeline if it is complete and no one has: its source is exhausted, every
    /// morsel is acknowledged, and every worker has left it. The caller that finishes it runs
    /// its `finalize`, starts the pipelines waiting on it, and wakes idle workers.
    fn try_finish(&self, index: usize) -> bool {
        let job = &self.jobs[index];
        // Read in this order: an exhausted source answers no further claim. Every claim that
        // answered a morsel counted itself before it asked, and attached before it
        // acknowledged, so nothing outstanding and no worker attached leaves nothing to wait
        // for.
        let complete = job.exhausted.load(Ordering::Acquire)
            && job.outstanding.load(Ordering::Acquire) == 0
            && job.attached.load(Ordering::Acquire) == 0;
        if !complete || job.finished.swap(true, Ordering::AcqRel) {
            return false;
        }
        if let Some(finalize) = &job.finalize {
            finalize();
        }
        // The closing follows the finalize and the last publish, which are the breaker's:
        // nothing more reaches a pipeline that reads the stream once its last stream is done. A
        // pipeline that was never published to starts here. Closing first builds it already closed;
        // the order is not otherwise observable at the source.
        for &reader in &job.stream_readers {
            if self.jobs[reader]
                .streams_open
                .fetch_sub(1, Ordering::AcqRel)
                == 1
            {
                self.close(PipelineId(reader));
                self.release_stream(reader);
            }
        }
        for &dependent in &job.dependents {
            if self.jobs[dependent].waiting.fetch_sub(1, Ordering::AcqRel) == 1 {
                self.start(dependent);
            }
        }
        self.unfinished.fetch_sub(1, Ordering::AcqRel);
        self.wake_idle();
        true
    }

    /// Record that `package`'s morsel is in the breaker and released.
    fn ack(&self, package: WorkPackage) {
        let before = self.jobs[package.pipeline.0]
            .outstanding
            .fetch_sub(1, Ordering::AcqRel);
        debug_assert!(
            before > 0,
            "a package is acknowledged once, after it was claimed"
        );
        self.try_finish(package.pipeline.0);
    }

    /// Whether `pipeline` has finished.
    #[cfg(test)]
    fn is_done(&self, pipeline: PipelineId) -> bool {
        self.jobs[pipeline.0].finished.load(Ordering::Acquire)
    }

    /// Whether every pipeline has finished.
    fn all_done(&self) -> bool {
        self.unfinished.load(Ordering::Acquire) == 0
    }

    /// Stop every worker from claiming: a worker panicked.
    fn fail(&self) {
        self.failed.store(true, Ordering::Release);
        self.wake_idle();
    }

    /// Move the epoch and wake every parked worker.
    fn wake_idle(&self) {
        self.epoch.fetch_add(1, Ordering::AcqRel);
        // The lock orders this notify after a worker's check and before its wait, or after its
        // wait began.
        drop(self.idle.lock_wait());
        self.wake.notify_all();
    }

    /// Wait until the epoch moves past `seen`, which the caller read before it looked for work.
    fn park(&self, seen: u64) {
        let mut guard = self.idle.lock_wait();
        self.parked.fetch_add(1, Ordering::AcqRel);
        // `fail` moves the epoch through `wake_idle`. A worker that reads `failed` leaves even
        // when that move is lost.
        while self.epoch.load(Ordering::Acquire) == seen && !self.failed.load(Ordering::Acquire) {
            #[cfg(any(test, feature = "test-helpers"))]
            {
                let (woken, timeout) = self
                    .wake
                    .wait_timeout(guard, TEST_PARK_DEADLINE)
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                guard = woken;
                assert!(
                    !timeout.timed_out()
                        || self.epoch.load(Ordering::Acquire) != seen
                        || self.failed.load(Ordering::Acquire),
                    "a worker stayed parked for {TEST_PARK_DEADLINE:?} while the epoch stood at \
                     {seen}: a wake-up was lost"
                );
            }
            #[cfg(not(any(test, feature = "test-helpers")))]
            {
                guard = self
                    .wake
                    .wait(guard)
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
            }
        }
        self.parked.fetch_sub(1, Ordering::AcqRel);
    }

    /// One step of a worker's turn: leave each pipeline whose source is exhausted, then claim
    /// a morsel and run it through `worker`. It never parks.
    ///
    /// A pipeline finishes only when its workers have left it, so a worker leaves as soon as
    /// the source is exhausted and not when it next has nothing to do. A failed dispatcher
    /// answers `Done` before the worker leaves anything: the run's result is discarded.
    ///
    /// `state` is minted by [`serve_state`](Self::serve_state) of this dispatcher and used on one
    /// thread, which a debug build checks.
    fn step(&self, worker: &mut impl PoolWorker, state: &mut ServeState) -> Step {
        debug_assert_eq!(
            state.dispatcher, self.id,
            "a serve state belongs to the dispatcher that minted it"
        );
        let me = std::thread::current().id();
        debug_assert!(
            state.owner.get_or_insert(me) == &me,
            "a serve state belongs to the thread that first stepped with it"
        );
        if self.failed.load(Ordering::Acquire) {
            return Step::Done;
        }
        for (index, held) in state.attached.iter_mut().enumerate() {
            if *held && self.jobs[index].exhausted.load(Ordering::Acquire) {
                worker.leave(PipelineId(index));
                *held = false;
                let before = self.jobs[index].attached.fetch_sub(1, Ordering::AcqRel);
                debug_assert!(before > 0, "a worker leaves a pipeline it is attached to");
                self.try_finish(index);
            }
        }
        match self.next(state.last) {
            Next::Package(package) => {
                let pipeline = package.pipeline;
                if !state.attached[pipeline.0] {
                    self.jobs[pipeline.0]
                        .attached
                        .fetch_add(1, Ordering::AcqRel);
                    state.attached[pipeline.0] = true;
                }
                state.last = Some(pipeline);
                worker.work(&package);
                self.ack(package);
                Step::Ran
            }
            Next::Wait => Step::Wait,
            Next::Done => Step::Done,
        }
    }

    /// One worker's turn: [`step`](Self::step) until every pipeline has finished or the
    /// dispatcher failed, parking when nothing is claimable.
    fn serve(&self, worker: &mut impl PoolWorker) {
        let mut state = self.serve_state();
        loop {
            // Read before the step looks for work: a wake that follows moves the epoch, and the
            // park returns at once.
            let seen = self.epoch.load(Ordering::Acquire);
            match self.step(worker, &mut state) {
                Step::Ran => {}
                Step::Wait => self.park(seen),
                Step::Done => return,
            }
        }
    }

    /// A fresh state for a worker of this dispatcher, which has run nothing.
    fn serve_state(&self) -> ServeState {
        ServeState {
            dispatcher: self.id,
            owner: None,
            attached: vec![false; self.jobs.len()],
            last: None,
        }
    }

    /// [`step`](Self::step) until nothing is claimable or the run is over: the turn of a worker
    /// that parks nowhere, because the caller delivers the arrivals that end a wait. `state`
    /// outlives the call, so a worker that is attached to a pipeline leaves it when a later
    /// call finds the source exhausted.
    ///
    /// A step that answers `Wait` after the epoch moved has already seen what ends a wait, which
    /// is what makes [`serve`](Self::serve)'s park return at once: the claim that finds a source
    /// exhausted moves the epoch, and the worker's next step leaves the pipeline and finishes
    /// it. The call takes that step instead of returning.
    ///
    /// The caller has no epoch to park on, so the `Wait` it gets is a wait only if no other
    /// thread publishes, closes, acknowledges or finishes a pipeline of this dispatcher: every
    /// call that moves the epoch is made on the thread that calls this. The threaded path, where
    /// other threads do, is `serve`.
    fn serve_until_wait(&self, worker: &mut impl PoolWorker, state: &mut ServeState) -> Settled {
        loop {
            let seen = self.epoch.load(Ordering::Acquire);
            match self.step(worker, state) {
                Step::Wait if self.epoch.load(Ordering::Acquire) == seen => return Settled::Wait,
                Step::Done => return Settled::Done,
                Step::Ran | Step::Wait => {}
            }
        }
    }
}

/// What a worker keeps between its steps on a [`Dispatcher`]: the pipelines it claimed from and
/// has not left, and the pipeline it ran last, which it tries first.
struct ServeState {
    /// The [`Dispatcher::id`] of the dispatcher that minted it.
    dispatcher: u64,
    /// The thread that first stepped with it. A state is one worker's, and a worker is a thread.
    owner: Option<std::thread::ThreadId>,
    /// Per pipeline, by `PipelineId`.
    attached: Vec<bool>,
    last: Option<PipelineId>,
}

/// What one [`Dispatcher::step`] did.
enum Step {
    /// The worker ran one morsel.
    Ran,
    /// Nothing is claimable now: a publish, a close, or a pipeline that finishes or starts may
    /// change that.
    Wait,
    /// Every pipeline has finished, or the dispatcher failed.
    Done,
}

/// What [`Dispatcher::serve_until_wait`] ends on.
enum Settled {
    /// Nothing is claimable until the caller delivers an arrival.
    Wait,
    /// Every pipeline has finished, or the dispatcher failed.
    Done,
}

/// Fails the [`Dispatcher`] when the thread holding it unwinds, so the other workers stop
/// claiming morsels instead of finishing a run whose result the panic discards.
struct FailOnUnwind<'a>(&'a Dispatcher);

impl Drop for FailOnUnwind<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.fail();
        }
    }
}

/// Where an inline run's fold leaves its answer, and the consumer that answers `main` to wake.
struct FoldedResult {
    // shared-state-ok: the fold's combined answer, set once when its pipeline finishes and read
    // by the producer that answers `main`.
    tile: Mutex<Option<Tile>>,
    // shared-state-ok: the consumer of `main`, woken when the answer is set. It holds no tile.
    consumer: Mutex<Box<dyn Consumer>>,
}

impl FoldedResult {
    fn new(consumer: Box<dyn Consumer>) -> Arc<Self> {
        Arc::new(Self {
            tile: Mutex::new(None),
            consumer: Mutex::new(consumer),
        })
    }

    /// Leave the answer and wake the consumer of `main`.
    fn set(&self, tile: Tile) {
        *self.tile.lock_wait() = Some(tile);
        self.consumer.lock_wait().notify(&Projection::Everything);
    }
}

/// The producer that answers `main` for a fold of an inline run: nothing before the fold finishes,
/// then its answer until it is released.
struct FoldedResultProducer {
    base: ProducerBase,
    result: Arc<FoldedResult>,
}

impl TileProducer for FoldedResultProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        match self.result.tile.lock_wait().clone() {
            Some(tile) => tile,
            None => self.tiling().empty_tile(),
        }
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
        *self.result.tile.lock_wait() = None;
    }
}

/// What one [`PooledRun::lap`] did.
#[derive(PartialEq, Debug)]
pub enum Lap {
    /// A worker's turn ran at least one morsel.
    Ran,
    /// Nothing is claimable until an arrival is published.
    Idle,
    /// Every pipeline has finished.
    Done,
    /// The dispatcher failed, so the run's answer is discarded: a worker panicked on another
    /// thread, or a delivery did.
    Failed,
}

/// A program's pipelines on the pool, served by the thread that calls [`lap`](Self::lap): one
/// worker, no threads. The scheduler loop delivers the arrivals, the lap runs every morsel they
/// made claimable, and `main` is read through a producer of the final breaker's output on the
/// driver thread, so the loop pulls `main` as it pulls a serial one.
/// See `src/interpreter/design-parallel.md`, "The inline driver".
pub struct PooledRun {
    /// Answers `main` until [`take_main`](Self::take_main) hands it to the driver.
    main: Option<Box<dyn TileProducer>>,
    /// The one worker's chain of each pipeline.
    chains: Vec<Box<dyn TileProducer>>,
    dispatcher: Arc<Dispatcher>,
    breakers: Vec<PoolBreaker>,
    partials: Vec<Option<Tile>>,
    state: ServeState,
    /// The sources of the pipelines that read one and whose arrivals have not ended, with what
    /// delivers to them. A lap closes one that says it is complete.
    open_sources: Vec<(PipelineHandle, Arc<dyn MorselSource>)>,
    // Dropped after the chains, which hold records with the sources, and after the taken chains'
    // operators, which the pool owns from the cut.
    _records: PooledRecords,
    _taken: HashMap<NodeId, Taken>,
}

impl PooledRun {
    /// Plan `program`, take it from the scheduler loop, subscribe its pipelines and seed the
    /// ones that read a data source, or say why the program is not one the pool runs. A refused
    /// program keeps its producer. `main_consumer` is woken when `main` has something to pull.
    ///
    /// A range ends by exhaustion. A pipeline over a source whose rows arrive from outside stays
    /// open, and its `main` is not terminal, until a lap sees the source's yield predicate cover
    /// every key ([`MorselSource::is_complete`]).
    pub fn start(
        ctx: &mut GlobalContext,
        program: &mut CompiledProgram,
        main_producer: &mut Option<Box<dyn TileProducer>>,
        config: &Config,
        main_consumer: Box<dyn Consumer>,
    ) -> Result<Self, Unsupported> {
        let plan = plan(&program.operator_graph)?;
        let output = program
            .main_mut()
            .ok_or_else(|| Unsupported("the program has no `main` output".into()))?;
        check_pipelines(&*output.op)?;
        let dropped = main_producer.take().or_else(|| output.producer.take());
        debug_assert!(
            dropped.is_some(),
            "the pool drops the producer that held the pipeline's record"
        );
        drop(dropped);
        let main_tiling = output.op.tiling().clone();
        let mut consumer = Some(main_consumer);
        let mut started = None;
        let mut start_chain = |chain: &mut Box<dyn TileOperator>| {
            let mut taken = HashMap::new();
            cut(chain, &mut taken);
            started = Some(start_planned(
                ctx,
                &plan,
                chain,
                taken,
                config,
                main_tiling.clone(),
                consumer.take().expect("the main chain is visited once"),
            ));
        };
        match plan.main().breaker {
            Breaker::Collect => start_chain(&mut output.op),
            Breaker::Fold { .. } => output.op.visit_inputs_mut(&mut |fold| {
                fold.visit_inputs_mut(&mut |input| start_chain(input));
            }),
            Breaker::Materialize { .. } => unreachable!("`main` is not a memo's input"),
        }
        Ok(started.expect("the main chain was visited"))
    }

    /// The pool's part of one pass of the scheduler loop, between the delivery and the pulls of the
    /// mains: a lap of `run` and the sinks it woke, and whether either did anything. Without a run
    /// it does nothing and leaves the sink pulls queued for the next delivery, so a program the
    /// pool refused passes as the plain loop passes it.
    pub fn serve_pass(run: Option<&mut Self>, scheduler: &mut Scheduler) -> bool {
        match run {
            Some(run) => {
                let ran = run.lap() == Lap::Ran;
                scheduler.pull_sinks() || ran
            }
            None => false,
        }
    }

    /// The producer that answers `main`, for the driver to pull.
    pub fn take_main(&mut self) -> Box<dyn TileProducer> {
        self.main.take().expect("`main` is taken once")
    }

    /// Serve every morsel the arrivals published so far, on this thread, and say what happened.
    /// A panic in a worker's chain fails the dispatcher and is raised here.
    pub fn lap(&mut self) -> Lap {
        let _fail = FailOnUnwind(&self.dispatcher);
        // A source whose yield predicate covers every key has delivered everything: what it
        // holds is published, and nothing else ends it.
        self.open_sources.retain(|(handle, source)| {
            let complete = source.is_complete();
            if complete {
                handle.publish(&Projection::Everything);
                handle.close();
            }
            !complete
        });
        let mut worker = MainWorker {
            chains: &mut self.chains,
            breakers: &self.breakers,
            partials: &mut self.partials,
            worked: 0,
        };
        let settled = self
            .dispatcher
            .serve_until_wait(&mut worker, &mut self.state);
        let worked = worker.worked;
        match (settled, worked) {
            (Settled::Done, _) if self.dispatcher.failed.load(Ordering::Acquire) => Lap::Failed,
            (Settled::Done, _) => Lap::Done,
            (Settled::Wait, 0) => Lap::Idle,
            (Settled::Wait, _) => Lap::Ran,
        }
    }
}

/// Subscribe `plan`'s pipelines over the chains the cut left, on one worker, and answer `main`
/// from the final breaker.
fn start_planned(
    ctx: &mut GlobalContext,
    plan: &Plan,
    main_chain: &mut Box<dyn TileOperator>,
    mut taken: HashMap<NodeId, Taken>,
    config: &Config,
    main_tiling: Tiling,
    main_consumer: Box<dyn Consumer>,
) -> PooledRun {
    enum Reads {
        Rows(Arc<Materialized>),
        Folded(Arc<FoldedResult>),
    }
    let mut main_chain = Some(main_chain);
    let mut main_consumer = Some(main_consumer);
    let mut reads = None;
    let (mut runs, mut notified, mut close_at_start) = (Vec::new(), Vec::new(), Vec::new());
    let mut sources = Vec::new();
    {
        let mut upstream: HashMap<NodeId, &mut Taken> =
            taken.iter_mut().map(|(k, v)| (*k, v)).collect();
        for pipeline in &plan.pipelines {
            let (chain, breaker): (&mut dyn TileOperator, PoolBreaker) = match &pipeline.breaker {
                Breaker::Materialize { memo } => {
                    let taken = upstream
                        .remove(memo)
                        .expect("the cut took the memo's input");
                    (
                        &mut *taken.chain,
                        PoolBreaker::Materialize {
                            output: taken.output.clone(),
                        },
                    )
                }
                Breaker::Collect => {
                    let chain = main_chain.take().expect("one pipeline ends in `main`");
                    let output = Materialized::new(chain.tiling().clone());
                    reads = Some(Reads::Rows(output.clone()));
                    (&mut **chain, PoolBreaker::Materialize { output })
                }
                Breaker::Fold { kind, accumulator } => {
                    let chain = main_chain.take().expect("one pipeline ends in `main`");
                    let result = FoldedResult::new(
                        main_consumer.take().expect("the consumer is taken once"),
                    );
                    reads = Some(Reads::Folded(result.clone()));
                    let breaker = PoolBreaker::Fold {
                        kind: *kind,
                        seed: kind.initial_accumulator(accumulator),
                        partials: Arc::new(Mutex::new(Vec::new())),
                        result: Some(result),
                    };
                    (&mut **chain, breaker)
                }
            };
            let source = source_of(&*chain).expect("the pipeline was checked to read one source");
            notified.push(pipeline.head == Head::Source);
            // A range ends by exhaustion. A source whose rows arrive from outside stays open
            // until it says it is complete ([`PooledRun::lap`]).
            close_at_start.push(false);
            sources.push(source.clone());
            runs.push(PipelineRun {
                chain,
                source,
                breaker,
                head: pipeline.head,
                after: Vec::new(),
                streams_from: pipeline
                    .streams_from
                    .iter()
                    .map(|&i| PipelineId(i))
                    .collect(),
            });
        }
    }
    let one_worker = Config {
        threads: 1,
        morsel_rows: config.morsel_rows,
    };
    let Prepared {
        dispatcher,
        handles,
        mut chains,
        records,
        breakers,
    } = prepare(ctx.scheduler(), runs, &one_worker, notified, close_at_start);
    let open_sources = handles
        .iter()
        .zip(sources)
        .zip(&plan.pipelines)
        .filter(|(_, pipeline)| pipeline.head == Head::Source)
        .map(|((handle, source), _)| (handle.clone(), source))
        .collect();
    // The reader registers before the first morsel, so no row leaves before it has read.
    let main = match reads.expect("one pipeline ends in `main`") {
        Reads::Rows(output) => BreakerOutput::new(output, main_tiling.clone(), false, None)
            .subscribe(
                main_tiling.universal_guard(),
                main_consumer.take().expect("the consumer is taken once"),
                ctx.scheduler(),
            ),
        Reads::Folded(result) => Box::new(FoldedResultProducer {
            base: ProducerBase::new(
                FoldedResultProducer::alloc_id(),
                &main_tiling,
                &OperatorBase::new(main_tiling.clone()),
                ctx.scheduler(),
            ),
            result,
        }),
    };
    let state = dispatcher.serve_state();
    PooledRun {
        main: Some(main),
        chains: chains.pop().expect("one worker"),
        partials: breakers
            .iter()
            .map(|breaker| match breaker {
                PoolBreaker::Fold { seed, .. } => Some(seed.clone()),
                PoolBreaker::Collect { .. } | PoolBreaker::Materialize { .. } => None,
            })
            .collect(),
        dispatcher,
        breakers,
        state,
        open_sources,
        _records: records,
        _taken: taken,
    }
}

#[cfg(test)]
#[path = "parallel_live_tests.rs"]
mod live_tests;

#[cfg(test)]
#[path = "parallel_source_tests.rs"]
mod source_tests;

#[cfg(test)]
#[path = "parallel_inline_tests.rs"]
mod inline_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::{
        IterateExtent, LiveSource, RangeSource, uint_keys_in, uint_range, zip_arms_at,
    };
    use crate::interpreter::{BaseType, CurryLevel, Extent};
    use crate::interpreter::{FunctionGuard, Predicate, Value};
    use intervalsets::Bounding;
    use std::collections::BTreeSet;
    use std::sync::mpsc;
    use std::time::Duration;

    const MAIN_PIPELINE: PipelineId = PipelineId(0);

    /// The `[first, last]` a morsel's guard names.
    fn bounds(guard: &TileGuard) -> (u64, u64) {
        let TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(set))) = guard else {
            panic!("a morsel is a domain interval");
        };
        let [interval] = set.intervals().as_slice() else {
            panic!("a morsel is one interval");
        };
        let value = |v: Option<&Value>| match v {
            Some(Value::UInt(n)) => *n,
            other => panic!("a position, got {other:?}"),
        };
        (value(interval.lval()), value(interval.rval()))
    }

    fn package(next: Next) -> WorkPackage {
        match next {
            Next::Package(package) => package,
            Next::Wait => panic!("expected a morsel, got Wait"),
            Next::Done => panic!("expected a morsel, got Done"),
        }
    }

    /// A worker that records what it ran and what it left, and optionally holds its first
    /// morsel until `gate` answers.
    #[derive(Default)]
    struct Recorder {
        morsels: Vec<(usize, (u64, u64))>,
        left: Vec<usize>,
        gate: Option<mpsc::Receiver<()>>,
    }

    impl PoolWorker for Recorder {
        fn work(&mut self, package: &WorkPackage) {
            self.morsels
                .push((package.pipeline.0, bounds(&package.guard)));
            if let Some(gate) = self.gate.take() {
                gate.recv().ok();
            }
        }

        fn leave(&mut self, pipeline: PipelineId) {
            self.left.push(pipeline.0);
        }
    }

    type Log = Arc<Mutex<Vec<String>>>;

    /// A dispatcher over a pipeline per entry of `rows`, each waiting on the pipelines
    /// `after` names, that logs `start i` when it starts and `finish i` when it finishes.
    fn graph(rows: &[u64], after: &[&[usize]], log: &Log) -> Dispatcher {
        let specs = rows
            .iter()
            .enumerate()
            .map(|(i, &n)| {
                let (started, finished) = (log.clone(), log.clone());
                PipelineSpec {
                    after: after[i].iter().map(|&a| PipelineId(a)).collect(),
                    streams_from: Vec::new(),
                    source: Box::new(move || {
                        started.lock_wait().push(format!("start {i}"));
                        Arc::new(RangeSource::new(n))
                    }),
                    finalize: Some(Box::new(move || {
                        finished.lock_wait().push(format!("finish {i}"));
                    })),
                }
            })
            .collect();
        Dispatcher::new(specs, 4)
    }

    fn dispatcher(rows: u64, morsel_rows: u64) -> Dispatcher {
        Dispatcher::new(
            vec![PipelineSpec {
                after: Vec::new(),
                streams_from: Vec::new(),
                source: Box::new(move || Arc::new(RangeSource::new(rows))),
                finalize: None,
            }],
            morsel_rows,
        )
    }

    fn position(log: &Log, event: &str) -> usize {
        log.lock_wait()
            .iter()
            .position(|e| e == event)
            .unwrap_or_else(|| panic!("`{event}` is in {:?}", log.lock_wait()))
    }

    #[test]
    fn morsels_are_disjoint_and_cover_the_range() {
        let dispatcher = dispatcher(10, 4);
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        assert_eq!(worker.morsels, [(0, (0, 3)), (0, (4, 7)), (0, (8, 9))]);
        assert_eq!(worker.left, [0]);
        assert!(dispatcher.is_done(MAIN_PIPELINE) && dispatcher.all_done());
    }

    #[test]
    fn an_empty_range_finishes_the_pipeline_when_first_asked() {
        let dispatcher = dispatcher(0, 4);
        assert!(
            !dispatcher.is_done(MAIN_PIPELINE),
            "a source is exhausted once it says so"
        );
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A claimed morsel keeps the pipeline from finishing until it is acknowledged, though the
    /// source is exhausted.
    #[test]
    fn a_claimed_morsel_keeps_the_pipeline_open_until_acknowledged() {
        let dispatcher = dispatcher(1, 4);
        let claimed = package(dispatcher.next(None));
        assert!(matches!(dispatcher.next(None), Next::Wait));
        assert!(!dispatcher.is_done(MAIN_PIPELINE));
        dispatcher.ack(claimed);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
        assert!(matches!(dispatcher.next(None), Next::Done));
    }

    /// After a failure `next` answers `Done`, whatever the source still holds.
    #[test]
    fn a_failed_dispatcher_hands_out_nothing() {
        let dispatcher = dispatcher(10, 4);
        dispatcher.fail();
        assert!(matches!(dispatcher.next(None), Next::Done));
    }

    /// A panicking worker stops the others from claiming.
    #[test]
    fn a_panicking_worker_stops_the_others_claiming() {
        let dispatcher = dispatcher(1000, 4);
        std::thread::scope(|scope| {
            let panicking = scope.spawn(|| {
                let _fail = FailOnUnwind(&dispatcher);
                panic!("a worker's chain panicked");
            });
            assert!(panicking.join().is_err());
            let mut worker = Recorder::default();
            dispatcher.serve(&mut worker);
            assert!(worker.morsels.is_empty());
        });
    }

    #[test]
    fn a_pipeline_waits_for_the_one_it_follows() {
        let log = Log::default();
        let dispatcher = graph(&[10, 6], &[&[], &[0]], &log);
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        assert_eq!(
            *log.lock_wait(),
            ["start 0", "finish 0", "start 1", "finish 1"]
        );
        assert_eq!(
            worker.morsels,
            [
                (0, (0, 3)),
                (0, (4, 7)),
                (0, (8, 9)),
                (1, (0, 3)),
                (1, (4, 5))
            ]
        );
        assert_eq!(worker.left, [0, 1]);
    }

    /// A pipeline with no rows finishes when asked, which starts the pipelines behind it.
    #[test]
    fn an_empty_pipeline_starts_the_ones_behind_it() {
        let log = Log::default();
        let dispatcher = graph(&[0, 0, 5], &[&[], &[0], &[1]], &log);
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        assert_eq!(worker.morsels, [(2, (0, 3)), (2, (4, 4))]);
        assert!(dispatcher.all_done());
        assert_eq!(
            log.lock_wait().len(),
            6,
            "every pipeline started and finished"
        );
    }

    /// A pipeline waiting on two starts after both have finished.
    #[test]
    fn a_pipeline_starts_after_every_pipeline_it_follows() {
        let log = Log::default();
        let dispatcher = graph(&[4, 4, 4, 4], &[&[], &[0], &[0], &[1, 2]], &log);
        dispatcher.serve(&mut Recorder::default());
        assert!(position(&log, "start 3") > position(&log, "finish 1"));
        assert!(position(&log, "start 3") > position(&log, "finish 2"));
        assert!(position(&log, "start 1") > position(&log, "finish 0"));
        assert!(position(&log, "start 2") > position(&log, "finish 0"));
    }

    /// A pipeline the plan puts before the one it follows is refused: dependencies run
    /// forward, so they form no cycle.
    #[test]
    #[should_panic(expected = "earlier pipelines only")]
    fn a_dependency_on_a_later_pipeline_is_refused() {
        graph(&[1, 1], &[&[1], &[]], &Log::default());
    }

    /// A worker stays on its pipeline while it has morsels, and a worker told to prefer a
    /// pipeline takes from it first.
    #[test]
    fn a_worker_stays_on_the_pipeline_it_is_on() {
        let log = Log::default();
        let independent = graph(&[8, 8], &[&[], &[]], &log);
        assert_eq!(package(independent.next(Some(PipelineId(1)))).pipeline.0, 1);
        assert_eq!(package(independent.next(None)).pipeline.0, 0);
        let again = graph(&[8, 8], &[&[], &[]], &log);
        let mut worker = Recorder::default();
        again.serve(&mut worker);
        let order: Vec<usize> = worker.morsels.iter().map(|(p, _)| *p).collect();
        assert_eq!(
            order,
            [0, 0, 1, 1],
            "pipeline 0 is drained before pipeline 1"
        );
    }

    /// Workers on a chain of two pipelines claim every position of each once, start each
    /// pipeline once, and leave every pipeline they claimed from before it finishes.
    #[test]
    fn concurrent_workers_run_a_chain_of_pipelines() {
        for _ in 0..10 {
            run_a_chain_concurrently();
        }
    }

    fn run_a_chain_concurrently() {
        let (rows, workers) = (20_003, 8);
        let log = Log::default();
        let dispatcher = graph(&[rows, rows], &[&[], &[0]], &log);
        let recorders: Vec<Recorder> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .map(|_| {
                    scope.spawn(|| {
                        let mut worker = Recorder::default();
                        dispatcher.serve(&mut worker);
                        worker
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("a worker returns"))
                .collect()
        });
        assert_eq!(
            *log.lock_wait(),
            ["start 0", "finish 0", "start 1", "finish 1"]
        );
        for pipeline in 0..2 {
            let mut morsels: Vec<(u64, u64)> = recorders
                .iter()
                .flat_map(|r| r.morsels.iter())
                .filter(|(p, _)| *p == pipeline)
                .map(|(_, m)| *m)
                .collect();
            morsels.sort_unstable();
            let mut next = 0;
            for (first, last) in morsels {
                assert_eq!(first, next, "pipeline {pipeline}: no gap or overlap");
                next = last + 1;
            }
            assert_eq!(next, rows);
        }
        for recorder in &recorders {
            let claimed: BTreeSet<usize> = recorder.morsels.iter().map(|(p, _)| *p).collect();
            let left: BTreeSet<usize> = recorder.left.iter().copied().collect();
            assert_eq!(
                claimed, left,
                "a worker leaves each pipeline it claimed from"
            );
            assert_eq!(recorder.left.len(), left.len(), "and leaves it once");
        }
    }

    /// The positions that are ready at a live source, which the test advances.
    struct ReadyPositions {
        ready: Mutex<Predicate>,
        next: AtomicU64,
    }

    type Ready = Arc<ReadyPositions>;

    /// A live source over the positions that are ready, as a pipeline's source.
    fn live_source() -> (Arc<LiveSource>, Ready) {
        let ready = Arc::new(ReadyPositions {
            ready: Mutex::new(Predicate::False),
            next: AtomicU64::new(0),
        });
        let read = ready.clone();
        let source = Arc::new(LiveSource::new(
            move || read.ready.lock_wait().clone(),
            uint_keys_in,
        ));
        (source, ready)
    }

    /// `count` positions arrive after the ones that did and are published to `pipeline`, as the
    /// delivering thread does: the rows first, then the region.
    fn arrive(dispatcher: &Dispatcher, pipeline: PipelineId, ready: &Ready, count: u64) {
        let first = ready.next.fetch_add(count, Ordering::AcqRel);
        let region = uint_range(first, first + count - 1);
        {
            let mut all = ready.ready.lock_wait();
            *all = all.union(&region);
        }
        dispatcher.publish(pipeline, &Projection::admitting(region));
    }

    fn live_dispatcher(source: &Arc<LiveSource>, morsel_rows: u64) -> Dispatcher {
        let source: Arc<dyn MorselSource> = source.clone();
        Dispatcher::new(
            vec![PipelineSpec {
                after: Vec::new(),
                streams_from: Vec::new(),
                source: Box::new(move || source.clone()),
                finalize: None,
            }],
            morsel_rows,
        )
    }

    /// A pipeline over a live source answers `Wait` while nothing is published, hands out each
    /// arrival once it is published, and finishes when the source is closed and drained.
    #[test]
    fn a_live_pipeline_hands_out_arrivals_and_finishes_when_closed() {
        let (source, rows) = live_source();
        let dispatcher = live_dispatcher(&source, 4);
        assert!(matches!(dispatcher.next(None), Next::Wait));
        arrive(&dispatcher, MAIN_PIPELINE, &rows, 6);
        let first = package(dispatcher.next(None));
        assert_eq!(bounds(&first.guard), (0, 3));
        let second = package(dispatcher.next(None));
        assert_eq!(bounds(&second.guard), (4, 5));
        assert!(
            matches!(dispatcher.next(None), Next::Wait),
            "open and drained"
        );
        dispatcher.ack(first);
        dispatcher.ack(second);
        assert!(
            !dispatcher.is_done(MAIN_PIPELINE),
            "an arrival may still come"
        );
        dispatcher.close(MAIN_PIPELINE);
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A dispatcher whose second pipeline, over `source`, starts once the first, a finite one,
    /// has finished.
    fn live_behind_another(source: &Arc<LiveSource>, morsel_rows: u64) -> Dispatcher {
        let live: Arc<dyn MorselSource> = source.clone();
        Dispatcher::new(
            vec![
                PipelineSpec {
                    after: Vec::new(),
                    streams_from: Vec::new(),
                    source: Box::new(|| Arc::new(RangeSource::new(1))),
                    finalize: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
                    streams_from: Vec::new(),
                    source: Box::new(move || live.clone()),
                    finalize: None,
                },
            ],
            morsel_rows,
        )
    }

    /// The morsels of the live pipeline that `serve` ran.
    fn live_morsels(dispatcher: &Dispatcher) -> Vec<(u64, u64)> {
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        worker
            .morsels
            .iter()
            .filter(|(p, _)| *p == 1)
            .map(|(_, b)| *b)
            .collect()
    }

    /// Regions published to a pipeline that has not started are united, and the source claims
    /// the union.
    #[test]
    fn regions_published_before_the_pipeline_starts_are_united() {
        let (source, ready) = live_source();
        let dispatcher = live_behind_another(&source, 8);
        arrive(&dispatcher, PipelineId(1), &ready, 2);
        arrive(&dispatcher, PipelineId(1), &ready, 3);
        dispatcher.close(PipelineId(1));
        assert_eq!(live_morsels(&dispatcher), [(0, 4)]);
    }

    /// An `Everything` published before the pipeline starts is resolved when the source is built,
    /// to the positions ready then.
    #[test]
    fn an_everything_published_before_the_pipeline_starts_covers_what_is_ready_by_then() {
        let (source, ready) = live_source();
        let dispatcher = live_behind_another(&source, 8);
        *ready.ready.lock_wait() = uint_range(0, 3);
        dispatcher.publish(PipelineId(1), &Projection::Everything);
        *ready.ready.lock_wait() = uint_range(0, 5);
        dispatcher.close(PipelineId(1));
        assert_eq!(live_morsels(&dispatcher), [(0, 5)]);
    }

    /// Poll `condition` until it holds, failing after ten seconds. The limit is under the
    /// watchdog's `DEADLINE`, so a condition that never holds fails naming itself.
    fn wait_until(condition: impl Fn() -> bool) {
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        while !condition() {
            assert!(
                std::time::Instant::now() < deadline,
                "the condition did not hold within ten seconds"
            );
            std::thread::yield_now();
        }
    }

    /// A worker with nothing to claim wakes when a region is published, runs it while the source
    /// is open, and returns once the source is closed.
    #[test]
    fn a_parked_worker_wakes_on_a_publish_and_on_a_close() {
        let (source, rows) = live_source();
        let dispatcher = live_dispatcher(&source, 4);
        within_deadline_on(
            "a_parked_worker_wakes_on_a_publish_and_on_a_close",
            &dispatcher,
            DEADLINE,
            || {
                std::thread::scope(|scope| {
                    // A failed wait fails the dispatcher, which wakes the parked worker, so the scope
                    // joins it instead of hanging.
                    let _fail = FailOnUnwind(&dispatcher);
                    let worker = scope.spawn(|| {
                        let mut worker = Recorder::default();
                        dispatcher.serve(&mut worker);
                        worker
                    });
                    let claimed = |count: u64| {
                        let source = source.clone();
                        move || uint_keys_in(&source.claimed(), u64::MAX).len() as u64 >= count
                    };
                    arrive(&dispatcher, MAIN_PIPELINE, &rows, 3);
                    wait_until(claimed(3));
                    assert!(
                        !worker.is_finished(),
                        "the source is open, so the worker waits"
                    );
                    arrive(&dispatcher, MAIN_PIPELINE, &rows, 2);
                    wait_until(claimed(5));
                    assert!(!worker.is_finished(), "the source is still open");
                    dispatcher.close(MAIN_PIPELINE);
                    let worker = worker
                        .join()
                        .expect("the worker returns once the source is closed");
                    let ran: Vec<_> = worker.morsels.iter().map(|(_, b)| *b).collect();
                    assert_eq!(ran, [(0, 2), (3, 4)]);
                    assert_eq!(worker.left, [0], "it left the pipeline before it finished");
                    assert!(dispatcher.all_done());
                })
            },
        );
    }

    /// A worker that serves through repeated `serve_until_wait` calls, with the state carried
    /// between them, runs the morsels `serve` runs and leaves the pipelines `serve` leaves, in
    /// the same order.
    #[test]
    fn serve_until_wait_runs_what_serve_runs() {
        let served = {
            let dispatcher = dispatcher(10, 4);
            let mut worker = Recorder::default();
            dispatcher.serve(&mut worker);
            worker
        };
        let dispatcher = dispatcher(10, 4);
        let (mut worker, mut state) = (Recorder::default(), dispatcher.serve_state());
        assert!(matches!(
            dispatcher.serve_until_wait(&mut worker, &mut state),
            Settled::Done
        ));
        assert_eq!(worker.morsels, served.morsels);
        assert_eq!(worker.left, served.left);
        assert!(dispatcher.all_done());
    }

    /// Over a live source one worker stops at each `Wait`, resumes when an arrival is published,
    /// and leaves the pipeline in the call that finds the source closed, which is the sequence
    /// `serve` gives for the same arrivals.
    #[test]
    fn serve_until_wait_waits_on_a_live_source_and_resumes_from_its_state() {
        let served = {
            let (source, rows) = live_source();
            let dispatcher = live_dispatcher(&source, 4);
            arrive(&dispatcher, MAIN_PIPELINE, &rows, 4);
            arrive(&dispatcher, MAIN_PIPELINE, &rows, 4);
            dispatcher.close(MAIN_PIPELINE);
            let mut worker = Recorder::default();
            dispatcher.serve(&mut worker);
            worker
        };
        let (source, rows) = live_source();
        let dispatcher = live_dispatcher(&source, 4);
        let (mut worker, mut state) = (Recorder::default(), dispatcher.serve_state());
        assert!(
            matches!(
                dispatcher.serve_until_wait(&mut worker, &mut state),
                Settled::Wait
            ),
            "nothing is published"
        );
        for _ in 0..2 {
            arrive(&dispatcher, MAIN_PIPELINE, &rows, 4);
            assert!(matches!(
                dispatcher.serve_until_wait(&mut worker, &mut state),
                Settled::Wait
            ));
        }
        assert!(worker.left.is_empty(), "the source is open");
        dispatcher.close(MAIN_PIPELINE);
        assert!(matches!(
            dispatcher.serve_until_wait(&mut worker, &mut state),
            Settled::Done
        ));
        assert_eq!(worker.morsels, served.morsels);
        assert_eq!(worker.left, served.left);
    }

    /// The plan classifies every operator kind the corpus of compiled programs holds on purpose:
    /// exactly six are admitted in a chain, and every other kind is refused with its own name.
    #[test]
    fn every_operator_kind_the_corpus_holds_is_classified_on_purpose() {
        use crate::interpreter::tile_operators::visit_inputs_tests::survey;
        let (kinds, _) = survey();
        let mut admitted = Vec::new();
        for kind in kinds {
            match classify(kind) {
                Class::Streaming(_) | Class::Source | Class::Cut => admitted.push(kind),
                Class::Memo | Class::Operand | Class::Extract | Class::Fold => {}
                Class::Refuse(reason) => assert!(
                    reason.contains(kind),
                    "a refusal names the operator it refuses: {reason}"
                ),
            }
        }
        assert_eq!(
            admitted,
            [
                "FanOutSlot",
                "IterateExtent",
                "MapResult",
                "MapResultWithSource",
                "VariantProject",
                "VariantWrap"
            ],
            "only the streaming operators, the sources and the slots are admitted"
        );
    }

    /// A chain that reads a value another reads is two pipelines: the one that feeds the `Memo`
    /// materializes, and the one behind it streams from it.
    #[test]
    fn a_chain_that_reads_a_shared_value_is_planned_as_two_pipelines() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        let mut ctx = GlobalContext::default();
        let loaded = LoadedProgram::test("xs = [x + 1 for x in [1, 2, 3, 4]]\n[a * 2 for a in xs]");
        let compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).expect("compiles");
        let planned = plan(&compiled.operator_graph).expect("a shared chain is two pipelines");
        assert_eq!(planned.pipeline_count(), 2);
        let (upstream, downstream) = (&planned.pipelines[0], &planned.pipelines[1]);
        assert!(upstream.head == Head::Source);
        assert!(matches!(upstream.breaker, Breaker::Materialize { .. }));
        assert!(upstream.streams_from.is_empty());
        assert!(downstream.head == Head::Breaker);
        assert!(matches!(downstream.breaker, Breaker::Collect));
        assert_eq!(downstream.streams_from, [0]);
    }

    /// A `Memo` is read by one slot of a plan: planning the chain that reads it again is refused.
    #[test]
    fn a_memo_read_by_a_second_slot_of_the_plan_is_refused() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        let mut ctx = GlobalContext::default();
        let loaded = LoadedProgram::test("xs = [x + 1 for x in [1, 2, 3, 4]]\n[a * 2 for a in xs]");
        let compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).expect("compiles");
        let graph = &compiled.operator_graph;
        let by_id = graph
            .nodes()
            .iter()
            .map(|node| match node {
                GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => (*id, node),
            })
            .collect();
        let top = graph
            .nodes()
            .iter()
            .find_map(|node| match node {
                GraphNode::Sink { input, .. } => Some(input.subscribed),
                GraphNode::Operator { .. } => None,
            })
            .expect("a main sink");
        let mut planner = Planner {
            by_id,
            pipelines: Vec::new(),
            memos: HashSet::new(),
        };
        planner
            .pipeline(top, Breaker::Collect)
            .expect("the first slot");
        let refused = planner
            .pipeline(top, Breaker::Collect)
            .expect_err("the same memo again");
        assert!(
            refused.to_string().contains("more than one slot"),
            "{refused}"
        );
    }

    /// The cut replaces the slot with a `BreakerOutput`, takes the chain that fed the `Memo`, and
    /// leaves no slot in the chains it hands back.
    #[test]
    fn the_cut_takes_the_chain_behind_a_memo_and_leaves_a_breaker_output() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        fn kinds(op: &dyn TileOperator, found: &mut Vec<&'static str>) {
            found.push(op.kind());
            op.visit_inputs(&mut |edge| kinds(edge.target, found));
        }
        let mut ctx = GlobalContext::default();
        let loaded = LoadedProgram::test("xs = [x + 1 for x in [1, 2, 3]]\n[a * 2 for a in xs]");
        let mut compiled = compile_program(&mut ctx, &loaded, Box::new(|| {})).expect("compiles");
        let planned = plan(&compiled.operator_graph).expect("two pipelines");
        assert_eq!(planned.pipelines.len(), 2);
        let main = compiled.main_mut().expect("a main output");
        assert_eq!(check_pipelines(&*main.op).ok(), Some(1));

        let mut taken = HashMap::new();
        cut(&mut main.op, &mut taken);

        let mut behind = Vec::new();
        kinds(&*main.op, &mut behind);
        assert!(behind.contains(&"BreakerOutput"), "{behind:?}");
        assert!(!behind.contains(&"FanOutSlot"), "{behind:?}");
        let [taken] = <[_; 1]>::try_from(taken.into_values().collect::<Vec<_>>())
            .ok()
            .expect("one memo, one chain");
        let mut before = Vec::new();
        kinds(&*taken.chain, &mut before);
        assert!(before.contains(&"IterateExtent"), "{before:?}");
        assert!(!before.contains(&"BreakerOutput"), "{before:?}");
    }

    /// A serve state names the dispatcher that minted it, so a state of another dispatcher with
    /// as many pipelines is rejected, and not stepped as if its attachments were this one's.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a serve state belongs to the dispatcher that minted it")]
    fn a_serve_state_of_another_dispatcher_of_the_same_size_is_rejected() {
        let (a, b) = (dispatcher(4, 4), dispatcher(4, 4));
        let mut state = a.serve_state();
        b.step(&mut Recorder::default(), &mut state);
    }

    /// A serve state is one worker's, and a worker is a thread.
    #[test]
    #[cfg(debug_assertions)]
    fn a_serve_state_stepped_on_a_second_thread_is_rejected() {
        let dispatcher = dispatcher(8, 4);
        let mut state = dispatcher.serve_state();
        dispatcher.step(&mut Recorder::default(), &mut state);
        let panic = match std::thread::scope(|scope| {
            scope
                .spawn(|| dispatcher.step(&mut Recorder::default(), &mut state))
                .join()
        }) {
            Err(panic) => panic,
            Ok(_) => panic!("the second thread's step panics"),
        };
        let message = match panic.downcast_ref::<String>() {
            Some(message) => message.as_str(),
            None => panic
                .downcast_ref::<&str>()
                .copied()
                .expect("an assertion message"),
        };
        assert!(
            message.contains("belongs to the thread that first stepped"),
            "{message}"
        );
    }

    /// A failed dispatcher answers `Done` before the worker leaves anything or claims a morsel.
    #[test]
    fn a_failed_dispatcher_ends_the_turn_before_the_worker_leaves() {
        let dispatcher = dispatcher(4, 4);
        let (mut worker, mut state) = (Recorder::default(), dispatcher.serve_state());
        // One morsel, run; the source is exhausted at the next claim, and the worker is attached.
        assert!(matches!(
            dispatcher.step(&mut worker, &mut state),
            Step::Ran
        ));
        assert!(matches!(dispatcher.next(None), Next::Wait));
        dispatcher.fail();
        assert!(matches!(
            dispatcher.serve_until_wait(&mut worker, &mut state),
            Settled::Done
        ));
        assert!(worker.left.is_empty(), "nothing is left on a failed run");
    }

    /// A pipeline over a source that logs `start {name}` when it starts and `finish {name}` when it
    /// finishes.
    fn logged(
        name: &'static str,
        log: &Log,
        after: &[usize],
        streams_from: &[usize],
        source: impl Fn() -> Arc<dyn MorselSource> + Send + Sync + 'static,
    ) -> PipelineSpec {
        let (started, finished) = (log.clone(), log.clone());
        PipelineSpec {
            after: after.iter().map(|&a| PipelineId(a)).collect(),
            streams_from: streams_from.iter().map(|&a| PipelineId(a)).collect(),
            source: Box::new(move || {
                started.lock_wait().push(format!("start {name}"));
                source()
            }),
            finalize: Some(Box::new(move || {
                finished.lock_wait().push(format!("finish {name}"));
            })),
        }
    }

    fn started(log: &Log, name: &str) -> bool {
        log.lock_wait().contains(&format!("start {name}"))
    }

    /// A pipeline that streams from a finite one starts at the first publish to it, while the
    /// pipeline it streams from has a morsel running.
    #[test]
    fn a_streaming_pipeline_starts_at_the_first_publish_before_the_upstream_finishes() {
        let log = Log::default();
        let (source, rows) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                logged("up", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("down", &log, &[], &[0], move || live.clone()),
            ],
            4,
        );
        let running = package(dispatcher.next(None));
        assert_eq!(running.pipeline.0, 0);
        assert!(!started(&log, "down"), "nothing was published");
        arrive(&dispatcher, PipelineId(1), &rows, 2);
        assert!(started(&log, "down"));
        assert!(
            !dispatcher.is_done(PipelineId(0)),
            "the upstream still has a morsel running"
        );
        let down = package(dispatcher.next(Some(PipelineId(1))));
        assert_eq!((down.pipeline.0, bounds(&down.guard)), (1, (0, 1)));
        dispatcher.ack(running);
        dispatcher.ack(down);
    }

    /// A pipeline that streams from one that publishes nothing starts when that one finishes,
    /// with its source closed, and finishes without a morsel.
    #[test]
    fn a_streaming_pipeline_starts_at_the_upstream_finish_when_nothing_was_published() {
        let log = Log::default();
        let (source, _) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                logged("up", &log, &[], &[], || Arc::new(RangeSource::new(0))),
                logged("down", &log, &[], &[0], move || live.clone()),
            ],
            4,
        );
        assert!(!started(&log, "down"));
        // Not `serve`: a pipeline that is not closed would park the worker for good.
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(
            position(&log, "finish up") < position(&log, "start down"),
            "{:?}",
            log.lock_wait()
        );
        assert!(dispatcher.all_done());
    }

    /// A pipeline that streams from one upstream and follows a build side does not start while
    /// the build side is unfinished, though a region was published to it and its upstream
    /// finished. It starts when the build side finishes, and its source holds the region.
    #[test]
    fn a_published_pipeline_stays_blocked_while_a_build_side_is_unfinished() {
        let log = Log::default();
        let (source, rows) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                logged("build", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("up", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("probe", &log, &[0], &[1], move || live.clone()),
            ],
            4,
        );
        let build = package(dispatcher.next(Some(PipelineId(0))));
        let up = package(dispatcher.next(Some(PipelineId(1))));
        assert_eq!((build.pipeline.0, up.pipeline.0), (0, 1));
        arrive(&dispatcher, PipelineId(2), &rows, 3);
        dispatcher.ack(up);
        assert!(matches!(dispatcher.next(None), Next::Wait));
        assert!(
            dispatcher.is_done(PipelineId(1)),
            "the stream's upstream finished"
        );
        assert!(
            !started(&log, "probe"),
            "the build side is unfinished: {:?}",
            log.lock_wait()
        );
        dispatcher.ack(build);
        assert!(started(&log, "probe"));
        assert!(
            position(&log, "finish build") < position(&log, "start probe"),
            "{:?}",
            log.lock_wait()
        );
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        assert_eq!(
            worker.morsels,
            [(2, (0, 2))],
            "the region published while blocked"
        );
    }

    /// A pipeline streaming from two upstreams is closed when the last of them finishes, and not
    /// when the first does: a region published after the first finished is claimed, and the
    /// pipeline stays open until the second finishes.
    #[test]
    fn a_stream_from_two_pipelines_closes_when_the_last_finishes() {
        let log = Log::default();
        let (source, rows) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                logged("a", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("b", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("down", &log, &[], &[0, 1], move || live.clone()),
            ],
            4,
        );
        arrive(&dispatcher, PipelineId(2), &rows, 2);
        let a = package(dispatcher.next(Some(PipelineId(0))));
        let b = package(dispatcher.next(Some(PipelineId(1))));
        let down = package(dispatcher.next(Some(PipelineId(2))));
        dispatcher.ack(a);
        dispatcher.ack(down);
        assert!(matches!(dispatcher.next(None), Next::Wait), "b is running");
        assert!(dispatcher.is_done(PipelineId(0)));
        assert!(
            !dispatcher.is_done(PipelineId(2)),
            "the second upstream is running"
        );

        arrive(&dispatcher, PipelineId(2), &rows, 2);
        let later = package(dispatcher.next(Some(PipelineId(2))));
        assert_eq!(
            (later.pipeline.0, bounds(&later.guard)),
            (2, (2, 3)),
            "a region published after the first upstream finished"
        );
        dispatcher.ack(later);
        dispatcher.ack(b);
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(dispatcher.all_done());
    }

    /// The source builder of a pipeline runs on the thread whose publish released the pipeline's
    /// last wait, so the builder is under the contract of a publisher.
    #[test]
    fn the_builder_of_a_streaming_pipeline_runs_on_the_publishing_thread() {
        let built_on = Arc::new(Mutex::new(None));
        let (source, rows) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let recorded = built_on.clone();
        let dispatcher = Dispatcher::new(
            vec![
                PipelineSpec {
                    after: Vec::new(),
                    streams_from: Vec::new(),
                    source: Box::new(|| Arc::new(RangeSource::new(1))),
                    finalize: None,
                },
                PipelineSpec {
                    after: Vec::new(),
                    streams_from: vec![PipelineId(0)],
                    source: Box::new(move || {
                        *recorded.lock_wait() = Some(std::thread::current().id());
                        live.clone()
                    }),
                    finalize: None,
                },
            ],
            4,
        );
        let publisher = std::thread::scope(|scope| {
            scope
                .spawn(|| {
                    arrive(&dispatcher, PipelineId(1), &rows, 1);
                    std::thread::current().id()
                })
                .join()
                .expect("the publisher returns")
        });
        assert_eq!(*built_on.lock_wait(), Some(publisher));
        assert_ne!(publisher, std::thread::current().id());
    }

    /// Make the keys `first..=last` ready at a live source and publish them to `pipeline`.
    fn arrive_keys(dispatcher: &Dispatcher, pipeline: PipelineId, ready: &Ready, keys: (u64, u64)) {
        let region = uint_range(keys.0, keys.1);
        {
            let mut all = ready.ready.lock_wait();
            *all = all.union(&region);
        }
        dispatcher.publish(pipeline, &Projection::admitting(region));
    }

    /// An upstream worker that publishes the keys of each morsel it ran to the pipeline behind
    /// it, either as it runs them or all at once when it leaves, and records what the downstream
    /// pipeline's morsels held.
    struct Publishing<'a> {
        dispatcher: &'a Dispatcher,
        ready: &'a Ready,
        per_morsel: bool,
        held: Vec<(u64, u64)>,
        downstream: Vec<(u64, u64)>,
    }

    impl PoolWorker for Publishing<'_> {
        fn work(&mut self, package: &WorkPackage) {
            let keys = bounds(&package.guard);
            match package.pipeline.0 {
                0 if self.per_morsel => {
                    arrive_keys(self.dispatcher, PipelineId(1), self.ready, keys)
                }
                0 => self.held.push(keys),
                _ => self.downstream.push(keys),
            }
        }

        fn leave(&mut self, pipeline: PipelineId) {
            if pipeline.0 == 0 {
                for keys in self.held.drain(..) {
                    arrive_keys(self.dispatcher, PipelineId(1), self.ready, keys);
                }
            }
        }
    }

    /// Run `body` on a thread of its own and fail if it does not finish within a minute, which
    /// is how a lost wake-up shows.
    fn finishes_within_a_minute<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
        let (done, finished) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = done.send(body());
        });
        finished
            .recv_timeout(Duration::from_secs(60))
            .expect("the run finished: a lost wake-up leaves a worker parked")
    }

    /// One round: `threads` workers over an upstream of `rows` positions and a downstream that
    /// streams from it. Every downstream position is claimed once, and the downstream finishes
    /// after the upstream.
    fn stream_round(threads: usize, rows: u64, per_morsel: bool) {
        let log = Log::default();
        let (source, ready) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                logged("up", &log, &[], &[], move || {
                    Arc::new(RangeSource::new(rows))
                }),
                logged("down", &log, &[], &[0], move || live.clone()),
            ],
            4,
        );
        let claimed: Vec<(u64, u64)> = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..threads)
                .map(|_| {
                    scope.spawn(|| {
                        let _fail = FailOnUnwind(&dispatcher);
                        let mut worker = Publishing {
                            dispatcher: &dispatcher,
                            ready: &ready,
                            per_morsel,
                            held: Vec::new(),
                            downstream: Vec::new(),
                        };
                        dispatcher.serve(&mut worker);
                        worker.downstream
                    })
                })
                .collect();
            workers
                .into_iter()
                .flat_map(|worker| worker.join().expect("a worker returns"))
                .collect()
        });
        let mut positions: Vec<u64> = claimed.iter().flat_map(|&(a, b)| a..=b).collect();
        positions.sort_unstable();
        assert_eq!(
            positions,
            (0..rows).collect::<Vec<_>>(),
            "each position once"
        );
        assert!(dispatcher.all_done());
        assert!(
            position(&log, "finish up") < position(&log, "finish down"),
            "the downstream finishes last: {:?}",
            log.lock_wait()
        );
    }

    /// Eight workers, 200 rounds: the upstream's workers publish per morsel, and the downstream
    /// starts at the first publish and claims every position once.
    #[test]
    fn a_stream_published_per_morsel_is_claimed_once_across_threads() {
        finishes_within_a_minute(|| (0..200).for_each(|_| stream_round(8, 64, true)));
    }

    /// The same when each upstream worker publishes everything it ran when it leaves.
    #[test]
    fn a_stream_published_when_the_workers_leave_is_claimed_once_across_threads() {
        finishes_within_a_minute(|| (0..200).for_each(|_| stream_round(8, 64, false)));
    }

    /// A worker of the upstream panics while a pipeline streams from it and nothing was
    /// published: the dispatcher fails, every other worker gets `Done`, and none stays parked.
    #[test]
    fn a_panicking_upstream_worker_fails_a_streaming_dispatcher() {
        struct PanicsOnce<'a>(&'a AtomicBool);
        impl PoolWorker for PanicsOnce<'_> {
            fn work(&mut self, _package: &WorkPackage) {
                assert!(
                    self.0.swap(true, Ordering::AcqRel),
                    "the first morsel panics"
                );
            }

            fn leave(&mut self, _pipeline: PipelineId) {}
        }
        finishes_within_a_minute(|| {
            let log = Log::default();
            let (source, _) = live_source();
            let live: Arc<dyn MorselSource> = source.clone();
            let dispatcher = Dispatcher::new(
                vec![
                    logged("up", &log, &[], &[], || Arc::new(RangeSource::new(64))),
                    logged("down", &log, &[], &[0], move || live.clone()),
                ],
                4,
            );
            let panicked = AtomicBool::new(false);
            let results: Vec<_> = std::thread::scope(|scope| {
                let workers: Vec<_> = (0..4)
                    .map(|_| {
                        scope.spawn(|| {
                            let _fail = FailOnUnwind(&dispatcher);
                            dispatcher.serve(&mut PanicsOnce(&panicked));
                        })
                    })
                    .collect();
                workers.into_iter().map(|worker| worker.join()).collect()
            });
            assert_eq!(results.iter().filter(|r| r.is_err()).count(), 1);
            assert!(!dispatcher.all_done(), "the run did not complete");
            assert!(matches!(dispatcher.next(None), Next::Done));
        });
    }

    /// A source that answers its first claim `Idle` after `hook` ran, and `Exhausted` from then
    /// on: the claim of one worker that is in flight while another worker's claim finds the
    /// source exhausted.
    struct IdleOnce {
        hook: Mutex<Option<Box<dyn FnOnce() + Send>>>,
    }

    impl MorselSource for IdleOnce {
        fn claim(&self, _rows: u64) -> Claim {
            let hook = self.hook.lock_wait().take();
            match hook {
                Some(hook) => {
                    hook();
                    Claim::Idle
                }
                None => Claim::Exhausted,
            }
        }
    }

    /// A claim that answers `Idle` while another worker's claim answers `Exhausted` leaves the
    /// pipeline complete when its in-flight count drops, and it is that decrement that finishes
    /// it: the other worker's attempt saw the claim outstanding.
    #[test]
    fn an_idle_claim_that_ends_after_the_source_was_found_exhausted_finishes_the_pipeline() {
        let handle = Arc::new(OnceLock::<Arc<Dispatcher>>::new());
        let other_worker = handle.clone();
        let source: Arc<dyn MorselSource> = Arc::new(IdleOnce {
            hook: Mutex::new(Some(Box::new(move || {
                let dispatcher = other_worker.get().expect("the dispatcher is set");
                assert!(matches!(dispatcher.next(None), Next::Wait));
                assert!(
                    !dispatcher.is_done(MAIN_PIPELINE),
                    "the first claim is still in flight"
                );
            }))),
        });
        let dispatcher = Arc::new(Dispatcher::new(
            vec![PipelineSpec {
                after: Vec::new(),
                streams_from: Vec::new(),
                source: Box::new(move || source.clone()),
                finalize: None,
            }],
            4,
        ));
        assert!(handle.set(dispatcher.clone()).is_ok());
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A worker parked with nothing claimable wakes when a publish starts a pipeline that
    /// streams from a live one, runs its morsel, and returns when the upstream closes.
    #[test]
    fn a_parked_worker_wakes_when_a_publish_starts_a_streaming_pipeline() {
        let log = Log::default();
        let (up_source, up_rows) = live_source();
        let (down_source, down_rows) = live_source();
        let (up, down): (Arc<dyn MorselSource>, Arc<dyn MorselSource>) =
            (up_source.clone(), down_source.clone());
        let dispatcher = Dispatcher::new(
            vec![
                logged("up", &log, &[], &[], move || up.clone()),
                logged("down", &log, &[], &[0], move || down.clone()),
            ],
            4,
        );
        within_deadline_on(
            "a_parked_worker_wakes_when_a_publish_starts_a_streaming_pipeline",
            &dispatcher,
            DEADLINE,
            || {
                std::thread::scope(|scope| {
                    let _fail = FailOnUnwind(&dispatcher);
                    let worker = scope.spawn(|| {
                        let mut worker = Recorder::default();
                        dispatcher.serve(&mut worker);
                        worker
                    });
                    wait_until(|| dispatcher.parked.load(Ordering::Acquire) == 1);
                    arrive(&dispatcher, PipelineId(1), &down_rows, 2);
                    wait_until(|| uint_keys_in(&down_source.claimed(), u64::MAX).len() == 2);
                    assert!(!worker.is_finished(), "the upstream is open");
                    arrive(&dispatcher, PipelineId(0), &up_rows, 1);
                    dispatcher.close(PipelineId(0));
                    wait_until(|| worker.is_finished());
                    let worker = worker
                        .join()
                        .expect("the worker returns once both are closed");
                    assert_eq!(worker.morsels, [(1, (0, 1)), (0, (0, 0))]);
                    assert!(dispatcher.all_done());
                })
            },
        );
    }

    #[test]
    #[should_panic(expected = "a pipeline streams from earlier pipelines only")]
    fn a_pipeline_streaming_from_a_later_one_is_rejected() {
        let log = Log::default();
        Dispatcher::new(
            vec![
                logged("a", &log, &[], &[1], || Arc::new(RangeSource::new(1))),
                logged("b", &log, &[], &[], || Arc::new(RangeSource::new(1))),
            ],
            4,
        );
    }

    #[test]
    #[should_panic(expected = "a pipeline depends on another once")]
    fn a_pipeline_that_follows_and_streams_from_one_pipeline_is_rejected() {
        let log = Log::default();
        Dispatcher::new(
            vec![
                logged("a", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("b", &log, &[0], &[0], || Arc::new(RangeSource::new(1))),
            ],
            4,
        );
    }

    #[test]
    #[should_panic(expected = "a pipeline depends on another once")]
    fn a_pipeline_that_follows_one_pipeline_twice_is_rejected() {
        let log = Log::default();
        Dispatcher::new(
            vec![
                logged("a", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("b", &log, &[0, 0], &[], || Arc::new(RangeSource::new(1))),
            ],
            4,
        );
    }

    #[test]
    #[should_panic(expected = "a pipeline depends on another once")]
    fn a_pipeline_that_streams_from_one_pipeline_twice_is_rejected() {
        let log = Log::default();
        Dispatcher::new(
            vec![
                logged("a", &log, &[], &[], || Arc::new(RangeSource::new(1))),
                logged("b", &log, &[], &[0, 0], || Arc::new(RangeSource::new(1))),
            ],
            4,
        );
    }

    /// What reaches a pipeline before it starts is kept for its source: an arrival published to
    /// a pipeline behind another is claimed once the first finishes.
    #[test]
    fn a_region_published_before_the_pipeline_starts_is_kept() {
        let (source, rows) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![
                PipelineSpec {
                    after: Vec::new(),
                    streams_from: Vec::new(),
                    source: Box::new(|| Arc::new(RangeSource::new(2))),
                    finalize: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
                    streams_from: Vec::new(),
                    source: Box::new(move || live.clone()),
                    finalize: None,
                },
            ],
            4,
        );
        let behind = PipelineId(1);
        arrive(&dispatcher, behind, &rows, 3);
        dispatcher.close(behind);
        let mut worker = Recorder::default();
        dispatcher.serve(&mut worker);
        let behind_ran: Vec<_> = worker
            .morsels
            .iter()
            .filter(|(p, _)| *p == 1)
            .map(|(_, b)| *b)
            .collect();
        assert_eq!(behind_ran, [(0, 2)]);
        assert!(dispatcher.all_done());
    }

    /// How long a test that parks workers may take before its watchdog fails the dispatcher.
    const DEADLINE: Duration = Duration::from_secs(30);

    /// Run `body` with a watchdog beside it: when `body` has not returned within `limit`, the
    /// watchdog fails `dispatcher`, which wakes every worker parked on it, so a body that waits
    /// to join them returns, and the test then fails with `name` and the limit instead of
    /// hanging. A body that panics stops the watchdog and is raised again.
    ///
    /// The wake is the dispatcher's own epoch move, which a lost wake-up in the code under test
    /// would defeat; such a defect fails the test only where the workers' own waits end.
    fn within_deadline_on<R>(
        name: &str,
        dispatcher: &Dispatcher,
        limit: Duration,
        body: impl FnOnce() -> R,
    ) -> R {
        let (stop, stopped) = mpsc::channel::<()>();
        let expired = AtomicBool::new(false);
        let expired = &expired;
        let result = std::thread::scope(|scope| {
            scope.spawn(move || {
                if stopped.recv_timeout(limit).is_err() {
                    expired.store(true, Ordering::Release);
                    dispatcher.fail();
                }
            });
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(body));
            let _ = stop.send(());
            result
        });
        match (result, expired.load(Ordering::Acquire)) {
            (Ok(result), false) => result,
            (_, true) => panic!(
                "{name} did not finish within {limit:?}: the dispatcher was failed to wake its \
                 parked workers"
            ),
            (Err(panic), false) => std::panic::resume_unwind(panic),
        }
    }

    /// The watchdog fails the dispatcher when the body outlasts its limit, and the test fails by
    /// name: a worker parked on a pipeline nothing ever publishes to is woken by it.
    #[test]
    #[should_panic(expected = "a_test_that_parks_forever did not finish")]
    fn the_deadline_helper_fails_a_body_that_outlasts_its_limit() {
        let log = Log::default();
        let (source, _) = live_source();
        let live: Arc<dyn MorselSource> = source.clone();
        let dispatcher = Dispatcher::new(
            vec![logged("only", &log, &[], &[], move || live.clone())],
            4,
        );
        within_deadline_on(
            "a_test_that_parks_forever",
            &dispatcher,
            Duration::from_millis(50),
            || {
                std::thread::scope(|scope| {
                    scope.spawn(|| dispatcher.serve(&mut Recorder::default()));
                })
            },
        );
    }

    /// A worker with nothing to claim parks while another holds a morsel of the pipeline it
    /// waits on, and the finish that morsel allows wakes it to run the next pipeline.
    #[test]
    fn an_idle_worker_parks_until_a_pipeline_finishes() {
        let log = Log::default();
        let dispatcher = graph(&[1, 4], &[&[], &[0]], &log);
        let (release, gate) = mpsc::channel();
        within_deadline_on(
            "an_idle_worker_parks_until_a_pipeline_finishes",
            &dispatcher,
            DEADLINE,
            || {
                std::thread::scope(|scope| {
                    let holder = scope.spawn(|| {
                        let mut worker = Recorder {
                            gate: Some(gate),
                            ..Recorder::default()
                        };
                        dispatcher.serve(&mut worker);
                        worker
                    });
                    std::thread::sleep(Duration::from_millis(20));
                    let idle = scope.spawn(|| {
                        let mut worker = Recorder::default();
                        dispatcher.serve(&mut worker);
                        worker
                    });
                    std::thread::sleep(Duration::from_millis(20));
                    assert!(
                        !idle.is_finished(),
                        "nothing is claimable, so the worker parks"
                    );
                    assert!(!dispatcher.is_done(MAIN_PIPELINE));
                    release.send(()).expect("the holder is waiting");
                    let (holder, idle) =
                        (holder.join().expect("holder"), idle.join().expect("idle"));
                    let second: Vec<_> = holder
                        .morsels
                        .iter()
                        .chain(&idle.morsels)
                        .filter(|(p, _)| *p == 1)
                        .collect();
                    assert_eq!(second.len(), 1, "the second pipeline's morsel ran once");
                    assert!(dispatcher.all_done());
                })
            },
        );
    }

    /// A failure wakes a parked worker, which returns without claiming.
    #[test]
    fn a_failure_wakes_a_parked_worker() {
        let dispatcher = graph(&[1, 4], &[&[], &[0]], &Log::default());
        let (release, gate) = mpsc::channel();
        std::thread::scope(|scope| {
            let holder = scope.spawn(|| {
                let mut worker = Recorder {
                    gate: Some(gate),
                    ..Recorder::default()
                };
                dispatcher.serve(&mut worker);
            });
            std::thread::sleep(Duration::from_millis(20));
            let idle = scope.spawn(|| {
                let mut worker = Recorder::default();
                dispatcher.serve(&mut worker);
                worker.morsels.len()
            });
            std::thread::sleep(Duration::from_millis(20));
            assert!(!idle.is_finished());
            dispatcher.fail();
            assert_eq!(idle.join().expect("idle returns"), 0);
            release.send(()).expect("the holder is waiting");
            holder.join().expect("holder returns");
        });
    }

    /// A worker parked while attached wakes when another worker exhausts the source after it
    /// read the epoch: the exhaustion moves the epoch, and the worker then leaves, which
    /// finishes the pipeline.
    #[test]
    fn exhaustion_after_the_epoch_read_wakes_an_attached_worker() {
        let dispatcher = dispatcher(4, 4);
        // The attached worker's one morsel is done and acknowledged.
        let claimed = package(dispatcher.next(None));
        dispatcher.jobs[0].attached.fetch_add(1, Ordering::AcqRel);
        dispatcher.ack(claimed);
        let seen = dispatcher.epoch.load(Ordering::Acquire);
        // Another worker's claim ends the source. The attached worker keeps the pipeline open.
        assert!(matches!(dispatcher.next(None), Next::Wait));
        assert!(!dispatcher.is_done(MAIN_PIPELINE));
        std::thread::scope(|scope| {
            let parked = scope.spawn(|| dispatcher.park(seen));
            std::thread::sleep(Duration::from_millis(20));
            assert!(parked.is_finished(), "the epoch moved after it was read");
        });
        dispatcher.jobs[0].attached.fetch_sub(1, Ordering::AcqRel);
        assert!(dispatcher.try_finish(0));
        assert!(matches!(dispatcher.next(None), Next::Done));
    }

    /// `finalize` runs after every morsel of its pipeline has run, whatever the interleaving.
    #[test]
    fn finalize_runs_after_every_morsel_has_run() {
        let (rows, morsel_rows, workers) = (1003u64, 4u64, 8);
        for _ in 0..30 {
            let worked = Arc::new(AtomicUsize::new(0));
            let checked = worked.clone();
            let dispatcher = Dispatcher::new(
                vec![PipelineSpec {
                    after: Vec::new(),
                    streams_from: Vec::new(),
                    source: Box::new(move || Arc::new(RangeSource::new(rows))),
                    finalize: Some(Box::new(move || {
                        assert_eq!(
                            checked.load(Ordering::Acquire) as u64,
                            rows.div_ceil(morsel_rows),
                            "a morsel was still running"
                        );
                    })),
                }],
                morsel_rows,
            );
            std::thread::scope(|scope| {
                for _ in 0..workers {
                    scope.spawn(|| {
                        let mut worker = Counting(worked.clone());
                        dispatcher.serve(&mut worker);
                    });
                }
            });
            assert!(dispatcher.all_done());
        }
    }

    /// Counts the morsels it runs.
    struct Counting(Arc<AtomicUsize>);

    impl PoolWorker for Counting {
        fn work(&mut self, _package: &WorkPackage) {
            self.0.fetch_add(1, Ordering::AcqRel);
        }

        fn leave(&mut self, _pipeline: PipelineId) {}
    }

    /// A pipeline between two others has no rows, which finishes it on a worker's first ask
    /// while the others claim: every position of the last pipeline still runs once.
    #[test]
    fn concurrent_workers_run_through_an_empty_pipeline() {
        for _ in 0..30 {
            let log = Log::default();
            let dispatcher = graph(&[2003, 0, 2003], &[&[], &[0], &[1]], &log);
            let positions = AtomicUsize::new(0);
            std::thread::scope(|scope| {
                for _ in 0..8 {
                    scope.spawn(|| {
                        let mut worker = Recorder::default();
                        dispatcher.serve(&mut worker);
                        let ran: u64 = worker
                            .morsels
                            .iter()
                            .filter(|(p, _)| *p == 2)
                            .map(|(_, (first, last))| last - first + 1)
                            .sum();
                        positions.fetch_add(ran as usize, Ordering::AcqRel);
                    });
                }
            });
            assert_eq!(positions.load(Ordering::Acquire), 2003);
            assert_eq!(log.lock_wait().len(), 6);
        }
    }

    /// A `finalize` that panics fails the run: the other workers return without finishing.
    #[test]
    fn a_panicking_finalize_stops_the_other_workers() {
        let dispatcher = Dispatcher::new(
            vec![
                PipelineSpec {
                    after: Vec::new(),
                    streams_from: Vec::new(),
                    source: Box::new(|| Arc::new(RangeSource::new(40))),
                    finalize: Some(Box::new(|| panic!("the breaker's combine failed"))),
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
                    streams_from: Vec::new(),
                    source: Box::new(|| Arc::new(RangeSource::new(40))),
                    finalize: None,
                },
            ],
            4,
        );
        let outcomes: Vec<bool> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..4)
                .map(|_| {
                    scope.spawn(|| {
                        let _fail = FailOnUnwind(&dispatcher);
                        dispatcher.serve(&mut Recorder::default());
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().is_ok())
                .collect()
        });
        assert_eq!(
            outcomes.iter().filter(|ok| !**ok).count(),
            1,
            "one worker ran it"
        );
        assert!(!dispatcher.all_done());
        assert!(!dispatcher.is_done(PipelineId(1)));
    }

    fn iterate(extent: Extent) -> Box<dyn TileOperator> {
        Box::new(IterateExtent::new(extent))
    }

    #[test]
    fn the_source_is_the_one_leaf_that_cuts_morsels() {
        let source = source_of(&*iterate(Extent::uint_range(6))).expect("a finite range");
        assert!(source.claim(4).morsel().is_some());
    }

    #[test]
    fn a_chain_with_no_source_that_cuts_morsels_is_refused() {
        let refused = source_of(&*iterate(Extent::Base(BaseType::Int)))
            .err()
            .expect("an unbounded extent has no morsels");
        assert!(refused.to_string().contains("no source"), "{refused}");
    }

    #[test]
    fn a_chain_with_two_sources_is_refused() {
        let zipped = zip_arms_at(
            vec![
                iterate(Extent::uint_range(6)),
                iterate(Extent::uint_range(6)),
            ],
            CurryLevel::new(1),
        );
        let refused = source_of(&*zipped)
            .err()
            .expect("a pipeline is cut at one source");
        assert!(refused.to_string().contains("several sources"), "{refused}");
    }

    #[test]
    fn a_range_to_the_largest_position_is_cut_without_overflow() {
        let dispatcher = dispatcher(u64::MAX, u64::MAX);
        let claimed = package(dispatcher.next(None));
        assert_eq!(bounds(&claimed.guard), (0, u64::MAX - 1));
    }
}

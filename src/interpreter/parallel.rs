//! Morsel-driven execution of a program's pipelines, single-threaded: the dispatcher hands out
//! morsels and the scheduler loop's own thread runs them ([`PooledRun::lap`]).
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use std::{
    collections::{HashMap, HashSet},
    fmt,
    sync::{
        Arc, Mutex, OnceLock,
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
        Consumer, DataSourceDomainExtentImpl, LockNow, Materialized, PooledRecords, Predicate,
        Projection, Scheduler, Tile, TileGuard, Tiling,
        operator_graph::{EdgeKind, EdgeRole, GraphNode, OperatorGraph},
        sinks::SinkConsumer,
        tile_operators::{
            BreakerHandle, BreakerOutput, Claim, LiveSource, MorselSource, Round, Sunk,
            TileOperator, TileProducer,
        },
    },
};

/// How many rows a morsel holds.
pub struct Config {
    /// Rows per morsel: the row range a work package names, which the driver pulls through the
    /// chain at once.
    pub morsel_rows: u64,
}

impl Config {
    /// The variable naming the rows per morsel.
    pub const MORSEL_ROWS: &str = "CAMBRA_MORSEL_ROWS";

    /// Read the configuration from the environment: 4096 rows unless set. A value that does not
    /// parse, or a zero, reads as the default.
    pub fn from_env() -> Self {
        let morsel_rows = std::env::var(Self::MORSEL_ROWS)
            .ok()
            .and_then(|value| value.parse().ok())
            .filter(|rows| *rows > 0)
            .unwrap_or(4096);
        Self { morsel_rows }
    }
}

/// Why a program's outputs cannot run on the dispatcher: the plan supports one pipeline shape,
/// and this names what the graph has instead.
#[derive(Debug)]
pub struct Unsupported(String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the program's outputs are not morsel pipelines: {}",
            self.0
        )
    }
}

/// The pipelines the plan admits, upstream first: each ends in the breaker of an output (`main` or
/// a sink) or in the input of a `Memo`.
///
/// A pipeline is a chain of streaming operators from its head to its breaker: `MapResult`s each
/// applying a `Constant` to its input, or reading a `Memo` at the keys the input iterates (a keyed
/// read), and `MapResultWithSource`s each reading a source's value at the keys of an
/// `IterateExtent` directly beneath it, among others. A head is an `IterateExtent` over a source
/// ([`Head::Source`]), or a `FanOutSlot` over a `Memo` ([`Head::Breaker`]), which the plan cuts
/// at: the pipeline that feeds the `Memo` ends in a breaker that materializes
/// ([`BreakerKind::Materialize`]). A chain with a keyed read is a [`Head::Breaker`] pipeline over the
/// memo's output that also reads the source it iterates. Every operator in a
/// chain is streaming, so a worker's chain holds no state between morsels. Which rows the source
/// enumerates, and whether it can be cut into morsels, is the source's to say
/// ([`TileOperator::morsel_source`]).
pub struct Plan {
    /// Every pipeline after the ones it streams from.
    pipelines: Vec<PipelinePlan>,
    /// The output each final pipeline answers: `main` and the sinks the plan admits, by name and
    /// by position in `pipelines`.
    outputs: Vec<(String, usize)>,
}

impl Plan {
    /// The pipeline that ends in `main`.
    pub(crate) fn main(&self) -> &PipelinePlan {
        let (_, pipeline) = self
            .outputs
            .iter()
            .find(|(name, _)| name == "main")
            .expect("a plan that runs `main` holds its pipeline");
        &self.pipelines[*pipeline]
    }

    /// What the pipeline that ends in `main` ends in.
    pub fn main_breaker(&self) -> &BreakerKind {
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
    pub(crate) breaker: BreakerKind,
    /// The pipelines, by position in the plan, whose output it reads: the pipeline of the `Memo`
    /// its head slot reads, or the one a keyed read reads, for a [`Head::Breaker`], and none for a
    /// source.
    pub(crate) streams_from: Vec<usize>,
    /// Whether the pipeline, or a pipeline it streams from, holds a `Restrict` or a
    /// `VariantProject`, which drop keys. A keyed read of such a memo is not admitted yet: the
    /// morsel can name a key between its first and last that the memo holds no row for, which the
    /// slot is believed to answer as complete and absent, as the serial memo does, and the
    /// missing-key rule is not written down.
    pub(crate) drops_keys: bool,
}

impl BreakerKind {
    /// The operator whose producer is the breaker of the pipeline, for a pipeline the dispatcher
    /// runs through the [`Breaker`] interface.
    pub(crate) fn node(&self) -> Option<NodeId> {
        match self {
            BreakerKind::Collect => None,
            BreakerKind::Fold { aggregate, .. } | BreakerKind::Group { aggregate } => {
                Some(*aggregate)
            }
            BreakerKind::Invert { converse } => Some(*converse),
            BreakerKind::Materialize { memo } => Some(*memo),
        }
    }
}

/// The breaker a morsel pipeline ends in: what the pool keeps between morsels, and how it
/// answers the `main` output.
pub enum BreakerKind {
    /// The `main` sink itself: the collection, merged morsel by morsel.
    Collect,
    /// An `Aggregate` read by an `ExtractAggregate` into `main`: the aggregate's own producer,
    /// switched to sink mode, is the breaker of the pipeline, and `main` stays the program's own
    /// producer.
    Fold {
        kind: AggregateKind,
        /// The accumulator's tiling.
        accumulator: Tiling,
        /// The `Aggregate` the pipeline ends in.
        aggregate: NodeId,
    },
    /// A `MapAggregate` read by a `MapExtractAggregate` into `main`: the operator's own producer,
    /// switched to sink mode, is the breaker of the pipeline, and `main` stays the program's own
    /// producer.
    Group {
        /// The `MapAggregate` the pipeline ends in.
        aggregate: NodeId,
    },
    /// A `Converse` that a pipeline reads the groups of: the operator's own producer, switched to
    /// sink mode, is the breaker of the pipeline over the rows it inverts, and the group values
    /// are pushed at the terminal round.
    Invert {
        /// The `Converse` the pipeline ends in.
        converse: NodeId,
    },
    /// The input of a `Memo`: the rows the pipelines that read it stream from.
    Materialize {
        /// The `Memo` the output stands for.
        memo: NodeId,
    },
}

/// The streaming operators the plan admits in a chain.
enum Streaming {
    /// Applies an operand to its `input`: the `Constant` function of a `MapResult`, read whole by
    /// every morsel, or the `Constant` of a `MapResultToConst`. A `MapResult` may instead apply a
    /// slot of a `Memo` (a keyed read, [`Planner::keyed_read`]). The field is the operand edge's
    /// name.
    Applies(&'static str),
    /// Reads a source's value at the keys of an `IterateExtent` directly beneath it.
    MapResultWithSource,
    /// A unary operator whose keys are the input's, or a subset of them, and which answers a pull
    /// at a guard from the input's answer at the same guard: `VariantWrap`, `VariantProject` and
    /// `Restrict`. A key it drops is in the guard's region and has no row. `VariantProject` and
    /// `Restrict` are the operators that drop keys ([`PipelinePlan::drops_keys`]).
    Unary,
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
    /// A `Constant`: the operand a `MapResult` or a `MapResultToConst` applies, which every
    /// morsel reads whole. It is never the head of a chain.
    Operand,
    /// The extract over a fold at the top of `main`.
    Extract,
    /// The fold an extract reads.
    Fold,
    /// The `MapExtractAggregate` over a grouped fold at the top of `main`.
    ExtractGroups,
    /// The grouped fold an `ExtractGroups` reads.
    Groups,
    /// The inversion of a collection: the head of a pipeline that reads the groups, which the
    /// plan cuts at.
    Converse,
    /// An operator the plan does not admit, and the reason.
    Refuse(String),
}

/// How the plan classifies an operator by its kind: the one table of the kinds it meets. It ends
/// in an arm that refuses, so an operator the plan has not considered is refused rather than run.
fn classify(kind: &str) -> Class {
    match kind {
        "MapResult" => Class::Streaming(Streaming::Applies("fn")),
        "MapResultToConst" => Class::Streaming(Streaming::Applies("constant")),
        "MapResultWithSource" => Class::Streaming(Streaming::MapResultWithSource),
        "VariantWrap" | "VariantProject" | "Restrict" => Class::Streaming(Streaming::Unary),
        "IterateExtent" => Class::Source,
        "FanOutSlot" => Class::Cut,
        "Memo" => Class::Memo,
        "Constant" => Class::Operand,
        "ExtractAggregate" => Class::Extract,
        "Aggregate" => Class::Fold,
        "MapExtractAggregate" => Class::ExtractGroups,
        "MapAggregate" => Class::Groups,
        "Converse" => Class::Converse,
        other => Class::Refuse(format!("`{other}` is not a streaming operator here")),
    }
}

/// Cut `graph` into the plan the inline driver runs: `main` and every sink are outputs, each
/// ending a pipeline. A sink reads its pipeline's breaker through a `BreakerOutput`
/// ([`PooledRun::start`]).
pub fn plan_inline(graph: &OperatorGraph) -> Result<Plan, Unsupported> {
    plan_outputs(graph, true)
}

fn plan_outputs(graph: &OperatorGraph, admit_sinks: bool) -> Result<Plan, Unsupported> {
    let by_id: HashMap<NodeId, &GraphNode> = graph
        .nodes()
        .iter()
        .map(|node| match node {
            GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => (*id, node),
        })
        .collect();
    let mut sinks = Vec::new();
    for node in graph.nodes() {
        if let GraphNode::Sink { name, input, .. } = node {
            if name != "main" && !admit_sinks {
                return Err(Unsupported(format!(
                    "the program also writes the sink `{name}`"
                )));
            }
            sinks.push((name.clone(), input.subscribed));
        }
    }
    if sinks.is_empty() || (!admit_sinks && sinks.iter().all(|(name, _)| name != "main")) {
        return Err(Unsupported("the program has no `main` output".into()));
    }
    let mut planner = Planner {
        by_id,
        pipelines: Vec::new(),
        memos: HashSet::new(),
        keyed_memos: HashMap::new(),
        converses: HashSet::new(),
    };
    let mut outputs = Vec::new();
    for (name, top) in sinks {
        // The breaker is read off the top of the chain: an extract over a fold, or the sink. Only
        // `main` is a fold: a sink dispatches a collection.
        let (breaker, at) = match name == "main" {
            true => planner.breaker_at(top),
            false => (BreakerKind::Collect, top),
        };
        outputs.push((name, planner.pipeline(at, breaker)?));
    }
    Ok(Plan {
        pipelines: planner.pipelines,
        outputs,
    })
}

/// The plan under construction: the graph, the pipelines planned so far, and the pipeline planned
/// for each `Memo`, so that every slot that reads one streams from the same pipeline.
struct Planner<'g> {
    by_id: HashMap<NodeId, &'g GraphNode>,
    pipelines: Vec<PipelinePlan>,
    /// The `Memo`s a slot that starts a chain reads. Such a slot takes the memo's pipeline as the
    /// chain's own upstream, so a second is refused. A memo read at keys is in `keyed_memos`
    /// instead, and any number of chains read it.
    memos: HashSet<NodeId>,
    /// The pipeline planned for each `Memo` that chains read at their own keys.
    keyed_memos: HashMap<NodeId, usize>,
    /// The `Converse`s the plan has cut at: each is read once, since the pipeline that ends in it
    /// pushes its groups to one parent.
    converses: HashSet<NodeId>,
}

impl Planner<'_> {
    /// What the pipeline of the output whose chain tops out at `top` ends in, and where its chain
    /// starts: an `ExtractAggregate` over an `Aggregate` is a fold, and anything else the
    /// collection itself.
    fn breaker_at(&self, top: NodeId) -> (BreakerKind, NodeId) {
        if let Some(GraphNode::Operator { kind, inputs, .. }) = self.by_id.get(&top)
            && matches!(classify(kind), Class::Extract)
            && let [edge] = inputs.as_slice()
            && let Some(GraphNode::Operator {
                kind: fold_kind,
                tiling: Tiling::Aggregation { kind, accumulator },
                inputs: fold_inputs,
                ..
            }) = self.by_id.get(&edge.subscribed)
            && matches!(classify(fold_kind), Class::Fold)
            && let [fold_edge] = fold_inputs.as_slice()
        {
            let fold = BreakerKind::Fold {
                kind: *kind,
                accumulator: (**accumulator).clone(),
                aggregate: edge.subscribed,
            };
            return (fold, fold_edge.subscribed);
        }
        if let Some(GraphNode::Operator { kind, inputs, .. }) = self.by_id.get(&top)
            && matches!(classify(kind), Class::ExtractGroups)
            && let [edge] = inputs.as_slice()
            && let Some(GraphNode::Operator {
                kind: group_kind,
                inputs: group_inputs,
                ..
            }) = self.by_id.get(&edge.subscribed)
            && matches!(classify(group_kind), Class::Groups)
            && let [group_edge] = group_inputs.as_slice()
        {
            let group = BreakerKind::Group {
                aggregate: edge.subscribed,
            };
            return (group, group_edge.subscribed);
        }
        (BreakerKind::Collect, top)
    }

    /// The kind of the operator `id` names, or why the graph holds none.
    fn kind_of(&self, id: NodeId) -> Option<&'static str> {
        match self.by_id.get(&id) {
            Some(GraphNode::Operator { kind, .. }) => Some(kind),
            Some(GraphNode::Sink { .. }) | None => None,
        }
    }

    /// A `MapResult` whose function is the slot `slot` of a `Memo` reads that memo at each key of
    /// its input (a keyed read). The memo's pipeline is planned once, whichever
    /// number of reads there are, and every read of one chain is of one memo.
    fn keyed_read(&mut self, slot: NodeId, keyed: &mut Option<NodeId>) -> Result<(), Unsupported> {
        let Some(GraphNode::Operator { inputs, .. }) = self.by_id.get(&slot).copied() else {
            return Err(Unsupported(
                "a keyed read of something that is not a slot".into(),
            ));
        };
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
        let [upstream] = memo_inputs.as_slice() else {
            return Err(Unsupported("a `Memo` without its one input".into()));
        };
        if !matches!(classify(memo_kind), Class::Memo)
            || !matches!(upstream.kind, EdgeKind::Value { deferred: false })
        {
            return Err(Unsupported(
                "a keyed read of something that is not a `Memo`'s own input".into(),
            ));
        }
        if keyed.is_some_and(|other| other != memo) {
            return Err(Unsupported(
                "a chain keyed-reads more than one `Memo`: its morsels are the keys of one memo, \
                 and a key of the other may not be merged"
                    .into(),
            ));
        }
        if self.memos.contains(&memo) {
            return Err(Unsupported(
                "a `Memo` read by a slot that starts a chain is also read at keys".into(),
            ));
        }
        if !self.keyed_memos.contains_key(&memo) {
            let planned = self.pipeline(upstream.subscribed, BreakerKind::Materialize { memo })?;
            self.keyed_memos.insert(memo, planned);
        }
        *keyed = Some(memo);
        Ok(())
    }

    /// Admission is by kind, and a streaming operator is a morsel operator only where it works on
    /// each key of a collection: its answer is a collection over the keys its input's collection
    /// has. At the outermost level `MapResultToConst` reads its input whole and `VariantWrap`
    /// wraps it whole, and neither answers a collection over the input's keys, so a morsel's guard
    /// would cut something it does not name. The operator's tiling and its input's must be
    /// collections over one extent.
    fn keeps_outer_domain(
        &self,
        kind: &str,
        own: &Tiling,
        input: NodeId,
    ) -> Result<(), Unsupported> {
        let input_tiling = match self.by_id.get(&input) {
            Some(GraphNode::Operator { tiling, .. }) => Some(tiling),
            Some(GraphNode::Sink { .. }) | None => None,
        };
        match (own, input_tiling) {
            (
                Tiling::DataFunction { domain, .. },
                Some(Tiling::DataFunction {
                    domain: input_domain,
                    ..
                }),
            ) if domain == input_domain => Ok(()),
            _ => Err(Unsupported(format!(
                "a `{kind}` at the outermost level answers other than a collection over its \
                 input's keys"
            ))),
        }
    }

    /// Plan the pipeline whose chain starts at `top` and ends in `breaker`, after the pipelines
    /// it streams from, and say where it is in the plan.
    fn pipeline(&mut self, top: NodeId, breaker: BreakerKind) -> Result<usize, Unsupported> {
        let mut at = top;
        let mut keyed: Option<NodeId> = None;
        let mut drops_keys = false;
        // Set by a keyed read: the operator beneath it must hand it keys as values.
        let mut values_are_keys = false;
        let (head, streams_from) = loop {
            let node = self.by_id.get(&at).copied();
            let Some(GraphNode::Operator {
                kind,
                inputs,
                tiling,
                ..
            }) = node
            else {
                return Err(Unsupported("the chain reaches no source".into()));
            };
            // A keyed `MapResult` reads the memo at the values of its input, so those values must be
            // the keys of the iteration: an `IterateExtent` answers them, and a `Restrict` answers
            // the keys that pass. Any other operator answers other values, which are keys of
            // nothing the memo's claims ordered.
            if std::mem::take(&mut values_are_keys)
                && !matches!(*kind, "IterateExtent" | "Restrict")
            {
                return Err(Unsupported(format!(
                    "a keyed read reads the memo at the values of its input, which must be the \
                     keys, and a `{kind}` answers other values"
                )));
            }
            match classify(kind) {
                Class::Refuse(reason) => return Err(Unsupported(reason)),
                Class::Operand => {
                    return Err(Unsupported(
                        "a `Constant` is read whole by the operator that applies it and is no source of rows".into(),
                    ));
                }
                Class::Memo
                | Class::Extract
                | Class::Fold
                | Class::ExtractGroups
                | Class::Groups => {
                    return Err(Unsupported(format!(
                        "`{kind}` is not a streaming operator here"
                    )));
                }
                Class::Source => match keyed {
                    None => break (Head::Source, Vec::new()),
                    Some(memo) => {
                        let planned = self.keyed_memos[&memo];
                        let Some(GraphNode::Operator {
                            tiling:
                                Tiling::DataFunction {
                                    domain: memo_keys, ..
                                },
                            ..
                        }) = self.by_id.get(&memo).copied()
                        else {
                            return Err(Unsupported("a `Memo` that is not a collection".into()));
                        };
                        if !matches!(tiling, Tiling::DataFunction { domain, .. } if domain == memo_keys)
                        {
                            return Err(Unsupported(
                                "a keyed read of a `Memo` over keys that are not the iterated source's"
                                    .into(),
                            ));
                        }
                        if self.pipelines[planned].drops_keys {
                            return Err(Unsupported(
                                "a keyed read of a `Memo` whose pipeline can drop a key".into(),
                            ));
                        }
                        break (Head::Breaker, vec![planned]);
                    }
                },
                Class::Converse => {
                    // The chain of a pipeline that ends in a breaker is the breaker's own, which
                    // reads the `Converse`'s producer; a collecting pipeline subscribes its chain
                    // afresh, which would invert a second time.
                    if matches!(breaker, BreakerKind::Collect) {
                        return Err(Unsupported(
                            "a `Converse` read by a collecting pipeline".into(),
                        ));
                    }
                    if keyed.is_some() {
                        return Err(Unsupported(
                            "a keyed read in a chain that starts at a breaker's output".into(),
                        ));
                    }
                    let [edge] = inputs.as_slice() else {
                        return Err(Unsupported("a `Converse` without its one input".into()));
                    };
                    if !matches!(edge.kind, EdgeKind::Value { deferred: false }) {
                        return Err(Unsupported(
                            "the chain closes a cycle or reads a shared node".into(),
                        ));
                    }
                    // Only the outermost collection is inverted by a breaker: its input is one
                    // mapping to scalars, and a deeper level stands beneath enclosing rows.
                    let inverts_the_outermost = matches!(
                        self.by_id.get(&edge.subscribed),
                        Some(GraphNode::Operator {
                            tiling: Tiling::DataFunction { codomain, .. },
                            ..
                        }) if matches!(**codomain, Tiling::Scalar(_))
                    );
                    if !inverts_the_outermost {
                        return Err(Unsupported(
                            "a `Converse` of a level beneath enclosing rows".into(),
                        ));
                    }
                    if !self.converses.insert(at) {
                        return Err(Unsupported(
                            "a `Converse` is read by more than one pipeline".into(),
                        ));
                    }
                    let planned =
                        self.pipeline(edge.subscribed, BreakerKind::Invert { converse: at })?;
                    break (Head::Breaker, vec![planned]);
                }
                Class::Cut if keyed.is_some() => {
                    return Err(Unsupported(
                        "a keyed read in a chain that starts at a breaker's output".into(),
                    ));
                }
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
                    if self.keyed_memos.contains_key(&memo) {
                        return Err(Unsupported(
                            "a `Memo` read at keys is also read by a slot that starts a chain"
                                .into(),
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
                        self.pipeline(upstream.subscribed, BreakerKind::Materialize { memo })?;
                    drops_keys |= self.pipelines[planned].drops_keys;
                    break (Head::Breaker, vec![planned]);
                }
                Class::Streaming(Streaming::Applies(operand)) => {
                    let edge = |role: &str| {
                        inputs
                            .iter()
                            .find(|edge| matches!(edge.role, EdgeRole::Named(name) if name == role))
                    };
                    let (Some(data), Some(function)) = (edge("input"), edge(operand)) else {
                        return Err(Unsupported(format!("a `{kind}` without its two inputs")));
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
                    self.keeps_outer_domain(kind, tiling, data.subscribed)?;
                    let applier = kind;
                    match self.kind_of(function.subscribed) {
                        Some(kind) if matches!(classify(kind), Class::Operand) => {}
                        Some(kind) if operand == "fn" && matches!(classify(kind), Class::Cut) => {
                            self.keyed_read(function.subscribed, &mut keyed)?;
                            values_are_keys = true;
                        }
                        Some(kind) => {
                            return Err(Unsupported(format!(
                                "a `{applier}` applies a `{kind}`, and only a `Constant` is \
                                 streamed, or for a `MapResult` a slot read at keys"
                            )));
                        }
                        None => {
                            return Err(Unsupported(format!(
                                "a `{applier}` applies something the graph holds no operator for"
                            )));
                        }
                    }
                    at = data.subscribed;
                }
                Class::Streaming(Streaming::Unary) => {
                    drops_keys |= matches!(*kind, "Restrict" | "VariantProject");
                    let input = owned_input(kind, inputs)?;
                    self.keeps_outer_domain(kind, tiling, input.subscribed)?;
                    at = input.subscribed;
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
        if let Some(memo) = keyed {
            drops_keys |= self.pipelines[self.keyed_memos[&memo]].drops_keys;
        }
        // The walk ends at one head, so a pipeline reads the pushes of one breaker pipeline.
        debug_assert!(
            streams_from.len() <= 1,
            "a planned pipeline streams from at most one pipeline: {streams_from:?}"
        );
        self.pipelines.push(PipelinePlan {
            head,
            breaker,
            streams_from,
            drops_keys,
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
    /// What the serial producers this pipeline replaces had released of each source: the pool's
    /// record for each source operator of the chain starts there. Empty for a run no serial
    /// producer read.
    inherits: Vec<Inherited>,
    /// The breaker that runs the pipeline when it ends in a memo: the dispatcher pulls it for each
    /// morsel, and `chain` is a placeholder.
    sink: Option<BreakerHandle>,
}

/// What the serial producers a pool replaces had released of one source.
type Inherited = (Arc<Mutex<dyn DataSourceDomainExtentImpl>>, Predicate);

/// A run's pipelines, subscribed and seeded, before any worker serves them.
struct Prepared {
    dispatcher: Arc<Dispatcher>,
    handles: Vec<PipelineHandle>,
    /// One chain per pipeline, indexed by `PipelineId`.
    chains: Vec<Box<dyn TileProducer>>,
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
                breaker: run.sink.clone(),
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
    // One chain per pipeline, indexed by `PipelineId`. Notifications reach the dispatcher through
    // the chain's head consumer. The path from the source to it is region-driven and acyclic
    // (`plan_inline` admits no shared node or recurrence below a head), so no consumer on it
    // drops or widens the region.
    //
    // The chains hold release records with a source, one per source operator and named for the
    // pool: the chain releases the morsels it ran, and a source reclaims what every record
    // releases. The records outlive the chains and retire when `records` drops.
    let identity = pool_release_identity();
    let (chains, records): (Vec<Box<dyn TileProducer>>, _) =
        scheduler.with_pooled_release_records(identity.clone(), |scheduler| {
            runs.iter_mut()
                .enumerate()
                .map(|(pipeline, run)| {
                    let head: Box<dyn Consumer> = match run.head {
                        // The keys of a pipeline that streams from a breaker are pushed to it,
                        // and what its chain notifies adds nothing.
                        Head::Breaker => Box::new(|| {}),
                        Head::Source if notified[pipeline] => Box::new(PipelineConsumer {
                            pipeline: handles[pipeline].clone(),
                        }),
                        Head::Source => Box::new(|| {}),
                    };
                    run.chain
                        .subscribe(tilings[pipeline].universal_guard(), head, scheduler)
                })
                .collect()
        });
    // The records start where the serial producers they replace had released, per source
    // operator: a key already handed to a reader is not offered again.
    for run in &runs {
        if run.inherits.is_empty() {
            continue;
        }
        let mut names = Vec::new();
        visit_operators(&*run.chain, &mut |op| {
            if let Some(id) = op.operator_id() {
                let name = format!("{identity}/{id:?}");
                if records.holds(&name) {
                    names.push(name);
                }
            }
        });
        for (source, released) in &run.inherits {
            let mut source = source.lock_wait();
            for name in &names {
                source.release(name, released.clone());
            }
        }
    }
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

/// `f` on `op` and on every operator beneath it.
fn visit_operators(op: &dyn TileOperator, f: &mut dyn FnMut(&dyn TileOperator)) {
    f(op);
    op.visit_inputs(&mut |edge| visit_operators(edge.target, f));
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

/// The consumer at the head of a pipeline over a data source: a notification publishes the region
/// it carries to the pipeline's source and never pulls, which is what `region_driven` says.
struct PipelineConsumer {
    pipeline: PipelineHandle,
}

impl Consumer for PipelineConsumer {
    fn notify(&mut self, arrived: &Projection) {
        debug_assert!(
            *arrived != Projection::Nothing,
            "no producer notifies of an empty region"
        );
        // A region of fields names where a change is in a record, and the pipeline's source cuts
        // keys: only everything it has ready is safe to hand out.
        match arrived {
            Projection::Fields(_) => self.pipeline.publish(&Projection::Everything),
            keys => self.pipeline.publish(keys),
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

/// What a pipeline serving the outputs `owners` inherits of each source: what every one of their
/// serial producers had released, so a key an output was not yet handed is offered again to the
/// outputs that were.
fn inherited_by(owners: &[&str], inherited: &HashMap<String, Vec<Inherited>>) -> Vec<Inherited> {
    let mut common: Option<Vec<Inherited>> = None;
    for owner in owners {
        let theirs = inherited.get(*owner).cloned().unwrap_or_default();
        common = Some(match common {
            None => theirs,
            Some(so_far) => so_far
                .into_iter()
                .filter_map(|(source, released)| {
                    let (_, other) = theirs.iter().find(|(s, _)| Arc::ptr_eq(s, &source))?;
                    Some((source, released.intersect(other)))
                })
                .collect(),
        });
    }
    common.unwrap_or_default()
}

/// The source a pipeline's morsels are cut from: the one source under the chain.
fn pipeline_source(chain: &dyn TileOperator) -> Arc<dyn MorselSource> {
    source_of(chain).expect("the pipeline was checked to read one source")
}

/// The breaker's state while the workers run.
enum PoolBreaker {
    /// The collection, merged morsel by morsel.
    Collect {
        // shared-state-ok: the sink's own state. Every worker merges into it, and no operator
        // reads it: it answers `main` once every worker has returned.
        collector: Mutex<Tile>,
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
            PoolBreaker::Collect { .. } => None,
        }
    }
}

/// The pool's worker over the plan's pipelines: per pipeline its chain and the breaker the
/// pipeline feeds. `work` and `leave` index them by the package's pipeline.
struct MainWorker<'a> {
    chains: &'a mut [Box<dyn TileProducer>],
    breakers: &'a [PoolBreaker],
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
        match &self.breakers[pipeline] {
            PoolBreaker::Collect { collector } => collector.lock_wait().merge(tile),
            PoolBreaker::Materialize { output } => {
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

    fn leave(&mut self, _pipeline: PipelineId) {}
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
    /// The pipeline's breaker, when it is a [`Breaker`]: the dispatcher calls its `pull_sink` for
    /// each morsel in place of a worker, and its `finalize` for each round. A pipeline with none
    /// runs as before.
    breaker: Option<BreakerHandle>,
}

/// What the dispatcher keeps of a breaker pipeline's rounds, which one thread reads and writes.
struct Rounds {
    /// Whether a round is owed: a morsel ran since the last round, or no round has run yet. A
    /// breaker may hold keys before its first morsel (a memo that adopted its pull-mode cache), and
    /// the first round pushes them.
    ran: bool,
    /// How many morsels the breaker has pulled.
    sunk: usize,
    /// Whether the terminal round has run.
    terminal: bool,
    /// The thread that drives the pipeline's breaker, which is the first to call it.
    driver: Option<std::thread::ThreadId>,
    /// The keys pushed to the parent pipelines in every round so far, which a push is checked
    /// against.
    pushed: Predicate,
}

impl Rounds {
    /// Every call of a breaker is made on one thread.
    fn on_driver(&mut self) {
        let me = std::thread::current().id();
        assert!(
            self.driver.get_or_insert(me) == &me,
            "a breaker pipeline is driven by one thread"
        );
    }
}

/// What a breaker's `finalize` may do to the dispatcher: push keys that are final to the
/// pipelines that read the breaker, which are the pipelines that list its pipeline in
/// `streams_from`.
pub struct Pushes<'d> {
    dispatcher: &'d Dispatcher,
    parents: &'d [usize],
    pushed: &'d mut Predicate,
}

impl Pushes<'_> {
    /// Make the keys of `region` claimable by each parent pipeline. A key is pushed once: a parent
    /// claims each pushed key once, so a later push of it would never be served.
    ///
    /// # Panics
    ///
    /// When a key of `region` was pushed before. The check runs in every build: a parent that
    /// claimed the key once would lose the rows of its second push.
    pub fn push(&mut self, region: &Predicate) {
        assert!(
            self.pushed.intersect(region).is_false(),
            "a key is pushed in one round only: {region:?} against {:?}",
            self.pushed
        );
        *self.pushed = self.pushed.union(region);
        for &parent in self.parents {
            self.dispatcher
                .publish(PipelineId(parent), &Projection::admitting(region.clone()));
        }
    }
}

/// The source of a parent pipeline's morsels: the keys pushed to it, cut by the breaker's
/// `first_keys`, each claimed once.
fn pushed_source(breaker: &BreakerHandle) -> Arc<dyn MorselSource> {
    let breaker = breaker.clone();
    // A pushed key is ready by being pushed, so the source's ready region is every key.
    Arc::new(LiveSource::new(
        || Predicate::True,
        move |region, rows| {
            let keys = breaker.first_keys(region, rows);
            // A pushed key is a key the breaker holds, so a region that is not empty names one,
            // and a key outside the region would be claimed by nobody.
            debug_assert!(
                !keys.is_empty() && keys.iter().all(|key| region.contains(key)),
                "first_keys answers keys of the region: {keys:?} for {region:?}"
            );
            keys
        },
    ))
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
/// The driver claims a morsel from a pipeline's source with [`next`](Self::next) and acknowledges
/// it with [`ack`](Self::ack) once the morsel is released. A pipeline finishes when its source
/// has answered `Exhausted`, every morsel it answered is acknowledged, and the driver has left
/// it. The driver completes it by running its `finalize` and starts the pipelines waiting on it.
/// See `src/interpreter/design-parallel.md`, "The dispatcher".
struct Dispatcher {
    /// Names this dispatcher in the [`ServeState`]s it mints, so a state of another dispatcher
    /// is recognized whatever its size.
    id: u64,
    /// Per pipeline, by `PipelineId`.
    jobs: Vec<Job>,
    /// Rows a morsel holds, which a claim takes at most.
    morsel_rows: u64,
    /// Pipelines not yet finished.
    unfinished: AtomicUsize,
    /// Set when the driver panics: every `next` answers `Done` from then on.
    failed: AtomicBool,
    /// Counts the events that can end a wait: a pipeline finishing or exhausting its source, a
    /// publish, a close and a failure.
    epoch: AtomicU64,
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
    breaker: Option<BreakerHandle>,
    // shared-state-ok: the dispatcher's own bookkeeping of a breaker pipeline's rounds, read and
    // written on its thread. It holds no tile.
    rounds: Mutex<Rounds>,
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
        for (index, spec) in pipelines.iter().enumerate() {
            let behind_breakers: Vec<usize> = spec
                .streams_from
                .iter()
                .filter(|from| pipelines[from.0].breaker.is_some())
                .map(|from| from.0)
                .collect();
            assert!(
                behind_breakers.is_empty() || spec.streams_from.len() == 1,
                "a pipeline streams from one breaker pipeline: {index} streams from {:?}",
                spec.streams_from
                    .iter()
                    .map(|from| from.0)
                    .collect::<Vec<_>>()
            );
        }
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
                rounds: Mutex::new(Rounds {
                    ran: spec.breaker.is_some(),
                    sunk: 0,
                    terminal: false,
                    driver: None,
                    pushed: Predicate::False,
                }),
                breaker: spec.breaker,
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
                        if job.breaker.is_some() {
                            job.rounds.lock_now().ran = true;
                        }
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
                        self.drain(index);
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
        if job.breaker.is_some() {
            debug_assert_eq!(
                job.streams_open.load(Ordering::Acquire),
                0,
                "the terminal round runs after every pipeline it streams from finished"
            );
            self.round(index, true);
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

    /// The pipeline has no morsel left to claim: a breaker pipeline that ran a morsel since its
    /// last round runs a round.
    fn drain(&self, index: usize) {
        let job = &self.jobs[index];
        if job.breaker.is_none() || job.outstanding.load(Ordering::Acquire) != 0 {
            return;
        }
        if std::mem::take(&mut job.rounds.lock_now().ran) {
            self.round(index, false);
        }
    }

    /// Run a round of the breaker of pipeline `index`: `finalize`, which pushes the keys that are
    /// final to the pipelines that read it.
    fn round(&self, index: usize, terminal: bool) {
        let job = &self.jobs[index];
        let breaker = job.breaker.as_ref().expect("a round runs for a breaker");
        let mut rounds = job.rounds.lock_now();
        rounds.on_driver();
        debug_assert!(!rounds.terminal, "no round runs after the terminal round");
        rounds.terminal = terminal;
        rounds.ran = false;
        let mut pushes = Pushes {
            dispatcher: self,
            parents: &job.stream_readers,
            pushed: &mut rounds.pushed,
        };
        breaker.finalize(Round { terminal }, &mut pushes);
    }

    /// Run the morsel of `package` through its pipeline's breaker: the breaker pulls its own
    /// input at the morsel's guard and merges it.
    fn sink_morsel(&self, package: &WorkPackage) {
        let job = &self.jobs[package.pipeline.0];
        {
            let mut rounds = job.rounds.lock_now();
            rounds.on_driver();
            debug_assert!(
                !rounds.terminal,
                "pull_sink is not called after the terminal round"
            );
            rounds.sunk += 1;
        }
        let breaker = job
            .breaker
            .as_ref()
            .expect("a morsel of a breaker pipeline");
        breaker.pull_sink(package.guard.clone());
    }

    /// How many keys the breakers of this dispatcher hold.
    #[cfg(any(test, feature = "test-helpers"))]
    fn breaker_held_keys(&self) -> usize {
        self.jobs
            .iter()
            .filter_map(|job| job.breaker.as_ref())
            .map(|breaker| breaker.held_keys())
            .sum()
    }

    /// How many morsels the breakers of this dispatcher have pulled.
    fn sunk_morsels(&self) -> usize {
        self.jobs.iter().map(|job| job.rounds.lock_now().sunk).sum()
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
    fn is_done(&self, pipeline: PipelineId) -> bool {
        self.jobs[pipeline.0].finished.load(Ordering::Acquire)
    }

    /// Stop every worker from claiming: a worker panicked.
    fn fail(&self) {
        self.failed.store(true, Ordering::Release);
        self.wake_idle();
    }

    /// Move the epoch: something that can end a wait happened.
    fn wake_idle(&self) {
        self.epoch.fetch_add(1, Ordering::AcqRel);
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
                match self.jobs[pipeline.0].breaker {
                    Some(_) => self.sink_morsel(&package),
                    None => worker.work(&package),
                }
                self.ack(package);
                Step::Ran
            }
            Next::Wait => Step::Wait,
            Next::Done => Step::Done,
        }
    }

    /// Whether every pipeline has finished.
    #[cfg(test)]
    fn all_done(&self) -> bool {
        self.unfinished.load(Ordering::Acquire) == 0
    }

    /// [`serve_until_wait`](Self::serve_until_wait) with a fresh state, for a test that runs a
    /// dispatcher to what is claimable.
    #[cfg(test)]
    fn serve(&self, worker: &mut impl PoolWorker) {
        let mut state = self.serve_state();
        self.serve_until_wait(worker, &mut state);
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
    /// is why the call does not return there: the claim that finds a source exhausted moves the
    /// epoch, and the next step leaves the pipeline and finishes it.
    ///
    /// Every call that moves the epoch is made on the thread that calls this, so the `Wait` it
    /// gets is a wait until the caller delivers an arrival.
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
    state: ServeState,
    /// The sources of the pipelines that read one and whose arrivals have not ended, with what
    /// delivers to them. A lap closes one that says it is complete.
    open_sources: Vec<OpenSource>,
    // Dropped after the chains, which hold records with the sources, and after the taken chains'
    // operators, which the pool owns from the cut.
    _records: PooledRecords,
    _placeholders: HashMap<usize, Box<dyn TileOperator>>,
}

/// A source whose arrivals have not ended, and what delivers to its pipeline.
struct OpenSource {
    handle: PipelineHandle,
    source: Arc<dyn MorselSource>,
    /// Whether each lap publishes what the source has ready to the pipeline, since no
    /// notification does.
    poll: bool,
}

/// The breakers a run switches to sink mode, by the node of the operator that is the breaker (a
/// memo, or the aggregate of a fold): the breaker, the tiling of what its pipeline pulls and, for a
/// pipeline that reads a data source, the source its morsels are cut from.
struct SunkBreakers {
    handles: HashMap<NodeId, BreakerHandle>,
    tilings: HashMap<NodeId, Tiling>,
    sources: HashMap<NodeId, Arc<dyn MorselSource>>,
}

/// `f` on the operator `id` beneath `op`, if there is one.
fn with_operator(op: &dyn TileOperator, id: NodeId, f: &mut dyn FnMut(&dyn TileOperator)) {
    if op.operator_id() == Some(id) {
        f(op);
        return;
    }
    op.visit_inputs(&mut |edge| with_operator(edge.target, id, f));
}

/// What a run needs of each memo of `plan`, or why the program stays on the plain loop. Read before anything is dropped or switched.
fn sunk_breakers(
    scheduler: &Scheduler,
    program: &CompiledProgram,
    plan: &Plan,
) -> Result<SunkBreakers, Unsupported> {
    let mut sunk = SunkBreakers {
        handles: HashMap::new(),
        tilings: HashMap::new(),
        sources: HashMap::new(),
    };
    let node_tiling = |wanted: &NodeId| {
        program
            .operator_graph
            .nodes()
            .iter()
            .find_map(|node| match node {
                GraphNode::Operator { id, tiling, .. } if id == wanted => Some(tiling.clone()),
                _ => None,
            })
            .ok_or_else(|| Unsupported("a breaker the graph holds no node for".into()))
    };
    for pipeline in &plan.pipelines {
        let Some(node) = pipeline.breaker.node() else {
            continue;
        };
        let handle = scheduler.breaker(node).ok_or_else(|| {
            Unsupported("a breaker registered none, or its producer is gone".into())
        })?;
        // What the breaker's pipeline pulls: a memo's input has the memo's own tiling, and an
        // aggregate's is its input's.
        let pulled = match &pipeline.breaker {
            BreakerKind::Materialize { .. } => node_tiling(&node)?,
            BreakerKind::Fold { .. } | BreakerKind::Group { .. } | BreakerKind::Invert { .. } => {
                let mut input = None;
                for graph_node in program.operator_graph.nodes() {
                    if let GraphNode::Operator { id, inputs, .. } = graph_node
                        && *id == node
                        && let [edge] = inputs.as_slice()
                    {
                        input = Some(edge.subscribed);
                    }
                }
                node_tiling(
                    &input.ok_or_else(|| Unsupported("an aggregate without its input".into()))?,
                )?
            }
            BreakerKind::Collect => unreachable!("a collecting pipeline has no node"),
        };
        if !matches!(pulled, Tiling::DataFunction { .. }) {
            return Err(Unsupported(
                "a breaker that does not pull a collection".into(),
            ));
        }
        if pipeline.head == Head::Source {
            let mut found = None;
            for output in &program.outputs {
                with_operator(&*output.op, node, &mut |breaker_op| {
                    breaker_op.visit_inputs(&mut |edge| found = Some(source_of(edge.target)));
                });
            }
            let source =
                found.ok_or_else(|| Unsupported("a breaker not in the graph".into()))??;
            sunk.sources.insert(node, source);
        }
        sunk.handles.insert(node, handle);
        sunk.tilings.insert(node, pulled);
    }
    Ok(sunk)
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
        let plan = plan_inline(&program.operator_graph)?;
        // What each output's serial producers had released of each source, read before the
        // producers are dropped and their records retire.
        let inherited: HashMap<String, Vec<Inherited>> = program
            .outputs
            .iter()
            .map(|output| {
                (
                    output.name.clone(),
                    ctx.scheduler().released_by(&output.source_producers),
                )
            })
            .collect();
        let sunk = sunk_breakers(ctx.scheduler(), program, &plan)?;
        let (mut main, mut sinks) = (None, Vec::new());
        for output in program.outputs.iter_mut() {
            match output.is_main() {
                true => main = Some(output),
                false => sinks.push(output),
            }
        }
        for output in main.iter().chain(sinks.iter()) {
            check_pipelines(&*output.op)?;
        }
        // Everything the pool can refuse is read; the program is the pool's from here. The
        // producers `compile_program` subscribed for the outputs go: they registered records that
        // release nothing, which a source would hold its reclaim at. `main`'s is in the output or
        // with the caller that moved it out to drive it, and a sink's is its consumer's.
        let mut kept_main = None;
        if let Some(output) = main.as_mut() {
            let producer = main_producer.take().or_else(|| output.producer.take());
            debug_assert!(
                producer.is_some(),
                "the pool takes the producer that held the pipeline's record"
            );
            // A fold's pipeline ends in the aggregate's own producer, so `main`'s producer stays
            // the program's; any other `main` is answered from the pool's output.
            match plan.main().breaker {
                BreakerKind::Fold { .. } | BreakerKind::Group { .. } => kept_main = producer,
                _ => drop(producer),
            }
        }
        for output in &sinks {
            let consumer = output
                .sink_consumer
                .as_ref()
                .expect("a sink output has its consumer");
            drop(consumer.lock_now().take_producer());
        }
        let sink_chains: Vec<SinkChain<'_>> = sinks
            .into_iter()
            .map(|output| SinkChain {
                name: output.name.clone(),
                consumer: output
                    .sink_consumer
                    .clone()
                    .expect("a sink output has its consumer"),
                chain: &mut output.op,
            })
            .collect();
        let mut pending = Some((sink_chains, main_consumer));
        let mut started = None;
        let mut start_chain = |chain: Option<(&mut Box<dyn TileOperator>, Tiling)>| {
            let (sinks, consumer) = pending.take().expect("the chains are started once");
            let main = chain.map(|(chain, tiling)| MainChain {
                chain,
                tiling,
                consumer,
            });
            started = Some(start_planned(
                ctx,
                &plan,
                main,
                sinks,
                StartContext {
                    config,
                    inherited: &inherited,
                    sunk: &sunk,
                    kept_main: kept_main.take(),
                },
            ));
        };
        match main {
            None => start_chain(None),
            Some(output) => {
                let tiling = output.op.tiling().clone();
                match plan.main().breaker {
                    BreakerKind::Collect => start_chain(Some((&mut output.op, tiling))),
                    BreakerKind::Fold { .. } | BreakerKind::Group { .. } => start_chain(None),
                    BreakerKind::Materialize { .. } | BreakerKind::Invert { .. } => {
                        unreachable!("`main` is not a breaker's input")
                    }
                }
            }
        }
        Ok(started.expect("the chains were started"))
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

    /// How many keys the breakers of this run hold: rows absorbed and not yet released by every
    /// reader. Zero once every row has been read and released, which a test asserts.
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn held_keys(&self) -> usize {
        self.breakers
            .iter()
            .map(|breaker| match breaker {
                PoolBreaker::Materialize { output } => output.held_keys(),
                PoolBreaker::Collect { .. } => 0,
            })
            .sum::<usize>()
            + self.dispatcher.breaker_held_keys()
    }

    /// The producer that answers `main`, for the driver to pull, or none for a program without a
    /// `main`.
    pub fn take_main(&mut self) -> Option<Box<dyn TileProducer>> {
        self.main.take()
    }

    /// Serve every morsel the arrivals published so far, on this thread, and say what happened.
    /// A panic in a worker's chain fails the dispatcher and is raised here.
    pub fn lap(&mut self) -> Lap {
        let _fail = FailOnUnwind(&self.dispatcher);
        // A source whose yield predicate covers every key has delivered everything: what it
        // holds is published, and nothing else ends it.
        let dispatcher = &self.dispatcher;
        self.open_sources.retain(|open| {
            if dispatcher.is_done(open.handle.pipeline) {
                return false;
            }
            let complete = open.source.is_complete();
            if complete || open.poll {
                open.handle.publish(&Projection::Everything);
            }
            if complete {
                open.handle.close();
            }
            !complete
        });
        let sunk_before = self.dispatcher.sunk_morsels();
        let mut worker = MainWorker {
            chains: &mut self.chains,
            breakers: &self.breakers,
            worked: 0,
        };
        let settled = self
            .dispatcher
            .serve_until_wait(&mut worker, &mut self.state);
        let worked = worker.worked + (self.dispatcher.sunk_morsels() - sunk_before);
        match (settled, worked) {
            (Settled::Done, _) if self.dispatcher.failed.load(Ordering::Acquire) => Lap::Failed,
            (Settled::Done, _) => Lap::Done,
            (Settled::Wait, 0) => Lap::Idle,
            (Settled::Wait, _) => Lap::Ran,
        }
    }
}

/// The chain that ends in `main`, with `main`'s tiling and the consumer woken when it has
/// something to pull.
struct MainChain<'a> {
    chain: &'a mut Box<dyn TileOperator>,
    tiling: Tiling,
    consumer: Box<dyn Consumer>,
}

/// The chain that ends in a sink, and the consumer that pulls the sink.
struct SinkChain<'a> {
    name: String,
    chain: &'a mut Box<dyn TileOperator>,
    // shared-state-ok: the sink's own consumer. The pool installs a producer in it and it
    // schedules the sink's pull; no tile passes through it between operators.
    consumer: Arc<Mutex<SinkConsumer>>,
}

/// What [`start_planned`] reads besides the plan and the chains.
struct StartContext<'a> {
    config: &'a Config,
    inherited: &'a HashMap<String, Vec<Inherited>>,
    sunk: &'a SunkBreakers,
    /// `main`'s own producer, when its pipeline ends in a breaker the program already holds.
    kept_main: Option<Box<dyn TileProducer>>,
}

/// Subscribe `plan`'s pipelines over the chains the cut left, on one worker, answer `main` from
/// its breaker, and pull each sink through a producer of its breaker's output.
fn start_planned(
    ctx: &mut GlobalContext,
    plan: &Plan,
    main: Option<MainChain<'_>>,
    sinks: Vec<SinkChain<'_>>,
    StartContext {
        config,
        inherited,
        sunk,
        kept_main,
    }: StartContext<'_>,
) -> PooledRun {
    let (mut main_chain, mut main_consumer, main_tiling) = match main {
        Some(main) => (Some(main.chain), Some(main.consumer), Some(main.tiling)),
        None => (None, None, None),
    };
    let mut sink_chains: HashMap<String, &mut Box<dyn TileOperator>> = HashMap::new();
    let mut sinks = sinks;
    // shared-state-ok: the sinks' own consumers, as `SinkChain::consumer`.
    let sink_consumers: Vec<(String, Arc<Mutex<SinkConsumer>>)> = sinks
        .iter()
        .map(|sink| (sink.name.clone(), sink.consumer.clone()))
        .collect();
    for sink in sinks.iter_mut() {
        sink_chains.insert(sink.name.clone(), &mut *sink.chain);
    }
    // The outputs each pipeline serves: the pipelines that stream into an output's pipeline serve
    // it. A memo that several outputs read at keys has one pipeline, which serves all of them.
    let mut owners: Vec<Vec<&str>> = vec![Vec::new(); plan.pipelines.len()];
    for (name, at) in &plan.outputs {
        let mut pending = vec![*at];
        while let Some(pipeline) = pending.pop() {
            if !owners[pipeline].contains(&name.as_str()) {
                owners[pipeline].push(name);
            }
            pending.extend(&plan.pipelines[pipeline].streams_from);
        }
    }
    let mut reads: HashMap<String, Arc<Materialized>> = HashMap::new();
    let (mut runs, mut notified, mut close_at_start) = (Vec::new(), Vec::new(), Vec::new());
    let mut sources = Vec::new();
    // A memo or an aggregate in sink mode is its pipeline's breaker, and the pipeline holds a
    // placeholder where a chain would be.
    let mut placeholders: HashMap<usize, Box<dyn TileOperator>> = HashMap::new();
    for (position, pipeline) in plan.pipelines.iter().enumerate() {
        if let Some(node) = pipeline.breaker.node() {
            placeholders.insert(position, Box::new(Sunk::new(sunk.tilings[&node].clone())));
            sunk.handles[&node].begin_sinking();
        }
    }
    {
        let mut placeholder_refs: HashMap<usize, &mut Box<dyn TileOperator>> =
            placeholders.iter_mut().map(|(k, v)| (*k, v)).collect();
        for (position, pipeline) in plan.pipelines.iter().enumerate() {
            let output_name = || {
                plan.outputs
                    .iter()
                    .find(|(_, at)| *at == position)
                    .map(|(name, _)| name.clone())
                    .expect("a collecting pipeline ends in an output")
            };
            let (chain, breaker): (&mut dyn TileOperator, PoolBreaker) = match &pipeline.breaker {
                BreakerKind::Materialize { .. }
                | BreakerKind::Fold { .. }
                | BreakerKind::Group { .. }
                | BreakerKind::Invert { .. } => {
                    let placeholder = placeholder_refs
                        .remove(&position)
                        .expect("a breaker pipeline has its placeholder");
                    // The dispatcher runs the pipeline through its breaker, so the pool's own
                    // breaker is not read.
                    let unused = PoolBreaker::Collect {
                        collector: Mutex::new(placeholder.tiling().empty_tile()),
                    };
                    (&mut **placeholder, unused)
                }
                BreakerKind::Collect => {
                    let name = output_name();
                    let chain = match name == "main" {
                        true => main_chain.take().expect("one pipeline ends in `main`"),
                        false => sink_chains
                            .remove(&name)
                            .expect("one pipeline ends in each sink"),
                    };
                    let output = Materialized::new(chain.tiling().clone());
                    reads.insert(name, output.clone());
                    (&mut **chain, PoolBreaker::Materialize { output })
                }
            };
            let node_of = |pipeline: usize| {
                plan.pipelines[pipeline]
                    .breaker
                    .node()
                    .expect("a pipeline streams from a breaker's pipeline")
            };
            let source = match (pipeline.breaker.node(), pipeline.head) {
                (Some(node), Head::Source) => sunk.sources[&node].clone(),
                (_, Head::Breaker) => {
                    pushed_source(&sunk.handles[&node_of(pipeline.streams_from[0])])
                }
                (None, Head::Source) => pipeline_source(&*chain),
            };
            notified.push(pipeline.head == Head::Source);
            // A range ends by exhaustion. A source whose rows arrive from outside stays open
            // until it says it is complete ([`PooledRun::lap`]).
            close_at_start.push(false);
            sources.push(source.clone());
            let sink = pipeline
                .breaker
                .node()
                .map(|node| sunk.handles[&node].clone());
            runs.push(PipelineRun {
                sink,
                chain,
                source,
                breaker,
                head: pipeline.head,
                after: Vec::new(),
                inherits: inherited_by(&owners[position], inherited),
                streams_from: pipeline
                    .streams_from
                    .iter()
                    .map(|&i| PipelineId(i))
                    .collect(),
            });
        }
    }
    let Prepared {
        dispatcher,
        handles,
        chains,
        records,
        breakers,
    } = prepare(ctx.scheduler(), runs, config, notified, close_at_start);
    let open_sources = handles
        .iter()
        .zip(sources)
        .zip(&plan.pipelines)
        .filter(|(_, pipeline)| pipeline.head == Head::Source)
        .map(|((handle, source), pipeline)| OpenSource {
            handle: handle.clone(),
            source,
            // A breaker in sink mode swallows its input's notifications, so the lap tells its
            // pipeline's source what is ready.
            poll: pipeline.breaker.node().is_some(),
        })
        .collect();
    // The reader registers before the first morsel, so no row leaves before it has read. A fold's
    // `main` is the program's own producer.
    let main_producer = match (kept_main, main_tiling) {
        (Some(kept), _) => Some(kept),
        (None, Some(tiling)) => {
            let output = reads.remove("main").expect("`main` has a breaker");
            Some(
                BreakerOutput::new(output, tiling.clone(), false, None).subscribe(
                    tiling.universal_guard(),
                    main_consumer.take().expect("the consumer is taken once"),
                    ctx.scheduler(),
                ),
            )
        }
        (None, None) => None,
    };
    // A sink is pulled through a reader of its breaker's output on this thread, so its consumer
    // is woken as `main`'s is, and the pull hands the sink what arrived and releases it.
    for (name, consumer) in sink_consumers {
        let output = reads
            .remove(&name)
            .unwrap_or_else(|| unreachable!("a sink's pipeline collects: {name}"));
        let tiling = output.tiling().clone();
        let producer = BreakerOutput::new(output, tiling.clone(), false, None).subscribe(
            tiling.universal_guard(),
            Box::new(consumer.clone()),
            ctx.scheduler(),
        );
        consumer.lock_now().install_producer(producer);
    }
    let state = dispatcher.serve_state();
    PooledRun {
        main: main_producer,
        chains,
        dispatcher,
        breakers,
        state,
        open_sources,
        _records: records,
        _placeholders: placeholders,
    }
}

#[cfg(test)]
#[path = "parallel_breaker_tests.rs"]
mod breaker_tests;

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
    use std::sync::mpsc;

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
                    breaker: None,
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
                breaker: None,
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
                breaker: None,
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
                    breaker: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
                    streams_from: Vec::new(),
                    source: Box::new(move || live.clone()),
                    finalize: None,
                    breaker: None,
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
    /// exactly eight are admitted in a chain, and every other kind is refused with its own name.
    #[test]
    fn every_operator_kind_the_corpus_holds_is_classified_on_purpose() {
        use crate::interpreter::tile_operators::visit_inputs_tests::survey;
        let (kinds, _) = survey();
        let mut admitted = Vec::new();
        for kind in kinds {
            match classify(kind) {
                Class::Streaming(_) | Class::Source | Class::Cut => admitted.push(kind),
                Class::Memo
                | Class::Operand
                | Class::Extract
                | Class::Fold
                | Class::ExtractGroups
                | Class::Groups
                | Class::Converse => {}
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
                "MapResultToConst",
                "MapResultWithSource",
                "Restrict",
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
        let planned =
            plan_inline(&compiled.operator_graph).expect("a shared chain is two pipelines");
        assert_eq!(planned.pipeline_count(), 2);
        let (upstream, downstream) = (&planned.pipelines[0], &planned.pipelines[1]);
        assert!(upstream.head == Head::Source);
        assert!(matches!(upstream.breaker, BreakerKind::Materialize { .. }));
        assert!(upstream.streams_from.is_empty());
        assert!(downstream.head == Head::Breaker);
        assert!(matches!(downstream.breaker, BreakerKind::Collect));
        assert_eq!(downstream.streams_from, [0]);
    }

    /// A `Memo` is read by one slot that starts a chain: planning another chain that starts at a
    /// slot of it is refused. A memo read at keys has no such limit.
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
            keyed_memos: HashMap::new(),
            converses: HashSet::new(),
        };
        planner
            .pipeline(top, BreakerKind::Collect)
            .expect("the first slot");
        let refused = planner
            .pipeline(top, BreakerKind::Collect)
            .expect_err("the same memo again");
        assert!(
            refused.to_string().contains("more than one slot"),
            "{refused}"
        );
    }

    /// A pipeline that serves several outputs inherits what every one of their serial producers had
    /// released, per source: a key an output was not yet handed is read again for it. Two outputs
    /// that released different keys give the intersection, whichever is first or last, and an
    /// output that read a source the other did not leaves that source out.
    #[test]
    fn a_pipeline_serving_two_outputs_inherits_the_intersection_of_their_releases() {
        use crate::interpreter::{BaseType, Extent, TestDataSource};
        let source = |name: &str| -> Arc<Mutex<dyn DataSourceDomainExtentImpl>> {
            Arc::new(Mutex::new(TestDataSource::new(
                name,
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )))
        };
        let upto = |last: u64| Predicate::at_or_below(Value::UInt(last));
        let (shared, other) = (source("shared"), source("other"));
        let inherited = HashMap::from([
            (
                "first".to_string(),
                vec![(shared.clone(), upto(4)), (other.clone(), upto(9))],
            ),
            ("second".to_string(), vec![(shared.clone(), upto(2))]),
        ]);
        for owners in [["first", "second"], ["second", "first"]] {
            let got = inherited_by(&owners, &inherited);
            assert_eq!(
                got.len(),
                1,
                "{owners:?}: a source one output did not read drops out"
            );
            assert!(Arc::ptr_eq(&got[0].0, &shared), "{owners:?}");
            assert_eq!(got[0].1, upto(2), "{owners:?}: the intersection of the two");
        }
        assert_eq!(inherited_by(&["first"], &inherited).len(), 2);
        assert!(inherited_by(&[], &inherited).is_empty());
    }

    /// Hand-built graphs for the refusals of a keyed read that no CHL program reaches, or that the
    /// compiler reaches only with a refusal of its own first. Each names the property it checks.
    mod keyed_graphs {
        use super::*;
        use crate::interpreter::{BaseType, Extent, operator_graph::InputEdge};

        fn keys() -> Extent {
            Extent::uint_range(8)
        }

        fn collection(domain: Extent) -> Tiling {
            Tiling::data_function(domain, Tiling::Scalar(Extent::Base(BaseType::Int)))
        }

        fn edge(role: &'static str, to: NodeId) -> InputEdge {
            InputEdge {
                role: EdgeRole::Named(role),
                kind: EdgeKind::Value { deferred: false },
                subscribed: to,
            }
        }

        fn node(kind: &'static str, domain: Extent, inputs: Vec<InputEdge>) -> (NodeId, GraphNode) {
            let id = NodeId::fresh();
            (
                id,
                GraphNode::Operator {
                    id,
                    kind,
                    tiling: collection(domain),
                    inputs,
                },
            )
        }

        /// The nodes of a graph, built up.
        #[derive(Default)]
        struct Nodes(Vec<GraphNode>);

        impl Nodes {
            fn add(&mut self, built: (NodeId, GraphNode)) -> NodeId {
                self.0.push(built.1);
                built.0
            }

            fn iterate(&mut self, domain: Extent) -> NodeId {
                self.add(node("IterateExtent", domain, vec![]))
            }

            fn filled(&mut self, domain: Extent) -> NodeId {
                let source = self.iterate(domain.clone());
                self.add(node(
                    "MapResultWithSource",
                    domain,
                    vec![edge("input", source)],
                ))
            }

            fn memo(&mut self, input: NodeId) -> NodeId {
                self.add(node("Memo", keys(), vec![edge("input", input)]))
            }

            fn slot(&mut self, memo: NodeId) -> NodeId {
                self.add(node(
                    "FanOutSlot",
                    keys(),
                    vec![InputEdge {
                        role: EdgeRole::Named("fan"),
                        kind: EdgeKind::Share,
                        subscribed: memo,
                    }],
                ))
            }

            fn read(&mut self, input: NodeId, function: NodeId) -> NodeId {
                self.read_in(keys(), input, function)
            }

            fn read_in(&mut self, domain: Extent, input: NodeId, function: NodeId) -> NodeId {
                self.add(node(
                    "MapResult",
                    domain,
                    vec![edge("input", input), edge("fn", function)],
                ))
            }

            fn constant(&mut self) -> NodeId {
                self.add(node("Constant", keys(), vec![]))
            }

            fn restrict(&mut self, predicate: NodeId) -> NodeId {
                self.add(node("Restrict", keys(), vec![edge("predicate", predicate)]))
            }

            fn planner(&self) -> Planner<'_> {
                Planner {
                    by_id: self
                        .0
                        .iter()
                        .map(|node| match node {
                            GraphNode::Operator { id, .. } | GraphNode::Sink { id, .. } => {
                                (*id, node)
                            }
                        })
                        .collect(),
                    pipelines: Vec::new(),
                    memos: HashSet::new(),
                    keyed_memos: HashMap::new(),
                    converses: HashSet::new(),
                }
            }
        }

        fn refused(planner: &mut Planner<'_>, top: NodeId) -> String {
            planner
                .pipeline(top, BreakerKind::Collect)
                .expect_err("the plan refuses the chain")
                .to_string()
        }

        /// A `MapExtractAggregate` over a `MapAggregate` at the top of an output is a grouped fold
        /// whose pipeline ends in the `MapAggregate` and starts at its input.
        #[test]
        fn a_map_extract_over_a_map_aggregate_is_a_group_breaker() {
            let mut nodes = Nodes::default();
            let source = nodes.filled(keys());
            let groups = nodes.add(node("MapAggregate", keys(), vec![edge("input", source)]));
            let extract = nodes.add(node(
                "MapExtractAggregate",
                keys(),
                vec![edge("input", groups)],
            ));
            let planner = nodes.planner();
            let (breaker, chain) = planner.breaker_at(extract);
            assert!(
                matches!(breaker, BreakerKind::Group { aggregate } if aggregate == groups),
                "the group breaker names the `MapAggregate`"
            );
            assert_eq!(
                chain, source,
                "the pipeline starts at the aggregate's input"
            );
        }

        /// A `Converse` under a grouped fold is a pipeline of its own that the fold's pipeline
        /// streams from.
        #[test]
        fn a_converse_under_a_grouped_fold_is_a_pipeline_the_fold_streams_from() {
            let mut nodes = Nodes::default();
            let source = nodes.filled(keys());
            let converse = nodes.add(node("Converse", keys(), vec![edge("input", source)]));
            let groups = nodes.add(node("MapAggregate", keys(), vec![edge("input", converse)]));
            let extract = nodes.add(node(
                "MapExtractAggregate",
                keys(),
                vec![edge("input", groups)],
            ));
            let mut planner = nodes.planner();
            let (breaker, chain) = planner.breaker_at(extract);
            let last = planner.pipeline(chain, breaker).expect("planned");
            assert_eq!(planner.pipelines.len(), 2);
            let (inversion, folding) = (&planner.pipelines[0], &planner.pipelines[last]);
            assert!(
                matches!(inversion.breaker, BreakerKind::Invert { converse: c } if c == converse)
            );
            assert!(inversion.head == Head::Source);
            assert!(matches!(folding.breaker, BreakerKind::Group { .. }));
            assert!(folding.head == Head::Breaker);
            assert_eq!(folding.streams_from, [0]);
        }

        /// The pipeline that ends in a `Converse` pushes its groups to one parent, so a second read
        /// of the same `Converse` is refused.
        #[test]
        fn a_converse_read_by_two_pipelines_is_refused() {
            let mut nodes = Nodes::default();
            let source = nodes.filled(keys());
            let converse = nodes.add(node("Converse", keys(), vec![edge("input", source)]));
            let groups = nodes.add(node("MapAggregate", keys(), vec![edge("input", converse)]));
            let mut planner = nodes.planner();
            planner
                .pipeline(converse, BreakerKind::Group { aggregate: groups })
                .expect("the first read");
            let second = planner
                .pipeline(converse, BreakerKind::Group { aggregate: groups })
                .err()
                .expect("a second read")
                .to_string();
            assert!(second.contains("more than one pipeline"), "{second}");
        }

        /// A collecting pipeline subscribes its chain afresh, which would invert a second time, so
        /// it does not start at a `Converse`.
        #[test]
        fn a_converse_read_by_a_collecting_pipeline_is_refused() {
            let mut nodes = Nodes::default();
            let source = nodes.filled(keys());
            let converse = nodes.add(node("Converse", keys(), vec![edge("input", source)]));
            let mut planner = nodes.planner();
            assert!(refused(&mut planner, converse).contains("read by a collecting pipeline"));
        }

        /// A `MapAggregate` with no extraction above it is not a group breaker.
        #[test]
        fn a_map_aggregate_alone_is_not_a_group_breaker() {
            let mut nodes = Nodes::default();
            let source = nodes.filled(keys());
            let groups = nodes.add(node("MapAggregate", keys(), vec![edge("input", source)]));
            let planner = nodes.planner();
            let (breaker, chain) = planner.breaker_at(groups);
            assert!(matches!(breaker, BreakerKind::Collect));
            assert_eq!(chain, groups);
        }

        /// A keyed read is admitted over the iterated source's own extent.
        #[test]
        fn a_keyed_read_over_the_memos_own_extent_is_planned() {
            let mut nodes = Nodes::default();
            let slot = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                nodes.slot(memo)
            };
            let source = nodes.iterate(keys());
            let read = nodes.read(source, slot);
            let mut planner = nodes.planner();
            planner
                .pipeline(read, BreakerKind::Collect)
                .expect("a keyed read is planned");
            assert!(
                planner
                    .pipelines
                    .last()
                    .is_some_and(|last| last.head == Head::Breaker && last.streams_from.len() == 1)
            );
        }

        /// The memo is read at the values of the input, so they must be the keys.
        #[test]
        fn a_keyed_read_of_values_that_are_not_the_keys_is_refused() {
            let mut nodes = Nodes::default();
            let slot = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                nodes.slot(memo)
            };
            let values = nodes.filled(keys());
            let by_value = nodes.read(values, slot);
            let source = nodes.iterate(keys());
            let function = nodes.constant();
            let mapped = nodes.read(source, function);
            let by_mapped = nodes.read(mapped, slot);
            let mut planner = nodes.planner();
            for top in [by_value, by_mapped] {
                let reason = refused(&mut planner, top);
                assert!(reason.contains("which must be the keys"), "{reason}");
            }
        }

        /// A chain whose morsels are one memo's merged keys cannot read another memo.
        #[test]
        fn a_chain_that_keyed_reads_two_memos_is_refused() {
            let mut nodes = Nodes::default();
            let (slot_a, slot_b) = {
                let first = nodes.filled(keys());
                let first = nodes.memo(first);
                let second = nodes.filled(keys());
                let second = nodes.memo(second);
                (nodes.slot(first), nodes.slot(second))
            };
            let source = nodes.iterate(keys());
            let inner = nodes.read(source, slot_a);
            let kept = nodes.restrict(inner);
            let outer = nodes.read(kept, slot_b);
            let mut planner = nodes.planner();
            let reason = refused(&mut planner, outer);
            assert!(reason.contains("more than one `Memo`"), "{reason}");
        }

        /// A memo read by a slot that starts a chain, and at keys, in either order.
        #[test]
        fn a_memo_read_both_by_a_head_slot_and_at_keys_is_refused() {
            let mut nodes = Nodes::default();
            let (head, keyed_slot) = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                (nodes.slot(memo), nodes.slot(memo))
            };
            let source = nodes.iterate(keys());
            let read = nodes.read(source, keyed_slot);
            let mut planner = nodes.planner();
            planner
                .pipeline(head, BreakerKind::Collect)
                .expect("a head slot");
            let reason = refused(&mut planner, read);
            assert!(reason.contains("also read at keys"), "{reason}");

            let mut planner = nodes.planner();
            planner
                .pipeline(read, BreakerKind::Collect)
                .expect("a keyed read");
            let reason = refused(&mut planner, head);
            assert!(
                reason.contains("also read by a slot that starts a chain"),
                "{reason}"
            );
        }

        /// The iterated source must have the memo's own keys.
        #[test]
        fn a_keyed_read_over_another_extent_is_refused() {
            let mut nodes = Nodes::default();
            let slot = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                nodes.slot(memo)
            };
            let source = nodes.iterate(Extent::uint_range(9));
            let read = nodes.read_in(Extent::uint_range(9), source, slot);
            let mut planner = nodes.planner();
            let reason = refused(&mut planner, read);
            assert!(
                reason.contains("keys that are not the iterated source's"),
                "{reason}"
            );
        }

        /// A keyed read under a chain that starts at a breaker's output has no iterated source.
        #[test]
        fn a_keyed_read_in_a_chain_that_starts_at_a_breaker_is_refused() {
            let mut nodes = Nodes::default();
            let slot = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                nodes.slot(memo)
            };
            let other = {
                let filled = nodes.filled(keys());
                let memo = nodes.memo(filled);
                nodes.slot(memo)
            };
            let function = nodes.constant();
            let mapped = nodes.read(other, function);
            let kept = nodes.restrict(mapped);
            let read = nodes.read(kept, slot);
            let mut planner = nodes.planner();
            let reason = refused(&mut planner, read);
            assert!(reason.contains("starts at a breaker's output"), "{reason}");
        }

        /// The slot must read a `Memo`'s own input.
        #[test]
        fn a_keyed_read_of_something_that_is_not_a_memo_is_refused() {
            let mut nodes = Nodes::default();
            let not_a_memo = nodes.filled(keys());
            let slot = nodes.slot(not_a_memo);
            let source = nodes.iterate(keys());
            let read = nodes.read(source, slot);
            let mut planner = nodes.planner();
            let reason = refused(&mut planner, read);
            assert!(reason.contains("not a `Memo`'s own input"), "{reason}");
        }

        /// A memo whose pipeline holds a `Restrict` drops keys, and is not read at keys yet.
        #[test]
        fn a_keyed_read_of_a_memo_that_drops_keys_is_refused() {
            let mut nodes = Nodes::default();
            let slot = {
                let filled = nodes.filled(keys());
                let kept = nodes.restrict(filled);
                let memo = nodes.memo(kept);
                nodes.slot(memo)
            };
            let source = nodes.iterate(keys());
            let read = nodes.read(source, slot);
            let mut planner = nodes.planner();
            let reason = refused(&mut planner, read);
            assert!(reason.contains("can drop a key"), "{reason}");
        }
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
            breaker: None,
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
                breaker: None,
            }],
            4,
        ));
        assert!(handle.set(dispatcher.clone()).is_ok());
        assert!(matches!(dispatcher.next(None), Next::Done));
        assert!(dispatcher.is_done(MAIN_PIPELINE));
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
                    breaker: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
                    streams_from: Vec::new(),
                    source: Box::new(move || live.clone()),
                    finalize: None,
                    breaker: None,
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

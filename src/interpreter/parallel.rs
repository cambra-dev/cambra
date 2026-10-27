//! Morsel-driven execution of a program's `main` pipeline on a pool of worker threads.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use std::{
    collections::HashMap,
    fmt,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
};

use crate::{
    ccl::{
        AggregateKind,
        context::{CompiledProgram, GlobalContext},
        provenance::NodeId,
    },
    interpreter::{
        LockNow, Predicate, Tile, TileGuard, Tiling,
        operator_graph::{EdgeKind, EdgeRole, GraphNode, OperatorGraph},
        tile_operators::{MorselSource, TileOperator, TileProducer},
    },
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

/// The pipeline shape the plan admits: any number of `MapResult`s whose function operand is a
/// `Constant`, over an `IterateExtent`, into the breaker. Every operator in the chain is
/// streaming, so a worker's chain holds no state between morsels. Which rows the source
/// enumerates, and whether it can be cut into morsels, is the source's to say
/// ([`TileOperator::morsel_source`]).
pub struct MainPipeline {
    /// What the chain ends in.
    pub breaker: Breaker,
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
}

/// Cut `graph` into the plan the pool runs, or say why it cannot.
pub fn plan_main(graph: &OperatorGraph) -> Result<MainPipeline, Unsupported> {
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
    if let Some(GraphNode::Operator {
        kind: "ExtractAggregate",
        inputs,
        ..
    }) = by_id.get(&at)
        && let [edge] = inputs.as_slice()
        && let Some(GraphNode::Operator {
            kind: "Aggregate",
            tiling: Tiling::Aggregation { kind, accumulator },
            inputs: fold_inputs,
            ..
        }) = by_id.get(&edge.subscribed)
        && let [fold_edge] = fold_inputs.as_slice()
    {
        breaker = Breaker::Fold {
            kind: *kind,
            accumulator: (**accumulator).clone(),
        };
        at = fold_edge.subscribed;
    }
    loop {
        match by_id.get(&at) {
            Some(GraphNode::Operator {
                kind: "MapResult",
                inputs,
                ..
            }) => {
                let edge = |role: &str| {
                    inputs
                        .iter()
                        .find(|edge| matches!(edge.role, EdgeRole::Named(name) if name == role))
                };
                let (Some(data), Some(function)) = (edge("input"), edge("fn")) else {
                    return Err(Unsupported("a `MapResult` without its two inputs".into()));
                };
                // The chain is a tree the walk descends once: an edge wired through a
                // `CycleSlot` closes a cycle, and a `Share` edge reaches a fan, neither of
                // which the plan admits, so following only owned edges bounds the walk.
                for edge in [data, function] {
                    if !matches!(edge.kind, EdgeKind::Value { deferred: false }) {
                        return Err(Unsupported(
                            "the chain closes a cycle or reads a shared node".into(),
                        ));
                    }
                }
                match by_id.get(&function.subscribed) {
                    Some(GraphNode::Operator {
                        kind: "Constant", ..
                    }) => {}
                    Some(GraphNode::Operator { kind, .. }) => {
                        return Err(Unsupported(format!(
                            "a `MapResult` applies a `{kind}`, and only a `Constant` is streamed"
                        )));
                    }
                    Some(GraphNode::Sink { .. }) | None => {
                        return Err(Unsupported(
                            "a `MapResult` applies something the graph holds no operator for"
                                .into(),
                        ));
                    }
                }
                at = data.subscribed;
            }
            Some(GraphNode::Operator {
                kind: "IterateExtent",
                ..
            }) => return Ok(MainPipeline { breaker }),
            Some(GraphNode::Operator { kind, .. }) => {
                return Err(Unsupported(format!(
                    "`{kind}` is not a streaming operator here"
                )));
            }
            Some(GraphNode::Sink { .. }) | None => {
                return Err(Unsupported("the chain reaches no source".into()));
            }
        }
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
    let pipeline = plan_main(&program.operator_graph)?;
    let output = program
        .main_mut()
        .ok_or_else(|| Unsupported("the program has no `main` output".into()))?;
    // The chain the workers subscribe: the whole output for a collection, the fold's input
    // for a fold, reached through the extract and the fold the plan saw.
    let chain_op: &mut dyn TileOperator = match pipeline.breaker {
        Breaker::Collect => &mut *output.op,
        Breaker::Fold { .. } => output
            .op
            .pool_input()
            .and_then(TileOperator::pool_input)
            .expect(
                "the plan saw an extract over a fold, and both reach through to the fold's input",
            ),
    };
    let source = source_of(chain_op)?;
    let tiling = chain_op.tiling().clone();
    // One chain per pipeline per worker, indexed by `PipelineId`: the plan has one pipeline.
    let mut chains: Vec<Vec<Box<dyn TileProducer>>> = (0..config.threads.max(1))
        .map(|_| {
            vec![chain_op.subscribe(tiling.universal_guard(), Box::new(|| {}), ctx.scheduler())]
        })
        .collect();
    let dispatcher = Dispatcher::new(vec![source], config.morsel_rows.max(1));
    let breaker = match &pipeline.breaker {
        Breaker::Collect => PoolBreaker::Collect {
            collector: Mutex::new(tiling.empty_tile()),
        },
        Breaker::Fold { kind, accumulator } => PoolBreaker::Fold {
            kind: *kind,
            seed: kind.initial_accumulator(accumulator),
            partials: Mutex::new(Vec::new()),
        },
    };
    // The chains are lent to the workers and dropped here, after the scope, one at a time:
    // a producer's drop detaches its probe with a lock that must not find the probe table
    // held by another worker's `get`.
    std::thread::scope(|scope| {
        // Armed before the first spawn: a spawn that panics stops the workers already running
        // from claiming further morsels.
        let _fail = FailOnUnwind(&dispatcher);
        for worker_chains in chains.iter_mut() {
            let (dispatcher, breaker) = (&dispatcher, &breaker);
            scope.spawn(move || run_worker(worker_chains, dispatcher, breaker));
        }
    });
    drop(chains);
    debug_assert!(
        dispatcher.is_done(MAIN_PIPELINE),
        "every worker returned, so every morsel was claimed and acknowledged"
    );
    Ok(breaker.finish())
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
        partials: Mutex<Vec<Tile>>,
    },
}

impl PoolBreaker {
    /// The answer once every worker has returned: complete, since the source answered every row
    /// it has, every package was acknowledged after its rows reached the breaker, and every
    /// fold worker has handed in its partial.
    fn finish(self) -> Tile {
        match self {
            PoolBreaker::Collect { collector } => {
                let mut tile = collector
                    .into_inner()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                // The statement the universal pull makes, `True`, is the collection's.
                if let Tile::DataFunction {
                    domain_predicate, ..
                } = &mut tile
                {
                    *domain_predicate = Predicate::True;
                }
                tile
            }
            PoolBreaker::Fold {
                kind,
                seed,
                partials,
            } => {
                let partials = partials
                    .into_inner()
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
                let mut total = seed;
                for partial in &partials {
                    kind.accumulate(&mut total, partial, 0, partial.rows());
                }
                // What `ExtractAggregate` emits once the fold is terminal.
                kind.extract(total)
            }
        }
    }
}

/// One worker's loop: take a package, pull the morsel through the package's pipeline, hand
/// the tile to the breaker, release the morsel, acknowledge the package, until the dispatcher
/// has none left. A fold worker then hands in its partial.
fn run_worker(
    chains: &mut [Box<dyn TileProducer>],
    dispatcher: &Dispatcher,
    breaker: &PoolBreaker,
) {
    let _fail = FailOnUnwind(dispatcher);
    let mut partial = match breaker {
        PoolBreaker::Collect { .. } => None,
        PoolBreaker::Fold { seed, .. } => Some(seed.clone()),
    };
    while let Some(package) = dispatcher.next() {
        let chain = &mut chains[package.pipeline.0];
        let mut tile = chain.get(package.guard.clone());
        match (breaker, &mut partial) {
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
        }
        // The release is the breaker's acknowledgement: the source may reclaim the morsel
        // only once the collector or the worker's partial holds its rows.
        chain.release(package.guard.clone());
        dispatcher.ack(package);
    }
    if let (PoolBreaker::Fold { partials, .. }, Some(partial)) = (breaker, partial) {
        partials.lock_wait().push(partial);
    }
}

/// A pipeline of a plan, by its position in the plan.
#[derive(Clone, Copy)]
struct PipelineId(usize);

/// The pipeline the plan's `main` chain is: the plan holds one pipeline.
const MAIN_PIPELINE: PipelineId = PipelineId(0);

/// One morsel of one pipeline: the unit a worker takes from the [`Dispatcher`].
///
/// The morsel is named by the guard a worker pulls the pipeline's chain at, never by its
/// rows: the tile is produced by that pull, so data reaches the breaker only through `get`.
struct WorkPackage {
    pipeline: PipelineId,
    guard: TileGuard,
}

/// What hands out the morsels of every pipeline of a plan, and records which pipelines can
/// still produce one.
///
/// A worker claims a morsel from a pipeline's source with [`next`](Self::next) and acknowledges
/// it with [`ack`](Self::ack) once the morsel is released. `next` never waits: a source either
/// answers a morsel or has none left. A pipeline is done when its source has answered `None`
/// and every morsel it answered is acknowledged. The dispatcher holds atomics and no lock. See
/// `src/interpreter/design-parallel.md`, "The dispatcher".
struct Dispatcher {
    /// Per pipeline, by `PipelineId`.
    jobs: Vec<Job>,
    /// Rows a morsel holds, which a worker claims at most.
    morsel_rows: u64,
    /// Set when a worker panics: every `next` answers `None` from then on, so the other
    /// workers stop claiming morsels of a run whose result is discarded.
    failed: AtomicBool,
}

/// One pipeline's source and its standing in the [`Dispatcher`].
struct Job {
    source: Arc<dyn MorselSource>,
    /// Whether the source has answered `None`, which is final.
    exhausted: AtomicBool,
    /// Morsels claimed and not acknowledged, plus claims in flight.
    outstanding: AtomicUsize,
}

impl Dispatcher {
    /// A dispatcher over one pipeline per source, in order.
    fn new(sources: Vec<Arc<dyn MorselSource>>, morsel_rows: u64) -> Self {
        Self {
            jobs: sources
                .into_iter()
                .map(|source| Job {
                    source,
                    exhausted: AtomicBool::new(false),
                    outstanding: AtomicUsize::new(0),
                })
                .collect(),
            morsel_rows,
            failed: AtomicBool::new(false),
        }
    }

    /// The next morsel of the first pipeline that has one, or `None` once every pipeline's
    /// source is exhausted or a worker failed.
    ///
    /// `None` is final because every pipeline's source exists from the start. A pipeline that
    /// appears after another finishes, behind a breaker, makes `None` mean "nothing now", and
    /// the dispatcher is where a worker would then wait.
    fn next(&self) -> Option<WorkPackage> {
        if self.failed.load(Ordering::Acquire) {
            return None;
        }
        for (index, job) in self.jobs.iter().enumerate() {
            if job.exhausted.load(Ordering::Acquire) {
                continue;
            }
            // Counted before the claim, so a thread that finds the source exhausted and no
            // outstanding morsel knows no claim is in flight.
            job.outstanding.fetch_add(1, Ordering::AcqRel);
            match job.source.claim(self.morsel_rows) {
                Some(guard) => {
                    return Some(WorkPackage {
                        pipeline: PipelineId(index),
                        guard,
                    });
                }
                None => {
                    job.outstanding.fetch_sub(1, Ordering::AcqRel);
                    job.exhausted.store(true, Ordering::Release);
                }
            }
        }
        None
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
    }

    /// Whether `pipeline`'s source is exhausted and every morsel it answered is acknowledged.
    fn is_done(&self, pipeline: PipelineId) -> bool {
        let job = &self.jobs[pipeline.0];
        // A claim counts itself before it asks the source, and the source's cursor orders its
        // updates. A thread that read `exhausted` read it after the claim that ended the
        // source, which the cursor ordered after every claim that answered a morsel, so it
        // reads each of those claims' counts: an exhausted source with nothing outstanding has
        // nothing in flight.
        job.exhausted.load(Ordering::Acquire) && job.outstanding.load(Ordering::Acquire) == 0
    }

    /// Stop every worker from claiming: a worker panicked.
    fn fail(&self) {
        self.failed.store(true, Ordering::Release);
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::{IterateExtent, RangeSource, zip_arms_at};
    use crate::interpreter::{BaseType, CurryLevel, Extent};
    use crate::interpreter::{FunctionGuard, Value};
    use intervalsets::Bounding;

    /// The `[first, last]` a package's guard names.
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

    fn dispatcher(rows: u64, morsel_rows: u64) -> Dispatcher {
        Dispatcher::new(vec![Arc::new(RangeSource::new(rows))], morsel_rows)
    }

    /// Everything a dispatcher hands out, in order, until it answers `None`.
    fn drain(dispatcher: &Dispatcher) -> Vec<(u64, u64)> {
        let mut taken = Vec::new();
        while let Some(package) = dispatcher.next() {
            taken.push(bounds(&package.guard));
            dispatcher.ack(package);
        }
        taken
    }

    fn iterate(extent: Extent) -> Box<dyn TileOperator> {
        Box::new(IterateExtent::new(extent))
    }

    #[test]
    fn the_source_is_the_one_leaf_that_cuts_morsels() {
        let source = source_of(&*iterate(Extent::uint_range(6))).expect("a finite range");
        assert!(source.claim(4).is_some());
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

    /// The first pipeline with a morsel answers, and the package names it.
    #[test]
    fn the_first_pipeline_with_a_morsel_answers() {
        let dispatcher = Dispatcher::new(
            vec![Arc::new(RangeSource::new(1)), Arc::new(RangeSource::new(5))],
            4,
        );
        let mut answered = Vec::new();
        while let Some(package) = dispatcher.next() {
            answered.push((package.pipeline.0, bounds(&package.guard)));
            dispatcher.ack(package);
        }
        assert_eq!(answered, [(0, (0, 0)), (1, (0, 3)), (1, (4, 4))]);
        assert!(dispatcher.is_done(PipelineId(0)) && dispatcher.is_done(PipelineId(1)));
    }

    #[test]
    fn a_range_to_the_largest_position_is_cut_without_overflow() {
        let dispatcher = dispatcher(u64::MAX, u64::MAX);
        let package = dispatcher.next().expect("the whole range is one morsel");
        assert_eq!(bounds(&package.guard), (0, u64::MAX - 1));
        dispatcher.ack(package);
        assert!(dispatcher.next().is_none());
    }

    #[test]
    fn morsels_are_disjoint_and_cover_the_range() {
        let dispatcher = dispatcher(10, 4);
        assert_eq!(drain(&dispatcher), [(0, 3), (4, 7), (8, 9)]);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    #[test]
    fn an_empty_range_hands_out_nothing_and_is_done_once_asked() {
        let dispatcher = dispatcher(0, 4);
        assert!(
            !dispatcher.is_done(MAIN_PIPELINE),
            "a source is exhausted once it has said so"
        );
        assert!(dispatcher.next().is_none());
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A claimed morsel keeps the pipeline from being done until it is acknowledged, though the
    /// source is exhausted.
    #[test]
    fn a_claimed_morsel_keeps_the_pipeline_open_until_acknowledged() {
        let dispatcher = dispatcher(1, 4);
        let package = dispatcher.next().expect("the one morsel");
        assert!(dispatcher.next().is_none());
        assert!(!dispatcher.is_done(MAIN_PIPELINE));
        dispatcher.ack(package);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// After a failure `next` answers `None`, whatever the source still holds.
    #[test]
    fn a_failed_dispatcher_hands_out_nothing() {
        let dispatcher = dispatcher(10, 4);
        dispatcher.fail();
        assert!(dispatcher.next().is_none());
    }

    /// A panicking worker stops the others from claiming, and the scope re-raises its panic.
    #[test]
    fn a_panicking_worker_stops_the_others_claiming() {
        let dispatcher = dispatcher(1000, 4);
        std::thread::scope(|scope| {
            let panicking = scope.spawn(|| {
                let _fail = FailOnUnwind(&dispatcher);
                panic!("a worker's chain panicked");
            });
            assert!(panicking.join().is_err());
            assert_eq!(drain(&dispatcher), []);
        });
    }

    /// Workers claiming at once split the range: every position is in exactly one morsel.
    #[test]
    fn concurrent_workers_claim_every_position_once() {
        let (rows, workers) = (100_003, 8);
        let dispatcher = dispatcher(rows, 7);
        let mut morsels: Vec<(u64, u64)> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .map(|_| scope.spawn(|| drain(&dispatcher)))
                .collect();
            handles
                .into_iter()
                .flat_map(|handle| handle.join().expect("a worker returns"))
                .collect()
        });
        morsels.sort_unstable();
        let mut next = 0;
        for (first, last) in morsels {
            assert_eq!(first, next, "morsels abut with no gap or overlap");
            next = last + 1;
        }
        assert_eq!(next, rows);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }
}

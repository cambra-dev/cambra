//! Morsel-driven execution of a program's `main` pipeline on a pool of worker threads.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use std::{
    collections::HashMap,
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
        Consumer, LockNow, Predicate, Projection, Scheduler, Tile, TileGuard, Tiling,
        operator_graph::{EdgeKind, EdgeRole, GraphNode, OperatorGraph},
        tile_operators::{Claim, MorselSource, TileOperator, TileProducer},
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

/// The pipeline shape the plan admits: any number of `MapResult`s, each applying a `Constant`
/// function operand to its input, and `MapResultWithSource`s, each reading a source's value at the
/// keys of an `IterateExtent` directly beneath it, over an `IterateExtent`, into the breaker.
/// Every operator in the chain is streaming, so a worker's chain holds no state between morsels.
/// Which rows the source enumerates, and whether it can be cut into morsels, is the source's to
/// say ([`TileOperator::morsel_source`]).
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
            // Reads a source's value at each key of its input: the keys are the input's, so the
            // chain streams.
            Some(GraphNode::Operator {
                kind: "MapResultWithSource",
                inputs,
                ..
            }) => {
                let [input] = inputs.as_slice() else {
                    return Err(Unsupported(
                        "a `MapResultWithSource` without its one input".into(),
                    ));
                };
                if !matches!(input.kind, EdgeKind::Value { deferred: false }) {
                    return Err(Unsupported(
                        "the chain closes a cycle or reads a shared node".into(),
                    ));
                }
                // It releases its source by correlating the keys it is released at with the
                // keys it reads, which only an `IterateExtent` beneath it states: over any other
                // input it releases the source on a universal guard alone, and the pool releases
                // morsels.
                if !matches!(
                    by_id.get(&input.subscribed),
                    Some(GraphNode::Operator {
                        kind: "IterateExtent",
                        ..
                    })
                ) {
                    return Err(Unsupported(
                        "a `MapResultWithSource` reads a source's value at the keys of an \
                         `IterateExtent` only"
                            .into(),
                    ));
                }
                at = input.subscribed;
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
    // The program is the pool's from here: a program the plan or `source_of` refused still has
    // its producer, and the scheduler loop drives it. The pool owns the pipeline's release
    // record, so the producer `compile_program` subscribed for `main` goes: it registered a
    // record that releases nothing, which a source would hold its reclaim at. It is in the
    // program's output, or with the caller that moved it out to drive it.
    let dropped = main_producer.take().or_else(|| output.producer.take());
    debug_assert!(
        dropped.is_some(),
        "the pool drops the producer that held the pipeline's record"
    );
    drop(dropped);
    let breaker = match &pipeline.breaker {
        Breaker::Collect => PoolBreaker::Collect {
            collector: Mutex::new(chain_op.tiling().empty_tile()),
        },
        Breaker::Fold { kind, accumulator } => PoolBreaker::Fold {
            kind: *kind,
            seed: kind.initial_accumulator(accumulator),
            partials: Mutex::new(Vec::new()),
        },
    };
    Ok(run_pipeline(
        ctx.scheduler(),
        chain_op,
        source,
        breaker,
        config,
        delivery,
    ))
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
fn run_pipeline(
    scheduler: &mut Scheduler,
    chain_op: &mut dyn TileOperator,
    source: Arc<dyn MorselSource>,
    breaker: PoolBreaker,
    config: &Config,
    delivery: Option<DeliveringThread<'_>>,
) -> Tile {
    let tiling = chain_op.tiling().clone();
    let dispatcher = Arc::new(Dispatcher::new(
        vec![PipelineSpec {
            after: Vec::new(),
            source: Box::new(move || source.clone()),
            finalize: None,
        }],
        config.morsel_rows.max(1),
    ));
    let handle = PipelineHandle {
        dispatcher: dispatcher.clone(),
        pipeline: PipelineId(0),
    };
    // One chain per pipeline per worker, indexed by `PipelineId`: the plan has one pipeline.
    // Notifications reach the dispatcher through the first worker's chain. Every chain's
    // source registration is notified of the same region, and one consumer publishes it: a
    // second would publish what the source has already claimed. The path from the source to
    // that consumer is region-driven and acyclic (`plan_main` admits no shared node or
    // recurrence), so no consumer on it drops or widens the region.
    //
    // The chains hold release records with a source, one per source operator and named for the
    // pool: each worker releases the morsels it ran, and a source reclaims what every record
    // releases. The records outlive the chains and retire when `records` drops.
    let (mut chains, records): (Vec<Vec<Box<dyn TileProducer>>>, _) = scheduler
        .with_pooled_release_records(pool_release_identity(), |scheduler| {
            (0..config.threads.max(1))
                .map(|worker| {
                    let head: Box<dyn Consumer> = match (&delivery, worker) {
                        (Some(_), 0) => Box::new(PipelineConsumer(handle.clone())),
                        _ => Box::new(|| {}),
                    };
                    vec![chain_op.subscribe(tiling.universal_guard(), head, scheduler)]
                })
                .collect()
        });
    // What the source holds when the pool starts is claimable: nothing notifies of rows that
    // arrived before the chains were subscribed, and a source's own subscription notification
    // reaches only worker 0's head and says nothing of them. Without a delivery no row arrives
    // later, so the source closes now.
    handle.publish(&Projection::Everything);
    if delivery.is_none() {
        handle.close();
    }
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
                let (dispatcher, breaker) = (&dispatcher, &breaker);
                scope.spawn(move || run_worker(worker_chains, dispatcher, breaker))
            })
            .collect();
        let delivered = delivery.and_then(|delivery| {
            let delivered = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
    if let Some(panic) = panic {
        std::panic::resume_unwind(panic);
    }
    drop(chains);
    drop(records);
    debug_assert!(
        dispatcher.all_done(),
        "every worker returned, so every pipeline finished"
    );
    breaker.finish()
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

/// One pool worker over the plan's one pipeline: its chain, the breaker it feeds, and for a
/// fold the partial it folds into. A plan with several pipelines needs a partial and a chain per
/// pipeline, which `leave` and `work` would index by the package's pipeline.
struct MainWorker<'a> {
    chains: &'a mut [Box<dyn TileProducer>],
    breaker: &'a PoolBreaker,
    partial: Option<Tile>,
}

impl PoolWorker for MainWorker<'_> {
    /// Pull the morsel through the package's pipeline, hand the tile to the breaker, release
    /// the morsel.
    fn work(&mut self, package: &WorkPackage) {
        let chain = &mut self.chains[package.pipeline.0];
        let mut tile = chain.get(package.guard.clone());
        match (self.breaker, &mut self.partial) {
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
    }

    /// A fold worker hands its partial in once, after its last morsel.
    fn leave(&mut self, pipeline: PipelineId) {
        debug_assert_eq!(pipeline.0, 0, "this worker serves the plan's one pipeline");
        if let (PoolBreaker::Fold { partials, .. }, Some(partial)) =
            (self.breaker, self.partial.take())
        {
            partials.lock_wait().push(partial);
        }
    }
}

/// One worker's turn on the dispatcher, until every pipeline has finished.
fn run_worker(
    chains: &mut [Box<dyn TileProducer>],
    dispatcher: &Dispatcher,
    breaker: &PoolBreaker,
) {
    let _fail = FailOnUnwind(dispatcher);
    let partial = match breaker {
        PoolBreaker::Collect { .. } => None,
        PoolBreaker::Fold { seed, .. } => Some(seed.clone()),
    };
    dispatcher.serve(&mut MainWorker {
        chains,
        breaker,
        partial,
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
    /// The source the pipeline's workers claim from, built once every pipeline in `after` has
    /// finished: a pipeline downstream of a breaker reads what the breaker produced. Called
    /// once, by the thread that finishes the last of them.
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
    /// Pipelines waiting on this one.
    dependents: Vec<usize>,
    /// Pipelines this one still waits on.
    waiting: AtomicUsize,
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
        for (index, spec) in pipelines.iter().enumerate() {
            for earlier in &spec.after {
                assert!(
                    earlier.0 < index,
                    "a pipeline waits on earlier pipelines only, got {} after {}",
                    index,
                    earlier.0
                );
                dependents[earlier.0].push(index);
            }
        }
        let jobs: Vec<Job> = pipelines
            .into_iter()
            .zip(dependents)
            .map(|(spec, dependents)| Job {
                waiting: AtomicUsize::new(spec.after.len()),
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
        let early = job.early.lock_wait();
        let source = (job.build)();
        source.publish(&early.region);
        if early.closed {
            source.close();
        }
        assert!(job.source.set(source).is_ok(), "a pipeline starts once");
    }

    /// The keys `arrived` have been added to the pipeline's source: unite the region into what
    /// the source can hand out, and wake the workers parked for want of a morsel.
    ///
    /// The caller has written the rows and made their keys ready before it calls, and holds
    /// no lock this call takes: the pipeline's early state, the source's state, the lock the
    /// source's yield-predicate function reads, and the lock that parks idle workers. The source
    /// takes the region under its own lock, and the epoch moves after that, so a worker that finds
    /// no morsel in its claim read the epoch before the move and its park returns at once.
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
        while self.epoch.load(Ordering::Acquire) == seen {
            guard = self
                .wake
                .wait(guard)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
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
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the inline driver is its caller")
    )]
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

#[cfg(test)]
#[path = "parallel_live_tests.rs"]
mod live_tests;

#[cfg(test)]
#[path = "parallel_source_tests.rs"]
mod source_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::{
        IterateExtent, LiveSource, RangeSource, uint_keys_in, uint_range, zip_arms_at,
    };
    use crate::interpreter::{BaseType, CurryLevel, Extent};
    use crate::interpreter::{FunctionGuard, Value};
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
                    source: Box::new(|| Arc::new(RangeSource::new(1))),
                    finalize: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
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

    /// Poll `condition` until it holds, failing after ten seconds.
    fn wait_until(condition: impl Fn() -> bool) {
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        while !condition() {
            assert!(
                std::time::Instant::now() < deadline,
                "the condition held in time"
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
        });
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
                    source: Box::new(|| Arc::new(RangeSource::new(2))),
                    finalize: None,
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
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

    /// A worker with nothing to claim parks while another holds a morsel of the pipeline it
    /// waits on, and the finish that morsel allows wakes it to run the next pipeline.
    #[test]
    fn an_idle_worker_parks_until_a_pipeline_finishes() {
        let log = Log::default();
        let dispatcher = graph(&[1, 4], &[&[], &[0]], &log);
        let (release, gate) = mpsc::channel();
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
            let (holder, idle) = (holder.join().expect("holder"), idle.join().expect("idle"));
            let second: Vec<_> = holder
                .morsels
                .iter()
                .chain(&idle.morsels)
                .filter(|(p, _)| *p == 1)
                .collect();
            assert_eq!(second.len(), 1, "the second pipeline's morsel ran once");
            assert!(dispatcher.all_done());
        });
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
                    source: Box::new(|| Arc::new(RangeSource::new(40))),
                    finalize: Some(Box::new(|| panic!("the breaker's combine failed"))),
                },
                PipelineSpec {
                    after: vec![PipelineId(0)],
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

//! Morsel-driven execution of a program's `main` pipeline on a pool of worker threads.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use std::{
    collections::{HashMap, VecDeque},
    fmt,
    sync::{Condvar, Mutex},
};

use intervalsets::{Bounding, Interval, IntervalSet};

use crate::{
    ccl::{
        context::{CompiledProgram, GlobalContext},
        provenance::NodeId,
    },
    interpreter::{
        Extent, FunctionGuard, LockNow, Predicate, Tile, TileGuard, Tiling, Value,
        operator_graph::{EdgeKind, EdgeRole, GraphNode, OperatorGraph},
        tile_operators::TileProducer,
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

/// The one pipeline shape the plan admits: `IterateExtent` over a finite range `[0, rows)`,
/// then any number of `MapResult`s whose function operand is a `Constant`, into the `main`
/// sink. Every operator in it is streaming, so a worker's chain holds no state between
/// morsels, and the sink is the only breaker.
#[derive(Debug)]
pub struct MainPipeline {
    /// The positions the source enumerates, `0..rows`.
    pub rows: u64,
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
                tiling,
                ..
            }) => {
                let Tiling::DataFunction {
                    domain: Extent::UIntRange(set),
                    ..
                } = tiling
                else {
                    return Err(Unsupported(format!(
                        "the source iterates `{tiling}`, and only a finite range is cut into \
                         morsels"
                    )));
                };
                return match set.intervals().as_slice() {
                    // An empty literal is the range `[0, 0)`.
                    [] => Ok(MainPipeline { rows: 0 }),
                    [one] if one.lval() == Some(&0) && one.rval().is_some() => Ok(MainPipeline {
                        rows: one.rval().map_or(0, |last| last + 1),
                    }),
                    _ => Err(Unsupported(format!(
                        "the source iterates `{tiling}`, and only a finite `[0, n)` is cut into \
                         morsels"
                    ))),
                };
            }
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

/// Run `program`'s `main` output on `config.threads` workers and return the whole collection,
/// complete, or say why the program is not one the pool runs.
///
/// Each worker owns one subscription of the chain. The pipeline's head publishes one
/// [`WorkPackage`] per morsel into the [`Dispatcher`] and closes the pipeline; each worker takes
/// packages from the dispatcher, pulls its chain at the package's guard, hands the tile to the
/// collector, releases the morsel once the collector holds it, and acknowledges the package.
/// The collector is the sink: it merges the workers' tiles and calls the collection complete
/// once the dispatcher reports the pipeline done.
pub fn run_main(
    ctx: &mut GlobalContext,
    program: &mut CompiledProgram,
    config: &Config,
) -> Result<Tile, Unsupported> {
    let pipeline = plan_main(&program.operator_graph)?;
    let output = program
        .main_mut()
        .ok_or_else(|| Unsupported("the program has no `main` output".into()))?;
    let tiling = output.op.tiling().clone();
    // One chain per pipeline per worker, indexed by `PipelineId`: the plan has one pipeline.
    let mut chains: Vec<Vec<Box<dyn TileProducer>>> = (0..config.threads.max(1))
        .map(|_| {
            vec![
                output
                    .op
                    .subscribe(tiling.universal_guard(), Box::new(|| {}), ctx.scheduler()),
            ]
        })
        .collect();
    let dispatcher = Dispatcher::new(1);
    let head = RangeHead {
        pipeline: MAIN_PIPELINE,
        rows: pipeline.rows,
        morsel_rows: config.morsel_rows.max(1),
    };
    let collector = Mutex::new(tiling.empty_tile());
    // The chains are lent to the workers and dropped here, after the scope, one at a time:
    // a producer's drop detaches its probe with a lock that must not find the probe table
    // held by another worker's `get`.
    std::thread::scope(|scope| {
        // Armed before the first spawn: a spawn that panics, or the head, ends the waits of the
        // workers already running.
        let _fail = FailOnUnwind(&dispatcher);
        for worker_chains in chains.iter_mut() {
            let (dispatcher, collector) = (&dispatcher, &collector);
            scope.spawn(move || run_worker(worker_chains, dispatcher, collector));
        }
        // The head runs on the calling thread while the workers drain the dispatcher.
        head.run(&dispatcher);
    });
    drop(chains);
    debug_assert!(
        dispatcher.is_done(MAIN_PIPELINE),
        "every worker returned, so the dispatcher drained a closed pipeline"
    );
    let mut tile = collector
        .into_inner()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    // The head published every row of `[0, rows)` and closed the pipeline, and every package
    // was acknowledged after its rows were merged, so the statement the universal pull makes,
    // `True`, is the collection's.
    if let Tile::DataFunction {
        domain_predicate, ..
    } = &mut tile
    {
        *domain_predicate = Predicate::True;
    }
    Ok(tile)
}

/// One worker's loop: take a package, pull the morsel through the package's pipeline, hand
/// the tile to the collector, release the morsel, acknowledge the package, until the
/// dispatcher has none left.
fn run_worker(
    chains: &mut [Box<dyn TileProducer>],
    dispatcher: &Dispatcher,
    collector: &Mutex<Tile>,
) {
    let _fail = FailOnUnwind(dispatcher);
    while let Some(package) = dispatcher.next() {
        let chain = &mut chains[package.pipeline.0];
        let tile = chain.get(package.guard.clone());
        collector.lock_wait().merge(tile);
        // The release is the sink's acknowledgement: the source may reclaim the morsel only
        // once the collector holds its rows.
        chain.release(package.guard.clone());
        dispatcher.ack(package);
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

/// The guard naming the morsel `[first, last]` of a range's positions.
fn morsel(first: u64, last: u64) -> TileGuard {
    TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
        IntervalSet::from(Interval::closed(Value::UInt(first), Value::UInt(last))),
    )))
}

/// The queue of work packages the workers take from, and the record of which pipelines can
/// still produce one.
///
/// A pipeline's head publishes packages and closes the pipeline once it will publish no more.
/// A worker takes a package with [`next`](Self::next), which waits while the queue is empty and
/// a pipeline is open, and acknowledges it with [`ack`](Self::ack) once the morsel is released.
/// A pipeline is done when it is closed and none of its packages is queued or taken. See
/// `src/interpreter/design-parallel.md`, "The dispatcher".
struct Dispatcher {
    // shared-state-ok: the queue between a pipeline's head and the workers. What crosses it
    // is a guard naming a morsel, never a tile: a worker produces the tile by pulling its own
    // chain at the guard.
    state: Mutex<DispatchState>,
    /// Signalled when a package is published, a pipeline closes or a worker fails: each can
    /// end a wait in `next`.
    changed: Condvar,
}

/// What the [`Dispatcher`]'s lock guards.
struct DispatchState {
    queue: VecDeque<WorkPackage>,
    /// Per pipeline, by `PipelineId`.
    pipelines: Vec<PipelineProgress>,
    /// Set when a worker or the head panics: every `next` answers `None` from then on, so the
    /// other workers return and the scope re-raises the panic instead of waiting for a package
    /// that will not come.
    failed: bool,
}

/// One pipeline's standing in the [`Dispatcher`].
struct PipelineProgress {
    /// Whether the head will publish no more packages.
    closed: bool,
    /// Packages a worker has taken and not acknowledged.
    taken: usize,
}

impl Dispatcher {
    /// A dispatcher over `pipelines` open pipelines with nothing queued.
    fn new(pipelines: usize) -> Self {
        let progress = (0..pipelines)
            .map(|_| PipelineProgress {
                closed: false,
                taken: 0,
            })
            .collect();
        Self {
            state: Mutex::new(DispatchState {
                queue: VecDeque::new(),
                pipelines: progress,
                failed: false,
            }),
            changed: Condvar::new(),
        }
    }

    /// Queue `package` behind every package already published.
    fn publish(&self, package: WorkPackage) {
        let mut state = self.state.lock_wait();
        debug_assert!(
            !state.pipelines[package.pipeline.0].closed,
            "a closed pipeline publishes no package"
        );
        state.queue.push_back(package);
        self.changed.notify_one();
    }

    /// Record that `pipeline`'s head will publish no more packages.
    fn close(&self, pipeline: PipelineId) {
        self.state.lock_wait().pipelines[pipeline.0].closed = true;
        self.changed.notify_all();
    }

    /// The oldest queued package, waiting while the queue is empty and a pipeline is open.
    /// `None` once the queue is empty and every pipeline is closed, or once a worker failed.
    fn next(&self) -> Option<WorkPackage> {
        let mut state = self.state.lock_wait();
        loop {
            if state.failed {
                return None;
            }
            if let Some(package) = state.queue.pop_front() {
                state.pipelines[package.pipeline.0].taken += 1;
                return Some(package);
            }
            if state.pipelines.iter().all(|progress| progress.closed) {
                return None;
            }
            state = self
                .changed
                .wait(state)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
    }

    /// Record that `package`'s morsel is in the breaker and released.
    fn ack(&self, package: WorkPackage) {
        let mut state = self.state.lock_wait();
        let progress = &mut state.pipelines[package.pipeline.0];
        debug_assert!(
            progress.taken > 0,
            "a package is acknowledged once, after it was taken"
        );
        progress.taken -= 1;
    }

    /// Whether `pipeline` is closed and none of its packages is queued or taken.
    fn is_done(&self, pipeline: PipelineId) -> bool {
        let state = self.state.lock_wait();
        let progress = &state.pipelines[pipeline.0];
        progress.closed
            && progress.taken == 0
            && !state
                .queue
                .iter()
                .any(|package| package.pipeline.0 == pipeline.0)
    }

    /// End every wait in `next`: a worker or the head panicked.
    fn fail(&self) {
        self.state.lock_wait().failed = true;
        self.changed.notify_all();
    }
}

/// Fails the [`Dispatcher`] when the thread holding it unwinds, so no other worker waits for a
/// package the panicking thread would have published or a pipeline it would have closed.
struct FailOnUnwind<'a>(&'a Dispatcher);

impl Drop for FailOnUnwind<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.fail();
        }
    }
}

/// The head of a pipeline over a finite range `[0, rows)`: it cuts the range into morsels of
/// `morsel_rows` rows, publishes one package per morsel in order, and closes the pipeline.
struct RangeHead {
    pipeline: PipelineId,
    rows: u64,
    morsel_rows: u64,
}

impl RangeHead {
    fn run(&self, dispatcher: &Dispatcher) {
        let mut first = 0;
        while first < self.rows {
            let last = (first + self.morsel_rows).min(self.rows) - 1;
            dispatcher.publish(WorkPackage {
                pipeline: self.pipeline,
                guard: morsel(first, last),
            });
            first = last + 1;
        }
        dispatcher.close(self.pipeline);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// The `[first, last]` a package's guard names.
    fn bounds(package: &WorkPackage) -> (u64, u64) {
        let TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(set))) = &package.guard
        else {
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

    /// Everything a dispatcher hands out, in order, until it answers `None`.
    fn drain(dispatcher: &Dispatcher) -> Vec<(u64, u64)> {
        let mut taken = Vec::new();
        while let Some(package) = dispatcher.next() {
            taken.push(bounds(&package));
            dispatcher.ack(package);
        }
        taken
    }

    #[test]
    fn a_range_head_publishes_disjoint_morsels_covering_the_range_and_closes() {
        let dispatcher = Dispatcher::new(1);
        RangeHead {
            pipeline: MAIN_PIPELINE,
            rows: 10,
            morsel_rows: 4,
        }
        .run(&dispatcher);
        assert_eq!(drain(&dispatcher), [(0, 3), (4, 7), (8, 9)]);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    #[test]
    fn an_empty_range_publishes_nothing_and_is_done() {
        let dispatcher = Dispatcher::new(1);
        RangeHead {
            pipeline: MAIN_PIPELINE,
            rows: 0,
            morsel_rows: 4,
        }
        .run(&dispatcher);
        assert!(dispatcher.next().is_none());
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A taken package keeps the pipeline from being done until it is acknowledged.
    #[test]
    fn a_taken_package_keeps_the_pipeline_open_until_acknowledged() {
        let dispatcher = Dispatcher::new(1);
        dispatcher.publish(WorkPackage {
            pipeline: MAIN_PIPELINE,
            guard: morsel(0, 0),
        });
        dispatcher.close(MAIN_PIPELINE);
        assert!(
            !dispatcher.is_done(MAIN_PIPELINE),
            "a queued package keeps it open"
        );
        let package = dispatcher.next().expect("the published package");
        assert!(!dispatcher.is_done(MAIN_PIPELINE));
        dispatcher.ack(package);
        assert!(dispatcher.is_done(MAIN_PIPELINE));
    }

    /// A worker waiting on an empty queue takes the next package once it is published, and
    /// returns once the pipeline closes.
    #[test]
    fn a_waiting_worker_wakes_on_publish_and_on_close() {
        let dispatcher = Dispatcher::new(1);
        std::thread::scope(|scope| {
            let worker = scope.spawn(|| drain(&dispatcher));
            std::thread::sleep(Duration::from_millis(20));
            assert!(
                !worker.is_finished(),
                "an open, empty queue keeps the worker waiting"
            );
            dispatcher.publish(WorkPackage {
                pipeline: MAIN_PIPELINE,
                guard: morsel(0, 1),
            });
            std::thread::sleep(Duration::from_millis(20));
            assert!(
                !worker.is_finished(),
                "an open pipeline keeps the worker waiting"
            );
            dispatcher.close(MAIN_PIPELINE);
            assert_eq!(worker.join().expect("the worker returns"), [(0, 1)]);
        });
    }

    /// After a failure `next` answers `None`, whatever is still queued.
    #[test]
    fn a_failed_dispatcher_hands_out_nothing() {
        let dispatcher = Dispatcher::new(1);
        dispatcher.publish(WorkPackage {
            pipeline: MAIN_PIPELINE,
            guard: morsel(0, 0),
        });
        dispatcher.fail();
        assert!(dispatcher.next().is_none());
    }

    /// A panicking worker ends every other worker's wait, so the scope re-raises the panic
    /// instead of waiting for a pipeline nobody will close.
    #[test]
    fn a_panicking_worker_releases_the_waiting_ones() {
        let dispatcher = Dispatcher::new(1);
        std::thread::scope(|scope| {
            let waiting = scope.spawn(|| drain(&dispatcher));
            std::thread::sleep(Duration::from_millis(20));
            assert!(
                !waiting.is_finished(),
                "an open, empty queue keeps the worker waiting"
            );
            let panicking = scope.spawn(|| {
                let _fail = FailOnUnwind(&dispatcher);
                panic!("a worker's chain panicked");
            });
            assert!(panicking.join().is_err());
            assert_eq!(waiting.join().expect("the waiting worker returns"), []);
        });
    }
}

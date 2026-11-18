//! The planner that runs a compiled program through the dispatcher: it reads the pipelines off
//! the program's producer chains, plans each edge between two of them, and drives the run on
//! the calling thread. See `src/interpreter/design-dispatcher.md`, "Running a compiled program".

use std::cell::RefCell;
use std::ops::ControlFlow;
use std::rc::Rc;
use std::sync::Arc;

use smol_str::SmolStr;

use super::loop_scope::{self, Member, induction};
use super::*;
use crate::ccl::context::CompiledProgram;
use crate::interpreter::CurryLevel;
use crate::interpreter::sinks::ProducerSlot;
use crate::interpreter::tile_operators::StoreCell;
use crate::interpreter::tiling::Tile;
use crate::interpreter::{BaseType, DataSink, DataSourceDomainExtentImpl, Extent};

/// Run `program`'s pipelines through a dispatcher of `morsel_rows` on the calling thread.
/// The breakers are the producers in the chains under its sinks' producers and its `main` output's that are pipeline
/// breakers (`TileProducer::as_breaking_mut`), each store a reader slot reaches, and each sink's
/// own and the `main` output's ([`SinkBreaker`]), whose pipeline no pipeline reads. A breaker's
/// pipeline reads the pipelines of the nearest breakers beneath it, and the consumer at the
/// breaker's input is placed in the pipeline: the [`Entry`] there for a breaker in a chain, the
/// sink's consumer for a sink, and the entry before the driver's consumer for the `main` output
/// (`CompiledOutput::main_entry`). A pipeline pulls only its breaker's input, and a sink's pipeline
/// pulls the sink's producer, so a sink receives its producer's answer one package at a time, and
/// the `main` output its answers merged at its finish ([`run_program_into`]). A sink is done once
/// its producer is released whole; the run ends with one pull of each sink, which signals
/// `CompiledProgram::done` once every sink is. It answers what it planned for each pipeline, in
/// pipeline order, and what the `main` output answered, merged ([`Run::main`]).
///
/// An induction store exposes concrete run control (`TileProducer::as_induction_store_mut`).
/// Request and ordered store-step pipelines target that same producer, whose body pipelines
/// share the run's dispatcher. The planner first configures each scoped body with local indices,
/// then appends those graph configurations with global pipeline IDs. Cross-scope dependencies are
/// represented by scope request pipelines; body entries accept pushes only from their own body.
///
/// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
///
/// Every pipeline that reads another holds the rows its pushes and its start bring until every
/// pipeline it reads has completed them, and reads each row once ([`Dispatcher::wait_for_inputs`]). A push
/// brings the rows it names at the reader's entry, restated by the consumers between the two, a
/// widening one's as every row. A reader reads its input whole ([`Dispatcher::read_whole`]) where
/// a pipeline it reads pushes along no route to it, which a route walk of the consumers between
/// them finds ([`routes_to`]), or where no push and no start region names a region of its input. The
/// region a push names comes from a probe: the pushing breaker pushes `Everything` through its
/// consumer, as a push in the run would climb it, and the planner looks at what reaches the
/// reader's entry ([`Landing::probe`]). So is each range under a reader of pushes (an
/// `IterateExtent`) probed, such as a literal's positions, the one producer with no input that
/// keeps its consumer (`ProducerBase::leaf`). What the ranges bring that no push can name is
/// queued for the reader at the start of the run as one region.
///
/// # Errors
///
/// Where planning encounters an unsupported program shape, before execution and with no entry or
/// sink left placed: live ranges whose arrivals cannot be routed to
/// a supported input projection; incompatible direct shared reads; a breaker with no consuming
/// mode; or a store refused by [`Planner::store_pipeline`].
///
/// # Panics
///
/// As [`run_program_into`].
pub fn run_program(program: &mut CompiledProgram, morsel_rows: usize) -> Result<Run, Refused> {
    run_program_polling(program, morsel_rows, &mut sleep_when_idle)
}

/// [`run_program`] with `on_idle` called each time nothing is claimable and a live source has
/// yielded no new region since the last poll, before the next poll: [`run_program`] sleeps, and
/// a test feeds the source there. `on_idle` runs inside the run, so it notifies no consumer
/// (`dispatcher::in_a_run`).
///
/// # Errors
///
/// As [`run_program`].
///
/// # Panics
///
/// As [`run_program`].
pub fn run_program_polling(
    program: &mut CompiledProgram,
    morsel_rows: usize,
    on_idle: &mut dyn FnMut(),
) -> Result<Run, Refused> {
    let collected = Arc::new(Collected::default());
    let planned = run_program_into(program, morsel_rows, collected.clone(), on_idle)?;
    Ok(Run {
        planned,
        main: collected.take(),
    })
}

/// [`run_program_polling`] handing `main` the answers of the `main` output (`SinkBreaker::main`):
/// with no live source, one answer at the output pipeline's finish, its packages' answers merged
/// with what the producer states complete; over a live
/// source, each package's answer as it is consumed, and at the finish the answer that states the
/// output complete. The answers add up to a terminal one. The driver of a program that reads a live
/// source prints each delivery's part of the `main` output as it arrives. It answers what it
/// planned for each pipeline, in pipeline order.
///
/// # Errors
///
/// As [`run_program`].
///
/// # Panics
///
/// Where a round of a loop's scope pulls an operator beneath the outermost keys at a level it
/// restates no projection at (`Planner::unrestated_in_rounds`), and where [`run`] panics. In a
/// debug build, where a run that returns has not released the `main` output's producer whole, where
/// the pull at the output's finish answers a key or a value no package consumed, and where the
/// answers do not add up to a terminal one.
pub fn run_program_into(
    program: &mut CompiledProgram,
    morsel_rows: usize,
    main: Arc<dyn DataSink>,
    on_idle: &mut dyn FnMut(),
) -> Result<Vec<Planned>, Refused> {
    // A `main` output's producer is the driver's to pull; the run takes it into a slot, as a
    // sink's sits in one, and hands it back after. A program has at most one.
    let mut taken = None;
    let mut targets: Vec<RunTarget> = Vec::new();
    for (at, output) in program.outputs.iter_mut().enumerate() {
        if let Some(consumer) = &output.sink_consumer {
            let consumer_ref = consumer.borrow();
            targets.push((
                consumer_ref.producer_slot().clone(),
                consumer_ref.sink(),
                TargetEntry::Sink(consumer.clone()),
            ));
        } else if let Some(producer) = output.producer.take() {
            assert!(taken.is_none(), "a program has at most one `main` output");
            let placement = output
                .main_entry
                .clone()
                .expect("a `main` output keeps the placement of the entry before its consumer");
            let slot: ProducerSlot = Rc::new(RefCell::new(Some(producer)));
            taken = Some((at, slot.clone()));
            targets.push((slot, main.clone(), TargetEntry::Main(placement)));
        }
    }
    let returned = MainGivenBackOnUnwind {
        outputs: &mut program.outputs,
        taken: taken.clone(),
    };
    let result = run_targets(&targets, morsel_rows, &mut Idle(on_idle)).map(|ended| match ended {
        Ended::Done(planned) => planned,
        Ended::Paused(_) => unreachable!("an observer that never breaks pauses no run"),
    });
    drop(returned);
    if let Some((at, slot)) = &taken {
        let producer = slot.borrow_mut().take();
        debug_assert!(
            result.is_err()
                || producer
                    .as_ref()
                    .is_some_and(|producer| producer.obsolete_guard().is_universal()),
            "a run that returns has released the `main` output's producer whole, so the driver \
             pulls nothing more of it"
        );
        program.outputs[*at].producer = producer;
    }
    let planned = result?;
    complete_sinks(&targets);
    Ok(planned)
}

/// Reconcile terminal output after every pipeline finishes and signal each sink's completion.
/// Producers answer from completed breakers and are released whole.
fn complete_sinks(targets: &[RunTarget]) {
    for (_, _, entry) in targets {
        if let TargetEntry::Sink(consumer) = entry {
            consumer.borrow_mut().complete();
        }
    }
}

/// What a run's driver is told at a run's boundaries, on the run's thread, inside the run
/// (`dispatcher::in_a_run`): a pass of a run over live sources polls them, then runs until nothing
/// is claimable. A run with no live source has no boundary.
pub trait RunObserver {
    /// The pass has polled its live sources and notified no pipeline yet.
    fn polled(&mut self) {}
    /// No package or finish is claimed and incomplete, and none is claimable. `changed` says
    /// whether the pass notified a pipeline or closed one. `Break` ends the run here.
    fn drained(&mut self, changed: bool) -> ControlFlow<()>;
}

/// [`run_program_into`]'s observer: it calls `on_idle` after a pass that changed nothing and
/// never ends a run.
struct Idle<'a>(&'a mut dyn FnMut());

impl RunObserver for Idle<'_> {
    fn drained(&mut self, changed: bool) -> ControlFlow<()> {
        if !changed {
            (self.0)();
        }
        ControlFlow::Continue(())
    }
}

/// How a run ended, with what it planned for each pipeline.
pub enum Ended {
    /// Every live source yields everything and every pipeline has finished. The run has taken its
    /// last pull of each sink.
    Done(Vec<Planned>),
    /// The observer broke at a drained boundary. The run left nothing placed and pulled no sink.
    Paused(Vec<Planned>),
}

/// The roots of a run over one compiled program's outputs, which `program` keeps.
#[derive(Default)]
pub struct Targets(Vec<RunTarget>);

impl Targets {
    /// Every sink output of `program`.
    pub fn add_sinks(&mut self, program: &CompiledProgram) {
        for output in &program.outputs {
            if let Some(consumer) = &output.sink_consumer {
                let consumer_ref = consumer.borrow();
                self.0.push((
                    consumer_ref.producer_slot().clone(),
                    consumer_ref.sink(),
                    TargetEntry::Sink(consumer.clone()),
                ));
            }
        }
    }

    /// `program`'s `main` output, whose producer the run pulls from `slot` and hands the answers
    /// to `sink` (`SinkBreaker::main`).
    ///
    /// # Panics
    ///
    /// Where `program` has no `main` output.
    pub fn add_main(
        &mut self,
        program: &CompiledProgram,
        slot: ProducerSlot,
        sink: Arc<dyn DataSink>,
    ) {
        let placement = program
            .main()
            .and_then(|output| output.main_entry.clone())
            .expect("a `main` output keeps the placement of the entry before its consumer");
        self.0.push((slot, sink, TargetEntry::Main(placement)));
    }

    /// Run the pipelines under every root until `observer` breaks or every live source yields
    /// everything, and on [`Ended::Done`] take the last pull of each sink.
    ///
    /// # Errors
    ///
    /// As [`run_program`]. A refused run leaves nothing placed.
    pub fn run(
        &self,
        morsel_rows: usize,
        observer: &mut dyn RunObserver,
    ) -> Result<Ended, Refused> {
        let ended = run_targets(&self.0, morsel_rows, observer)?;
        if let Ended::Done(_) = ended {
            complete_sinks(&self.0);
        }
        Ok(ended)
    }
}

/// [`run_program`]'s `on_idle`: a millisecond's sleep before the next poll.
fn sleep_when_idle() {
    thread::sleep(std::time::Duration::from_millis(1));
}

/// What a dispatched run planned, and what the `main` output answered.
pub struct Run {
    /// What the run planned for each pipeline, in pipeline order.
    pub planned: Vec<Planned>,
    /// The `main` output's answers, merged: terminal.
    /// `None` for a program with no `main` output.
    pub main: Option<Tile>,
}

/// A `main` output's answers, merged as a sink merges what it is handed.
#[derive(Default)]
struct Collected {
    // shared-state-ok: the I/O boundary at a `main` output, which nothing reads back into the
    // graph; `DataSink::process` takes `&self`.
    tile: Mutex<Option<Tile>>,
}

impl Collected {
    fn take(&self) -> Option<Tile> {
        self.tile
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
    }
}

impl DataSink for Collected {
    fn process(&self, tile: &Tile) {
        let mut slot = self.tile.lock().unwrap_or_else(PoisonError::into_inner);
        match slot.as_mut() {
            None => *slot = Some(tile.clone()),
            Some(merged) => merged.merge(tile.clone()),
        }
    }
}

/// Run the pipelines under `targets`' producers, each a root its sink breaker pulls: a sink's,
/// whose consumer is placed in the sink's pipeline, or a `main` output's, whose entry is placed in
/// the output's pipeline.
fn run_targets(
    targets: &[RunTarget],
    morsel_rows: usize,
    observer: &mut dyn RunObserver,
) -> Result<Ended, Refused> {
    let mut runs = InductionRuns::new();
    let _sinks = SinksUnplacedOnUnwind(targets);
    let mut planner = Planner::default();
    let mut sink_breakers = Vec::new();
    let mut sink_pipelines = Vec::new();
    for (at, (root, sink, entry)) in targets.iter().enumerate() {
        let breaker = match entry {
            TargetEntry::Sink(_) => {
                crate::interpreter::tile_operators::SinkBreaker::new(root.clone(), sink.clone())
            }
            TargetEntry::Main(_) => {
                crate::interpreter::tile_operators::SinkBreaker::main(root.clone(), sink.clone())
            }
        };
        let under = {
            let mut root = root.borrow_mut();
            let producer = root.as_mut().expect("a root holds the producer it pulls");
            planner.pipelines_under(&mut **producer, "sink")
        };
        let pipeline = planner.add(Located::Sink(at), format!("SinkBreaker#{at}"), None, under);
        sink_pipelines.push(pipeline);
        sink_breakers.push(RefCell::new(breaker));
    }
    planner.check_direct();
    if let Some(refused) = planner.refused.take() {
        unplace(&planner.placements, targets);
        return Err(refused);
    }
    for ((_, _, entry), (pipeline, breaker)) in targets
        .iter()
        .zip(sink_pipelines.iter().zip(&sink_breakers))
    {
        let local = PipelineId(planner.local[*pipeline]);
        match entry {
            TargetEntry::Sink(consumer) => consumer
                .borrow_mut()
                .place(local, breaker.borrow().input_tiling(InputId::ONLY)),
            TargetEntry::Main(placement) => placement.set(Some(local)),
        }
    }
    // The breakers each loop's scope keeps, those of loops nested in a transaction writer's body
    // included, for the check of their rounds below.
    let mut kept = Vec::new();
    let transactions: Vec<(StoreCell, usize, transaction_scope::WriterRun)> = planner
        .scopes
        .iter()
        .enumerate()
        .filter_map(|(scope, planned)| {
            planned
                .writer
                .map(|writer| (scope, writer, planned.store.clone()))
        })
        .map(|(scope, writer, store)| {
            (
                store,
                writer,
                planner.build_transaction(scope, morsel_rows, &mut kept, &mut runs),
            )
        })
        .collect();
    for (store, writer, run) in transactions {
        runs.install_transaction(&store, writer, run);
    }
    let members = planner.members(None);
    let scopes: Vec<Option<StoreCell>> = members
        .located
        .iter()
        .map(|located| match located {
            Located::Scope { scope, .. } => {
                Some(planner.build_scope(*scope, morsel_rows, &mut kept, &mut runs))
            }
            _ => None,
        })
        .collect();
    if let Some(why) = planner.unrestated_in_rounds(&kept) {
        panic!("a round of a loop's scope pulls each operator at a level it restates: {why}");
    }
    let scope_at = |pipeline: PipelineId| {
        scopes[pipeline.0]
            .as_ref()
            .expect("a scope's pipeline holds its scope")
    };
    for (pipeline, scope) in scopes.iter().enumerate() {
        if let Some(scope) = scope {
            induction(scope).decide_through_drive(PipelineId(pipeline));
        }
    }
    for (pipeline, located) in members.located.iter().enumerate() {
        if let Located::Store { store, input, .. } = located {
            let producer = transaction_scope::transaction(store);
            if let Some(writer) = producer.writer_of(InputId(*input)) {
                let run = producer.writer_run(writer);
                loop_scope::reach_member(&run.members[run.driver.0], &mut |breaker, _| {
                    if let Some(target) = breaker
                        .as_producer()
                        .and_then(|producer| producer.completes_through())
                    {
                        *target.borrow_mut() =
                            Some((PipelineId(pipeline), breaker.input_tiling(InputId::ONLY)));
                    }
                });
            }
        }
    }
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| match &members.located[pipeline.0] {
        Located::Sink(sink) => call(&mut *sink_breakers[*sink].borrow_mut(), InputId::ONLY),
        Located::Store { store, input, .. } => {
            let mut store = store.borrow_mut();
            call(
                store
                    .as_breaking_mut()
                    .expect("a planned store is a pipeline breaker"),
                InputId(*input),
            )
        }
        Located::Scope { .. } => call(&mut *induction(scope_at(pipeline)), InputId::ONLY),
        Located::Chain(handle) => call(&mut *handle.borrow_mut(), InputId::ONLY),
    };
    // Induction request and step roles target the same store producer.
    let mut end_of = |pipeline: PipelineId| match &members.located[pipeline.0] {
        Located::Scope { .. } => Some(induction(scope_at(pipeline)).pushing_end()),
        _ => None,
    };
    // A scope or transaction writer with no live range of its own inherits ranges from pipelines
    // whose pushes preserve its source keys. Seed-opening dependencies supply no source keys.
    // A loop's scope, which reads only pipelines that
    // range over one, as a loop over a let-bound source reads the source's memo, takes those
    // ranges as its own where each read's pushes reach its drive as the drive's positions: the
    // scope is then notified of each delivery as rounds, as over the source itself, and holds each
    // delivery until the pipelines it reads have completed it (`Dispatcher::wait_for_inputs`).
    let one = Projection::admitting(Predicate::point(Value::UInt(0)));
    let inherited: Vec<Vec<LiveLeaf>> = (0..members.live.len())
        .map(|pipeline| {
            let scope = scopes[pipeline].as_ref();
            let store = matches!(members.located[pipeline], Located::Store { .. });
            if scope.is_none() && !store {
                return Vec::new();
            }
            let mut input = None;
            reach(PipelineId(pipeline), &mut |breaker, at| {
                input = breaker.input_tiling(at).domain_extent();
            });
            if !members.live[pipeline].is_empty() || members.reads[pipeline].is_empty() {
                return Vec::new();
            }
            let mut leaves = Vec::new();
            for &read in &members.reads[pipeline] {
                if store && members.opens_before[read] {
                    continue;
                }
                if members.live[read].is_empty() || !members.reads[read].is_empty() {
                    return Vec::new();
                }
                if store {
                    let (pusher, _, pushed) = end_of(PipelineId(read))
                        .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                    let routes = routes_to(&pusher, &pushed, pipeline);
                    if routes.is_empty()
                        || routes.iter().any(|route| !route.keeps_keys)
                        || members.live[read].iter().any(|leaf| {
                            let one = leaf.probe_region();
                            let arrived = probe(&pusher, PipelineId(read), &one, pipeline);
                            input.as_ref() != Some(&leaf.extent)
                                || arrived.is_empty()
                                || arrived.iter().any(|arrival| {
                                    Projection::of(&arrival.guard).as_ref() != Ok(&one)
                                })
                        })
                    {
                        return Vec::new();
                    }
                    leaves.extend(members.live[read].iter().cloned());
                    continue;
                }
                let (pusher, _, pushed) = end_of(PipelineId(read))
                    .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                let mut scope = induction(scope.expect("a non-store inherits through its scope"));
                let routes = scope.routes(&pusher, &pushed);
                let arrived = scope.arrivals(&pusher, &one);
                let positions = !routes.is_empty()
                    && routes.iter().all(|route| route.keeps_keys)
                    && !arrived.is_empty()
                    && arrived
                        .iter()
                        .all(|arrival| Projection::of(&arrival.guard).as_ref() == Ok(&one));
                if !positions {
                    return Vec::new();
                }
                leaves.extend(members.live[read].iter().cloned());
            }
            leaves
        })
        .collect();
    let arrivals: Vec<bool> = members
        .live
        .iter()
        .zip(&inherited)
        .zip(&members.reads)
        .map(|((leaves, inherited), reads)| {
            (!leaves.is_empty() || !inherited.is_empty()) && !reads.is_empty()
        })
        .collect();
    let (mut dispatcher, mut planned) = plan_edges(
        &members.reads,
        &members.names,
        &members.leaves,
        &arrivals,
        true,
        &members.kinds,
        &members.pushes_with,
        &members.opens_before,
        morsel_rows,
        &mut reach,
        &mut end_of,
    );
    // A `main` output's pipeline consumes its packages in queue order.
    for ((_, _, entry), (pipeline, breaker)) in targets
        .iter()
        .zip(sink_pipelines.iter().zip(&sink_breakers))
    {
        if let TargetEntry::Main(_) = entry {
            let local = planner.local[*pipeline];
            dispatcher.order(PipelineId(local));
            if reads_a_scope(&members.located, &members.reads, local) {
                breaker.borrow_mut().reads_a_loop();
            }
        }
    }
    let mut live = Vec::new();
    let mut reads_as_keys = Vec::new();
    for (pipeline, (own, inherited)) in members.live.iter().zip(&inherited).enumerate() {
        let inherits = own.is_empty() && !inherited.is_empty();
        let leaves = match inherits {
            true => inherited,
            false => own,
        };
        if leaves.is_empty() {
            continue;
        }
        let mut input = None;
        reach(PipelineId(pipeline), &mut |breaker, at| {
            input = Some(breaker.input_tiling(at))
        });
        let input = input.expect("a reach calls the breaker it reaches");
        let mut starts: Vec<TileGuard> = Vec::new();
        let notifies = match (&members.located[pipeline], scopes[pipeline].as_ref()) {
            // Inherited ranges reach the drive as its positions. Nonprefix ranges wait for
            // completion; otherwise the scope holds each delivery on the pipelines it reads.
            (Located::Store { .. }, _) if inherits => Notifies::Items,
            _ if inherits => match leaves.iter().all(|leaf| leaf.ordering_path().is_some()) {
                true => Notifies::Rounds,
                false => Notifies::Whole,
            },
            // A transaction store places the entry before its writer's source, so its items
            // are a delivery's keys where the writer's source is
            // the source every range under the writer reads.
            (Located::Store { .. }, _) => {
                let items_of =
                    |leaf: &LiveLeaf| input.domain_extent().as_ref() == Some(&leaf.extent);
                // One whose writer reads the source otherwise, as a concatenation of the source and
                // a list, takes its input whole once the source yields everything.
                match leaves.iter().all(items_of) {
                    true => Notifies::Items,
                    false => Notifies::Whole,
                }
            }
            // A loop's scope runs a round per position the drive emits. Its drive's positions are
            // a delivery's keys where one key reaches the drive's entry as itself, over the
            // source's domain. A source read otherwise, inside a loop nested in this one among
            // them, ends the scope's rows only once it yields everything, so the scope then reads
            // its input whole.
            (_, Some(scope)) => {
                let keys_are_positions = leaves.iter().all(|leaf| {
                    if leaf.ordering_path().is_none() {
                        return false;
                    }
                    let one = leaf.probe_region();
                    let mut scope = induction(scope);
                    let routes = scope.routes(&leaf.consumer, &[leaf.probe_region()]);
                    let arrived = scope.arrivals(&leaf.consumer, &one);
                    !routes.is_empty()
                        && routes.iter().all(|route| route.keeps_keys)
                        && input.domain_extent().as_ref() == Some(&leaf.extent)
                        && !arrived.is_empty()
                        && arrived
                            .iter()
                            .all(|arrival| Projection::of(&arrival.guard).as_ref() == Ok(&one))
                });
                match keys_are_positions {
                    true => Notifies::Rounds,
                    false => Notifies::Whole,
                }
            }
            // Any other pipeline: the range's route to the pipeline's entry is read, as a stream
            // edge's is. A path that keeps the range's keys brings an arrival restated as a
            // projection of the input's keys at any level, notified as it arrives. A path that
            // widens them names every key of the input, which is final only once the source yields
            // everything, so the pipeline then reads its whole input once, every range's part of it
            // included.
            _ => {
                let mut notifies = Notifies::Arrivals;
                for leaf in leaves {
                    let one = leaf.probe_region();
                    let routes = routes_to(&leaf.consumer, std::slice::from_ref(&one), pipeline);
                    if routes.is_empty() {
                        unplace(&planner.placements, targets);
                        return Err(Refused(format!(
                            "a live source's arrivals reach no entry of {}, so no package names \
                             them",
                            members.names[pipeline]
                        )));
                    }
                    let arrived = probe(&leaf.consumer, PipelineId(pipeline), &one, pipeline);
                    if routes.iter().any(|route| !route.keeps_keys) {
                        notifies = Notifies::Whole;
                    } else if !arrived
                        .iter()
                        .all(|arrival| Projection::of(&arrival.guard).is_ok())
                    {
                        unplace(&planner.placements, targets);
                        return Err(Refused(format!(
                            "a live source's arrivals reach {} as a region that is no \
                             projection of its keys, which no package names",
                            members.names[pipeline]
                        )));
                    }
                }
                // A range of the pipeline's own that no source yields brings its rows once: its
                // probe's region is queued with the first notification. A range whose route
                // widens names every key of the input, which the pipeline then reads whole.
                if matches!(notifies, Notifies::Arrivals) {
                    for (range, pushes) in &members.leaves[pipeline] {
                        if routes_to(range, pushes, pipeline)
                            .iter()
                            .all(|route| route.keeps_keys)
                        {
                            let everything = Projection::Everything;
                            starts.extend(
                                probe(range, PipelineId(pipeline), &everything, pipeline)
                                    .into_iter()
                                    .map(|arrival| arrival.guard),
                            );
                        } else {
                            notifies = Notifies::Whole;
                        }
                    }
                }
                // A pipeline notified of arrivals takes no package but theirs and its ranges', so
                // a pipeline it reads whose pushes arrive as its own keys brings rows no arrival
                // names.
                if matches!(notifies, Notifies::Arrivals) {
                    let everything = Projection::Everything;
                    // The region of the pipeline's input its live ranges bring.
                    let arrived_region = leaves
                        .iter()
                        .flat_map(|leaf| {
                            probe(&leaf.consumer, PipelineId(pipeline), &everything, pipeline)
                        })
                        .fold(input.empty_guard(), |region, arrival| {
                            region.union(&arrival.guard)
                        });
                    for &read in &members.reads[pipeline] {
                        let (pusher, keyed, pushed) = end_of(PipelineId(read))
                            .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                        // A keyed breaker's push arrives as keys along a route that keeps them. A
                        // breaker of one value brings rows where its push names rows no arrival
                        // brings, as a let-bound record's collection field does; where it names
                        // only rows the arrivals bring, those rows read it, and wait for its
                        // complete push.
                        let as_keys = match keyed {
                            true => routes_to(&pusher, &pushed, pipeline)
                                .iter()
                                .any(|route| route.keeps_keys),
                            false => probe(&pusher, PipelineId(read), &everything, pipeline)
                                .iter()
                                .any(|arrival| {
                                    !arrival.guard.is_universal()
                                        && !guard_minus(&arrival.guard, &arrived_region).is_empty()
                                }),
                        };
                        // A pipeline whose pushes arrive as this one's keys brings rows no
                        // arrival names, so each of its pushes queues the rows it names.
                        if as_keys {
                            reads_as_keys.push((pipeline, read));
                        }
                    }
                }
                notifies
            }
        };
        planned[pipeline].live = true;
        planned[pipeline].whole |= matches!(notifies, Notifies::Whole);
        // A store or a loop's scope steps on the pipelines it reads by pull, so it holds each
        // delivery until they have completed it (`Dispatcher::wait_for_inputs`).
        if matches!(
            members.located[pipeline],
            Located::Store { .. } | Located::Scope { .. }
        ) && !members.reads[pipeline].is_empty()
        {
            dispatcher.wait_for_inputs(PipelineId(pipeline));
            planned[pipeline].held = true;
        }
        if matches!(notifies, Notifies::Whole) {
            starts.clear();
        }
        live.push(LivePipeline::new(
            PipelineId(pipeline),
            leaves.clone(),
            notifies,
            input,
            starts,
        ));
    }
    for (reader, read) in reads_as_keys {
        dispatcher.queue_pushes_of(PipelineId(reader), PipelineId(read));
    }
    // Over a live source a `main` output hands each package's answer as it consumes it, since
    // the run finishes it only once every source yields everything. A run with no live source
    // finishes it once its input is whole, so it merges its packages' answers until then and
    // hands one terminal answer.
    if !live.is_empty() {
        for ((_, _, entry), breaker) in targets.iter().zip(&sink_breakers) {
            if let TargetEntry::Main(_) = entry {
                breaker.borrow_mut().hand_each_package();
            }
        }
    }
    // Initialize every planned breaker before any package executes.
    for pipeline in 0..members.names.len() {
        reach(PipelineId(pipeline), &mut |breaker, _| breaker.begin_run());
    }
    let mut execution = Execution::new(&scopes, &mut dispatcher);
    for (pipeline, located) in members.located.iter().enumerate() {
        if let Located::Store { store, input, .. } = located {
            let writer = transaction_scope::transaction(store).writer_of(InputId(*input));
            if let Some(writer) = writer {
                execution.attach_transaction(
                    store,
                    writer,
                    InputId(*input),
                    PipelineId(pipeline),
                    &mut dispatcher,
                );
            }
        }
    }
    let mut root_reach = reach;
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
        execution.reach(pipeline, &mut root_reach, call);
    };
    let done = in_a_run(|| {
        // A range over a static extent has completed every key from the start.
        for (pipeline, ranges) in members.leaves.iter().enumerate() {
            for (range, _) in ranges {
                dispatcher.land_range_complete(
                    PipelineId(pipeline),
                    &Projection::Everything,
                    range,
                );
            }
        }
        match live.is_empty() {
            true => {
                execution.drive(&dispatcher, &mut reach);
                true
            }
            false => drive_live(&dispatcher, &mut reach, &execution, &mut live, observer),
        }
    });
    // Every breaker and range is terminal at the run's end, so each pipeline has recorded as
    // complete by each of its sources all that a push of the source's every key lands as at its
    // entry. A run that pauses stops at a drained boundary before its end, and checks nothing.
    #[cfg(debug_assertions)]
    if done {
        for (reader, reads) in members.reads.iter().enumerate() {
            let covered = |source: usize, reached: Vec<Arrival>, name: &str| {
                let Some(reached) = reached
                    .into_iter()
                    .map(|arrival| arrival.guard)
                    .reduce(|a, b| a.union(&b))
                else {
                    return;
                };
                let complete = dispatcher.complete_of(PipelineId(reader), PipelineId(source));
                debug_assert!(
                    complete.covers(&reached),
                    "{name} has completed all it reaches of {}'s input, {reached:?}, at the run's end, \
                     which records {complete:?}",
                    members.names[reader]
                );
            };
            for &read in reads {
                let (pusher, _, _) = end_of(PipelineId(read))
                    .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                let reached = probe(&pusher, PipelineId(read), &Projection::Everything, reader);
                covered(read, reached, &members.names[read]);
            }
            // A range reaches the entries of the pipelines it is listed under, and possibly others.
            let ranges = members
                .leaves
                .iter()
                .enumerate()
                .flat_map(|(pipeline, ranges)| {
                    ranges.iter().map(move |(range, _)| (pipeline, range))
                });
            let live = members
                .live
                .iter()
                .enumerate()
                .flat_map(|(pipeline, leaves)| {
                    leaves.iter().map(move |leaf| (pipeline, &leaf.consumer))
                });
            for (pipeline, range) in ranges.chain(live) {
                let reached = probe(range, PipelineId(pipeline), &Projection::Everything, reader);
                covered(reader, reached, "a range in its own chain");
            }
        }
    }
    for (plan, scope) in planned.iter_mut().zip(&scopes) {
        if let Some(scope) = scope {
            plan.rounds = std::mem::take(
                &mut induction(scope)
                    .run
                    .as_mut()
                    .expect("the plan owns its run")
                    .planned,
            );
        }
    }
    for (pipeline, located) in members.located.iter().enumerate() {
        if let Located::Store { store, input, .. } = located {
            let mut producer = transaction_scope::transaction(store);
            if let Some(writer) = producer.writer_of(InputId(*input)) {
                planned[pipeline].rounds =
                    std::mem::take(&mut producer.writer_run_mut(writer).planned);
            }
        }
    }
    Ok(match done {
        true => Ended::Done(planned),
        false => {
            // The next run plans the graph afresh and places what it reaches.
            unplace(&planner.placements, targets);
            Ended::Paused(planned)
        }
    })
}

/// The `main` producer [`run_program_into`] takes out of its output into the slot the run reads it
/// through, which it puts back into the output when the run unwinds, so a panic in the run loses
/// no `main`. A run that returns puts it back itself, after checking what the run left in it.
struct MainGivenBackOnUnwind<'p> {
    outputs: &'p mut [crate::ccl::context::CompiledOutput],
    taken: Option<(usize, ProducerSlot)>,
}

impl Drop for MainGivenBackOnUnwind<'_> {
    fn drop(&mut self) {
        if !thread::panicking() {
            return;
        }
        if let Some((at, slot)) = &self.taken {
            // The run's frames have dropped before this one, so nothing borrows the slot; a borrow
            // that still did would make a second panic here, which aborts.
            if let Ok(mut slot) = slot.try_borrow_mut() {
                self.outputs[*at].producer = slot.take();
            }
        }
    }
}

/// Owns installed scheduling metadata from planning through every run exit, including unwinding.
pub(super) struct InductionRuns {
    stores: Vec<StoreCell>,
    transactions: Vec<StoreCell>,
}

impl InductionRuns {
    pub(super) fn new() -> Self {
        Self {
            stores: Vec::new(),
            transactions: Vec::new(),
        }
    }

    fn install_transaction(
        &mut self,
        store: &StoreCell,
        writer: usize,
        run: transaction_scope::WriterRun,
    ) {
        let mut producer = transaction_scope::transaction(store);
        if producer.run.is_none() {
            self.transactions.push(store.clone());
            producer.run = Some(transaction_scope::TransactionRun {
                writers: Vec::new(),
                stalled: 0,
            });
        }
        let writers = &mut producer.run.as_mut().expect("a transaction run").writers;
        assert_eq!(
            writers.len(),
            writer,
            "writer bodies are installed in order"
        );
        writers.push(run);
    }
    fn install(&mut self, store: &StoreCell, run: loop_scope::InductionRun) {
        assert!(
            induction(store).run.is_none(),
            "a store has one run owner at a time"
        );
        self.stores.push(store.clone());
        induction(store).run = Some(run);
    }
}

impl Drop for InductionRuns {
    fn drop(&mut self) {
        for store in &self.transactions {
            transaction_scope::transaction(store).run = None;
        }
        for store in &self.stores {
            induction(store).clear_run();
        }
    }
}

// Body owners belong to the execution table, outside producer run metadata; a store retains
// no handle to itself through its handlers.
enum Handler {
    Root,
    Body(BreakerHandle),
    /// A scope's own pipeline, whose claims are the scope's requests.
    Request(Scope),
    /// A scope's step, whose claim ends a round or an attempt.
    Step(Scope),
}

/// A scope whose inner pipelines run on the run's shared dispatcher, between its request and
/// step handlers.
enum Scope {
    /// A loop: the store's rounds.
    Loop(StoreCell),
    /// One writer of a transaction store: its attempts.
    Writer { store: StoreCell, writer: usize },
}

impl Scope {
    fn reach(&self, call: &mut Call<'_>) {
        match self {
            Scope::Loop(store) => call(&mut *induction(store), InputId::ONLY),
            Scope::Writer { store, writer } => {
                let mut producer = transaction_scope::transaction(store);
                let (_, input) = producer.writer_run(*writer).attached();
                call(&mut *producer, input);
            }
        }
    }

    /// Whether a request is open, whose claim is in flight until it completes.
    fn has_request(&self) -> bool {
        match self {
            Scope::Loop(store) => induction(store).has_package(),
            Scope::Writer { store, writer } => transaction_scope::transaction(store)
                .writer_run(*writer)
                .has_request(),
        }
    }

    fn hold_followers(&self, dispatcher: &Dispatcher) {
        match self {
            Scope::Loop(store) => induction(store).hold_followers(dispatcher),
            Scope::Writer { store, writer } => transaction_scope::transaction(store)
                .writer_run_mut(*writer)
                .hold_followers(dispatcher),
        }
    }

    /// Land and acknowledge a request the scope has completed.
    fn complete(&self, dispatcher: &Dispatcher, package: Option<WorkPackage>) {
        let Some(package) = package else { return };
        let mut pushes = dispatcher.pushes(package.pipeline);
        match self {
            Scope::Loop(store) => {
                let store = induction(store);
                if store.pushes_while_consuming() {
                    pushes.push_final(&*store);
                }
            }
            Scope::Writer { store, .. } => {
                pushes.push_final(&*transaction_scope::transaction(store));
            }
        }
        dispatcher.land(pushes);
        dispatcher.acknowledge(package);
    }

    /// Open the request `package`, a claim of the scope's own pipeline.
    fn begin(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Scope::Loop(store) => {
                let completed = induction(store).begin_shared(dispatcher, package);
                self.complete(dispatcher, completed);
            }
            Scope::Writer { store, writer } => {
                transaction_scope::transaction(store).begin_request(dispatcher, *writer, package)
            }
        }
    }

    /// End the round or attempt whose step claimed `package`, and start the next or complete
    /// the request.
    fn step(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        let completed = match self {
            Scope::Loop(store) => {
                induction(store).complete_round();
                dispatcher.acknowledge(package);
                induction(store).queue_package_round(dispatcher)
            }
            Scope::Writer { store, writer } => {
                dispatcher.acknowledge(package);
                transaction_scope::transaction(store).finish_request(dispatcher, *writer)
            }
        };
        self.complete(dispatcher, completed);
    }

    fn begin_finish(&self, dispatcher: &Dispatcher, consumed: Option<TileGuard>) {
        match self {
            Scope::Loop(store) => induction(store).begin_shared_finish(dispatcher, consumed),
            Scope::Writer { store, writer } => transaction_scope::transaction(store)
                .begin_transaction_finish(dispatcher, *writer, consumed),
        }
    }

    /// Advance a scope the coordinator found waiting: finish its pipeline once the inner
    /// pipelines have, or publish what they hold and let their followers run. Whether anything
    /// changed.
    fn resume(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        let mut progressed = false;
        let finished = match self {
            Scope::Loop(store) => {
                progressed |= induction(store).initialize_seed();
                induction(store).take_shared_finish(dispatcher)
            }
            Scope::Writer { store, writer } => {
                transaction_scope::transaction(store).take_transaction_finish(dispatcher, *writer)
            }
        };
        if let Some((pipeline, consumed)) = finished {
            finish_with(dispatcher, reach, pipeline, consumed);
            if let Scope::Loop(store) = self {
                induction(store).unplace_shared();
            }
            return true;
        }
        // A loop publishes the inner pipelines a round settles; a writer, every inner pipeline.
        let pipelines = match self {
            Scope::Loop(store) => induction(store).settlement_pipelines(),
            Scope::Writer { store, writer } => transaction_scope::transaction(store)
                .writer_run(*writer)
                .pipelines(),
        };
        let before = dispatcher.changes();
        push_held(dispatcher, reach, pipelines);
        // No other claim executes during this scope's publication pass on the coordinator, so a
        // generation change here belongs to these pushes.
        if dispatcher.changes() != before {
            return true;
        }
        progressed
            | match self {
                Scope::Loop(store) => induction(store).release_followers(dispatcher),
                Scope::Writer { store, writer } => transaction_scope::transaction(store)
                    .writer_run_mut(*writer)
                    .release_followers(dispatcher),
            }
    }
}

pub(super) struct Execution {
    handlers: Vec<Handler>,
    roots: usize,
}

impl Execution {
    pub(super) fn new(scopes: &[Option<StoreCell>], dispatcher: &mut Dispatcher) -> Self {
        let mut execution = Self {
            handlers: scopes
                .iter()
                .map(|scope| match scope {
                    Some(store) => Handler::Request(Scope::Loop(store.clone())),
                    None => Handler::Root,
                })
                .collect(),
            roots: scopes.len(),
        };
        for (pipeline, scope) in scopes.iter().enumerate() {
            if let Some(store) = scope {
                execution.attach_store(store, dispatcher, PipelineId(pipeline));
            }
        }
        execution
    }

    /// The handlers of a scope's inner pipelines: a chain's breaker, or a nested loop's scope.
    fn member_handlers(members: &[Member]) -> impl Iterator<Item = Handler> + '_ {
        members.iter().map(|member| match member {
            Member::Chain(handle) => Handler::Body(handle.clone()),
            Member::Scope(child) => Handler::Request(Scope::Loop(child.clone())),
        })
    }

    fn attach_transaction(
        &mut self,
        store: &StoreCell,
        writer: usize,
        input: InputId,
        request: PipelineId,
        dispatcher: &mut Dispatcher,
    ) {
        let (graph, members) = {
            let mut producer = transaction_scope::transaction(store);
            let run = producer.writer_run_mut(writer);
            (
                run.graph.take().expect("an attempt graph is attached once"),
                run.members.clone(),
            )
        };
        let base = dispatcher.append_graph(graph);
        assert_eq!(
            base,
            self.handlers.len(),
            "each global pipeline has one handler"
        );
        self.handlers[request.0] = Handler::Request(Scope::Writer {
            store: store.clone(),
            writer,
        });
        self.handlers.extend(Self::member_handlers(&members));
        for (local, member) in members.iter().enumerate() {
            let pipeline = PipelineId(base + local);
            dispatcher.restrict_ingress(pipeline, base..base + members.len());
            dispatcher.hold_pipeline(pipeline, true);
            if let Member::Scope(child) = member {
                self.attach_store(child, dispatcher, pipeline);
            }
        }
        let body: Vec<_> = (base..base + members.len()).map(PipelineId).collect();
        let step = dispatcher.add_pipeline(body.clone());
        dispatcher.order(step);
        dispatcher.take_arrivals(step);
        for member in body {
            dispatcher.follow(step, member);
        }
        dispatcher.hold_pipeline(step, true);
        assert_eq!(step.0, self.handlers.len(), "each step has one handler");
        self.handlers.push(Handler::Step(Scope::Writer {
            store: store.clone(),
            writer,
        }));
        let mut producer = transaction_scope::transaction(store);
        let run = producer.writer_run_mut(writer);
        run.attach(loop_scope::SharedScope::new(request, base, step), input);
        loop_scope::reach_member(&run.members[run.driver.0], &mut |breaker, _| {
            for placement in &run.placements[run.driver.0] {
                placement.set(None);
            }
            if let Some(target) = breaker
                .as_producer()
                .and_then(|producer| producer.completes_through())
            {
                *target.borrow_mut() = Some((request, breaker.input_tiling(InputId::ONLY)));
            }
        });
    }

    fn attach_store(
        &mut self,
        store: &StoreCell,
        dispatcher: &mut Dispatcher,
        pipeline: PipelineId,
    ) {
        let (graph, members) = {
            let mut producer = induction(store);
            let run = producer.run.as_mut().expect("an induction run is planned");
            (
                run.body_graph
                    .take()
                    .expect("a body graph is attached once"),
                run.members.clone(),
            )
        };
        let base = dispatcher.append_graph(graph);
        assert_eq!(
            base,
            self.handlers.len(),
            "each global pipeline has one handler"
        );
        self.handlers.extend(Self::member_handlers(&members));
        for (local, member) in members.iter().enumerate() {
            dispatcher.restrict_ingress(PipelineId(base + local), base..base + members.len());
            if let Member::Scope(child) = member {
                self.attach_store(child, dispatcher, PipelineId(base + local));
            }
        }
        let body: Vec<_> = (base..base + members.len()).map(PipelineId).collect();
        let step = dispatcher.add_pipeline(body.clone());
        dispatcher.order(step);
        for &member in &body {
            dispatcher.follow(step, member);
            dispatcher.hold_pipeline(member, true);
        }
        dispatcher.hold_pipeline(step, true);
        assert_eq!(
            step.0,
            self.handlers.len(),
            "each global pipeline has one handler"
        );
        self.handlers
            .push(Handler::Step(Scope::Loop(store.clone())));
        induction(store)
            .run
            .as_mut()
            .expect("an induction run is planned")
            .shared = Some(loop_scope::SharedScope::new(pipeline, base, step));
        induction(store).decide_through_drive(pipeline);
    }

    pub(super) fn reach(&self, pipeline: PipelineId, root: &mut Reach<'_>, call: &mut Call<'_>) {
        match &self.handlers[pipeline.0] {
            Handler::Root => root(pipeline, call),
            Handler::Body(handle) => call(&mut *handle.borrow_mut(), InputId::ONLY),
            Handler::Request(scope) | Handler::Step(scope) => scope.reach(call),
        }
    }

    /// Every scope, each at its request handler.
    fn scopes(&self) -> impl Iterator<Item = &Scope> {
        self.handlers.iter().filter_map(|handler| match handler {
            Handler::Request(scope) => Some(scope),
            _ => None,
        })
    }

    fn hold_followers(&self, dispatcher: &Dispatcher) {
        for scope in self.scopes() {
            scope.hold_followers(dispatcher);
        }
    }

    pub(super) fn consume(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        package: WorkPackage,
    ) {
        match &self.handlers[package.pipeline.0] {
            Handler::Request(scope) => scope.begin(dispatcher, package),
            Handler::Step(scope) => scope.step(dispatcher, package),
            Handler::Root | Handler::Body(_) => consume_with(dispatcher, reach, package),
        }
        self.hold_followers(dispatcher);
    }

    pub(super) fn finish(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        pipeline: PipelineId,
        consumed: Option<TileGuard>,
    ) {
        match &self.handlers[pipeline.0] {
            Handler::Request(scope) => scope.begin_finish(dispatcher, consumed),
            Handler::Step(_) => dispatcher.finish(dispatcher.pushes(pipeline)),
            Handler::Root | Handler::Body(_) => finish_with(dispatcher, reach, pipeline, consumed),
        }
        self.hold_followers(dispatcher);
    }

    /// Assert what [`RunObserver::drained`] promises: no claim is in flight. A pause discards what
    /// one would leave (`src/interpreter/design-dispatcher.md`, "Pause and reload").
    #[cfg(debug_assertions)]
    pub(super) fn assert_nothing_in_flight(&self, dispatcher: &Dispatcher) {
        let in_flight: Vec<String> = dispatcher
            .in_flight()
            .into_iter()
            .map(|(pipeline, claim)| {
                let kind = match &self.handlers[pipeline] {
                    Handler::Root => "a pipeline of the program",
                    Handler::Body(_) => "a loop body",
                    Handler::Request(Scope::Loop(_)) => "a loop's store",
                    Handler::Step(Scope::Loop(_)) => "a loop's step",
                    Handler::Request(Scope::Writer { .. }) => "a transaction request",
                    Handler::Step(Scope::Writer { .. }) => "a transaction attempt",
                };
                format!("pipeline {pipeline}, {kind}, holds {claim}")
            })
            .collect();
        assert!(
            in_flight.is_empty(),
            "a drained boundary has no claim in flight: {}",
            in_flight.join("; ")
        );
    }

    pub(super) fn resume(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        let mut progressed = false;
        for scope in self.scopes() {
            progressed |= scope.resume(dispatcher, reach);
        }
        progressed
    }

    fn push_held(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
        let pipelines = self
            .handlers
            .iter()
            .enumerate()
            .filter(|(pipeline, handler)| {
                !matches!(handler, Handler::Step(_))
                    && !dispatcher.states[*pipeline].held.load(Ordering::SeqCst)
                    && !matches!(handler, Handler::Request(scope) if scope.has_request())
            })
            .map(|(pipeline, _)| PipelineId(pipeline))
            .collect::<Vec<_>>();
        push_held(dispatcher, reach, pipelines);
    }

    fn drive(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
        for pipeline in 0..self.roots {
            if dispatcher.is_source(PipelineId(pipeline)) {
                let mut input = None;
                reach(PipelineId(pipeline), &mut |breaker, at| {
                    input = Some(breaker.input_tiling(at))
                });
                let input = input.expect("a planned source has a breaker input");
                dispatcher.start_source(PipelineId(pipeline), &input, &input.empty_guard());
            }
        }
        loop {
            match dispatcher.try_claim(None) {
                Next::Package(package) => self.consume(dispatcher, reach, package),
                Next::Finish { pipeline, consumed } => {
                    self.finish(dispatcher, reach, pipeline, consumed)
                }
                Next::Wait(_) if self.resume(dispatcher, reach) => {}
                Next::Wait(_) => {
                    panic!("an acyclic run with no pending loop has a pipeline that may finish")
                }
                Next::Done => return,
                Next::Failed => panic!("a run on one thread fails only by panicking on it"),
            }
        }
    }
}

/// Whether `pipeline` reads a loop's scope, directly or through the pipelines it reads.
fn reads_a_scope(located: &[&Located], reads: &[Vec<usize>], pipeline: usize) -> bool {
    let mut seen = vec![false; reads.len()];
    let mut stack = vec![pipeline];
    while let Some(at) = stack.pop() {
        if std::mem::replace(&mut seen[at], true) {
            continue;
        }
        if matches!(located[at], Located::Scope { .. }) {
            return true;
        }
        stack.extend(reads[at].iter().copied());
    }
    false
}

/// The sink consumers of a run's `targets`, which it unplaces when the run unwinds, as
/// [`Planner`]'s `Drop` unplaces the entries: a run that panics leaves no consumer claiming a
/// pipeline of a dispatcher that is gone. A run that returns keeps its placements.
struct SinksUnplacedOnUnwind<'t>(&'t [RunTarget]);

impl Drop for SinksUnplacedOnUnwind<'_> {
    fn drop(&mut self) {
        if thread::panicking() {
            unplace(&[], self.0);
        }
    }
}

/// Unplace every entry `placements` holds and every sink consumer of `targets`: a refused run
/// runs nothing and leaves nothing placed. An entry left placed takes a delivery as a package of a
/// pipeline that no dispatcher holds instead of passing it to its inline reader
/// (`Entry::notify`).
fn unplace(placements: &[Vec<Placement>], targets: &[RunTarget]) {
    for placement in placements.iter().flatten() {
        placement.set(None);
    }
    for (_, _, entry) in targets {
        match entry {
            TargetEntry::Sink(consumer) => consumer.borrow_mut().unplace(),
            TargetEntry::Main(placement) => placement.set(None),
        }
    }
}

/// Why the planner refuses a program before any pipeline runs.
#[derive(Debug)]
pub struct Refused(String);

impl std::fmt::Display for Refused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Refused {}

/// How a pipeline takes its packages, which [`plan_edges`] plans its edges by.
#[derive(Clone, Copy, PartialEq)]
pub(super) enum Consumes {
    /// What the pipelines it reads push, as its edges' probes plan.
    Pushes,
    /// Its input whole, in order, once every pipeline it reads has finished, or over a live
    /// source each delivery once they have completed it: a store that steps itself, or a loop's
    /// scope.
    Whole,
    /// One row per round of the scope it runs in, which queues it the row, once every pipeline it
    /// reads is quiescent: the scope of a loop nested in the scope's loop.
    Rounds,
}

/// The dispatcher over the pipelines `reads` describes, with every pipeline that reads another
/// holding the rows its pushes bring until the pipelines it reads have completed them, reading its
/// input whole where a pipeline it reads reaches it along no route, and queued at the start the
/// regions no push names ([`run_program`] says how). `arrivals` says whether a
/// pipeline takes a live source's arrivals beside the pipelines it reads
/// ([`Dispatcher::take_arrivals`]), which wait for input completion ([`Dispatcher::wait_for_inputs`]). `opens` says the
/// dispatcher is the run's, where a store or a loop's scope holds its deliveries; in a loop's
/// scope it follows the pipelines it reads, round by round. `kinds` says how each
/// pipeline takes its packages; `pushes_with` names, for each pipeline, the first pipeline of its
/// breaker, whose record of what the breaker pushed it shares ([`Dispatcher::share_pushes`]);
/// `end_of` answers the consumer a pipeline pushes to where its breaker is no producer that
/// answers it.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_edges(
    reads: &[Vec<usize>],
    names: &[String],
    leaves: &[Vec<RangeLeaf>],
    arrivals: &[bool],
    opens: bool,
    kinds: &[Consumes],
    pushes_with: &[usize],
    opening: &[bool],
    morsel_rows: usize,
    reach: &mut Reach<'_>,
    end_of: &mut dyn FnMut(PipelineId) -> Option<(SharedConsumer, bool, Vec<Projection>)>,
) -> (Dispatcher, Vec<Planned>) {
    let mut dispatcher = Dispatcher::new(reads.to_vec(), morsel_rows);
    // Each push queued and each complete region recorded is checked against the routes walked
    // here (`Landing::queue`), so every read's routes are walked, whatever its reader consumes.
    for (reader, read) in reads.iter().enumerate() {
        for &read in read {
            let (pusher, _, pushes) =
                end_of(PipelineId(read)).unwrap_or_else(|| pushing_end(reach, PipelineId(read)));
            let (changes, completions) = walk_routes(&pusher, &pushes, reader);
            dispatcher.plan_routes(PipelineId(reader), PipelineId(read), changes, completions);
        }
    }
    for (pipeline, &opens) in opening.iter().enumerate() {
        if opens {
            dispatcher.opens_before(PipelineId(pipeline));
        }
    }
    // A store decides its positions in order; a scope steps its store in order.
    for (pipeline, kind) in kinds.iter().enumerate() {
        if *kind != Consumes::Pushes {
            dispatcher.order(PipelineId(pipeline));
        }
    }
    for first in 0..pushes_with.len() {
        let shared: Vec<PipelineId> = (0..pushes_with.len())
            .filter(|&pipeline| pushes_with[pipeline] == first)
            .map(PipelineId)
            .collect();
        if shared.len() > 1 {
            debug_assert_eq!(
                shared[0].0, first,
                "the pipelines of one breaker share the first one's record of its pushes"
            );
            dispatcher.share_pushes(&shared);
        }
    }
    let mut planned: Vec<Planned> = names
        .iter()
        .map(|name| Planned {
            name: name.clone(),
            whole: false,
            follows: Vec::new(),
            started: false,
            rounds: Vec::new(),
            live: false,
            held: false,
        })
        .collect();
    let mut starts = Vec::new();
    for (reader, read) in reads.iter().enumerate() {
        if read.is_empty() {
            continue;
        }
        if arrivals[reader] {
            match kinds[reader] {
                // A pipeline that pushes takes each delivery, waiting for inputs until the pipelines it reads
                // have completed it.
                Consumes::Pushes => {
                    dispatcher.take_arrivals(PipelineId(reader));
                    dispatcher.wait_for_inputs(PipelineId(reader));
                    planned[reader].held = true;
                }
                // A store or a loop's scope over a live source takes each delivery once the
                // pipelines it reads have completed it, or are quiescent where it follows them
                // (below), so it reads no row again.
                Consumes::Rounds | Consumes::Whole => dispatcher.take_arrivals(PipelineId(reader)),
            }
        }
        let mut input = None;
        reach(PipelineId(reader), &mut |breaker, at| {
            input = Some(breaker.input_tiling(at))
        });
        let input = input.expect("a reach calls the breaker it reaches");
        match kinds[reader] {
            // A store's pipeline reads its input whole once the pipelines beneath its cycle have
            // finished: a push from beneath stops at the store's entry rather than reach the
            // cycle.
            Consumes::Whole if !arrivals[reader] => {
                dispatcher.read_whole(PipelineId(reader), &input);
                planned[reader].whole = true;
                continue;
            }
            // A nested loop's scope takes the row the scope around it queues it once the pipelines
            // it reads have finished the round, since its rounds pull them, and a store or a
            // loop's scope over a live source takes each delivery so.
            // In the run's dispatcher a store or a loop's scope over a live source holds each
            // delivery on what the pipelines it reads have completed instead (`run_targets`).
            Consumes::Rounds | Consumes::Whole if opens => continue,
            Consumes::Rounds | Consumes::Whole => {
                for &follow in read {
                    dispatcher.follow(PipelineId(reader), PipelineId(follow));
                    planned[reader].follows.push(follow);
                }
                continue;
            }
            Consumes::Pushes => {}
        }
        // What the pushes of the pipelines it reads name of its input, `None` before any.
        let mut pushed: Option<TileGuard> = None;
        // Whether a pipeline it reads pushes along no route to it, so it reads that one by pull.
        let mut unreached = false;
        // The breakers whose routes were read, by the record of pushes their pipelines share
        // (`pushes_with`).
        let mut seen: Vec<usize> = Vec::new();
        let read_all = read;
        for &read in read {
            // The pipelines of one breaker push one region once between them, through the same
            // consumer, so they reach and name the same region.
            if seen.contains(&pushes_with[read]) {
                continue;
            }
            seen.push(pushes_with[read]);
            let (pusher, _, one) =
                end_of(PipelineId(read)).unwrap_or_else(|| pushing_end(reach, PipelineId(read)));
            let routes = routes_to(&pusher, &one, reader);
            if routes.is_empty() {
                unreached = true;
                continue;
            }
            // A row reached along a path that passes a complete region on and along one that drops
            // it depends on rows the region does not name, so the read decides it only once whole.
            if routes.iter().any(|route| route.completes_part)
                && routes.iter().any(|route| !route.completes_part)
            {
                for &shared in read_all
                    .iter()
                    .filter(|&&r| pushes_with[r] == pushes_with[read])
                {
                    dispatcher.completes_whole_only(PipelineId(reader), PipelineId(shared));
                }
            }
            // A read along a route reaches what a push of its every key, wholly complete, lands
            // as: a row elsewhere waits for nothing of it. One read by pull reaches all of it.
            let region = complete_reach(&pusher, PipelineId(read), reader)
                .iter()
                .fold(input.empty_guard(), |region, arrival| {
                    region.union(&arrival.guard)
                });
            for &shared in read_all
                .iter()
                .filter(|&&r| pushes_with[r] == pushes_with[read])
            {
                dispatcher.reaches(PipelineId(reader), PipelineId(shared), region.clone());
            }
            let keys: Vec<Value> = routes
                .iter()
                .filter_map(|route| route.final_key.clone())
                .collect();
            if !keys.is_empty() {
                dispatcher.require_final_keys(PipelineId(reader), PipelineId(read), keys);
            }
            let named = probe(&pusher, PipelineId(read), &Projection::Everything, reader)
                .into_iter()
                .fold(input.empty_guard(), |names, arrival| {
                    names.union(&arrival.guard)
                });
            pushed = Some(match pushed {
                Some(before) => before.union(&named),
                None => named,
            });
        }
        // What the ranges beneath it bring that no push names, which the run queues it at the
        // start.
        let left = leaves[reader]
            .iter()
            .flat_map(|(leaf, _)| probe(leaf, PipelineId(read[0]), &Projection::Everything, reader))
            .fold(input.empty_guard(), |left, arrival| {
                left.union(&match &pushed {
                    Some(pushed) => guard_minus(&arrival.guard, pushed),
                    None => arrival.guard,
                })
            });
        // Every reader holds the rows its pushes and its start bring until the pipelines it
        // reads have completed them, and reads each row once ([`Dispatcher::wait_for_inputs`]). A pipeline
        // that takes arrivals is queued its rows as its sources yield them, and any other reads
        // its input whole where a pipeline it reads reaches it by pull, or where nothing else
        // brings it a row.
        let whole = !arrivals[reader] && (unreached || (pushed.is_none() && left.is_empty()));
        if whole {
            dispatcher.read_whole(PipelineId(reader), &input);
            planned[reader].whole = true;
            continue;
        }
        if !planned[reader].held {
            dispatcher.wait_for_inputs(PipelineId(reader));
            planned[reader].held = true;
        }
        if !arrivals[reader] && !left.is_empty() {
            planned[reader].started = true;
            starts.push((PipelineId(reader), left));
        }
    }
    for (reader, guard) in &starts {
        dispatcher.queue_for(*reader, guard);
    }
    (dispatcher, planned)
}

/// A sink output's consumer, which the planner places in the sink's pipeline.
// shared-state-ok: the compiled output's own handle on its sink consumer
// (`CompiledOutput::sink_consumer`), which the planner places and reads the sink's producer
// through; no tile crosses it.
type SinkTarget = Rc<RefCell<crate::interpreter::sinks::SinkConsumer>>;

/// A root of the run: the slot of the producer its sink breaker pulls, the `DataSink` the breaker
/// hands each answer to, and what the planner places in the root's pipeline.
type RunTarget = (ProducerSlot, Arc<dyn DataSink>, TargetEntry);

/// What the planner places in a root's pipeline, so a push that climbs to the root queues there.
enum TargetEntry {
    /// A sink output's consumer.
    Sink(SinkTarget),
    /// The placement of the entry before a `main` output's consumer
    /// (`CompiledOutput::main_entry`).
    Main(Placement),
}

/// What [`run_program`] planned for one pipeline.
#[cfg_attr(test, derive(Debug))]
pub struct Planned {
    /// Its breaker's name.
    pub name: String,
    /// Whether it reads its input whole: once every pipeline it reads has finished, or, over a live
    /// source whose arrivals reach it widened or reach no drive of its loop's scope, once every
    /// live source under it yields everything.
    pub whole: bool,
    /// The sibling indices this pipeline follows in the reporting tree, taking no push of theirs
    /// ([`Dispatcher::follow`]). The reporting tree retains planning-local indices; execution uses
    /// remapped global pipeline IDs.
    pub follows: Vec<usize>,
    /// Whether the run queued it a region at the start: what the ranges under it (`IterateExtent`)
    /// bring, less what the pushes of the pipelines it reads name.
    pub started: bool,
    /// The loop body's planning tree, and nothing for an ordinary pipeline. Indices inside this
    /// list, including `follows`, refer to its siblings rather than runtime pipeline IDs.
    pub rounds: Vec<Planned>,
    /// Whether the run notifies it of what a live source yields.
    pub live: bool,
    /// Whether arrivals wait until the pipelines it reads have completed them
    /// ([`Dispatcher::wait_for_inputs`]).
    pub held: bool,
}

/// The consumer `pipeline`'s breaker pushes to, and whether its output has keys of its own, which
/// an operator on a path to a reader can widen: a push of one value is `Everything`.
fn pushing_end(
    reach: &mut Reach<'_>,
    pipeline: PipelineId,
) -> (SharedConsumer, bool, Vec<Projection>) {
    let mut end = None;
    reach(pipeline, &mut |breaker, _| {
        let producer = breaker.as_producer().unwrap_or_else(|| {
            panic!(
                "pipeline {} is read, so its breaker is a producer",
                pipeline.0
            )
        });
        // A store is keyed by its positions, which a transaction store pushes as it decides them.
        let keyed = matches!(
            producer.tiling(),
            Tiling::DataFunction { .. } | Tiling::Store { .. }
        );
        end = Some((
            producer.base().downstream.clone(),
            keyed,
            pushes_of(producer.tiling()),
        ));
    });
    let (downstream, keyed, pushed) = end.expect("a reach calls the breaker it reaches");
    let downstream = downstream.unwrap_or_else(|| {
        panic!(
            "pipeline {} is read, so its breaker pushes to a consumer",
            pipeline.0
        )
    });
    (downstream, keyed, pushed)
}

/// The pushes a route walk of `output`, a breaker's output, stands for ([`routes_to`]), since a
/// breaker pushes regions of its keys at any level: at each collection level the path of one key
/// per level down to it, and beneath the outermost level also one key of that level under every
/// key above it, each once per arm where a level's keys are a union. The walk ends at a level whose
/// keys are functions, which no key stands for, and a tiling with no level before such a one stands
/// for one push of `Everything`.
pub(super) fn pushes_of(output: &Tiling) -> Vec<Projection> {
    /// A key of each arm of `extent`, `None` where no key stands for its values.
    fn keys(extent: &Extent) -> Option<Vec<Value>> {
        Some(match extent {
            Extent::Base(base) => vec![match base {
                BaseType::Int => Value::Int(0),
                BaseType::UInt => Value::UInt(0),
                BaseType::String => Value::String(SmolStr::default()),
                BaseType::Bool => Value::Bool(false),
                BaseType::Unit => Value::Unit,
            }],
            Extent::UIntRange(_) | Extent::DataSourceDomain(_) => vec![Value::UInt(0)],
            Extent::Record(fields) => {
                let mut record = HashMap::new();
                for (name, extent) in fields {
                    record.insert(name.clone(), keys(extent)?.swap_remove(0));
                }
                vec![Value::Record(record)]
            }
            Extent::Union(arms) => {
                let mut tagged = Vec::new();
                for (tag, extent) in arms.iter() {
                    tagged.extend(keys(extent)?.into_iter().map(|inner| Value::Union {
                        tag: tag.clone(),
                        inner: Box::new(inner),
                    }));
                }
                tagged
            }
            Extent::Restricted { base, .. } => keys(base)?,
            Extent::Function { .. } => return None,
        })
        .filter(|keys| !keys.is_empty())
    }
    let mut pushes = Vec::new();
    let mut paths: Vec<Vec<Value>> = vec![Vec::new()];
    let mut at = output;
    loop {
        let (domain, beneath) = match at {
            Tiling::DataFunction { domain, codomain } => (domain, Some(codomain.as_ref())),
            Tiling::Store { domain, .. } => (domain, None),
            _ => break,
        };
        let Some(keys) = keys(domain) else { break };
        paths = paths
            .iter()
            .flat_map(|path| {
                keys.iter().map(move |key| {
                    let mut path = path.clone();
                    path.push(key.clone());
                    path
                })
            })
            .collect();
        pushes.extend(paths.iter().map(|path| Projection::of_path(path)));
        // A push of a key beneath every key above it, as a breaker pushes a row of each group.
        let level = paths[0].len() - 1;
        if level > 0 {
            pushes.extend(keys.iter().map(|key| {
                Projection::keys_at(CurryLevel::new(level), Predicate::point(key.clone()))
            }));
        }
        match beneath {
            Some(beneath) => at = beneath,
            None => break,
        }
    }
    if pushes.is_empty() {
        pushes.push(Projection::Everything);
    }
    pushes
}

/// The paths the pushes `regions` through `consumer` take to the entry of `reader`: the consumers
/// on the way pass each on as they pass a push on, into a routing landing ([`Landing::route`]).
/// `regions` are the pushes the routes stand for, a path at each level of the pusher's output
/// ([`pushes_of`]), so a consumer that passes another region on otherwise fails the check each
/// push makes against the planned routes ([`Dispatcher::plan_routes`]).
pub(super) fn routes_to(
    consumer: &SharedConsumer,
    regions: &[Projection],
    reader: usize,
) -> Vec<Route> {
    let mut landing = Landing::route();
    for region in regions {
        consumer.borrow_mut().notify(region, &mut landing);
    }
    landing
        .routes()
        .into_iter()
        .filter(|route| route.pipeline.0 == reader)
        .collect()
}

/// The routes a push through `consumer` takes to the entry of `reader` that every push queued
/// and every complete region recorded there is checked against ([`Dispatcher::plan_routes`]):
/// those of a change of each of `pushes` and of every key, which a widening passes on unwidened,
/// and those of a complete region ([`complete_routes_to`]).
pub(crate) fn walk_routes(
    consumer: &SharedConsumer,
    pushes: &[Projection],
    reader: usize,
) -> (Vec<Route>, Vec<Route>) {
    let mut changes = pushes.to_vec();
    if !changes.contains(&Projection::Everything) {
        changes.push(Projection::Everything);
    }
    (
        routes_to(consumer, &changes, reader),
        complete_routes_to(consumer, pushes, reader),
    )
}

/// The paths the pushes `regions` through `consumer` take to the entry of `reader` as complete
/// regions, of a source not yet wholly complete and of one that is, and `Everything` of the latter,
/// as [`routes_to`] walks a change. The two walks pool their routes: at run time a region is
/// `Everything` exactly when its source is wholly complete, but an operator may restate a region
/// that is not whole as `Everything`, which only the whole walk passes on through a widening.
pub(super) fn complete_routes_to(
    consumer: &SharedConsumer,
    regions: &[Projection],
    reader: usize,
) -> Vec<Route> {
    let mut routes = Vec::new();
    for whole in [false, true] {
        let mut landing = Landing::route_complete(whole);
        for region in regions
            .iter()
            .chain(whole.then_some(&Projection::Everything))
        {
            consumer.borrow_mut().notify(region, &mut landing);
        }
        routes.extend(landing.routes());
    }
    routes.retain(|route| route.pipeline.0 == reader);
    routes
}

/// What a push of `region` through `consumer`, as `from`'s, brings to the entry of `reader`.
pub(super) fn probe(
    consumer: &SharedConsumer,
    from: PipelineId,
    region: &Projection,
    reader: usize,
) -> Vec<Arrival> {
    let mut landing = Landing::probe(from);
    consumer.borrow_mut().notify(region, &mut landing);
    landing
        .arrivals()
        .into_iter()
        .filter(|arrival| arrival.pipeline.0 == reader)
        .collect()
}

/// The region of `reader`'s input a push of `from`'s every key reaches through `consumer` when
/// it is restated as a wholly complete region is: all `from` can ever decide of that input.
pub(super) fn complete_reach(
    consumer: &SharedConsumer,
    from: PipelineId,
    reader: usize,
) -> Vec<Arrival> {
    let mut landing = Landing::probe_complete(from);
    consumer
        .borrow_mut()
        .notify(&Projection::Everything, &mut landing);
    landing
        .arrivals()
        .into_iter()
        .filter(|arrival| arrival.pipeline.0 == reader)
        .collect()
}

/// Where [`run_program`] finds a pipeline's breaker.
enum Located {
    /// The shared cell owning a breaker subscription.
    Chain(BreakerHandle),
    /// The breaker of the sink, or the `main` output, of this index among the run's targets
    /// ([`SinkBreaker`]).
    ///
    /// [`SinkBreaker`]: crate::interpreter::tile_operators::SinkBreaker
    Sink(usize),
    /// The store of the cyclic fan-out `fan`, which steps itself, consuming its input `input`:
    /// a transaction store is the breaker of one pipeline per writer.
    Store {
        fan: usize,
        store: StoreCell,
        input: usize,
    },
    /// The scope of the store of the cyclic fan-out `fan`, which runs in rounds: the planner's
    /// scope of index `scope`.
    Scope { fan: usize, scope: usize },
}

/// A loop's scope as the planner walks it.
pub(super) struct PlannedScope {
    writer: Option<usize>,
    store: StoreCell,
    /// The id of the store's cyclic fan-out, which the breakers inside its cycle read through a
    /// recurrence slot.
    fan: usize,
    /// The request pipeline in the enclosing scoped planning graph, or the root graph for an
    /// outermost loop; `None` until the walk has planned its dependencies.
    pipeline: Option<usize>,
    /// How many pipelines its body graph has before global composition.
    count: usize,
    /// How many row levels its store has above its positions: its rounds run at paths of
    /// `depth + 1` keys.
    depth: usize,
}

/// One scoped planning graph, with local indices and the inputs [`plan_edges`] configures.
pub(super) struct Members<'p> {
    located: Vec<&'p Located>,
    pub(super) reads: Vec<Vec<usize>>,
    pub(super) names: Vec<String>,
    pub(super) leaves: Vec<Vec<RangeLeaf>>,
    pub(super) kinds: Vec<Consumes>,
    /// Per pipeline, the first pipeline of its breaker, whose record of the breaker's pushes it
    /// shares ([`plan_edges`]): itself, but for a store's later pipelines.
    pub(super) pushes_with: Vec<usize>,
    /// The placements of the entries of the breakers in chains: per pipeline, each entry it
    /// queues through.
    pub(super) placements: Vec<Vec<Placement>>,
    /// The ranges over a live source in each pipeline's chain.
    live: Vec<Vec<LiveLeaf>>,
    /// Per pipeline, whether it is a store's seed input, which the store's other pipelines wait
    /// for the consume of (`Dispatcher::opens_before`).
    pub(super) opens_before: Vec<bool>,
}

/// Pipelines discovered beneath a program's outputs, grouped by lexical loop scope during planning.
/// Indices in these arrays identify discovered pipelines. `local` indexes the root or body graph
/// configured for each group; attachment later remaps those groups into the shared dispatcher.
#[derive(Default)]
pub(super) struct Planner {
    /// Per discovered pipeline, its dependencies before scoped graph projection.
    reads: Vec<Vec<usize>>,
    located: Vec<Located>,
    names: Vec<String>,
    /// Per pipeline, the ranges in its chain (`ProducerBase::leaf`), above every breaker beneath
    /// it.
    leaves: Vec<Vec<RangeLeaf>>,
    /// Per pipeline, the ranges over a live source in its chain, above every breaker beneath it.
    live: Vec<Vec<LiveLeaf>>,
    /// Per pipeline, its body planning scope; `None` for the root graph.
    within: Vec<Option<usize>>,
    /// Per pipeline, its index within that scoped planning graph.
    local: Vec<usize>,
    /// Per pipeline, the placement of its breaker's entry, where the breaker is in a chain.
    placements: Vec<Vec<Placement>>,
    /// The pipelines of stores' seed inputs, which the store's other pipelines read and wait for
    /// the consume of (`Dispatcher::opens_before`).
    opens_before: Vec<usize>,
    /// The edges `(read, reader)` whose reader's breaker reads the breaker of `read` directly.
    direct: Vec<(usize, usize)>,
    pub(super) scopes: Vec<PlannedScope>,
    /// How many pipelines the root graph has before appending body graphs and store steps.
    count: usize,
    /// The scopes whose store's chain the walk is in, outermost first.
    walking: Vec<usize>,
    /// The first refusal the walk met, after which it plans nothing more.
    refused: Option<Refused>,
}

/// A run that unwinds, in planning or execution, leaves no entry claiming a pipeline of a
/// dispatcher that is gone; a run that returns leaves its placements as `run_targets` does. See
/// `src/interpreter/design-dispatcher.md`, "Running a compiled program".
impl Drop for Planner {
    fn drop(&mut self) {
        if thread::panicking() {
            for placement in self.placements.iter().flatten() {
                placement.set(None);
            }
        }
    }
}

/// What a chain holds beneath a producer, up to the nearest breakers.
#[derive(Default)]
struct Beneath {
    /// The pipelines of the nearest breakers, each once, and whether that breaker is the producer
    /// itself rather than beneath it.
    pipelines: Vec<(usize, bool)>,
    /// The ranges above those breakers (`ProducerBase::leaf`).
    leaves: Vec<RangeLeaf>,
    /// The constant collections above those breakers that are no function operand: producers
    /// with no input and keys of their own that keep no consumer, so no probe names their keys.
    unprobed: Vec<String>,
    /// The ranges over a live source above those breakers.
    live: Vec<LiveLeaf>,
}

/// A range over a static extent (`ProducerBase::leaf`): its consumer, and the pushes a route walk
/// of it stands for ([`pushes_of`] of its output), so a widening on its way reads as one.
pub(super) type RangeLeaf = (SharedConsumer, Vec<Projection>);

/// A live iteration range: its consumer and the full extent whose complete region is announced.
#[derive(Clone)]
pub(super) struct LiveLeaf {
    pub(super) consumer: SharedConsumer,
    pub(super) extent: Extent,
}

impl LiveLeaf {
    /// The path, through nested records, to the field whose positions order this range's
    /// positions, or `None` where the range need not yield a prefix of them.
    ///
    /// A record's positions are ordered by its first field in name order, as `Value::Record`
    /// compares them, so they yield a prefix where that field does and no later field reads a
    /// source. A range that reads no source yields all its positions at once. A round request must
    /// not include a later position while an earlier one can still arrive, so only a range with an
    /// ordering path is read in rounds.
    fn ordering_path(&self) -> Option<Vec<SmolStr>> {
        fn path(extent: &Extent) -> Option<Vec<SmolStr>> {
            match extent {
                Extent::DataSourceDomain(_) => Some(Vec::new()),
                Extent::Record(fields) => {
                    let mut fields: Vec<_> = fields.iter().collect();
                    fields.sort_by_key(|(name, _)| *name);
                    let Some(((first, extent), rest)) = fields.split_first() else {
                        return Some(Vec::new());
                    };
                    if rest.iter().any(|(_, extent)| extent.reads_a_source()) {
                        return None;
                    }
                    let mut path = path(extent)?;
                    path.insert(0, (*first).clone());
                    Some(path)
                }
                _ => (!extent.reads_a_source()).then(Vec::new),
            }
        }
        path(&self.extent)
    }

    fn probe_region(&self) -> Projection {
        fn probe(extent: &Extent) -> Predicate {
            match extent {
                Extent::Record(fields) => Predicate::Record(
                    fields
                        .iter()
                        .map(|(name, extent)| (name.clone(), probe(extent)))
                        .collect(),
                ),
                Extent::Union(arms) => {
                    Predicate::over_every_tag(arms.map(|_, extent| probe(extent)))
                }
                Extent::DataSourceDomain(_) => Predicate::point(Value::UInt(0)),
                _ => Predicate::True,
            }
        }
        Projection::admitting(probe(&self.extent))
    }
}

/// Whether `yielded`, the region a range has yielded, names a prefix of the positions of the field
/// at `path` ([`LiveLeaf::ordering_path`]): every position or none, or every position at or below
/// one. The other fields read no source, so their part of the region does not order rounds.
#[cfg(debug_assertions)]
fn yields_a_prefix(path: &[SmolStr], yielded: &Predicate) -> bool {
    let mut at = yielded;
    for field in path {
        at = match at {
            Predicate::Record(fields) => fields.get(field).unwrap_or_else(|| {
                panic!("a record range's yield names its field {field}: {yielded:?}")
            }),
            Predicate::True | Predicate::False => break,
            other => panic!(
                "a record range's yield is a record of its fields' yields, not {other:?}, so the \
                 prefix of field {field} has no spelling here"
            ),
        };
    }
    at.is_true()
        || at.is_false()
        || at.max_released_position().is_some_and(|last| {
            let prefix = Predicate::at_or_below(last.into_value());
            prefix.subsumes(at) && at.subsumes(&prefix)
        })
}

/// A live source, as a range over its domain reads it.
pub(super) type LiveSource = Rc<RefCell<dyn DataSourceDomainExtentImpl>>;

impl Beneath {
    /// Add `pipelines` to the pipelines beneath, each once: a reader that reaches a pipeline
    /// along two paths, as a filter reads its input for the values and the predicate, reads it
    /// once.
    fn read_once(&mut self, pipelines: Vec<(usize, bool)>) {
        for (pipeline, direct) in pipelines {
            if !self.pipelines.iter().any(|(seen, _)| *seen == pipeline) {
                self.pipelines.push((pipeline, direct));
            }
        }
    }
}

impl Planner {
    /// Refuse the program for `why`, where nothing refused it before.
    fn refuse(&mut self, why: String) {
        self.refused.get_or_insert(Refused(why));
    }

    /// Discover the nearest breakers beneath `producer`, assigning each to its body planning
    /// scope ([`scope_of`](Self::scope_of)). A pipeline is numbered after its dependencies, and
    /// a shared breaker keeps its first index. A recurrence slot ends the walk: its reader pulls
    /// the store.
    fn pipelines_under(
        &mut self,
        producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
        role: &str,
    ) -> Beneath {
        if self.refused.is_some() || producer.recurrence_of().is_some() {
            return Beneath::default();
        }
        if let Some(read) = producer.store_read() {
            return Beneath {
                pipelines: self
                    .store_pipeline(read)
                    .into_iter()
                    .map(|at| (at, false))
                    .collect(),
                ..Beneath::default()
            };
        }
        let handle = producer
            .base()
            .breaker_handle
            .as_ref()
            .and_then(std::rc::Weak::upgrade);
        if let Some(pipeline) = self
            .located
            .iter()
            .position(|at| matches!((at, &handle), (Located::Chain(seen), Some(handle)) if Rc::ptr_eq(seen, handle)))
        {
            return Beneath {
                pipelines: vec![(pipeline, true)],
                ..Beneath::default()
            };
        }
        let mut below = Beneath::default();
        let inputs = visit_inputs_checked(producer, &mut |role, input| {
            let under = self.pipelines_under(input, role);
            below.read_once(under.pipelines);
            below.leaves.extend(under.leaves);
            below.unprobed.extend(under.unprobed);
            below.live.extend(under.live);
        });
        let leaf = (inputs == 0)
            .then(|| producer.base().downstream.clone())
            .flatten();
        let placement = producer.base().placement.clone();
        // A function operand is a table its consumer looks values up in, and widens, so its keys
        // are no keys of the reader's input.
        if inputs == 0 && leaf.is_none() && role != "fn" && producer.tiling().is_data_function() {
            below.unprobed.push(producer.name());
        }
        let sources = producer.data_sources();
        let extent = producer.tiling().domain_extent();
        if sources
            .iter()
            .any(|source| source.borrow().element_extent() != Extent::Base(BaseType::UInt))
        {
            self.refuse(format!(
                "{} ranges over a live source without UInt positions",
                producer.name()
            ));
            return Beneath::default();
        }
        let (leaf, live) = match (leaf, extent) {
            (Some(consumer), Some(extent)) if !sources.is_empty() => {
                (None, Some(LiveLeaf { consumer, extent }))
            }
            (leaf, _) => (leaf, None),
        };
        below.live.extend(live);
        let Some(_) = producer.as_breaking_mut() else {
            below
                .leaves
                .extend(leaf.map(|consumer| (consumer, pushes_of(producer.tiling()))));
            for (_, direct) in &mut below.pipelines {
                *direct = false;
            }
            return below;
        };
        let within = self.scope_of(&*producer);
        let name = producer.name();
        let placement =
            placement.unwrap_or_else(|| panic!("{name} is placed in a pipeline by its entry"));
        let pipeline = self.add(
            Located::Chain(handle.expect("a subscribed breaker owns a handle")),
            name,
            within,
            below,
        );
        placement.set(Some(PipelineId(self.local[pipeline])));
        self.placements[pipeline] = vec![placement];
        Beneath {
            pipelines: vec![(pipeline, true)],
            ..Beneath::default()
        }
    }

    /// The innermost planning scope whose cycle contains `producer`, or `None` for the root
    /// graph when it belongs to no enclosing cycle.
    fn scope_of(
        &self,
        producer: &dyn crate::interpreter::tile_operators::TileProducer,
    ) -> Option<usize> {
        self.walking
            .iter()
            .rev()
            .copied()
            .find(|&scope| reaches_recurrence(producer, self.scopes[scope].fan))
    }

    /// The pipelines of the store `read` names, planning them the first time a reader reaches
    /// it: the scope's of a store that runs in rounds ([`scope_pipeline`](Self::scope_pipeline)),
    /// and otherwise the store's own, one per input (`Breaker::inputs`), a transaction store's
    /// writers each the input of one. The store's pipeline of an input reads the pipelines
    /// beneath the store's cycle under that input; the operators inside the cycle, its own
    /// breakers among them, read their inputs within that pipeline.
    ///
    /// Empty where the planner refuses the store ([`refuse`](Self::refuse)): a nested
    /// transaction store reached outside the scope of the loop around it; a store with no
    /// breaker implementation; and a store inside the cycle of a store that steps itself.
    pub(super) fn store_pipeline(
        &mut self,
        read: crate::interpreter::tile_operators::StoreRead,
    ) -> Vec<usize> {
        let planned: Vec<usize> = (0..self.located.len())
            .filter(|&pipeline| {
                matches!(
                    &self.located[pipeline],
                    Located::Store { fan, .. } | Located::Scope { fan, .. } if *fan == read.fan
                )
            })
            .collect();
        if !planned.is_empty() {
            return planned;
        }
        let within = self.scope_of(&**read.store.borrow());
        let is_induction = read.store.borrow_mut().as_induction_store_mut().is_some();
        if is_induction {
            return vec![self.scope_pipeline(read, within)];
        }
        // A nested transaction store runs in the scope of the loop around it, a row of its store
        // per round of that loop.
        if within.is_none() && !matches!(read.store.borrow().tiling(), Tiling::Store { .. }) {
            self.refuse(format!(
                "a nested transaction store, one per enclosing row, runs in no pipeline outside \
                 its loop's scope: its frontier is per row: {}",
                read.store.borrow().tiling()
            ));
            return Vec::new();
        }
        let cell = read.store.clone();
        let mut store = cell.borrow_mut();
        let name = store.name();
        assert!(
            within.is_none(),
            "{name} steps itself and runs in no loop's scope: only an induction store, which runs \
             in rounds, sits inside one"
        );
        let breaker = store
            .as_breaking_mut()
            .unwrap_or_else(|| panic!("{name} is a pipeline breaker"));
        let inputs = breaker.inputs();
        // What each input holds beneath the store's cycle. A store with seeds reads them as its
        // input 0, and its writers' sources as the inputs after, in the order it visits them; one
        // without reads its writers' sources from input 0.
        let mut writers = Vec::new();
        let mut seeds = Beneath::default();
        let mut seeded = false;
        visit_inputs_checked(
            &mut *store,
            &mut |role, producer| match role.starts_with("seed") {
                true => {
                    let under = self.pipelines_under(producer, role);
                    seeds.read_once(under.pipelines);
                    seeds.live.extend(under.live);
                    seeded = true;
                }
                false => writers.push(self.beneath_cycle(producer, read.fan)),
            },
        );
        let mut writer_scopes = Vec::new();
        let mut writer = 0;
        visit_inputs_checked(&mut *store, &mut |role, producer| {
            if role.starts_with("seed") {
                return;
            }
            let scope = self.scopes.len();
            self.scopes.push(PlannedScope {
                writer: Some(writer),
                store: read.store.clone(),
                fan: read.fan,
                pipeline: None,
                count: 0,
                depth: 0,
            });
            self.walking.push(scope);
            let body = self.pipelines_under(producer, role);
            self.walking.pop();
            writers[writer].pipelines = body.pipelines;
            writer_scopes.push(scope);
            writer += 1;
        });
        assert!(
            !writers.is_empty(),
            "a dispatched transaction store has a writer: its keys are the footprints of its \
             `with begin():` blocks"
        );
        assert_eq!(
            writers.len() + usize::from(seeded),
            inputs,
            "{name} reads its seeds as one input and each writer's source as one"
        );
        let below: Vec<Beneath> = match seeded {
            true => std::iter::once(seeds).chain(writers).collect(),
            false => writers,
        };
        if self.refused.is_some() {
            return Vec::new();
        }
        let breaker = store
            .as_breaking_mut()
            .unwrap_or_else(|| panic!("{name} is a pipeline breaker"));
        let placements: Vec<Vec<Placement>> = (0..inputs)
            .map(|input| {
                if seeded && input == 0 {
                    breaker.entry_placements(InputId(input))
                } else {
                    Vec::new()
                }
            })
            .collect();
        // A store reads each input whole once the pipelines beneath it have finished, so neither
        // ranges nor constants beneath it bring a key no push names. A live source beneath it is
        // read as the run notifies the store's pipeline of what the source yields. A writer's
        // pipeline reads the seed input's, its sibling: the store opens before it steps, so a
        // writer's package waits for the seed's (`Dispatcher::opens_before`).
        let mut seed_pipeline = None;
        below
            .into_iter()
            .zip(placements)
            .enumerate()
            .map(|(input, (mut below, placements))| {
                if let Some(seed) = seed_pipeline {
                    below.read_once(vec![(seed, false)]);
                }
                let pipeline = self.add(
                    Located::Store {
                        fan: read.fan,
                        store: read.store.clone(),
                        input,
                    },
                    name.clone(),
                    within,
                    Beneath {
                        pipelines: below.pipelines,
                        live: below.live,
                        ..Beneath::default()
                    },
                );
                if !(seeded && input == 0) {
                    self.scopes[writer_scopes[input - usize::from(seeded)]].pipeline =
                        Some(pipeline);
                }
                for placement in &placements {
                    placement.set(Some(PipelineId(self.local[pipeline])));
                }
                self.placements[pipeline] = placements;
                if seeded && input == 0 {
                    seed_pipeline = Some(pipeline);
                    self.opens_before.push(pipeline);
                }
                pipeline
            })
            .collect()
    }

    /// Add the store's request pipeline to the enclosing scoped planning graph (`within`),
    /// or the root graph when `within` is `None`. The walk of the store's chain
    /// plans the breakers inside its cycle as a body graph for the run's dispatcher. The
    /// store is in none, and its entry stays unplaced, so a push to it queues nothing. The
    /// scope's pipeline reads the pipelines beneath the cycle.
    fn scope_pipeline(
        &mut self,
        read: crate::interpreter::tile_operators::StoreRead,
        within: Option<usize>,
    ) -> usize {
        let scope = self.scopes.len();
        self.scopes.push(PlannedScope {
            writer: None,
            store: read.store.clone(),
            fan: read.fan,
            pipeline: None,
            count: 0,
            depth: rows_above_positions(read.store.borrow().tiling()),
        });
        self.walking.push(scope);
        let mut below = Beneath::default();
        let name = {
            let mut store = read.store.borrow_mut();
            visit_inputs_checked(&mut *store, &mut |role, input| {
                below.read_once(self.pipelines_under(input, role).pipelines);
            });
            store.name()
        };
        self.walking.pop();
        let pipeline = self.add(
            Located::Scope {
                fan: read.fan,
                scope,
            },
            format!("InductionRequest({name})"),
            within,
            Beneath {
                pipelines: below.pipelines,
                ..Beneath::default()
            },
        );
        self.scopes[scope].pipeline = Some(pipeline);
        // The store's seeds reach the scope's pipeline through their entries, which record what
        // each seed has completed; the scope takes no push of them.
        let seeds = read
            .store
            .borrow_mut()
            .as_breaking_mut()
            .map(|store| store.seed_placements())
            .unwrap_or_default();
        for placement in &seeds {
            placement.set(Some(PipelineId(self.local[pipeline])));
        }
        self.placements[pipeline].extend(seeds);
        pipeline
    }

    /// What a store's input `producer`, inside the cycle of the fan-out `fan`, holds beneath it:
    /// the pipelines beneath the cycle. A subtree that reaches no recurrence slot of `fan` is
    /// outside the cycle and planned as any chain is; inside it, a breaker is no pipeline.
    ///
    /// # Panics
    ///
    /// Where another store's fan-out is read inside the cycle.
    fn beneath_cycle(
        &mut self,
        producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
        fan: usize,
    ) -> Beneath {
        if !reaches_recurrence(producer, fan) {
            return self.pipelines_under(producer, "input");
        }
        if producer.store_read().is_some() {
            self.refuse(format!(
                "a store is read inside another store's cycle, one that steps itself, which no \
                 round reaches: a store there runs in no pipeline ({} reads it)",
                producer.name()
            ));
            return Beneath::default();
        }
        let mut below = Beneath::default();
        visit_inputs_checked(producer, &mut |_, input| {
            let under = self.beneath_cycle(input, fan);
            below.read_once(under.pipelines);
            below.live.extend(under.live);
        });
        below
    }

    /// Plan a pipeline at `located`, named `name`, in the dispatcher of the scope `within`
    /// (`None` for the run's), reading what `below` holds, and answer its id in the planner. Its
    /// id in its dispatcher is the count of the pipelines planned there before it.
    fn add(
        &mut self,
        located: Located,
        name: String,
        within: Option<usize>,
        below: Beneath,
    ) -> usize {
        let pipeline = self.located.len();
        // A source reads its input whole, so it consumes whatever keys a constant brings. A
        // reader of pushes takes only what the pushes and the ranges' probes name.
        debug_assert!(
            below.pipelines.is_empty() || below.unprobed.is_empty(),
            "{name} reads pushes, and {:?} beneath it bring keys no push or probe names: a \
             constant collection beneath a reader of pushes is a function operand",
            below.unprobed
        );
        for &(read, direct) in &below.pipelines {
            if direct {
                self.direct.push((read, pipeline));
            }
        }
        let count = match within {
            None => &mut self.count,
            Some(scope) => &mut self.scopes[scope].count,
        };
        self.local.push(*count);
        *count += 1;
        self.located.push(located);
        self.names.push(name);
        self.within.push(within);
        self.placements.push(Vec::new());
        self.reads
            .push(below.pipelines.iter().map(|(read, _)| *read).collect());
        self.leaves.push(below.leaves);
        self.live.push(below.live);
        pipeline
    }

    /// Refuse a pipeline that two breakers read where one reads it directly: only a fan-out slot
    /// keeps one reader's release from removing what another still reads. The pipelines of one
    /// store's inputs are one reader, since they share the store as their breaker: every one of
    /// them reads a seed's pipelines, and the store pulls and releases the seed once, when it
    /// opens.
    fn check_direct(&mut self) {
        if self.refused.is_some() {
            return;
        }
        let breaker_of = |pipeline: usize| match &self.located[pipeline] {
            Located::Store { input, .. } => pipeline - input,
            _ => pipeline,
        };
        for &(read, reader) in &self.direct {
            let mut readers: Vec<usize> = (0..self.reads.len())
                .filter(|&pipeline| self.reads[pipeline].contains(&read))
                .map(breaker_of)
                .collect();
            readers.sort_unstable();
            readers.dedup();
            if readers.len() != 1 {
                self.refused.get_or_insert(Refused(format!(
                    "{} reads {} directly, which another pipeline reads too; only a fan-out slot \
                     keeps one reader's release from removing what another still reads",
                    self.names[reader], self.names[read]
                )));
            }
        }
    }

    /// The pipeline of the planner's scope `scope`.
    fn scope_pipeline_of(&self, scope: usize) -> usize {
        self.scopes[scope]
            .pipeline
            .expect("a scope's pipeline is planned once the walk of its store's chain returns")
    }

    /// The body planning scope containing `pipeline`, then its ancestors through the root graph.
    fn scopes_around(&self, pipeline: usize) -> Vec<Option<usize>> {
        let mut around = vec![self.within[pipeline]];
        while let Some(Some(scope)) = around.last() {
            around.push(self.within[self.scope_pipeline_of(*scope)]);
        }
        around
    }

    /// Project a discovered pipeline into an ancestor planning scope: the pipeline itself,
    /// or the request pipeline representing its enclosing body in that ancestor.
    fn stand_in(&self, mut pipeline: usize, within: Option<usize>) -> usize {
        while self.within[pipeline] != within {
            let scope = self.within[pipeline].unwrap_or_else(|| {
                panic!(
                    "{} is planned inside scope {within:?}",
                    self.names[pipeline]
                )
            });
            pipeline = self.scope_pipeline_of(scope);
        }
        pipeline
    }

    /// Build a scoped planning graph with local indices (`None` selects the root graph).
    /// Cross-scope reads are projected into their nearest common ancestor through the request
    /// pipelines representing each body. A request pipeline never depends on its own body.
    fn members(&self, within: Option<usize>) -> Members<'_> {
        let ids: Vec<usize> = (0..self.located.len())
            .filter(|pipeline| self.within[*pipeline] == within)
            .collect();
        debug_assert!(
            ids.iter()
                .enumerate()
                .all(|(local, pipeline)| self.local[*pipeline] == local),
            "a scoped graph numbers pipelines in discovery order"
        );
        let mut reads = vec![Vec::new(); ids.len()];
        for (reader, pipeline_reads) in self.reads.iter().enumerate() {
            for &read in pipeline_reads {
                let around = self.scopes_around(read);
                let common = self
                    .scopes_around(reader)
                    .into_iter()
                    .find(|dispatcher| around.contains(dispatcher))
                    .expect("every planning scope has the root graph as an ancestor");
                if common != within {
                    continue;
                }
                let (reader, read) = (self.stand_in(reader, common), self.stand_in(read, common));
                let at = &mut reads[self.local[reader]];
                if reader != read && !at.contains(&self.local[read]) {
                    at.push(self.local[read]);
                }
            }
        }
        Members {
            located: ids
                .iter()
                .map(|pipeline| &self.located[*pipeline])
                .collect(),
            reads,
            names: ids
                .iter()
                .map(|pipeline| self.names[*pipeline].clone())
                .collect(),
            leaves: ids
                .iter()
                .map(|pipeline| self.leaves[*pipeline].clone())
                .collect(),
            kinds: ids
                .iter()
                .map(|pipeline| match &self.located[*pipeline] {
                    Located::Store { .. } => {
                        debug_assert!(
                            within.is_none(),
                            "a store that steps itself runs in the run's dispatcher; an induction \
                             store inside a loop's scope is a nested loop's scope"
                        );
                        Consumes::Whole
                    }
                    Located::Scope { .. } if within.is_none() => Consumes::Whole,
                    Located::Scope { .. } => Consumes::Rounds,
                    Located::Chain(_) | Located::Sink(_) => Consumes::Pushes,
                })
                .collect(),
            // A store's pipelines stand in `located` one after another, from its input 0
            // (`store_pipeline` adds them in one pass), so the pipeline of input `input` is
            // `input` places after the store's first.
            pushes_with: ids
                .iter()
                .map(|&pipeline| match &self.located[pipeline] {
                    Located::Store { fan, input, .. } => {
                        let first = pipeline - input;
                        debug_assert!(
                            matches!(
                                &self.located[first],
                                Located::Store { fan: f, input: 0, .. } if f == fan
                            ),
                            "a store's pipelines are planned one after another, its first \
                             input's first"
                        );
                        self.local[first]
                    }
                    _ => self.local[pipeline],
                })
                .collect(),
            placements: ids
                .iter()
                .map(|pipeline| self.placements[*pipeline].clone())
                .collect(),
            opens_before: ids
                .iter()
                .map(|pipeline| self.opens_before.contains(pipeline))
                .collect(),
            // A live source read inside a scope is read by the scope's pipeline, which stands
            // for the pipelines inside it.
            live: ids
                .iter()
                .map(|&pipeline| {
                    (0..self.located.len())
                        .filter(|&inside| {
                            self.scopes_around(inside).contains(&within)
                                && self.stand_in(inside, within) == pipeline
                        })
                        .flat_map(|inside| self.live[inside].clone())
                        .collect()
                })
                .collect(),
        }
    }

    /// The loop scope of the planner's scope `scope`.
    /// Each scope's index and the breaker handles it keeps are added to `kept`: the inner pipelines
    /// its rounds queue or push packages to ([`unrestated_in_rounds`](Self::unrestated_in_rounds)).
    pub(super) fn build_scope(
        &self,
        scope: usize,
        morsel_rows: usize,
        kept_scopes: &mut Vec<(usize, Vec<BreakerHandle>)>,
        runs: &mut InductionRuns,
    ) -> StoreCell {
        let pipelines = self.members(Some(scope));
        let members: Vec<Member> = pipelines
            .located
            .iter()
            .map(|located| match located {
                Located::Chain(handle) => Member::Chain(handle.clone()),
                Located::Scope { scope, .. } => {
                    Member::Scope(self.build_scope(*scope, morsel_rows, kept_scopes, runs))
                }
                Located::Store { .. } | Located::Sink(_) => {
                    unreachable!("a loop body has chains and induction requests")
                }
            })
            .collect();
        let store = self.scopes[scope].store.clone();
        let mut kept: Vec<usize> = (0..members.len()).collect();
        let (inner, planned, reads) = loop {
            let reads = reads_of_kept(&pipelines.reads, &kept);
            // A breaker in no pipeline keeps no entry: an id the planner gave it may be a kept
            // pipeline's here, and a probe would take it for an arrival there.
            for placement in pipelines.placements.iter().flatten() {
                placement.set(None);
            }
            let placed = ClearsPlacements(&pipelines.placements);
            for (at, &pipeline) in kept.iter().enumerate() {
                for placement in &pipelines.placements[pipeline] {
                    placement.set(Some(PipelineId(at)));
                }
            }
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                loop_scope::reach_member(&members[kept[pipeline.0]], call)
            };
            let names: Vec<String> = kept.iter().map(|&at| pipelines.names[at].clone()).collect();
            let leaves: Vec<_> = kept
                .iter()
                .map(|&at| pipelines.leaves[at].clone())
                .collect();
            let kinds: Vec<Consumes> = kept.iter().map(|&at| pipelines.kinds[at]).collect();
            // A nested loop's drive records its source's complete pushes at the loop's pipeline,
            // which execution sets once the body is attached (`Execution::attach_store`). The
            // body's route walks pass that record, so it names the loop's pipeline here while they
            // run.
            let nested: Vec<(usize, StoreCell)> = kept
                .iter()
                .enumerate()
                .filter_map(|(at, &member)| match &members[member] {
                    Member::Scope(scope) => Some((at, scope.clone())),
                    Member::Chain(_) => None,
                })
                .collect();
            for (at, scope) in &nested {
                let mut scope = induction(scope);
                debug_assert!(
                    !scope.decides_through_drive(),
                    "a nested loop's drive records at no pipeline between its own planning and its \
                     enclosing body's"
                );
                scope.decide_through_drive(PipelineId(*at));
            }
            // A live source read inside a scope is read by the scope's pipeline in the run's
            // dispatcher, so no inner pipeline is live.
            // A store inside a scope is a nested loop's, whose scope is one pipeline, so no two
            // inner pipelines share a breaker's pushes.
            let (inner, planned) = plan_edges(
                &reads,
                &names,
                &leaves,
                &vec![false; names.len()],
                false,
                &kinds,
                &(0..names.len()).collect::<Vec<_>>(),
                &vec![false; names.len()],
                morsel_rows,
                &mut reach,
                &mut |pipeline| match &members[kept[pipeline.0]] {
                    Member::Scope(scope) => Some(induction(scope).pushing_end()),
                    Member::Chain(_) => None,
                },
            );
            for (_, scope) in &nested {
                induction(scope).forget_through_drive();
            }
            drop(placed);
            let whole: Vec<usize> = planned
                .iter()
                .enumerate()
                .filter(|(at, plan)| plan.whole && pipelines.kinds[kept[*at]] == Consumes::Pushes)
                .map(|(at, _)| kept[at])
                .collect();
            if whole.is_empty() {
                break (inner, planned, reads);
            }
            kept.retain(|pipeline| !whole.contains(pipeline));
        };
        assert!(
            reads.iter().any(Vec::is_empty),
            "{} has a pipeline inside its cycle that reads none, the drive's",
            store.borrow().name()
        );
        let mut members: Vec<Option<Member>> = members.into_iter().map(Some).collect();
        let members: Vec<Member> = kept
            .iter()
            .map(|&at| members[at].take().expect("a pipeline is kept once"))
            .collect();
        // Reporting preserves the scope hierarchy; execution later remaps every body graph.
        let mut planned = planned;
        for (plan, member) in planned.iter_mut().zip(&members) {
            if let Member::Scope(scope) = member {
                plan.rounds = std::mem::take(
                    &mut induction(scope)
                        .run
                        .as_mut()
                        .expect("a nested run is planned")
                        .planned,
                );
            }
        }
        let starts: Vec<PipelineId> = (0..members.len())
            .filter(|&at| reads[at].is_empty() || !matches!(members[at], Member::Chain(_)))
            .map(PipelineId)
            .collect();
        let placements = kept
            .iter()
            .map(|&at| pipelines.placements[at].clone())
            .collect();
        let mut drives = Vec::new();
        for &start in &starts {
            if inner.is_source(start) && matches!(members[start.0], Member::Chain(_)) {
                let mut drive = false;
                loop_scope::reach_member(&members[start.0], &mut |breaker, _| {
                    drive = breaker
                        .as_producer()
                        .is_some_and(|producer| producer.next_position().is_some());
                });
                if drive {
                    drives.push(start);
                }
            }
        }
        let [drive] = drives.as_slice() else {
            panic!("an induction run has exactly one drive")
        };
        assert!(
            members.iter().all(|member| match member {
                Member::Scope(child) => !Rc::ptr_eq(&store, child),
                Member::Chain(_) => true,
            }),
            "run metadata does not retain its own store cell"
        );
        let run =
            loop_scope::InductionRun::new(inner, members, placements, starts, planned, *drive);
        runs.install(&store, run);
        kept_scopes.push((scope, induction(&store).chain_breakers()));
        store
    }

    fn build_transaction(
        &self,
        scope: usize,
        morsel_rows: usize,
        kept: &mut Vec<(usize, Vec<BreakerHandle>)>,
        runs: &mut InductionRuns,
    ) -> transaction_scope::WriterRun {
        let pipelines = self.members(Some(scope));
        let members: Vec<Member> = pipelines
            .located
            .iter()
            .map(|located| match located {
                Located::Chain(handle) => Member::Chain(handle.clone()),
                Located::Scope { scope, .. } => {
                    Member::Scope(self.build_scope(*scope, morsel_rows, kept, runs))
                }
                _ => unreachable!(
                    "a transaction body contains native pipelines and nested loop requests"
                ),
            })
            .collect();
        let placed = ClearsPlacements(&pipelines.placements);
        for (local, placements) in pipelines.placements.iter().enumerate() {
            for placement in placements {
                placement.set(Some(PipelineId(local)));
            }
        }
        for (local, member) in members.iter().enumerate() {
            if let Member::Scope(store) = member {
                induction(store).decide_through_drive(PipelineId(local));
            }
        }
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            loop_scope::reach_member(&members[pipeline.0], call)
        };
        let (graph, planned) = plan_edges(
            &pipelines.reads,
            &pipelines.names,
            &pipelines.leaves,
            &vec![false; members.len()],
            false,
            &pipelines.kinds,
            &(0..members.len()).collect::<Vec<_>>(),
            &vec![false; members.len()],
            morsel_rows,
            &mut reach,
            &mut |pipeline| match &members[pipeline.0] {
                Member::Scope(store) => Some(induction(store).pushing_end()),
                _ => None,
            },
        );
        let drivers: Vec<usize> = members
            .iter()
            .enumerate()
            .filter_map(|(local, member)| {
                let mut driver = false;
                loop_scope::reach_member(member, &mut |breaker, _| {
                    driver = breaker
                        .as_producer()
                        .is_some_and(|producer| producer.next_position().is_some());
                });
                driver.then_some(local)
            })
            .collect();
        let [driver] = drivers.as_slice() else {
            panic!("a writer body has one transaction driver")
        };
        for member in &members {
            if let Member::Scope(store) = member {
                induction(store).forget_through_drive();
            }
        }
        drop(placed);
        transaction_scope::WriterRun::new(
            graph,
            members,
            pipelines.placements.clone(),
            PipelineId(*driver),
            planned,
        )
    }

    /// Why a round of a scope whose store has rows above its positions breaks the invariant that it
    /// pulls each operator beneath the outermost keys at a level the operator restates
    /// ([`unrestated`]), naming the operator, or `None` where no round does. Such a store is a
    /// nested loop's, or one per row of a comprehension. `kept` holds each scope's breakers, as
    /// [`build_scope`](Self::build_scope) gathers them. The walk starts at each breaker such a
    /// scope keeps, at the level of its rounds, and ends at every consuming breaker, whose
    /// consume pulls its own inputs. A breaker removed from its body graph because it would read
    /// whole remains inline and passes the read on.
    fn unrestated_in_rounds(&self, kept: &[(usize, Vec<BreakerHandle>)]) -> Option<String> {
        let consuming: Vec<BreakerHandle> = (0..self.located.len())
            .filter(|&pipeline| self.within[pipeline].is_none())
            .filter_map(|pipeline| match &self.located[pipeline] {
                Located::Chain(handle) => Some(handle.clone()),
                _ => None,
            })
            .chain(kept.iter().flat_map(|(_, handles)| handles.iter().cloned()))
            .collect();
        kept.iter().find_map(|(scope, breakers)| {
            let planned = &self.scopes[*scope];
            if planned.depth == 0 {
                return None;
            }
            let level = CurryLevel::new(planned.depth);
            breakers
                .iter()
                .find_map(|handle| unrestated(&*handle.borrow(), Some(level), &consuming, true))
        })
    }
}

/// The reads of the pipelines `kept` holds, numbered by their place in it: a read of a pipeline
/// that is not kept is a read of the pipelines it reads.
fn reads_of_kept(reads: &[Vec<usize>], kept: &[usize]) -> Vec<Vec<usize>> {
    fn expand(reads: &[Vec<usize>], kept: &[usize], read: usize, into: &mut Vec<usize>) {
        match kept.iter().position(|&pipeline| pipeline == read) {
            Some(at) if !into.contains(&at) => into.push(at),
            Some(_) => {}
            None => {
                for &beneath in &reads[read] {
                    expand(reads, kept, beneath, into);
                }
            }
        }
    }
    kept.iter()
        .map(|&pipeline| {
            let mut into = Vec::new();
            for &read in &reads[pipeline] {
                expand(reads, kept, read, &mut into);
            }
            into
        })
        .collect()
}

/// How many row levels a store's tiling has above its positions: the collection levels around its
/// `Tiling::Store`.
fn rows_above_positions(tiling: &Tiling) -> usize {
    let mut beneath = tiling;
    while let Tiling::DataFunction { codomain, .. } = beneath {
        beneath = codomain;
    }
    debug_assert!(
        matches!(beneath, Tiling::Store { .. }),
        "a store's tiling is a store beneath collection levels: {tiling:?}"
    );
    tiling.levels()
}

/// Why a round of a loop's scope cannot pull the chain at `producer`, or `None` where every
/// operator it pulls beneath the outermost keys restates the keys it is pulled at. `pulled` is the
/// level `producer` is pulled at, `None` where it is pulled whole, and each operator passes its
/// level to its inputs as it declares (`TileProducer::input_level`). A pull at the outermost keys
/// is walked too: every producer restates those keys, but an operator such as `Uncurry` pulls
/// its input beneath them. The walk ends at a recurrence slot or another store's read, whose
/// store answers from its snapshot, and, past the breaker it starts at (`start`), at every breaker
/// in `consuming`, whose consume pulls its inputs and whose own scope checks them.
fn unrestated(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    pulled: Option<CurryLevel>,
    consuming: &[BreakerHandle],
    start: bool,
) -> Option<String> {
    if producer.recurrence_of().is_some() || producer.store_read().is_some() {
        return None;
    }
    if let Some(pulled) = pulled
        && producer.restates().refuses(pulled)
    {
        let name = producer.name();
        let kind = name.split('#').next().unwrap_or(&name);
        return Some(format!(
            "{kind} in a loop's cycle is pulled at the keys of {pulled} and restates {}",
            producer.restates()
        ));
    }
    if pulled.is_none()
        || (!start
            && producer
                .base()
                .breaker_handle
                .as_ref()
                .and_then(std::rc::Weak::upgrade)
                .is_some_and(|handle| consuming.iter().any(|seen| Rc::ptr_eq(seen, &handle))))
    {
        return None;
    }
    let mut why = None;
    producer.visit_input_producers(&mut |role, input| {
        let beneath = pulled.and_then(|pulled| producer.input_level(role, pulled));
        why = why
            .take()
            .or_else(|| unrestated(input, beneath, consuming, false));
    });
    why
}

/// Whether the chain under `producer` reads the fan-out `fan` through a recurrence slot: whether
/// it is inside that fan-out's store's cycle. The walk stops at every recurrence slot, the one
/// edge that closes a cycle.
fn reaches_recurrence(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    fan: usize,
) -> bool {
    if let Some(through) = producer.recurrence_of() {
        return through == fan;
    }
    let mut reaches = false;
    producer.visit_input_producers(&mut |_, input| {
        reaches = reaches || reaches_recurrence(input, fan);
    });
    reaches
}

/// The placements a planning pass sets for its probes, which it clears when it drops: when the
/// pass returns, and when a probe unwinds, so no entry is left claiming a pipeline of a pass that
/// did not finish.
pub(super) struct ClearsPlacements<'p>(pub(super) &'p [Vec<Placement>]);

impl Drop for ClearsPlacements<'_> {
    fn drop(&mut self) {
        for placement in self.0.iter().flatten() {
            placement.set(None);
        }
    }
}

/// Visit `producer`'s inputs mutably, and answer how many it has. The planner finds the pipelines
/// beneath a producer by walking its inputs mutably, and reads the role each input has there, so
/// this checks that `visit_input_producers_mut` visits what `visit_input_producers` lists: the
/// same producers, by address, in the same order and under the same roles.
///
/// # Panics
///
/// Where the two walks differ, naming the first input at which they do.
pub(super) fn visit_inputs_checked(
    producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
    visit: &mut dyn FnMut(&str, &mut dyn crate::interpreter::tile_operators::TileProducer),
) -> usize {
    fn address(input: &dyn crate::interpreter::tile_operators::TileProducer) -> usize {
        std::ptr::from_ref(input).cast::<()>() as usize
    }
    let mut listed = Vec::new();
    producer.visit_input_producers(&mut |role, input| {
        listed.push((role.to_owned(), address(input)));
    });
    // The producer is borrowed mutably while it walks, so its name is read before.
    let name = producer.name();
    let mut at = 0;
    producer.visit_input_producers_mut(&mut |role, input| {
        let expected = listed.get(at);
        if !expected.is_some_and(|(listed, address_listed)| {
            listed == role && *address_listed == address(&*input)
        }) {
            panic!(
                "{name} visits {} under `{role}` mutably as its input {at}, where it lists {:?}",
                input.name(),
                expected.map(|(role, _)| role)
            );
        }
        at += 1;
        visit(role, input);
    });
    assert_eq!(
        at,
        listed.len(),
        "{name} visits {at} inputs mutably and lists {}",
        listed.len()
    );
    at
}

/// The region of a range's keys a source's yield `yielded` decides.
fn complete_region(yielded: &Predicate) -> Projection {
    match yielded.is_true() {
        true => Projection::Everything,
        false => Projection::admitting(yielded.clone()),
    }
}

/// How the run notifies a live pipeline of what its sources deliver ([`LivePipeline::poll`]).
enum Notifies {
    /// Of the region a push of a delivery's keys through the range's consumer brings the
    /// pipeline's entry.
    Arrivals,
    /// Of its whole input, once every source it reads yields everything, and of nothing before.
    Whole,
    /// A loop's scope: of a delivery's keys as the positions of its rounds.
    Rounds,
    /// A transaction store: of a delivery's keys as its items. The store has the writer's drive
    /// read its source again ([`Breaker::read_source_again`]): the drive reads its source only
    /// once told it gained items.
    Items,
}

/// A source pipeline of the run's dispatcher over live sources, and the region of each range's
/// keys it has been notified of.
struct LivePipeline {
    pipeline: PipelineId,
    leaves: Vec<(LiveLeaf, Predicate)>,
    notifies: Notifies,
    /// The pipeline's breaker's input, which a notification is a guard of.
    input: Tiling,
    /// The regions the pipeline's own ranges bring, which no live source yields and no arrival
    /// names: notified with the first poll, and empty after.
    starts: Vec<TileGuard>,
    announced: TileGuard,
    closed: bool,
}

impl LivePipeline {
    fn new(
        pipeline: PipelineId,
        leaves: Vec<LiveLeaf>,
        notifies: Notifies,
        input: Tiling,
        starts: Vec<TileGuard>,
    ) -> Self {
        Self {
            pipeline,
            leaves: leaves
                .into_iter()
                .map(|leaf| (leaf, Predicate::False))
                .collect(),
            notifies,
            announced: input.empty_guard(),
            input,
            starts,
            closed: false,
        }
    }

    /// Notify `dispatcher`'s pipeline of what each range's sources yield beyond what it was
    /// notified of, as [`Notifies`] says, and close it once every source yields everything.
    /// `reach` reaches the pipeline's breaker. Answers whether a source yielded more or the
    /// pipeline closed.
    fn poll(&mut self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        if self.closed {
            return false;
        }
        let mut changed = !self.starts.is_empty();
        let mut arrivals = self.input.empty_guard();
        for start in std::mem::take(&mut self.starts) {
            arrivals = arrivals.union(&start);
        }
        let mut complete = true;
        // Several ranges can read one source, so a scope or a store is notified of the positions
        // they gained together, once.
        let mut positions = Predicate::False;
        let mut fresh_sources: Vec<LiveSource> = Vec::new();
        for (leaf, notified) in &mut self.leaves {
            let yielded = leaf.extent.complete_region();
            debug_assert!(
                notified.minus(&yielded).is_false(),
                "a source's yield only grows: it yields {yielded:?}, short of {notified:?}"
            );
            complete &= yielded.is_true();
            let fresh = yielded.minus(notified);
            if fresh.is_false() {
                continue;
            }
            changed = true;
            match self.notifies {
                Notifies::Arrivals => {
                    for arrival in probe(
                        &leaf.consumer,
                        self.pipeline,
                        &Projection::admitting(fresh),
                        self.pipeline.0,
                    ) {
                        arrivals = arrivals.union(&arrival.guard);
                    }
                }
                Notifies::Whole => {}
                Notifies::Rounds | Notifies::Items => {
                    // A round runs once every position before it is complete, so a range read in
                    // rounds must yield a prefix of the positions of the field that orders it. A
                    // transaction store releases each item by its exact key and its drive attempts
                    // the lowest item delivered, so its items need no order.
                    #[cfg(debug_assertions)]
                    if matches!(self.notifies, Notifies::Rounds) {
                        let path = leaf.ordering_path().expect(
                            "a scope is read in rounds only from ranges with an ordering path",
                        );
                        assert!(
                            yields_a_prefix(&path, &yielded),
                            "a range read in rounds yields a prefix of the positions of its \
                             ordering field {path:?}: {yielded:?}"
                        );
                    }
                    leaf.extent.for_each_source(&mut |source| {
                        if !fresh_sources.iter().any(|seen| Rc::ptr_eq(seen, source)) {
                            fresh_sources.push(source.clone());
                        }
                    });
                    positions = positions.union(&fresh);
                }
            }
            // The keys the source yields are complete: it yields a key once for good.
            dispatcher.land_range_complete(
                self.pipeline,
                &complete_region(&yielded),
                &leaf.consumer,
            );
            *notified = yielded;
        }
        let fresh = guard_minus(&arrivals, &self.announced);
        if !fresh.is_empty() {
            self.announced = self.announced.union(&fresh);
            notify_unreleased(dispatcher, reach, self.pipeline, &fresh);
        }
        if !positions.is_false() {
            if matches!(self.notifies, Notifies::Items) {
                for source in &fresh_sources {
                    reach(self.pipeline, &mut |breaker, _| {
                        breaker.read_source_again(source)
                    });
                }
            }
            notify_unreleased(
                dispatcher,
                reach,
                self.pipeline,
                &Projection::admitting(positions).guard(&self.input),
            );
        }
        if complete {
            if matches!(self.notifies, Notifies::Whole) {
                notify_unreleased(
                    dispatcher,
                    reach,
                    self.pipeline,
                    &self.input.universal_guard(),
                );
            }
            dispatcher.close(self.pipeline);
            self.closed = true;
            changed = true;
        }
        changed
    }
}

/// Queue the announced region that the pipeline's input has not released.
fn notify_unreleased(
    dispatcher: &Dispatcher,
    reach: &mut Reach<'_>,
    pipeline: PipelineId,
    announced: &TileGuard,
) {
    let mut pending = None;
    reach(pipeline, &mut |breaker, input| {
        pending = unreleased(
            announced,
            &breaker.input_released(input),
            &breaker.input_tiling(input),
        );
    });
    if let Some(pending) = pending {
        dispatcher.notify(pipeline, &pending);
    }
}

/// [`drive`] over a run with source pipelines over live sources (`live`). The other sources
/// start whole. Each pass polls the live sources
/// (`DataSourceDomainExtentImpl::check_for_new_data`), notifies each live pipeline of what they
/// yield ([`LivePipeline::poll`]), and runs until nothing is claimable, then tells `observer`
/// (`RunObserver::drained`). Answers `false` where the observer ended the run, and `true` once
/// every pipeline has finished.
fn drive_live(
    dispatcher: &Dispatcher,
    reach: &mut Reach<'_>,
    execution: &Execution,
    live: &mut [LivePipeline],
    observer: &mut dyn RunObserver,
) -> bool {
    for (pipeline, info) in dispatcher.infos.iter().take(execution.roots).enumerate() {
        if info.reads.is_empty() && !live.iter().any(|at| at.pipeline.0 == pipeline) {
            let mut input = None;
            reach(PipelineId(pipeline), &mut |breaker, at| {
                input = Some((breaker.input_tiling(at), breaker.input_released(at)));
            });
            let (input, released) = input.expect("a reach calls the breaker it reaches");
            dispatcher.start_source(PipelineId(pipeline), &input, &released);
        }
    }
    // A run after a pause or a reload starts over breakers that hold what an earlier run consumed,
    // and the run has no finish before its sources close, so each pushes what it holds first.
    execution.push_held(dispatcher, reach);
    loop {
        let mut sources: Vec<LiveSource> = Vec::new();
        for (leaf, _) in live.iter().flat_map(|at| &at.leaves) {
            leaf.extent.for_each_source(&mut |source| {
                if !sources.iter().any(|seen| Rc::ptr_eq(seen, source)) {
                    sources.push(source.clone());
                }
            });
        }
        for source in &sources {
            source.borrow_mut().check_for_new_data();
        }
        observer.polled();
        let mut changed = false;
        for at in live.iter_mut() {
            changed |= at.poll(dispatcher, reach);
        }
        loop {
            match dispatcher.try_claim(None) {
                Next::Package(package) => execution.consume(dispatcher, reach, package),
                Next::Finish { pipeline, consumed } => {
                    execution.finish(dispatcher, reach, pipeline, consumed)
                }
                Next::Wait(_) if execution.resume(dispatcher, reach) => {}
                Next::Wait(_) => {
                    // A breaker that pushes only at its finish, as `MapAggregate`, finishes only
                    // once every source yields everything: it pushes what it completed here, and the
                    // pass runs on while that brings anything.
                    let before = dispatcher.changes();
                    execution.push_held(dispatcher, reach);
                    if dispatcher.changes() != before {
                        continue;
                    }
                    assert!(
                        live.iter().any(|at| !at.closed),
                        "a run whose live pipelines have all closed has a pipeline that may finish"
                    );
                    break;
                }
                Next::Done => return true,
                Next::Failed => panic!("a run on one thread fails only by panicking on it"),
            }
        }
        #[cfg(debug_assertions)]
        {
            execution.assert_nothing_in_flight(dispatcher);
            for pipeline in 0..dispatcher.infos.len() {
                reach(PipelineId(pipeline), &mut |breaker, _| {
                    assert!(
                        !breaker.holds_unsettled_decisions(),
                        "a drained boundary leaves no store holding a decision it took and has \
                         not settled, which a reload there would drop: pipeline {pipeline}"
                    );
                });
            }
        }
        if observer.drained(changed).is_break() {
            return false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{TestTileProducer, two_levels_of_ints};
    use crate::interpreter::tile_operators::{
        MemoProducer, ProducerBase, TileProducer, impl_producer_base,
    };

    /// A record range over a source field yields a prefix where that field's yield is every
    /// position at or below one, whatever its other fields hold.
    #[test]
    #[cfg(debug_assertions)]
    fn a_record_range_yields_a_prefix_of_its_ordering_field() {
        let source: LiveSource = Rc::new(RefCell::new(crate::interpreter::TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let extent = Extent::Record(
            [
                (SmolStr::new("a"), Extent::DataSourceDomain(source)),
                (SmolStr::new("b"), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        );
        let path = ordering_path_of(&extent);
        assert_eq!(path, Some(vec![SmolStr::new("a")]));
        let path = path.expect("ordered by `a`");
        let yielded = |a: Predicate| {
            Predicate::Record(
                [(SmolStr::new("a"), a), (SmolStr::new("b"), Predicate::True)]
                    .into_iter()
                    .collect(),
            )
        };
        let upto = |last: u64| Predicate::at_or_below(Value::UInt(last));
        assert!(yields_a_prefix(&path, &yielded(upto(2))));
        assert!(!yields_a_prefix(
            &path,
            &yielded(upto(0).union(&Predicate::point(Value::UInt(2))))
        ));
        // A source whose only progress is its completion yields nothing, then everything.
        assert!(yields_a_prefix(&path, &yielded(Predicate::False)));
        assert!(yields_a_prefix(&path, &yielded(Predicate::True)));
    }

    /// A record with a source in a field after its first is ordered by no field.
    #[test]
    fn a_record_with_a_later_source_field_has_no_ordering_path() {
        let source: LiveSource = Rc::new(RefCell::new(crate::interpreter::TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let extent = Extent::Record(
            [
                (SmolStr::new("a"), Extent::Base(BaseType::Int)),
                (SmolStr::new("b"), Extent::DataSourceDomain(source)),
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(ordering_path_of(&extent), None);
    }

    fn ordering_path_of(extent: &Extent) -> Option<Vec<SmolStr>> {
        LiveLeaf {
            consumer: Rc::new(RefCell::new(|| {})),
            extent: extent.clone(),
        }
        .ordering_path()
    }

    /// A run that unwinds hands the `main` output's producer back to the program: here the run's
    /// first pass drains with a live source that has yielded nothing, and its idle callback panics.
    #[test]
    fn a_run_that_unwinds_gives_the_main_producer_back() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        use crate::interpreter::{BaseType, Extent, TestDataSource};

        struct Ignored;
        impl DataSink for Ignored {
            fn process(&self, _tile: &Tile) {}
        }

        let mut ctx = GlobalContext::default();
        ctx.register_source(Rc::new(RefCell::new(TestDataSource::new(
            "nums",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ))));
        let mut program = compile_program(
            &mut ctx,
            &LoadedProgram::test("[x * 2 for x in nums()]"),
            Box::new(|| {}),
        )
        .expect("the program compiles");
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = run_program_into(&mut program, usize::MAX, Arc::new(Ignored), &mut || {
                panic!("the idle callback panics")
            });
        }));
        assert!(unwound.is_err(), "the idle callback panics");
        assert!(
            program.main().is_some_and(|main| main.producer.is_some()),
            "the run gave the `main` producer back"
        );
    }

    /// A run that unwinds leaves no entry its planner placed: the planner clears them when it
    /// drops while the thread panics, and a planner that returns keeps them.
    #[test]
    fn a_planner_that_unwinds_unplaces_its_entries() {
        let placed = || {
            let placement = Placement::default();
            placement.set(Some(PipelineId(0)));
            placement
        };
        let (kept, cleared) = (placed(), placed());
        let mut planner = Planner::default();
        planner.placements.push(vec![kept.clone()]);
        drop(planner);
        assert_eq!(
            kept.get(),
            Some(PipelineId(0)),
            "a planner that returns keeps them"
        );
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut planner = Planner::default();
            planner
                .placements
                .extend([vec![cleared.clone()], Vec::new()]);
            panic!("a probe panics");
        }));
        assert!(unwound.is_err());
        assert_eq!(cleared.get(), None);
    }

    #[test]
    fn a_late_planning_error_clears_installed_induction_control() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        use indoc::indoc;
        let mut ctx = GlobalContext::default();
        let _sink = ctx.register_test_sink("out");
        let program = compile_program(
            &mut ctx,
            &LoadedProgram::test(indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                total += x
            out << total
        "}),
            Box::new(|| {}),
        )
        .expect("the loop compiles");
        let map = ctx.take_operator_map();
        let fan = map
            .operators()
            .into_iter()
            .find(|fan| fan.cached_tile().is_some())
            .expect("one store");
        let store = fan.store().expect("one subscribed store");
        let result: Result<(), &str> = {
            let mut runs = InductionRuns::new();
            let mut planner = Planner::default();
            planner.store_pipeline(crate::interpreter::tile_operators::StoreRead {
                fan: fan.id(),
                store: store.clone(),
            });
            planner.build_scope(0, usize::MAX, &mut Vec::new(), &mut runs);
            assert!(induction(&store).run.is_some());
            Err("a later live-source check refuses the plan")
        };
        assert!(result.is_err());
        assert!(induction(&store).run.is_none());
        assert!(
            induction(&store)
                .seed_placements()
                .iter()
                .all(|placement| placement.get().is_none())
        );
        drop(program);
    }

    #[test]
    fn execution_runs_loop_requests_as_body_and_step_packages() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        use crate::interpreter::Position;
        use crate::interpreter::commit_operator::store_frontier;
        use crate::interpreter::tile_operators::test_helpers::keys_between;
        use indoc::indoc;

        let mut contexts = Vec::new();
        let mut operators = Vec::new();
        let mut programs = Vec::new();
        let mut reader_placements = Vec::new();
        let mut scopes = Vec::new();
        let mut runs = InductionRuns::new();
        for source in [
            indoc! {"
                out = test_sink()
                total := 0
                for x in [1, 2, 3]:
                    total += x
                out << total
            "},
            indoc! {"
                out = test_sink()
                total := 0
                for x in [1, 2, 3]:
                    if x > 1:
                        total += x
                out << total
            "},
        ] {
            let mut ctx = GlobalContext::default();
            let _sink = ctx.register_test_sink("out");
            let program = compile_program(&mut ctx, &LoadedProgram::test(source), Box::new(|| {}))
                .expect("the loop compiles");
            let map = ctx.take_operator_map();
            let stores: Vec<_> = map
                .operators()
                .into_iter()
                .filter(|fan| fan.cached_tile().is_some())
                .collect();
            assert_eq!(stores.len(), 1);
            let mut planner = Planner::default();
            planner.store_pipeline(crate::interpreter::tile_operators::StoreRead {
                fan: stores[0].id(),
                store: stores[0].store().expect("one subscribed store"),
            });
            let consumer = program
                .outputs
                .iter()
                .find_map(|output| output.sink_consumer.as_ref())
                .expect("one sink");
            let slot = consumer.borrow().producer_slot().clone();
            planner.pipelines_under(
                &mut **slot.borrow_mut().as_mut().expect("the sink has a producer"),
                "sink",
            );
            let members = planner.members(None);
            let scope_pipeline = members
                .located
                .iter()
                .position(|located| matches!(located, Located::Scope { .. }))
                .expect("one scope");
            let reader = members
                .reads
                .iter()
                .position(|reads| reads.contains(&scope_pipeline))
                .expect("a reader of the scope");
            reader_placements.push(members.placements[reader].clone());
            let scope = planner.build_scope(0, usize::MAX, &mut Vec::new(), &mut runs);
            induction(&scope).begin_run();
            scopes.push(Some(scope));
            contexts.push(ctx);
            operators.push(map);
            programs.push(program);
        }
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![], vec![0], vec![1]], usize::MAX);
        for (pipeline, placements) in reader_placements.iter().enumerate() {
            dispatcher.order(PipelineId(pipeline));
            for placement in placements {
                placement.set(Some(PipelineId(pipeline + 2)));
            }
            dispatcher.notify(PipelineId(pipeline), &keys_between(0, 2));
        }
        scopes.resize_with(4, || None);
        let execution = Execution::new(&scopes, &mut dispatcher);
        for reader in [2, 3] {
            dispatcher.hold_pipeline(PipelineId(reader), true);
        }
        let mut root = |_: PipelineId, _: &mut Call<'_>| {
            panic!("the test's ordinary readers stay held");
        };
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            execution.reach(pipeline, &mut root, call);
        };
        for _ in 0..2 {
            let Next::Package(package) = dispatcher.try_claim(None) else {
                panic!("a loop request is queued")
            };
            execution.consume(&dispatcher, &mut reach, package);
        }
        for pipeline in 0..2 {
            assert_eq!(
                dispatcher.states[pipeline]
                    .acknowledged
                    .load(Ordering::SeqCst),
                0
            );
        }
        let mut steps = [0; 2];
        while (0..2).any(|pipeline| {
            dispatcher.states[pipeline]
                .acknowledged
                .load(Ordering::SeqCst)
                == 0
        }) {
            match dispatcher.try_claim(None) {
                Next::Package(package) => {
                    let step = match &execution.handlers[package.pipeline.0] {
                        Handler::Step(Scope::Loop(owner)) => {
                            (0..2).find(|&index| Rc::ptr_eq(scopes[index].as_ref().unwrap(), owner))
                        }
                        _ => None,
                    };
                    execution.consume(&dispatcher, &mut reach, package);
                    if let Some(index) = step {
                        let position = steps[index];
                        steps[index] += 1;
                        let snapshot = {
                            let mut store = induction(scopes[index].as_ref().unwrap());
                            let guard = store.tiling().universal_guard();
                            store.get(guard)
                        };
                        assert_eq!(
                            store_frontier(&snapshot),
                            Some(Position::new(Value::UInt(position)))
                        );
                        if position < 2 {
                            assert_eq!(
                                dispatcher.states[index].acknowledged.load(Ordering::SeqCst),
                                0
                            );
                        } else {
                            assert_eq!(
                                dispatcher.states[index].acknowledged.load(Ordering::SeqCst),
                                1
                            );
                            assert!(
                                dispatcher.states[index + 2].queue.region().is_some(),
                                "the completed request publishes to its actual reader before returning"
                            );
                        }
                    }
                }
                Next::Wait(_) => assert!(
                    execution.resume(&dispatcher, &mut reach),
                    "pending requests have body or step work"
                ),
                _ => panic!("open loop requests finish through their queued steps"),
            }
        }
        assert_eq!(steps, [3, 3]);
        for index in 0..2 {
            assert_eq!(
                operators[index].live_state().into_values().next(),
                Some(Value::Int([6, 5][index]))
            );
        }
    }

    /// A memo over a producer that restates the outermost keys only.
    fn memo_over_outermost() -> MemoProducer {
        let (tile, tiling) = two_levels_of_ints();
        MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        )
    }

    /// An inner pipeline's breaker is pulled at the paths of its scope's rounds and pulls its
    /// input there, so `unrestated` names an input that restates only the outermost keys.
    #[test]
    fn a_breaker_pulled_beneath_the_outermost_keys_finds_an_input_that_restates_none() {
        let memo = memo_over_outermost();
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a loop's cycle is pulled at the keys of level 1 and restates \
                 the outermost keys only"
            )
        );
    }

    /// A breaker that consumes ends the walk: its consume pulls its inputs, and its own scope
    /// checks them. An inline breaker passes the read on to its inputs.
    #[test]
    fn a_placed_breaker_ends_the_walk_and_an_inline_one_passes_it_on() {
        let (_, tiling) = two_levels_of_ints();
        let inner = crate::interpreter::tile_operators::share_breaker(memo_over_outermost());
        let mut handle = None;
        inner.visit_input_producers(&mut |_, input| {
            handle = input
                .base()
                .breaker_handle
                .as_ref()
                .and_then(std::rc::Weak::upgrade);
        });
        let outer = MemoProducer::over(inner, &tiling);
        let level = Some(CurryLevel::new(1));
        assert_eq!(
            unrestated(
                &outer,
                level,
                &[handle.expect("the inner breaker has a handle")],
                true
            ),
            None
        );
        assert!(
            unrestated(&outer, level, &[], true)
                .is_some_and(|why| why.starts_with("TestTile in a loop's cycle"))
        );
    }

    /// A breaker in no inner pipeline is pulled whole, so nothing beneath it is pulled at a
    /// round's paths.
    #[test]
    fn a_breaker_pulled_whole_finds_nothing_beneath_it() {
        let memo = memo_over_outermost();
        assert_eq!(unrestated(&memo, None, &[], true), None);
    }

    /// A producer that restates every level and pulls its one input a level beneath the level it
    /// is pulled at, whatever that input restates.
    struct Deepens {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    impl TileProducer for Deepens {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn restates(&self) -> crate::interpreter::Restates {
            crate::interpreter::Restates::Every
        }

        fn input_level(&self, _role: &str, level: CurryLevel) -> Option<CurryLevel> {
            Some(CurryLevel::new(level.index() + 1))
        }

        fn get_impl(&mut self, _guard: TileGuard) -> Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// A pull at the outermost keys is walked: an operator that pulls its input beneath the keys
    /// it is pulled at reaches an input that restates the outermost keys only at level 1.
    #[test]
    fn an_outermost_pull_that_an_operator_deepens_finds_an_input_that_restates_none() {
        let (tile, tiling) = two_levels_of_ints();
        let deepens = Deepens {
            base: ProducerBase::unowned(Deepens::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling.clone())),
        };
        let memo = MemoProducer::over(Box::new(deepens), &tiling);
        let why = unrestated(&memo, Some(CurryLevel::OUTERMOST), &[], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a loop's cycle is pulled at the keys of level 1 and restates the \
                 outermost keys only"
            )
        );
    }

    /// A collection three levels deep, `0 ↦ {0 ↦ {0 ↦ 10, 1 ↦ 11}, 1 ↦ {0 ↦ 20, 1 ↦ 21}}`, read
    /// through a producer that restates its outermost keys only and logs the guards it is pulled
    /// at.
    struct OutermostOnly {
        tile: Tile,
        tiling: Tiling,
        pulled: Rc<RefCell<Vec<TileGuard>>>,
    }

    impl OutermostOnly {
        fn new() -> Self {
            use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Tiling};
            use bit_set::BitSet;
            let tiling = Tiling::data_function(
                Extent::uint_range(1),
                Tiling::data_function(
                    Extent::uint_range(2),
                    Tiling::data_function(
                        Extent::uint_range(2),
                        Tiling::Scalar(Extent::Base(BaseType::Int)),
                    ),
                ),
            );
            let tile = Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::UInts(vec![0, 1]),
                    Box::new(Tile::grouped(
                        vec![0, 2],
                        ColumnValue::UInts(vec![0, 1, 0, 1]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 11, 20, 21]))),
                        Predicate::True,
                        BitSet::new(),
                    )),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            );
            Self {
                tile,
                tiling,
                pulled: Default::default(),
            }
        }
    }

    struct OutermostOnlyProducer {
        base: ProducerBase,
        tile: Tile,
        pulled: Rc<RefCell<Vec<TileGuard>>>,
    }

    impl crate::interpreter::tile_operators::TileOperator for OutermostOnly {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(
            &self,
            _visit: &mut dyn FnMut(crate::interpreter::operator_graph::InputEdgeSpec<'_>),
        ) {
        }

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _cx: &mut crate::interpreter::SubscribeContext,
        ) -> Box<dyn TileProducer> {
            Box::new(OutermostOnlyProducer {
                base: ProducerBase::unowned(OutermostOnlyProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                pulled: self.pulled.clone(),
            })
        }
    }

    impl TileProducer for OutermostOnlyProducer {
        impl_producer_base!();

        fn get_impl(&mut self, guard: TileGuard) -> Tile {
            self.pulled.borrow_mut().push(guard.clone());
            let mut tile = self.tile.clone();
            tile.restrict_to(&guard.projection(&self.name()), self.tiling());
            tile
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// An `Uncurry` beneath a standing level, over an input that restates its outermost keys
    /// only, is pulled in a round at the pairs of a row. It pulls its input at the row, the level
    /// it declares, so the walk accepts it, and the walk and the pull agree on the level.
    #[test]
    fn an_uncurry_over_an_input_that_restates_the_outermost_keys_is_walked_at_its_pull() {
        use crate::interpreter::tile_operators::{TileOperator, Uncurry};
        use crate::interpreter::{Predicate, Projection, SubscribeContext, Value, tuple_field};
        let input = OutermostOnly::new();
        let pulled = input.pulled.clone();
        let mut uncurry = Uncurry::new_at(Box::new(input), CurryLevel::new(1));
        let mut producer = uncurry.subscribe(
            uncurry.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let round = CurryLevel::new(1);
        assert_eq!(unrestated(&*producer, Some(round), &[], true), None);
        let declared = producer.input_level("input", round);
        assert_eq!(declared, Some(CurryLevel::OUTERMOST));
        let pair = Value::Record(
            [
                (tuple_field(0), Value::UInt(1)),
                (tuple_field(1), Value::UInt(0)),
            ]
            .into_iter()
            .collect(),
        );
        let path = [Value::UInt(0), pair];
        let answer = producer
            .get(Projection::keys_at(round, Predicate::exactly(&path)).guard(producer.tiling()));
        assert_eq!(answer.paths_at(round), std::slice::from_ref(&path.to_vec()));
        let [guard] = pulled.borrow().clone().try_into().expect("one pull");
        assert_eq!(
            Projection::of(&guard).expect("a projection").level(),
            declared
        );
    }

    /// A producer that restates every level and reads its one input whole
    /// (`TileProducer::input_level` answers `None`).
    struct ReadsWhole {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
    }

    impl TileProducer for ReadsWhole {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn restates(&self) -> crate::interpreter::Restates {
            crate::interpreter::Restates::Every
        }

        fn input_level(&self, _role: &str, _level: CurryLevel) -> Option<CurryLevel> {
            None
        }

        fn get_impl(&mut self, _guard: TileGuard) -> Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&mut self, _guard: TileGuard) {}
    }

    /// An input a producer reads whole is pulled at no level beneath the outermost keys, so
    /// `unrestated` names none that restates the outermost keys only.
    #[test]
    fn an_input_read_whole_finds_nothing() {
        let (tile, tiling) = two_levels_of_ints();
        let reads_whole = ReadsWhole {
            base: ProducerBase::unowned(ReadsWhole::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling.clone())),
        };
        let memo = MemoProducer::over(Box::new(reads_whole), &tiling);
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[], true);
        assert_eq!(why, None);
    }
}

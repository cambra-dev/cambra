//! The planner that runs a compiled program through the dispatcher: it reads the pipelines off
//! the program's producer chains, plans each edge between two of them, and drives the run on
//! the calling thread. See `src/interpreter/design-operators.md`, "Running a compiled program".

use std::cell::RefCell;
use std::ops::ControlFlow;
use std::rc::Rc;
use std::sync::Arc;

use super::loop_scope::{self, Member, induction};
use super::*;
use crate::ccl::context::CompiledProgram;
use crate::interpreter::CurryLevel;
use crate::interpreter::sinks::ProducerSlot;
use crate::interpreter::tile_operators::StoreCell;
use crate::interpreter::tiling::Tile;
use crate::interpreter::{BaseType, DataSink, DataSourceDomainExtentImpl, Extent};

/// Run `program`'s pipelines through a dispatcher of `morsel_rows` on the calling thread, the
/// program compiled with its sinks unpulled (`GlobalContext::defer_sink_pulls`). The breakers are
/// the producers in the chains under its sinks' producers and its `main` output's that are pipeline
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
/// Every pipeline that reads another parks the rows its pushes and its start bring until every
/// pipeline it reads has decided them, and reads each row once ([`Dispatcher::park`]). A push
/// brings the rows it names at the reader's entry, restated by the consumers between the two, a
/// widening one's as every row. A reader reads its input whole ([`Dispatcher::read_whole`]) where
/// a pipeline it reads pushes along no route to it, which the consumers between them declare
/// ([`Consumer::route`]), or where no push and no start region names a region of its input. The
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
/// sink left placed: sinks compiled in pull mode; live ranges whose arrivals cannot be routed to
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
/// with what the producer states complete, the answer pull mode's one pull makes; over a live
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
    if !program.sink_pulls_deferred() {
        return Err(Refused(
            "the program was compiled with its sinks pulled, which runs part of it in pull mode \
             (`GlobalContext::defer_sink_pulls`)"
                .to_string(),
        ));
    }
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
    let result = run_targets(&targets, morsel_rows, &mut Idle(on_idle)).map(|ended| match ended {
        Ended::Done(planned) => planned,
        Ended::Paused(_) => unreachable!("an observer that never breaks pauses no run"),
    });
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
    pull_sinks(&targets);
    Ok(planned)
}

/// The run's last pull of each sink of `targets`, as pull mode's last: its producer answers from
/// what the breakers consumed and is released whole, so the pull hands the sink nothing new and
/// finds it done, which signals `CompiledProgram::done` once every sink has.
fn pull_sinks(targets: &[RunTarget]) {
    for (_, _, entry) in targets {
        if let TargetEntry::Sink(consumer) = entry {
            consumer.borrow().pull_now();
        }
    }
}

/// What a run's driver is told at a run's boundaries, on the run's thread, inside the run
/// (`dispatcher::in_a_run`): a pass of a run over live sources polls them, then runs until nothing
/// is claimable. A run with no live source has no boundary.
pub trait RunObserver {
    /// The pass has polled its live sources and notified no pipeline yet.
    fn polled(&mut self) {}
    /// No package is in flight and none is claimable. `changed` says whether the pass notified a
    /// pipeline or closed one. `Break` ends the run here.
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
            pull_sinks(&self.0);
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
    let mut planner = Planner::default();
    let roots: Vec<ProducerSlot> = targets.iter().map(|(slot, _, _)| slot.clone()).collect();
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
    let members = planner.members(None);
    let mut kept = Vec::new();
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
    let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
        if pipeline.0 >= members.located.len() {
            for scope in scopes.iter().flatten() {
                if induction(scope).reach_shared(pipeline, call) {
                    return;
                }
            }
            panic!("global pipeline {} belongs to a loop body", pipeline.0);
        }
        match &members.located[pipeline.0] {
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
            Located::Chain(id) => {
                let mut call = Some(call);
                for root in &roots {
                    let mut root = root.borrow_mut();
                    let producer = root.as_mut().expect("a root holds the producer it pulls");
                    if reach_in_chain(&mut **producer, *id, &mut call) {
                        return;
                    }
                }
                panic!("pipeline {} has its breaker in a root's chain", pipeline.0)
            }
        }
    };
    // Induction request and step roles target the same store producer.
    let mut end_of = |pipeline: PipelineId| match &members.located[pipeline.0] {
        Located::Scope { .. } => Some(induction(scope_at(pipeline)).pushing_end()),
        _ => None,
    };
    // A loop's scope with no range of its own over a live source, which reads only pipelines that
    // range over one, as a loop over a let-bound source reads the source's memo, takes those
    // ranges as its own where each read's pushes reach its drive as the drive's positions: the
    // scope is then notified of each delivery as rounds, as over the source itself, and parks each
    // delivery until the pipelines it reads have decided it (`Dispatcher::park`).
    let one = Projection::admitting(Predicate::point(Value::UInt(0)));
    let inherited: Vec<Vec<LiveLeaf>> = (0..members.live.len())
        .map(|pipeline| {
            let Some(scope) = scopes[pipeline].as_ref() else {
                return Vec::new();
            };
            if !members.live[pipeline].is_empty() || members.reads[pipeline].is_empty() {
                return Vec::new();
            }
            let mut leaves = Vec::new();
            for &read in &members.reads[pipeline] {
                if members.live[read].is_empty() || !members.reads[read].is_empty() {
                    return Vec::new();
                }
                let (pusher, _) = end_of(PipelineId(read))
                    .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                let mut scope = induction(scope);
                let routes = scope.routes(&pusher);
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
        morsel_rows,
        &mut reach,
        &mut end_of,
    );
    for (pipeline, &opens) in members.opens_before.iter().enumerate() {
        if opens {
            dispatcher.opens_before(PipelineId(pipeline));
        }
    }
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
            // completion; otherwise the scope parks each delivery on the pipelines it reads.
            _ if inherits => match leaves.iter().all(LiveLeaf::yields_prefix) {
                true => Notifies::Rounds,
                false => Notifies::Whole,
            },
            // A transaction store's input is its writer's source, read behind an entry no
            // planner places, so its items are a delivery's keys where the writer's source is
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
                    if !leaf.yields_prefix() {
                        return false;
                    }
                    let one = leaf.probe_region();
                    let mut scope = induction(scope);
                    let routes = scope.routes(&leaf.consumer);
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
                    let routes = routes_to(&leaf.consumer, pipeline);
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
                    for range in &members.leaves[pipeline] {
                        if routes_to(range, pipeline)
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
                        let (pusher, keyed) = end_of(PipelineId(read))
                            .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                        // A keyed breaker's push arrives as keys along a route that keeps them. A
                        // breaker of one value brings rows where its push names rows no arrival
                        // brings, as a let-bound record's collection field does; where it names
                        // only rows the arrivals bring, those rows read it, and wait parked for its
                        // decided push.
                        let as_keys = match keyed {
                            true => routes_to(&pusher, pipeline)
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
        // A store or a loop's scope steps on the pipelines it reads by pull, so it parks each
        // delivery until they have decided it (`Dispatcher::park`).
        if matches!(
            members.located[pipeline],
            Located::Store { .. } | Located::Scope { .. }
        ) && !members.reads[pipeline].is_empty()
        {
            dispatcher.park(PipelineId(pipeline));
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
    // hands one, as pull mode's one pull does.
    if !live.is_empty() {
        for ((_, _, entry), breaker) in targets.iter().zip(&sink_breakers) {
            if let TargetEntry::Main(_) = entry {
                breaker.borrow_mut().hand_each_package();
            }
        }
    }
    // The run drives every breaker it planned, so each takes its consuming mode here, before any
    // package, and keeps it for the run.
    for pipeline in 0..members.names.len() {
        reach(PipelineId(pipeline), &mut |breaker, _| {
            breaker.enter_consuming_mode()
        });
    }
    let mut execution = Execution::new(&scopes);
    execution.attach(&mut dispatcher);
    let done = in_a_run(|| {
        // A range over a static extent has decided every key from the start.
        for (pipeline, ranges) in members.leaves.iter().enumerate() {
            for range in ranges {
                dispatcher.land_range_decided(PipelineId(pipeline), &Projection::Everything, range);
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
    // decided by each of its sources all that a push of the source's every key lands as at its
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
                let decided = dispatcher.decided_of(PipelineId(reader), PipelineId(source));
                debug_assert!(
                    decided.covers(&reached),
                    "{name} has decided all it reaches of {}'s input, {reached:?}, at the run's end, \
                     which records {decided:?}",
                    members.names[reader]
                );
            };
            for &read in reads {
                let (pusher, _) = end_of(PipelineId(read))
                    .unwrap_or_else(|| pushing_end(&mut reach, PipelineId(read)));
                let reached = probe(&pusher, PipelineId(read), &Projection::Everything, reader);
                covered(read, reached, &members.names[read]);
            }
            // A range reaches the entries of the pipelines it is listed under, and possibly others.
            let ranges = members
                .leaves
                .iter()
                .enumerate()
                .flat_map(|(pipeline, ranges)| ranges.iter().map(move |range| (pipeline, range)));
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
    Ok(match done {
        true => Ended::Done(planned),
        false => {
            // The next run plans the graph afresh and places what it reaches.
            unplace(&planner.placements, targets);
            Ended::Paused(planned)
        }
    })
}

/// Owns installed scheduling metadata from planning through every run exit, including unwinding.
pub(super) struct InductionRuns {
    stores: Vec<StoreCell>,
}

impl InductionRuns {
    pub(super) fn new() -> Self {
        Self { stores: Vec::new() }
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
        for store in &self.stores {
            induction(store).clear_run();
        }
    }
}

pub(super) struct Execution {
    scopes: Vec<Option<StoreCell>>,
    steps: Vec<Option<StoreCell>>,
    roots: usize,
}

impl Execution {
    pub(super) fn new(scopes: &[Option<StoreCell>]) -> Self {
        Self {
            scopes: scopes.to_vec(),
            steps: vec![None; scopes.len()],
            roots: scopes.len(),
        }
    }

    pub(super) fn attach(&mut self, dispatcher: &mut Dispatcher) {
        for pipeline in 0..self.roots {
            if let Some(scope) = self.scopes[pipeline].clone() {
                Self::attach_store(
                    &scope,
                    dispatcher,
                    PipelineId(pipeline),
                    &mut self.scopes,
                    &mut self.steps,
                );
            }
        }
    }

    fn attach_store(
        store: &StoreCell,
        dispatcher: &mut Dispatcher,
        pipeline: PipelineId,
        stores: &mut Vec<Option<StoreCell>>,
        steps: &mut Vec<Option<StoreCell>>,
    ) {
        let graph = induction(store)
            .run
            .as_mut()
            .expect("an induction run is planned")
            .body_graph
            .take()
            .expect("a body graph is attached once");
        let base = dispatcher.append_graph(graph);
        let count = induction(store)
            .run
            .as_ref()
            .expect("an induction run is planned")
            .members
            .len();
        for local in 0..count {
            dispatcher.restrict_ingress(PipelineId(base + local), base..base + count);
        }
        stores.resize_with(dispatcher.infos.len(), || None);
        steps.resize_with(dispatcher.infos.len(), || None);
        let children: Vec<_> = induction(store)
            .run
            .as_ref()
            .expect("an induction run is planned")
            .members
            .iter()
            .enumerate()
            .filter_map(|(at, member)| match member {
                Member::Scope(child) => Some((PipelineId(base + at), child.clone())),
                Member::Chain(_) => None,
            })
            .collect();
        for (pipeline, child) in children {
            stores[pipeline.0] = Some(child.clone());
            Self::attach_store(&child, dispatcher, pipeline, stores, steps);
        }
        let body: Vec<_> = (base..base + count).map(PipelineId).collect();
        let step = dispatcher.add_pipeline(body.clone());
        dispatcher.order(step);
        for &member in &body {
            dispatcher.follow(step, member);
            dispatcher.hold_pipeline(member, true);
        }
        dispatcher.hold_pipeline(step, true);
        stores.resize_with(dispatcher.infos.len(), || None);
        steps.resize_with(dispatcher.infos.len(), || None);
        steps[step.0] = Some(store.clone());
        induction(store)
            .run
            .as_mut()
            .expect("an induction run is planned")
            .shared = Some(loop_scope::SharedLoop {
            pipeline,
            base,
            step,
            active: false,
            followers_released: false,
            finishing: None,
        });
    }

    fn complete(&self, dispatcher: &Dispatcher, scope: &StoreCell, package: Option<WorkPackage>) {
        if let Some(package) = package {
            let mut pushes = dispatcher.pushes(package.pipeline);
            let store = induction(scope);
            if store.pushes_while_consuming() {
                pushes.push_final(&*store);
            }
            drop(store);
            dispatcher.land(pushes);
            dispatcher.acknowledge(package);
        }
    }

    fn hold_followers(&self, dispatcher: &Dispatcher) {
        for scope in self.scopes.iter().flatten() {
            induction(scope).hold_followers(dispatcher);
        }
    }

    pub(super) fn consume(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        package: WorkPackage,
    ) {
        if let Some(scope) = &self.steps[package.pipeline.0] {
            induction(scope).complete_round();
            dispatcher.acknowledge(package);
            let completed = induction(scope).queue_package_round(dispatcher);
            self.complete(dispatcher, scope, completed);
        } else if let Some(scope) = &self.scopes[package.pipeline.0] {
            let completed = induction(scope).begin_shared(dispatcher, package);
            self.complete(dispatcher, scope, completed);
        } else {
            consume_with(dispatcher, reach, package);
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
        if self.steps[pipeline.0].is_some() {
            dispatcher.finish(dispatcher.pushes(pipeline));
        } else if let Some(scope) = &self.scopes[pipeline.0] {
            induction(scope).begin_shared_finish(dispatcher, consumed);
        } else {
            finish_with(dispatcher, reach, pipeline, consumed);
        }
        self.hold_followers(dispatcher);
    }

    pub(super) fn resume(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) -> bool {
        let mut progressed = false;
        for scope in self.scopes.iter().flatten() {
            let finished = induction(scope).take_shared_finish(dispatcher);
            if let Some((pipeline, consumed)) = finished {
                finish_with(dispatcher, reach, pipeline, consumed);
                induction(scope).unplace_shared();
                progressed = true;
                continue;
            }
            let pipelines = induction(scope).settlement_pipelines();
            let before = dispatcher.changes();
            push_held(dispatcher, reach, pipelines);
            // No other claim executes during this scope's publication pass on the serial
            // coordinator, so a generation change here belongs to these pushes.
            if dispatcher.changes() != before {
                progressed = true;
            } else {
                progressed |= induction(scope).release_followers(dispatcher);
            }
        }
        progressed
    }

    fn push_held(&self, dispatcher: &Dispatcher, reach: &mut Reach<'_>) {
        let pipelines = (0..dispatcher.infos.len())
            .filter(|&pipeline| {
                self.steps[pipeline].is_none()
                    && !dispatcher.states[pipeline].held.load(Ordering::SeqCst)
                    && !self.scopes[pipeline]
                        .as_ref()
                        .is_some_and(|scope| induction(scope).has_package())
            })
            .map(PipelineId)
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

/// Unplace every entry `placements` holds and every sink consumer of `targets`: a refused run
/// runs nothing, so it leaves nothing placed. A later run in pull mode pushes nothing, but a
/// placed entry claims a pipeline that no dispatcher holds.
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

/// Why the planner refuses a program: a shape no pipeline runs yet, which pull mode runs.
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
    /// source each delivery once they have decided it: a store that steps itself, or a loop's
    /// scope.
    Whole,
    /// One row per round of the scope it runs in, which queues it the row, once every pipeline it
    /// reads is quiescent: the scope of a loop nested in the scope's loop.
    Rounds,
}

/// The dispatcher over the pipelines `reads` describes, with every pipeline that reads another
/// parking the rows its pushes bring until the pipelines it reads have decided them, reading its
/// input whole where a pipeline it reads reaches it along no route, and queued at the start the
/// regions no push names ([`run_program`] says how). `arrivals` says whether a
/// pipeline takes a live source's arrivals beside the pipelines it reads
/// ([`Dispatcher::take_arrivals`]), which it parks ([`Dispatcher::park`]). `opens` says the
/// dispatcher is the run's, where a store or a loop's scope parks its deliveries; in a loop's
/// scope it follows the pipelines it reads, round by round. `kinds` says how each
/// pipeline takes its packages; `pushes_with` names, for each pipeline, the first pipeline of its
/// breaker, whose record of what the breaker pushed it shares ([`Dispatcher::share_pushes`]);
/// `end_of` answers the consumer a pipeline pushes to where its breaker is no producer that
/// answers it.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_edges(
    reads: &[Vec<usize>],
    names: &[String],
    leaves: &[Vec<SharedConsumer>],
    arrivals: &[bool],
    opens: bool,
    kinds: &[Consumes],
    pushes_with: &[usize],
    morsel_rows: usize,
    reach: &mut Reach<'_>,
    end_of: &mut dyn FnMut(PipelineId) -> Option<(SharedConsumer, bool)>,
) -> (Dispatcher, Vec<Planned>) {
    let mut dispatcher = Dispatcher::new(reads.to_vec(), morsel_rows);
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
                // A pipeline that pushes takes each delivery, parked until the pipelines it reads
                // have decided it.
                Consumes::Pushes => {
                    dispatcher.take_arrivals(PipelineId(reader));
                    dispatcher.park(PipelineId(reader));
                    planned[reader].held = true;
                }
                // A store or a loop's scope over a live source takes each delivery once the
                // pipelines it reads have decided it, or are quiescent where it follows them
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
            // In the run's dispatcher a store or a loop's scope over a live source parks each
            // delivery on what the pipelines it reads have decided instead (`run_targets`).
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
        // The nested loops' scopes it reads, whose finish of each round it waits for.
        let mut follows = Vec::new();
        // What the pushes of the pipelines it reads name of its input, `None` before any.
        let mut pushed: Option<TileGuard> = None;
        // Whether a pipeline it reads pushes along no route to it, so it reads that one by pull.
        let mut unreached = false;
        // The breakers whose routes were read, by the record of pushes their pipelines share
        // (`pushes_with`).
        let mut seen: Vec<usize> = Vec::new();
        let read_all = read;
        for &read in read {
            // A nested loop's scope runs a row per round of the scope around it, and a reader
            // inside the cycle around it reads the row once the nested scope is quiescent.
            if kinds[read] == Consumes::Rounds {
                follows.push(read);
                continue;
            }
            // The pipelines of one breaker push one region once between them, through the same
            // consumer, so they reach and name the same region.
            if seen.contains(&pushes_with[read]) {
                continue;
            }
            seen.push(pushes_with[read]);
            let (pusher, _) =
                end_of(PipelineId(read)).unwrap_or_else(|| pushing_end(reach, PipelineId(read)));
            let routes = routes_to(&pusher, reader);
            if routes.is_empty() {
                unreached = true;
                continue;
            }
            // A row reached along a path that passes a decided region on and along one that drops
            // it depends on rows the region does not name, so the read decides it only once whole.
            if routes.iter().any(|route| route.decides_part)
                && routes.iter().any(|route| !route.decides_part)
            {
                for &shared in read_all
                    .iter()
                    .filter(|&&r| pushes_with[r] == pushes_with[read])
                {
                    dispatcher.decides_whole_only(PipelineId(reader), PipelineId(shared));
                }
            }
            // A read along a route reaches what a push of its every key, wholly decided, lands
            // as: a row elsewhere waits for nothing of it. One read by pull reaches all of it.
            let region = decided_reach(&pusher, PipelineId(read), reader)
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
            .flat_map(|leaf| probe(leaf, PipelineId(read[0]), &Projection::Everything, reader))
            .fold(input.empty_guard(), |left, arrival| {
                left.union(&match &pushed {
                    Some(pushed) => guard_minus(&arrival.guard, pushed),
                    None => arrival.guard,
                })
            });
        // Every reader parks the rows its pushes and its start bring until the pipelines it
        // reads have decided them, and reads each row once ([`Dispatcher::park`]). A pipeline
        // that takes arrivals is queued its rows as its sources yield them, and any other reads
        // its input whole where a pipeline it reads reaches it by pull, or where nothing else
        // brings it a row.
        let whole = !arrivals[reader] && (unreached || (pushed.is_none() && left.is_empty()));
        if whole {
            dispatcher.read_whole(PipelineId(reader), &input);
            planned[reader].whole = true;
            continue;
        }
        for &follow in &follows {
            dispatcher.follow(PipelineId(reader), PipelineId(follow));
            planned[reader].follows.push(follow);
        }
        if !planned[reader].held {
            dispatcher.park(PipelineId(reader));
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
#[derive(Debug)]
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
    /// Whether it parks its arrivals until the pipelines it reads have decided them
    /// ([`Dispatcher::park`]).
    pub held: bool,
}

/// The consumer `pipeline`'s breaker pushes to, and whether its output has keys of its own, which
/// an operator on a path to a reader can widen: a push of one value is `Everything`.
fn pushing_end(reach: &mut Reach<'_>, pipeline: PipelineId) -> (SharedConsumer, bool) {
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
        end = Some((producer.base().downstream.clone(), keyed));
    });
    let (downstream, keyed) = end.expect("a reach calls the breaker it reaches");
    let downstream = downstream.unwrap_or_else(|| {
        panic!(
            "pipeline {} is read, so its breaker pushes to a consumer",
            pipeline.0
        )
    });
    (downstream, keyed)
}

/// The paths a push through `consumer` takes to the entry of `reader`, as the consumers on the
/// way declare them ([`Consumer::route`]).
pub(super) fn routes_to(consumer: &SharedConsumer, reader: usize) -> Vec<Route> {
    let mut routes = Routes::new();
    consumer.borrow_mut().route(&mut routes);
    routes
        .reached()
        .into_iter()
        .filter(|route| route.pipeline.0 == reader)
        .collect()
}

/// What a push of `region` through `consumer`, as `from`'s, brings to the entry of `reader`.
pub(super) fn probe(
    consumer: &SharedConsumer,
    from: PipelineId,
    region: &Projection,
    reader: usize,
) -> Vec<Arrival> {
    let mut landing = Landing::probe(from);
    consumer.borrow_mut().push(region, &mut landing);
    landing
        .arrivals()
        .into_iter()
        .filter(|arrival| arrival.pipeline.0 == reader)
        .collect()
}

/// The region of `reader`'s input a push of `from`'s every key reaches through `consumer` when
/// it is restated as a wholly decided region is: all `from` can ever decide of that input.
pub(super) fn decided_reach(
    consumer: &SharedConsumer,
    from: PipelineId,
    reader: usize,
) -> Vec<Arrival> {
    let mut landing = Landing::probe_decided(from);
    consumer
        .borrow_mut()
        .push(&Projection::Everything, &mut landing);
    landing
        .arrivals()
        .into_iter()
        .filter(|arrival| arrival.pipeline.0 == reader)
        .collect()
}

/// Where [`run_program`] finds a pipeline's breaker.
enum Located {
    /// In a sink's producer chain, or a store's, by its address ([`address`]).
    Chain(usize),
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
    pub(super) leaves: Vec<Vec<SharedConsumer>>,
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
    /// Per pipeline, the consumers of the ranges in its chain (`ProducerBase::leaf`), above
    /// every breaker beneath it.
    leaves: Vec<Vec<SharedConsumer>>,
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

/// What a chain holds beneath a producer, up to the nearest breakers.
#[derive(Default)]
struct Beneath {
    /// The pipelines of the nearest breakers, each once, and whether that breaker is the producer
    /// itself rather than beneath it.
    pipelines: Vec<(usize, bool)>,
    /// The consumers of the ranges above those breakers (`ProducerBase::leaf`).
    leaves: Vec<SharedConsumer>,
    /// The constant collections above those breakers that are no function operand: producers
    /// with no input and keys of their own that keep no consumer, so no probe names their keys.
    unprobed: Vec<String>,
    /// The ranges over a live source above those breakers.
    live: Vec<LiveLeaf>,
}

/// A live iteration range: its consumer and the full extent whose decided region is announced.
#[derive(Clone)]
pub(super) struct LiveLeaf {
    pub(super) consumer: SharedConsumer,
    pub(super) extent: Extent,
}

impl LiveLeaf {
    // Round requests must not include a later position while earlier positions can still arrive.
    fn yields_prefix(&self) -> bool {
        fn prefix(extent: &Extent) -> bool {
            match extent {
                Extent::DataSourceDomain(_) => true,
                Extent::Record(fields) => {
                    let mut fields: Vec<_> = fields.iter().collect();
                    fields.sort_by_key(|(name, _)| *name);
                    fields.first().is_none_or(|(_, extent)| prefix(extent))
                        && fields
                            .iter()
                            .skip(1)
                            .all(|(_, extent)| !extent.reads_a_source())
                }
                _ => !extent.reads_a_source(),
            }
        }
        prefix(&self.extent)
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
        let id = address(producer);
        if let Some(pipeline) = self
            .located
            .iter()
            .position(|at| matches!(at, Located::Chain(seen) if *seen == id))
        {
            return Beneath {
                pipelines: vec![(pipeline, true)],
                ..Beneath::default()
            };
        }
        let mut below = Beneath::default();
        let mut inputs = 0;
        let mut seen = 0;
        producer.visit_input_producers(&mut |_, _| seen += 1);
        producer.visit_input_producers_mut(&mut |role, input| {
            inputs += 1;
            let under = self.pipelines_under(input, role);
            below.read_once(under.pipelines);
            below.leaves.extend(under.leaves);
            below.unprobed.extend(under.unprobed);
            below.live.extend(under.live);
        });
        assert_eq!(
            inputs,
            seen,
            "{} visits as many inputs mutably as it lists, so the walk reaches every breaker \
             beneath it",
            producer.name()
        );
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
        let Some(breaker) = producer.as_breaking_mut() else {
            below.leaves.extend(leaf);
            for (_, direct) in &mut below.pipelines {
                *direct = false;
            }
            return below;
        };
        if let Some(why) = breaker.no_consuming_mode() {
            self.refuse(why);
            return Beneath::default();
        }
        let within = self.scope_of(&*producer);
        let name = producer.name();
        let placement =
            placement.unwrap_or_else(|| panic!("{name} is placed in a pipeline by its entry"));
        let pipeline = self.add(Located::Chain(id), name, within, below);
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
    /// breakers among them, stay in pull mode within it.
    ///
    /// Empty where the planner refuses the store ([`refuse`](Self::refuse)): a nested
    /// transaction store reached outside the scope of the loop around it; a store with no
    /// consuming mode; and a store inside the cycle of a store that steps itself.
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
        if let Some(why) = breaker.no_consuming_mode() {
            self.refuse(why);
            return Vec::new();
        }
        let inputs = breaker.inputs();
        // What each input holds beneath the store's cycle. A store with seeds reads them as its
        // input 0, and its writers' sources as the inputs after, in the order it visits them; one
        // without reads its writers' sources from input 0.
        let mut writers = Vec::new();
        let mut seeds = Beneath::default();
        let mut seeded = false;
        store.visit_input_producers_mut(&mut |role, producer| match role.starts_with("seed") {
            true => {
                let under = self.pipelines_under(producer, role);
                seeds.read_once(under.pipelines);
                seeds.live.extend(under.live);
                seeded = true;
            }
            false => writers.push(self.beneath_cycle(producer, read.fan)),
        });
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
                let placements = breaker.entry_placements(InputId(input));
                assert!(
                    !placements.is_empty(),
                    "{name} is placed in a pipeline by its entry"
                );
                placements
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
            store.visit_input_producers_mut(&mut |role, input| {
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
        // each seed has decided; the scope takes no push of them.
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
        let (mut inputs, mut seen) = (0, 0);
        producer.visit_input_producers(&mut |_, _| seen += 1);
        producer.visit_input_producers_mut(&mut |_, input| {
            inputs += 1;
            let under = self.beneath_cycle(input, fan);
            below.read_once(under.pipelines);
            below.live.extend(under.live);
        });
        assert_eq!(
            inputs,
            seen,
            "{} visits as many inputs mutably as it lists, so the walk of a store's cycle reaches \
             every pipeline beneath it",
            producer.name()
        );
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
    /// Each scope's address and the breakers it keeps are added to `kept`: the inner pipelines
    /// its rounds queue or push packages to ([`unrestated_in_rounds`](Self::unrestated_in_rounds)).
    pub(super) fn build_scope(
        &self,
        scope: usize,
        morsel_rows: usize,
        kept_scopes: &mut Vec<(usize, Vec<usize>)>,
        runs: &mut InductionRuns,
    ) -> StoreCell {
        let pipelines = self.members(Some(scope));
        let members: Vec<Member> = pipelines
            .located
            .iter()
            .map(|located| match located {
                Located::Chain(id) => Member::Chain(*id),
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
            for (at, &pipeline) in kept.iter().enumerate() {
                for placement in &pipelines.placements[pipeline] {
                    placement.set(Some(PipelineId(at)));
                }
            }
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                loop_scope::reach_member(
                    &mut induction(&store),
                    &members[kept[pipeline.0]],
                    pipeline,
                    call,
                )
            };
            let names: Vec<String> = kept.iter().map(|&at| pipelines.names[at].clone()).collect();
            let leaves: Vec<_> = kept
                .iter()
                .map(|&at| pipelines.leaves[at].clone())
                .collect();
            let kinds: Vec<Consumes> = kept.iter().map(|&at| pipelines.kinds[at]).collect();
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
                morsel_rows,
                &mut reach,
                &mut |pipeline| match &members[kept[pipeline.0]] {
                    Member::Scope(scope) => Some(induction(scope).pushing_end()),
                    Member::Chain(_) => None,
                },
            );
            for placement in pipelines.placements.iter().flatten() {
                placement.set(None);
            }
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
        let sources: Vec<_> = (0..members.len())
            .map(|at| inner.is_source(PipelineId(at)))
            .collect();
        let mut drives = Vec::new();
        for &start in &starts {
            if sources[start.0] && matches!(members[start.0], Member::Chain(_)) {
                let mut drive = false;
                loop_scope::reach_member(
                    &mut induction(&store),
                    &members[start.0],
                    start,
                    &mut |breaker, _| {
                        drive = breaker
                            .as_producer()
                            .is_some_and(|producer| producer.next_position().is_some());
                    },
                );
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
        let run = loop_scope::InductionRun::new(
            inner, sources, members, placements, starts, planned, *drive,
        );
        runs.install(&store, run);
        kept_scopes.push((scope, induction(&store).chain_breakers()));
        store
    }

    /// Why a round of a scope whose store has rows above its positions breaks the invariant that it
    /// pulls each operator beneath the outermost keys at a level the operator restates
    /// ([`unrestated`]), naming the operator, or `None` where no round does. Such a store is a
    /// nested loop's, or one per row of a comprehension. `kept` holds each scope's breakers, as
    /// [`build_scope`](Self::build_scope) gathers them. The walk starts at each breaker such a
    /// scope keeps, at the level of its rounds, and ends at every consuming breaker, whose
    /// consume pulls its own inputs. A breaker removed from its body graph because it would read
    /// whole remains in pull mode and passes the pull on.
    fn unrestated_in_rounds(&self, kept: &[(usize, Vec<usize>)]) -> Option<String> {
        let consuming: Vec<usize> = (0..self.located.len())
            .filter(|&pipeline| self.within[pipeline].is_none())
            .filter_map(|pipeline| match self.located[pipeline] {
                Located::Chain(id) => Some(id),
                _ => None,
            })
            .chain(kept.iter().flat_map(|(_, ids)| ids.iter().copied()))
            .collect();
        kept.iter().find_map(|(scope, breakers)| {
            let planned = &self.scopes[*scope];
            if planned.depth == 0 {
                return None;
            }
            let level = CurryLevel::new(planned.depth);
            let store = planned.store.borrow();
            breakers.iter().find_map(|&id| {
                let mut found = None;
                store.visit_input_producers(&mut |_, input| {
                    if found.is_none() {
                        found = at_address(
                            input,
                            id,
                            &mut Some(
                                |breaker: &dyn crate::interpreter::tile_operators::TileProducer| {
                                    unrestated(breaker, Some(level), &consuming, true)
                                },
                            ),
                        );
                    }
                });
                debug_assert!(
                    found.is_some(),
                    "a breaker scope {scope} keeps sits in its store's chain, inside the cycle"
                );
                found.flatten()
            })
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

/// A producer's identity in its chain: the address of its boxed state, which does not move while
/// the chain stands. `TileProducer::producer_id` counts per producer type, so two producers of
/// different types share one.
pub(super) fn address(producer: &dyn crate::interpreter::tile_operators::TileProducer) -> usize {
    std::ptr::from_ref(producer).cast::<()>() as usize
}

/// Why a round of a loop's scope cannot pull the chain at `producer`, or `None` where every
/// operator it pulls beneath the outermost keys restates the keys it is pulled at. `pulled` is the
/// level `producer` is pulled at, `None` where it is pulled whole or at the outermost keys, and
/// each operator passes its level to its inputs as it declares (`TileProducer::input_level`). The
/// walk ends at a recurrence slot or another store's read, whose store answers from its snapshot,
/// and, past the breaker it starts at (`start`), at every breaker in `consuming`, whose consume
/// pulls its inputs and whose own scope checks them.
fn unrestated(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    pulled: Option<CurryLevel>,
    consuming: &[usize],
    start: bool,
) -> Option<String> {
    if producer.recurrence_of().is_some() || producer.store_read().is_some() {
        return None;
    }
    let pulled = pulled.filter(|&pulled| pulled != CurryLevel::OUTERMOST);
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
    if pulled.is_none() || (!start && consuming.contains(&address(producer))) {
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

/// Call `f` with the producer at address `id` ([`address`]) in the chain under `producer`, and
/// answer what it answers; `None` where the chain holds no such producer. The walk crosses a
/// nested store's read, since a scope's breakers include the ones its nested loop's source is
/// read through, and stops at a recurrence slot, which closes a store's cycle.
fn at_address<R>(
    producer: &dyn crate::interpreter::tile_operators::TileProducer,
    id: usize,
    f: &mut Option<impl FnOnce(&dyn crate::interpreter::tile_operators::TileProducer) -> R>,
) -> Option<R> {
    if address(producer) == id {
        return f.take().map(|f| f(producer));
    }
    if producer.recurrence_of().is_some() {
        return None;
    }
    let mut found = None;
    producer.visit_input_producers(&mut |_, input| {
        if found.is_none() {
            found = at_address(input, id, f);
        }
    });
    found
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

/// Call `call` with the breaker at address `id` in the chain under `producer`, and answer whether
/// it was found.
pub(super) fn reach_in_chain(
    producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
    id: usize,
    call: &mut Option<&mut Call<'_>>,
) -> bool {
    if address(producer) == id {
        let breaker = producer
            .as_breaking_mut()
            .expect("a pipeline's producer is a breaker");
        (call.take().expect("a breaker is reached once"))(breaker, InputId::ONLY);
        return true;
    }
    let mut found = false;
    producer.visit_input_producers_mut(&mut |_, input| {
        found = found || reach_in_chain(input, id, call);
    });
    found
}

/// The region of a range's keys a source's yield `yielded` decides.
fn decided_region(yielded: &Predicate) -> Projection {
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
        for start in std::mem::take(&mut self.starts) {
            notify_unreleased(dispatcher, reach, self.pipeline, &start);
        }
        let mut complete = true;
        // Several ranges can read one source, so a scope or a store is notified of the positions
        // they gained together, once.
        let mut positions = Predicate::False;
        let mut fresh_sources: Vec<LiveSource> = Vec::new();
        for (leaf, notified) in &mut self.leaves {
            let yielded = leaf.extent.decided_region();
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
                        notify_unreleased(dispatcher, reach, self.pipeline, &arrival.guard);
                    }
                }
                Notifies::Whole => {}
                Notifies::Rounds | Notifies::Items => {
                    // A drive and a transaction store decide positions in order, and a round or an
                    // attempt runs once every position before it is complete, so a source read in
                    // positions yields a prefix of them.
                    debug_assert!(
                        !matches!(leaf.extent, Extent::DataSourceDomain(_))
                            || yielded.is_true()
                            || yielded.max_released_position().is_some_and(|last| {
                                let prefix = Predicate::at_or_below(last.into_value());
                                prefix.subsumes(&yielded) && yielded.subsumes(&prefix)
                            }),
                        "a live source read in positions yields a prefix of them: {yielded:?}"
                    );
                    leaf.extent.for_each_source(&mut |source| {
                        if !fresh_sources.iter().any(|seen| Rc::ptr_eq(seen, source)) {
                            fresh_sources.push(source.clone());
                        }
                    });
                    positions = positions.union(&fresh);
                }
            }
            // The keys the source yields are decided: it yields a key once for good.
            dispatcher.land_range_decided(self.pipeline, &decided_region(&yielded), &leaf.consumer);
            *notified = yielded;
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
    // and the run has no finish before its sources close, so each pushes what it holds first, as
    // a compile's pull of each sink does in pull mode.
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
                    // once every source yields everything: it pushes what it decided here, and the
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

    #[test]
    fn a_late_planning_error_clears_installed_induction_control() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::load::LoadedProgram;
        use indoc::indoc;
        let mut ctx = GlobalContext::default();
        ctx.defer_sink_pulls();
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
        let result: Result<(), &str> = (|| {
            let mut runs = InductionRuns::new();
            let mut planner = Planner::default();
            planner.store_pipeline(crate::interpreter::tile_operators::StoreRead {
                fan: fan.id(),
                store: store.clone(),
            });
            planner.build_scope(0, usize::MAX, &mut Vec::new(), &mut runs);
            assert!(induction(&store).run.is_some());
            Err("a later live-source check refuses the plan")
        })();
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
            ctx.defer_sink_pulls();
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
            induction(&scope).enter_consuming_mode();
            scopes.push(Some(scope));
            contexts.push(ctx);
            operators.push(map);
            programs.push(program);
        }
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![], vec![0], vec![1]], usize::MAX);
        for pipeline in 0..2 {
            dispatcher.order(PipelineId(pipeline));
            for placement in &reader_placements[pipeline] {
                placement.set(Some(PipelineId(pipeline + 2)));
            }
            dispatcher.notify(PipelineId(pipeline), &keys_between(0, 2));
        }
        scopes.resize_with(4, || None);
        let mut execution = Execution::new(&scopes);
        execution.attach(&mut dispatcher);
        for reader in [2, 3] {
            dispatcher.hold_pipeline(PipelineId(reader), true);
        }
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            for scope in scopes.iter().flatten() {
                if induction(scope).reach_shared(pipeline, call) {
                    return;
                }
            }
            panic!("the execution handler retains scope requests and handles store steps");
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
                    let step = execution.steps[package.pipeline.0].as_ref().map(|owner| {
                        (0..2)
                            .find(|&index| Rc::ptr_eq(scopes[index].as_ref().unwrap(), owner))
                            .unwrap()
                    });
                    execution.consume(&dispatcher, &mut reach, package);
                    if let Some(index) = step {
                        let position = steps[index];
                        steps[index] += 1;
                        let snapshot = {
                            let mut store = induction(scopes[index].as_ref().unwrap());
                            let guard = store.tiling().universal_guard();
                            store.offer_impl(guard)
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
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[address(&memo)], true);
        assert_eq!(
            why.as_deref(),
            Some(
                "TestTile in a loop's cycle is pulled at the keys of level 1 and restates \
                 the outermost keys only"
            )
        );
    }

    /// A breaker that consumes ends the walk: its consume pulls its inputs, and its own scope
    /// checks them. One in pull mode passes the pull on to its inputs.
    #[test]
    fn a_consuming_breaker_ends_the_walk_and_one_in_pull_mode_passes_it_on() {
        let (_, tiling) = two_levels_of_ints();
        let outer = MemoProducer::over(Box::new(memo_over_outermost()), &tiling);
        let mut inner = 0;
        outer.visit_input_producers(&mut |_, input| inner = address(input));
        let level = Some(CurryLevel::new(1));
        assert_eq!(unrestated(&outer, level, &[inner], true), None);
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
        let why = unrestated(&memo, Some(CurryLevel::new(1)), &[address(&memo)], true);
        assert_eq!(why, None);
    }
}

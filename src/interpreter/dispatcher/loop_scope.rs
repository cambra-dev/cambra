//! Loop request control and body graph planning for the run's shared dispatcher.
//! See `src/interpreter/design-dispatcher.md`, "A loop in rounds".

use super::plan::{Planned, probe, pushes_of, routes_to};
use super::*;
use crate::interpreter::commit_operator::InductionStoreProducer;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
use crate::interpreter::tile_operators::{StoreCell, TileProducer};

/// Where a loop scope finds the breaker of one of its inner pipelines.
#[derive(Clone)]
pub(super) enum Member {
    /// The shared cell owning an inner pipeline's breaker subscription.
    Chain(BreakerHandle),
    /// The scope of a loop nested in this one, which runs the rounds of one row of its store per
    /// round, the row of the round's position.
    Scope(StoreCell),
}

/// Dispatcher metadata installed on one induction producer for one run. It retains no handle to
/// its own StoreCell; the plan's lifetime guard clears it before that run exits.
pub(crate) struct InductionRun {
    pub(super) body: Body,
    /// The inner pipelines a round queues its position for: the sources, and the nested loops,
    /// which take it once the pipelines they read have finished the round.
    starts: Vec<PipelineId>,
    opened: bool,
    request: Option<Request>,
}

/// A scope's inner pipelines: a loop's body ([`InductionRun`]), or a transaction writer's
/// ([`WriterRun`](super::transaction_scope::WriterRun)). Planning builds them as a graph of their
/// own, which execution appends to the run's shared dispatcher between the scope's own pipeline
/// and its step (`Execution::attach_body` in `plan.rs`).
pub(super) struct Body {
    /// The planned graph, until execution appends it.
    graph: Option<Dispatcher>,
    pub(super) members: Vec<Member>,
    /// Each inner pipeline's entries, by local id. While the body runs, every entry is placed at
    /// its pipeline's global id except a source's, which stays unplaced so the source's pushes
    /// reach their completeness targets. Every entry is cleared once the body finishes, and when
    /// it is dropped.
    placements: Vec<Vec<Placement>>,
    /// The body planning tree, in local pipeline order.
    pub(super) planned: Vec<Planned>,
    /// The one inner pipeline whose breaker answers `TileProducer::next_position`: a loop's drive,
    /// a writer's transaction driver.
    pub(super) driver: PipelineId,
    /// Where the body sits in the run's shared dispatcher, once appended.
    attached: Option<Attached>,
    /// Whether the inner pipelines' entries are placed at their global ids and the pipelines
    /// run, which they do from the first request on. Only an attached body activates.
    active: bool,
    /// Whether the followers are released since they were last held, so a release is made once.
    followers_released: bool,
    /// The region the scope's pipeline consumed, from the scope's finish until the inner pipelines
    /// and the step have finished.
    finishing: Option<Option<TileGuard>>,
}

/// Where a body sits in the run's shared dispatcher.
pub(super) struct Attached {
    /// The scope's own pipeline in the dispatcher around it, whose claims are its requests.
    pub(super) pipeline: PipelineId,
    /// The global id of the first inner pipeline; the others follow it in local order.
    base: usize,
    /// The pipeline that follows every inner one, whose claim ends a round or an attempt.
    pub(super) step: PipelineId,
}

impl Body {
    pub(super) fn new(
        graph: Dispatcher,
        members: Vec<Member>,
        placements: Vec<Vec<Placement>>,
        planned: Vec<Planned>,
        driver: PipelineId,
    ) -> Self {
        Self {
            graph: Some(graph),
            members,
            placements,
            planned,
            driver,
            attached: None,
            active: false,
            followers_released: false,
            finishing: None,
        }
    }

    /// The planned graph, for execution to append to the run's dispatcher.
    pub(super) fn take_graph(&mut self) -> Dispatcher {
        self.graph.take().expect("a body's graph is appended once")
    }

    /// Record where execution appended the graph: after the scope's pipeline `pipeline`, from
    /// global id `base`, with the step `step`.
    pub(super) fn attach(&mut self, pipeline: PipelineId, base: usize, step: PipelineId) {
        debug_assert!(
            self.graph.is_none() && self.attached.is_none(),
            "a body's graph is taken, then attached, once"
        );
        self.attached = Some(Attached {
            pipeline,
            base,
            step,
        });
    }

    /// Where the body sits in the run's dispatcher.
    ///
    /// # Panics
    ///
    /// Before [`attach`](Self::attach): a body is reached through the handlers attaching installs.
    pub(super) fn attached(&self) -> &Attached {
        self.attached
            .as_ref()
            .expect("a body is reached once it is attached")
    }

    pub(super) fn is_attached(&self) -> bool {
        self.attached.is_some()
    }

    pub(super) fn is_active(&self) -> bool {
        self.active
    }

    /// The global id of the inner pipeline `local`; its local id before the body is attached,
    /// while planning probes the body graph alone.
    pub(super) fn global(&self, local: PipelineId) -> PipelineId {
        PipelineId(self.attached.as_ref().map_or(0, |attached| attached.base) + local.0)
    }

    /// The global ids of the inner pipelines, none before the body is attached.
    pub(super) fn pipelines(&self) -> Vec<PipelineId> {
        match &self.attached {
            Some(attached) => (attached.base..attached.base + self.members.len())
                .map(PipelineId)
                .collect(),
            None => Vec::new(),
        }
    }

    /// The inner pipelines and the step.
    fn with_step(&self) -> impl Iterator<Item = PipelineId> + use<> {
        let step = self.attached().step;
        self.pipelines().into_iter().chain(std::iter::once(step))
    }

    /// Place each inner pipeline's entries at its global id, except a source's, and let the inner
    /// pipelines and the step run. Whether this call activated the body: it does so once.
    pub(super) fn activate(&mut self, dispatcher: &Dispatcher) -> bool {
        if self.active {
            return false;
        }
        self.active = true;
        for (local, placements) in self.placements.iter().enumerate() {
            let pipeline = self.global(PipelineId(local));
            for placement in placements {
                placement.set((!dispatcher.is_source(pipeline)).then_some(pipeline));
            }
            dispatcher.hold_pipeline(pipeline, false);
        }
        dispatcher.hold_pipeline(self.attached().step, false);
        true
    }

    /// Hold back the pipelines that follow the inner pipelines and the step, once the body runs.
    pub(super) fn hold_followers(&mut self, dispatcher: &Dispatcher) {
        if !self.active {
            return;
        }
        dispatcher.hold_followers(self.with_step(), true);
        self.followers_released = false;
    }

    /// Let the pipelines that follow the inner pipelines and the step run, unless the body does
    /// not run or they already may. Whether this call released them.
    pub(super) fn release_followers(&mut self, dispatcher: &Dispatcher) -> bool {
        if !self.active || self.followers_released {
            return false;
        }
        dispatcher.hold_followers(self.with_step(), false);
        self.followers_released = true;
        true
    }

    /// Begin the scope's finish, which consumed `consumed` of the scope's pipeline.
    pub(super) fn begin_finish(&mut self, consumed: Option<TileGuard>) {
        debug_assert!(self.finishing.is_none(), "a scope finishes once");
        self.finishing = Some(consumed);
    }

    /// Whether the scope's finish has begun and the body has not finished.
    pub(super) fn is_finishing(&self) -> bool {
        self.finishing.is_some()
    }

    /// Close the inner sources, so the inner pipelines finish once they have read what is queued.
    pub(super) fn close_sources(&self, dispatcher: &Dispatcher) {
        for pipeline in self.pipelines() {
            if dispatcher.is_source(pipeline) {
                dispatcher.close(pipeline);
            }
        }
    }

    /// The scope's pipeline and the region it consumed, once its finish has begun and the inner
    /// pipelines and the step have all finished.
    pub(super) fn take_finish(
        &mut self,
        dispatcher: &Dispatcher,
    ) -> Option<(PipelineId, Option<TileGuard>)> {
        self.finishing.as_ref()?;
        let pipeline = self.attached.as_ref()?.pipeline;
        let finished = self
            .with_step()
            .all(|pipeline| dispatcher.states[pipeline.0].phase.load() == Phase::Finished);
        if !finished {
            return None;
        }
        let consumed = self.finishing.take().expect("the finish is pending");
        Some((pipeline, consumed))
    }

    /// Call `call` with the breaker of the inner pipeline `local`.
    pub(super) fn reach(&self, local: PipelineId, call: &mut Call<'_>) {
        reach_member(&self.members[local.0], call);
    }

    /// Where the driver's source records its complete pushes ([`CompletionTarget`]).
    pub(super) fn driver_target(&self) -> Option<CompletionTarget> {
        let mut target = None;
        self.reach(self.driver, &mut |breaker, _| {
            target = breaker
                .as_producer()
                .and_then(|producer| producer.completes_through());
        });
        target
    }

    /// Have the driver's source record its complete pushes at `pipeline`, the scope's pipeline,
    /// as complete regions of the driver's input ([`CompletionTarget`]).
    pub(super) fn complete_driver_through(&self, pipeline: PipelineId) {
        self.reach(self.driver, &mut |breaker, _| {
            if let Some(target) = breaker
                .as_producer()
                .and_then(|producer| producer.completes_through())
            {
                *target.borrow_mut() = Some((pipeline, breaker.input_tiling(InputId::ONLY)));
            }
        });
    }

    /// Clear every inner pipeline's entries.
    pub(super) fn unplace(&self) {
        for placement in self.placements.iter().flatten() {
            placement.set(None);
        }
    }
}

/// A dropped body leaves no entry placed and no completion recorded at a pipeline of its run.
impl Drop for Body {
    fn drop(&mut self) {
        self.unplace();
        if let Some(target) = self.driver_target() {
            *target.borrow_mut() = None;
        }
    }
}

struct Request {
    read: bool,
    emitted: bool,
    closing: bool,
    round: Option<TileGuard>,
    package: WorkPackage,
}

impl InductionRun {
    pub(super) fn new(body: Body, starts: Vec<PipelineId>) -> Self {
        Self {
            body,
            starts,
            opened: false,
            request: None,
        }
    }
}

pub(super) fn induction(
    store: &StoreCell,
) -> crate::interpreter::tile_operators::StoreBorrow<'_, InductionStoreProducer> {
    store.borrow_mut().map(|producer| {
        producer
            .as_induction_store_mut()
            .expect("a loop store has concrete induction state")
    })
}

impl InductionStoreProducer {
    fn run(&self) -> &InductionRun {
        self.run.as_ref().expect("an induction run is planned")
    }
    fn run_mut(&mut self) -> &mut InductionRun {
        self.run.as_mut().expect("an induction run is planned")
    }

    /// The run's body, for the execution that attaches and drives it.
    pub(super) fn body_mut(&mut self) -> &mut Body {
        &mut self.run_mut().body
    }

    fn pipeline(&self, local: PipelineId) -> PipelineId {
        self.run().body.global(local)
    }

    fn activate(&mut self, dispatcher: &Dispatcher) {
        if self.run_mut().body.activate(dispatcher) {
            self.hold_followers(dispatcher);
        }
    }

    pub(super) fn hold_followers(&mut self, dispatcher: &Dispatcher) {
        self.run_mut().body.hold_followers(dispatcher);
    }

    pub(super) fn settlement_pipelines(&self) -> Vec<PipelineId> {
        let body = &self.run().body;
        if !body.is_active() || self.run().request.is_none() {
            return Vec::new();
        }
        (0..body.members.len())
            .filter(|&local| {
                !matches!(&body.members[local], Member::Scope(scope) if induction(scope).has_package())
            })
            .map(|local| body.global(PipelineId(local)))
            .collect()
    }

    pub(super) fn release_followers(&mut self, dispatcher: &Dispatcher) -> bool {
        let run = self.run_mut();
        // The serial coordinator takes one claim before holding followers again.
        run.request.is_some() && run.body.release_followers(dispatcher)
    }

    pub(super) fn begin_shared(
        &mut self,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) -> Option<WorkPackage> {
        self.activate(dispatcher);
        self.begin_package(package);
        self.queue_package_round(dispatcher)
    }

    pub(super) fn begin_shared_finish(
        &mut self,
        dispatcher: &Dispatcher,
        consumed: Option<TileGuard>,
    ) {
        assert!(
            !self.has_package(),
            "a scope finishes after completing its requests"
        );
        self.activate(dispatcher);
        let body = &mut self.run_mut().body;
        body.begin_finish(consumed);
        body.close_sources(dispatcher);
    }

    /// Place local entries for a planning probe; attached execution keeps global entries live.
    fn placed<R>(&mut self, run: impl FnOnce(&mut Self) -> R) -> R {
        if self.run().body.is_active() {
            return run(self);
        }
        let placements = self.run().body.placements.clone();
        let _placed = Placed::new(&placements);
        run(self)
    }

    fn reach_local(&mut self, pipeline: PipelineId, call: &mut Call<'_>) {
        let member = self.run().body.members[pipeline.0].clone();
        reach_member(&member, call);
    }

    pub(super) fn clear_run(&mut self) {
        if self.run.is_none() {
            return;
        }
        for placement in self.seed_placements() {
            placement.set(None);
        }
        self.run = None;
    }

    pub(crate) fn begin_loop_run(&mut self) {
        let Some(run) = &self.run else { return };
        let count = run.body.members.len();
        for local in 0..count {
            self.reach_local(PipelineId(local), &mut |breaker, _| breaker.begin_run());
        }
    }

    fn terminal(&self) -> bool {
        self.final_guard().is_universal()
    }

    /// The path of the position the drive emits next, which the next round runs: the next its
    /// source delivers. `None` once the source delivers no more.
    ///
    /// # Panics
    ///
    /// Where no source in the store's chain among the scope's pipelines, or more than one, is a
    /// drive.
    fn next_round_position(&mut self) -> Option<Vec<Value>> {
        let drive = self.drive();
        let mut next = None;
        self.reach_local(drive, &mut |breaker, _| {
            next = breaker
                .as_producer()
                .and_then(|producer| producer.next_position())
                .flatten();
        });
        next
    }

    /// The drive: the one source pipeline in the store's chain whose breaker answers
    /// `TileProducer::next_position`.
    ///
    /// # Panics
    ///
    /// Where no source in the store's chain among the scope's pipelines, or more than one, is a
    /// drive.
    fn drive(&self) -> PipelineId {
        self.run().body.driver
    }

    /// Have the entry in front of the drive's source record a complete push of the source's keys
    /// at `pipeline`, this scope's pipeline in the dispatcher around it, as complete positions of
    /// the store's input: the drive reads its source by pull, so no push of the source reaches the
    /// scope's entry otherwise, and the scope would park each round until the source is whole.
    pub(super) fn decide_through_drive(&mut self, pipeline: PipelineId) {
        let input = self.input_tiling(InputId::ONLY);
        let target = self
            .drive_target()
            .expect("a loop's drive records its source's complete pushes");
        *target.borrow_mut() = Some((pipeline, input));
    }

    /// Undo [`decide_through_drive`](Self::decide_through_drive): the drive's source's complete
    /// pushes record nothing.
    pub(super) fn forget_through_drive(&mut self) {
        if let Some(target) = self.drive_target() {
            *target.borrow_mut() = None;
        }
    }

    /// Whether the drive's source's complete pushes record at some pipeline.
    pub(super) fn decides_through_drive(&mut self) -> bool {
        self.drive_target()
            .is_some_and(|target| target.borrow().is_some())
    }

    /// Where the drive's source's complete pushes record ([`CompletionTarget`]).
    fn drive_target(&mut self) -> Option<CompletionTarget> {
        self.run().body.driver_target()
    }

    /// The paths the pushes `regions` from the range in front of `consumer` take to the drive's
    /// entry ([`routes_to`]).
    pub(super) fn routes(
        &mut self,
        consumer: &SharedConsumer,
        regions: &[Projection],
    ) -> Vec<Route> {
        let drive = self.drive();
        self.placed(|_| routes_to(consumer, regions, drive.0))
    }

    /// Where a push of `region` from the range in front of `consumer` lands at the drive's entry,
    /// as guards of the drive's input, the drive's source: a planner probes how a live source's
    /// arrivals reach the scope's rounds.
    pub(super) fn arrivals(
        &mut self,
        consumer: &SharedConsumer,
        region: &Projection,
    ) -> Vec<Arrival> {
        let drive = self.drive();
        self.placed(|_| probe(consumer, drive, region, drive.0))
    }

    /// Have the drive read what its source holds, emitting nothing: a consume at no position. A
    /// loop nested in another learns the positions of a row once the round of the loop around it
    /// has run, so the scope reads them before it runs the row's rounds.
    fn read_source(&mut self) {
        let drive = self.drive();
        self.reach_local(drive, &mut |breaker, input| {
            let none = breaker.input_tiling(input).empty_guard();
            breaker.consume_impl(input, none);
        });
    }

    fn closing_readers(&self, dispatcher: &Dispatcher) -> Vec<PipelineId> {
        (0..self.run().body.members.len())
            .map(PipelineId)
            .filter(|&pipeline| {
                !(dispatcher.is_source(self.pipeline(pipeline))
                    && matches!(self.run().body.members[pipeline.0], Member::Chain(_)))
            })
            .collect()
    }

    /// The row `guard`, a guard of the store's input, as each inner pipeline in `readers` takes
    /// it: where a push of the row from the drive reaches the pipeline's entry, what it lands as
    /// there, restated by every operator on the way, as `Uncurry` restates the row as the pairs it
    /// heads; elsewhere the row itself, for a pipeline whose input the store's positions key.
    fn row_for(
        &mut self,
        guard: &TileGuard,
        readers: &[PipelineId],
    ) -> Vec<(PipelineId, TileGuard)> {
        let drive = self.drive();
        let mut consumer = None;
        self.reach_local(drive, &mut |breaker, _| {
            consumer = breaker
                .as_producer()
                .and_then(|producer| producer.base().downstream.clone());
        });
        let consumer = consumer.expect("a loop's drive pushes to the pipelines that read it");
        let region = Projection::of(guard)
            .unwrap_or_else(|why| panic!("a loop's round names a row of its store: {why}"));
        let mut landing = Landing::probe(self.pipeline(drive));
        consumer.borrow_mut().notify(&region, &mut landing);
        let arrivals = landing.arrivals();
        readers
            .iter()
            .flat_map(|&reader| {
                let landed: Vec<(PipelineId, TileGuard)> = arrivals
                    .iter()
                    .filter(|arrival| arrival.pipeline.0 == self.pipeline(reader).0)
                    .map(|arrival| (reader, arrival.guard.clone()))
                    .collect();
                if !landed.is_empty() {
                    return landed;
                }
                let mut fits = false;
                self.reach_local(reader, &mut |breaker, input| {
                    fits = guard.check_from(&breaker.input_tiling(input))
                });
                match fits {
                    true => vec![(reader, guard.clone())],
                    false => Vec::new(),
                }
            })
            .collect()
    }

    fn begin_package(&mut self, package: WorkPackage) {
        assert!(
            self.run().request.is_none(),
            "a loop completes one request before starting another"
        );
        if !self.run().opened {
            // The drive reads before the opening step, so the step emits no position outside
            // a round. Each emitted position must run the body before the next store step.
            self.read_source();
            let none = self.input_tiling(InputId::ONLY).empty_guard();
            self.consume_impl(InputId::ONLY, none);
            self.run_mut().opened = true;
        }
        let rows = !matches!(self.tiling(), Tiling::Store { .. });
        if rows {
            self.placed(|scope| scope.read_source());
        }
        self.run_mut().request = Some(Request {
            read: rows,
            emitted: false,
            closing: false,
            round: None,
            package,
        });
    }

    pub(super) fn has_package(&self) -> bool {
        self.run().request.is_some()
    }

    pub(super) fn queue_package_round(&mut self, dispatcher: &Dispatcher) -> Option<WorkPackage> {
        let rows = !matches!(self.tiling(), Tiling::Store { .. });
        let mut request = self
            .run_mut()
            .request
            .take()
            .expect("a loop has a pending request");
        assert!(
            request.round.is_none(),
            "the body and store step complete before the next round"
        );
        if request.closing {
            return Some(request.package);
        }
        loop {
            if !self.terminal()
                && let Some(position) = self.next_round_position()
                && request.package.guard.covers_path(&position)
            {
                let guard = Projection::of_path(&position).guard(&self.input_tiling(InputId::ONLY));
                let starts = self.run().starts.clone();
                self.placed(|store| store.queue_round_on(dispatcher, &guard, &starts));
                request.emitted = true;
                request.round = Some(guard);
                self.run_mut().request = Some(request);
                return None;
            }
            // A flat scope reads newly delivered source positions at most once per request,
            // after exhausting the positions the drive buffered before this request.
            if request.read || self.terminal() || self.next_round_position().is_some() {
                break;
            }
            self.placed(|scope| scope.read_source());
            request.read = true;
        }
        let closing = rows
            || (!request.emitted
                && !self.terminal()
                && !guard_minus(&request.package.guard, &self.input_released(InputId::ONLY))
                    .is_empty());
        if !closing {
            return Some(request.package);
        }
        self.placed(|scope| {
            // A row's last position does not state the row's end. Render the drive once more
            // at no position so the closing round can release the row whole, including an
            // empty row. A flat request closes only positions the source emitted none of.
            if rows {
                scope.read_source();
            }
            scope.queue_round_on(
                dispatcher,
                &request.package.guard,
                &scope.closing_readers(dispatcher),
            );
        });
        request.closing = true;
        request.round = Some(request.package.guard.clone());
        self.run_mut().request = Some(request);
        None
    }

    /// Step the queued round after its body and held pushes settle.
    pub(super) fn complete_round(&mut self) {
        let guard = self
            .run_mut()
            .request
            .as_mut()
            .and_then(|request| request.round.take())
            .expect("a loop steps one queued round");
        self.placed(|scope| scope.step_round(&guard));
    }

    /// Queue the body's work for one position or closing row, before the store steps it.
    fn queue_round_on(
        &mut self,
        dispatcher: &Dispatcher,
        guard: &TileGuard,
        starts: &[PipelineId],
    ) {
        self.read_cycle_again();
        let (sources, readers): (Vec<PipelineId>, Vec<PipelineId>) = starts
            .iter()
            .partition(|&&start| dispatcher.is_source(self.pipeline(start)));
        for source in sources {
            dispatcher.notify(self.pipeline(source), guard);
        }
        for (reader, row) in self.row_for(guard, &readers) {
            // A reader whose input has released the whole row consumed it final, its end
            // included, and reads it no more: it is no longer there to read. A row released in
            // part is read again whole, for its end.
            let mut released = false;
            self.reach_local(reader, &mut |breaker, input| {
                released = guard_minus(&row, &breaker.input_released(input)).is_empty()
            });
            if !released {
                dispatcher.queue_round(self.pipeline(reader), &row);
            }
        }
        if self.run().body.is_attached() {
            dispatcher.queue_round(self.run().body.attached().step, guard);
        }
    }

    /// Step the store after the round's body and held pushes have settled.
    fn step_round(&mut self, guard: &TileGuard) {
        self.consume_impl(InputId::ONLY, guard.clone());
        assert!(
            self.final_guard().is_universal()
                || guard_minus(guard, &self.input_released(InputId::ONLY)).is_empty(),
            "{}'s step in the round of {guard:?} decides it",
            self.name()
        );
    }
}

/// Call `call` with `member`'s breaker, the inner pipeline `pipeline`'s: in `store`'s chain, or
/// a nested loop's scope.
pub(super) fn reach_member(member: &Member, call: &mut Call<'_>) {
    match member {
        Member::Scope(store) => call(&mut *induction(store), InputId::ONLY),
        Member::Chain(handle) => call(&mut *handle.borrow_mut(), InputId::ONLY),
    }
}

impl InductionStoreProducer {
    /// The breaker subscriptions of the inner pipelines a round queues or publishes.
    pub(super) fn chain_breakers(&self) -> Vec<BreakerHandle> {
        self.run()
            .body
            .members
            .iter()
            .filter_map(|member| match member {
                Member::Chain(handle) => Some(handle.clone()),
                Member::Scope(_) => None,
            })
            .collect()
    }

    /// The consumer the scope's pipeline pushes to, the store's, and whether the store pushes a
    /// region of its keys: a nested store pushes rows, and a flat store the positions its rounds
    /// decide where it pushes any before it is terminal (`pushes_complete_positions`). Any other
    /// pushes everything, once it is terminal.
    pub(super) fn pushing_end(&self) -> (SharedConsumer, bool, Vec<Projection>) {
        let keyed = matches!(self.tiling(), Tiling::DataFunction { .. })
            || crate::interpreter::commit_operator::pushes_complete_positions(self.tiling());
        let downstream = self
            .base()
            .downstream
            .clone()
            .unwrap_or_else(|| panic!("{} is read, so it pushes to a consumer", self.name()));
        (downstream, keyed, pushes_of(self.tiling()))
    }
}

/// Local entry placement for a planning probe, cleared when the probe returns.
struct Placed<'p> {
    placements: &'p [Vec<Placement>],
}

impl<'p> Placed<'p> {
    fn new(placements: &'p [Vec<Placement>]) -> Self {
        for (pipeline, placements) in placements.iter().enumerate() {
            for placement in placements {
                debug_assert!(
                    placement.get().is_none(),
                    "a loop scope's inner entries are unplaced while the scope does not run"
                );
                placement.set(Some(PipelineId(pipeline)));
            }
        }
        Self { placements }
    }
}

impl Drop for Placed<'_> {
    fn drop(&mut self) {
        for placement in self.placements.iter().flatten() {
            placement.set(None);
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::super::plan::{Execution, Planner, ScopeRuns};
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::commit_operator::store_frontier;
    use crate::interpreter::operator_conversion::OperatorMap;
    use crate::interpreter::tile_operators::TileProducer;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{Position, Tile};

    /// `total` summed over `[1, 2, 3]` and written to `out`: 6.
    const SUM: &str = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            total += x
        out << total
    "};

    /// [`SUM`] with the write guarded by `x > 1`: 5. The guard puts `Memo`s inside the cycle,
    /// between the drive's and the store's body.
    const GUARDED_SUM: &str = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            if x > 1:
                total += x
        out << total
    "};

    /// A program compiled with its sinks unpulled and no notification delivered, and the scope of
    /// its one store.
    struct Compiled {
        _runs: ScopeRuns,
        _ctx: GlobalContext,
        operators: OperatorMap,
        scope: StoreCell,
        dispatcher: Dispatcher,
        execution: Execution,
    }

    impl Compiled {
        fn of(source: &str) -> Self {
            let mut ctx = GlobalContext::default();
            let _sink = ctx.register_test_sink("out");
            let loaded = LoadedProgram::test(source);
            compile_program(&mut ctx, &loaded, Box::new(|| {}))
                .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
            let operators = ctx.take_operator_map();
            let stores: Vec<_> = operators
                .operators()
                .into_iter()
                .filter(|fan| fan.cached_tile().is_some())
                .collect();
            assert_eq!(stores.len(), 1, "one store");
            let mut planner = Planner::default();
            planner.store_pipeline(crate::interpreter::tile_operators::StoreRead {
                fan: stores[0].id(),
                store: stores[0].store().expect("the program subscribed its store"),
            });
            assert_eq!(planner.scopes.len(), 1, "an induction store runs in rounds");
            let mut runs = ScopeRuns::new();
            let scope = planner.build_scope(0, usize::MAX, &mut Vec::new(), &mut runs);
            induction(&scope).begin_run();
            let mut dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
            dispatcher.order(PipelineId(0));
            let execution = Execution::new(&[Some(scope.clone())], &mut dispatcher);
            Self {
                _runs: runs,
                _ctx: ctx,
                operators,
                scope,
                dispatcher,
                execution,
            }
        }

        fn tick(&self) -> Option<PipelineId> {
            let mut root = |_: PipelineId, _: &mut Call<'_>| {
                panic!("the test's pipelines all belong to its induction run");
            };
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                self.execution.reach(pipeline, &mut root, call);
            };
            match self.dispatcher.try_claim(None) {
                Next::Package(package) => {
                    let pipeline = package.pipeline;
                    self.execution
                        .consume(&self.dispatcher, &mut reach, package);
                    Some(pipeline)
                }
                Next::Finish { pipeline, consumed } => {
                    self.execution
                        .finish(&self.dispatcher, &mut reach, pipeline, consumed);
                    Some(pipeline)
                }
                Next::Wait(_) => {
                    assert!(
                        self.execution.resume(&self.dispatcher, &mut reach),
                        "a pending loop has body, settlement, or step work"
                    );
                    None
                }
                Next::Done => panic!("a test ticks only while work remains"),
                Next::Failed => panic!("the test run failed"),
            }
        }

        fn drain_request(&self) {
            for _ in 0..1000 {
                if self.dispatcher.outstanding(PipelineId(0)) == 0 {
                    return;
                }
                self.tick();
            }
            panic!("a finite loop completes its request");
        }

        fn consume(&self, guard: TileGuard) {
            self.dispatcher.notify(PipelineId(0), &guard);
            self.drain_request();
        }

        fn run_one_round(&self) {
            let step = induction(&self.scope).run().body.attached().step;
            for _ in 0..1000 {
                if self.tick() == Some(step) {
                    return;
                }
            }
            panic!("a queued round reaches its store step");
        }

        /// The store as a consuming breaker answers it.
        fn snapshot(&self) -> Tile {
            let mut store = induction(&self.scope);
            let guard = store.tiling().universal_guard();
            store.get(guard)
        }

        /// The value the store holds for its one variable.
        fn value(&self) -> Value {
            let state = self.operators.live_state();
            assert_eq!(state.len(), 1, "one variable: {state:?}");
            state.into_values().next().expect("one variable")
        }
    }

    /// A morsel of one position is one round, which decides the position; the round of the last
    /// position leaves the store terminal, holding the expected writes, and its body released.
    #[test]
    fn a_round_decides_its_position() {
        let compiled = Compiled::of(SUM);
        for position in [0, 1] {
            compiled.consume(keys_between(position, position));
            let snapshot = compiled.snapshot();
            assert_eq!(
                store_frontier(&snapshot),
                Some(Position::new(Value::UInt(position))),
                "the round of position {position} decides it"
            );
            assert!(!snapshot.is_terminal());
        }
        compiled.consume(keys_between(2, 2));
        assert!(compiled.snapshot().is_terminal());
        assert!(
            induction(&compiled.scope)
                .input_released(InputId::ONLY)
                .is_universal(),
            "a terminal body whose every decision is stepped is released whole"
        );
        assert_eq!(compiled.value(), Value::Int(6));
    }

    #[test]
    fn a_claimed_request_stays_in_flight_until_its_last_round() {
        let compiled = Compiled::of(SUM);
        compiled
            .dispatcher
            .notify(PipelineId(0), &keys_between(0, 1));
        compiled
            .dispatcher
            .notify(PipelineId(0), &keys_between(2, 2));
        compiled.run_one_round();
        assert_eq!(
            store_frontier(&compiled.snapshot()),
            Some(Position::new(Value::UInt(0)))
        );
        assert!(
            compiled.dispatcher.claim_of(PipelineId(0)).is_none(),
            "the second request waits until the first request's last step"
        );
        assert_eq!(compiled.dispatcher.outstanding(PipelineId(0)), 2);
        compiled.run_one_round();
        assert_eq!(
            store_frontier(&compiled.snapshot()),
            Some(Position::new(Value::UInt(1)))
        );
        assert_eq!(compiled.dispatcher.outstanding(PipelineId(0)), 1);
        compiled.drain_request();
        assert!(compiled.snapshot().is_terminal());
        assert_eq!(compiled.value(), Value::Int(6));
    }

    /// A loop scope's open request is its store pipeline's claimed package, in flight until the
    /// request's last step, so a drained boundary at that point fails its check.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "pipeline 0, a loop's store, holds a claimed package")]
    fn an_open_request_is_in_flight() {
        let compiled = Compiled::of(SUM);
        compiled
            .dispatcher
            .notify(PipelineId(0), &keys_between(0, 2));
        compiled.run_one_round();
        compiled
            .execution
            .assert_nothing_in_flight(&compiled.dispatcher);
    }

    /// A completed request leaves nothing in flight.
    #[test]
    #[cfg(debug_assertions)]
    fn a_completed_request_leaves_nothing_in_flight() {
        let compiled = Compiled::of(SUM);
        compiled.consume(keys_between(0, 2));
        compiled
            .execution
            .assert_nothing_in_flight(&compiled.dispatcher);
    }

    #[test]
    fn requests_resume_between_rounds_independently() {
        let sum = Compiled::of(SUM);
        let guarded = Compiled::of(GUARDED_SUM);
        for compiled in [&sum, &guarded] {
            let whole = induction(&compiled.scope)
                .input_tiling(InputId::ONLY)
                .universal_guard();
            compiled.dispatcher.notify(PipelineId(0), &whole);
        }
        for position in 0..3 {
            for compiled in [&sum, &guarded] {
                compiled.run_one_round();
                assert_eq!(
                    store_frontier(&compiled.snapshot()),
                    Some(Position::new(Value::UInt(position)))
                );
                if position < 2 {
                    assert_eq!(compiled.dispatcher.outstanding(PipelineId(0)), 1);
                    assert!(!compiled.snapshot().is_terminal());
                }
            }
        }
        sum.drain_request();
        guarded.drain_request();
        assert!(sum.snapshot().is_terminal());
        assert!(guarded.snapshot().is_terminal());
        assert_eq!(sum.value(), Value::Int(6));
        assert_eq!(guarded.value(), Value::Int(5));
    }

    #[test]
    #[should_panic(expected = "the body and store step complete before the next round")]
    fn a_request_cannot_queue_the_next_round_before_stepping() {
        let compiled = Compiled::of(SUM);
        let whole = induction(&compiled.scope)
            .input_tiling(InputId::ONLY)
            .universal_guard();
        compiled.dispatcher.notify(PipelineId(0), &whole);
        assert_eq!(compiled.tick(), Some(PipelineId(0)));
        let _ = induction(&compiled.scope).queue_package_round(&compiled.dispatcher);
    }

    /// A guarded loop's `Memo`s are inner pipelines, which each round queues the position for and
    /// runs before the store steps.
    #[test]
    fn a_guarded_loop_runs_its_memos_each_round() {
        let compiled = Compiled::of(GUARDED_SUM);
        let kinds = |kind: &str| {
            induction(&compiled.scope)
                .run()
                .body
                .planned
                .iter()
                .filter(|plan| plan.name.starts_with(kind))
                .count()
        };
        assert!(
            kinds("InductionDriver") == 1 && kinds("Memo") >= 1,
            "the drive and the guard's `Memo`s: {:?}",
            induction(&compiled.scope).run().body.planned
        );
        let whole = induction(&compiled.scope)
            .input_tiling(InputId::ONLY)
            .universal_guard();
        compiled.consume(whole);
        assert!(compiled.snapshot().is_terminal());
        assert_eq!(compiled.value(), Value::Int(5));
    }

    /// The store holds the positions its rounds complete before it is terminal, and everything
    /// after.
    #[test]
    fn the_store_holds_its_complete_positions_then_everything_once_terminal() {
        let compiled = Compiled::of(SUM);
        compiled.consume(keys_between(0, 0));
        let (held, complete) = {
            let store = induction(&compiled.scope);
            (store.final_guard(), store.complete())
        };
        assert!(
            !held.is_empty() && !held.is_universal() && held == complete,
            "{held:?}, deciding {complete:?}"
        );
        compiled.consume(keys_between(1, 2));
        assert!(induction(&compiled.scope).final_guard().is_universal());
    }

    /// A call on the drive [`with_drive`] finds.
    type OnDrive<'f> = dyn FnMut(&mut dyn TileProducer) + 'f;

    /// Call `f` with the drive in `scope`'s store's chain: the producer that answers a next
    /// position.
    fn with_drive(scope: &mut InductionStoreProducer, f: impl FnOnce(&mut dyn TileProducer)) {
        fn find(producer: &mut dyn TileProducer, f: &mut Option<&mut OnDrive<'_>>) {
            if producer.next_position().is_some() {
                (f.take().expect("one drive in the store's chain"))(producer);
                return;
            }
            producer.visit_input_producers_mut(&mut |_, input| find(input, f));
        }
        let mut f = Some(f);
        let mut call = |drive: &mut dyn TileProducer| (f.take().expect("called once"))(drive);
        let mut call: Option<&mut OnDrive<'_>> = Some(&mut call);
        scope.visit_input_producers_mut(&mut |_, input| find(input, &mut call));
        assert!(call.is_none(), "the store's chain holds a drive");
    }

    /// How many pulls `drive`'s source has taken.
    fn source_pulls(drive: &dyn TileProducer) -> u64 {
        let mut pulls = 0;
        drive.visit_input_producers(&mut |role, input| {
            if role == "source" {
                pulls = input.base().reads;
            }
        });
        pulls
    }

    /// A consume of the drive emits a position only where its package names it: not a position
    /// past the next, not for an empty package, and the next where the package names it. A
    /// consuming drive answers a pull from that consume and reads its source no more.
    #[test]
    fn a_drive_emits_only_the_position_its_package_names() {
        let compiled = Compiled::of(SUM);
        // As the scope's first consume does: the drive reads its source, then the store opens.
        induction(&compiled.scope).read_source();
        {
            let mut store = induction(&compiled.scope);
            let none = store.input_tiling(InputId::ONLY).empty_guard();
            store.consume_in_pipeline(InputId::ONLY, none);
        }
        let held = |drive: &mut dyn TileProducer| {
            drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker")
                .complete()
        };
        with_drive(&mut induction(&compiled.scope), |drive| {
            assert_eq!(drive.next_position(), Some(Some(vec![Value::UInt(0)])));
            let breaker = drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker");
            breaker.consume_in_pipeline(InputId::ONLY, keys_between(1, 1));
            breaker.consume_in_pipeline(
                InputId::ONLY,
                breaker.input_tiling(InputId::ONLY).empty_guard(),
            );
            assert!(
                !held(drive).covers_path(&[Value::UInt(0)]),
                "nothing emitted"
            );
            let breaker = drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker");
            breaker.consume_in_pipeline(InputId::ONLY, keys_between(0, 0));
            assert!(
                held(drive).covers_path(&[Value::UInt(0)]),
                "position 0 emitted"
            );
            assert_eq!(drive.next_position(), Some(Some(vec![Value::UInt(1)])));
            let before = source_pulls(drive);
            let whole = drive.tiling().universal_guard();
            let pulled = drive.get(whole);
            assert!(pulled.to_guard().covers_path(&[Value::UInt(0)]));
            assert_eq!(
                drive.next_position(),
                Some(Some(vec![Value::UInt(1)])),
                "a pull emits nothing"
            );
            assert_eq!(source_pulls(drive), before, "a pull reads no source");
        });
    }

    /// A scope whose store is not terminal at its finish panics.
    #[test]
    #[should_panic(expected = "finishes the run terminal")]
    fn a_scope_short_of_terminal_at_its_finish_panics() {
        let compiled = Compiled::of(SUM);
        compiled.consume(keys_between(0, 0));
        compiled.dispatcher.close(PipelineId(0));
        for _ in 0..1000 {
            compiled.tick();
        }
        panic!("a short-of-terminal store must reject its finish");
    }
}

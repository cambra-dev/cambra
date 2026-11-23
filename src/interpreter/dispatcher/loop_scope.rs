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
    /// The position round a request ended with undecided: the next request runs it again first,
    /// since the drive has emitted its position already ([`complete_round`](InductionStoreProducer::complete_round)).
    rerun: Option<TileGuard>,
}

/// What a round of a loop, or an attempt of a transaction writer, queues: computed while the scope
/// holds its store, and queued once it has released it ([`RoundWork::queue`]), so a worker that
/// claims a package of the round reads the store through its own pull rather than the snapshot
/// the store published after its last step (`src/interpreter/design-dispatcher.md`, "Bodies on
/// workers").
#[must_use = "a round's work is queued once the scope releases its store"]
#[derive(Default)]
pub(super) struct RoundWork(Vec<RoundItem>);

enum RoundItem {
    /// A source pipeline notified of the round's region ([`Dispatcher::notify`]).
    Notify(PipelineId, TileGuard),
    /// A pipeline given the round's package ([`RoundWork::queue_round`]).
    Queue(PipelineId, TileGuard),
    /// A nested loop's scope given the round's row, which it queues once its drive's source has
    /// delivered the row ([`Body::hold_row`]).
    Hold(StoreCell, TileGuard),
}

impl RoundWork {
    pub(super) fn notify(&mut self, pipeline: PipelineId, guard: &TileGuard) {
        self.0.push(RoundItem::Notify(pipeline, guard.clone()));
    }

    pub(super) fn queue_round(&mut self, pipeline: PipelineId, guard: &TileGuard) {
        self.0.push(RoundItem::Queue(pipeline, guard.clone()));
    }

    pub(super) fn hold_round(&mut self, scope: &StoreCell, guard: &TileGuard) {
        self.0.push(RoundItem::Hold(scope.clone(), guard.clone()));
    }

    /// Queue the work, in the order it was gathered. The scope's store is released by now.
    pub(super) fn queue(self, dispatcher: &Dispatcher) {
        for item in self.0 {
            match item {
                RoundItem::Notify(pipeline, guard) => dispatcher.notify(pipeline, &guard),
                RoundItem::Queue(pipeline, guard) => dispatcher.queue_for(pipeline, &guard),
                RoundItem::Hold(scope, guard) => {
                    let mut scope = induction(&scope);
                    let body = scope.body_mut();
                    body.hold_row(&guard);
                    body.queue_offered(dispatcher, true);
                }
            }
        }
    }
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
    /// Whether the scope's pipeline is finishing: from the scope's finish until the inner pipelines
    /// and the step have finished.
    finishing: bool,
    /// Whether a loop's scope has closed its step's arrivals
    /// ([`close_step_when_settled`](Self::close_step_when_settled)).
    step_closed: bool,
    /// The guard of the step's package for the open round or attempt, which the scope queues once
    /// the inner pipelines are quiescent ([`Body::queue_step_when_quiescent`]).
    pending_step: Option<TileGuard>,
    /// What the scope's input offered and the scope has not queued yet: the pushes of the drive's
    /// source, its live arrivals and its start ([`queue_offered`](Self::queue_offered)).
    offers: Offers,
    /// Whether the scope is a nested loop's, whose rows the loop around it gives it: what its
    /// drive's source offers then releases those rows ([`hold_row`](Self::hold_row)) rather than
    /// being queued itself.
    rows_from_outer: bool,
    /// The rows the loop around a nested loop gave it, waiting for its drive's source to deliver
    /// them.
    held: Option<TileGuard>,
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
            finishing: false,
            step_closed: false,
            pending_step: None,
            offers: Offers::default(),
            rows_from_outer: false,
            held: None,
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

    /// Place each inner pipeline's entries at its global id, except a source's. Whether this call
    /// activated the body: it does so once.
    pub(super) fn activate(&mut self, dispatcher: &Dispatcher) -> bool {
        if self.active {
            return false;
        }
        self.active = true;
        for (local, placements) in self.placements.iter().enumerate() {
            let pipeline = self.global(PipelineId(local));
            for placement in placements {
                placement.set((!dispatcher.is_source(pipeline)).then_some(pipeline));
                placement.set_scope(Some(self.offers.clone()));
            }
        }
        true
    }

    /// Hold back the pipelines that follow the inner pipelines and the step, once the body runs.
    pub(super) fn hold_followers(&self, dispatcher: &Dispatcher) {
        if !self.active {
            return;
        }
        dispatcher.hold_followers(self.with_step(), true);
    }

    /// Let the pipelines that follow the inner pipelines and the step run, where the body runs and
    /// the step's hold is still `read`, taken before the publication pass that decided the release:
    /// held, and held again by no claim since ([`Dispatcher::release_followers_if`]). Whether this
    /// call released them.
    pub(super) fn release_followers(&self, dispatcher: &Dispatcher, read: FollowersHold) -> bool {
        self.active && dispatcher.release_followers_if(self.with_step(), self.attached().step, read)
    }

    /// The step's follower hold, read before a publication pass, or `None` before the body is
    /// attached.
    pub(super) fn followers_hold(&self, dispatcher: &Dispatcher) -> Option<FollowersHold> {
        Some(dispatcher.followers_hold(self.attached.as_ref()?.step))
    }

    /// End the open round or attempt with a step package of `guard` once the inner pipelines are
    /// quiescent.
    pub(super) fn end_round_with(&mut self, guard: &TileGuard) {
        debug_assert!(
            self.pending_step.is_none(),
            "a scope runs one round or attempt at a time"
        );
        self.pending_step = Some(guard.clone());
    }

    /// Queue the step's package of the open round or attempt where every inner pipeline, and every
    /// pipeline one reads, has consumed every package queued for it: the round's work has run,
    /// pushes it brought included. Whether it queued the package.
    pub(super) fn queue_step_when_quiescent(&mut self, dispatcher: &Dispatcher) -> bool {
        // A body package's consume acknowledges the package and then holds the followers
        // (`Execution::consume`), both on the coordinator before this check runs, so the hold read
        // here is the one that acknowledgement set.
        if self.pending_step.is_none()
            || !dispatcher.quiescent(self.pipelines().into_iter().map(|pipeline| pipeline.0))
            || dispatcher.followers_hold(self.attached().step).0 & 1 == 1
            || self.members_hold_rows()
        {
            return false;
        }
        let guard = self.pending_step.take().expect("checked above");
        dispatcher.queue_for(self.attached().step, &guard);
        true
    }

    /// Begin the scope's finish.
    pub(super) fn begin_finish(&mut self) {
        debug_assert!(!self.finishing, "a scope finishes once");
        self.finishing = true;
    }

    /// Whether the scope's finish has begun and the body has not finished.
    pub(super) fn is_finishing(&self) -> bool {
        self.finishing
    }

    /// Close the inner sources, so the inner pipelines finish once they have read what is queued.
    pub(super) fn close_sources(&self, dispatcher: &Dispatcher) {
        for pipeline in self.pipelines() {
            if dispatcher.is_source(pipeline) {
                dispatcher.close(pipeline);
            }
        }
    }

    /// Close a loop's step once the scope is finishing, its last round's step is queued and every
    /// inner pipeline has finished. Whether it closed it.
    ///
    /// The step reads the inner pipelines, and closing on their finish alone would let it finish
    /// before the scope queues the last round's step: a worker finishes an inner pipeline while
    /// the coordinator still holds that step, which waits for the round to publish. So the step
    /// takes arrivals, and its scope closes them. A transaction writer's step closes once the
    /// finish's attempt has run (`WriterRun::close`).
    pub(super) fn close_step_when_settled(&mut self, dispatcher: &Dispatcher) -> bool {
        if !self.finishing
            || self.step_closed
            || self.pending_step.is_some()
            || !self
                .pipelines()
                .iter()
                .all(|pipeline| dispatcher.states[pipeline.0].phase.load() == Phase::Finished)
        {
            return false;
        }
        self.step_closed = true;
        dispatcher.close(self.attached().step);
        true
    }

    /// The scope's pipeline, once its finish has begun and the inner pipelines and the step have
    /// all finished.
    pub(super) fn take_finish(&mut self, dispatcher: &Dispatcher) -> Option<PipelineId> {
        if !self.finishing {
            return None;
        }
        let pipeline = self.attached.as_ref()?.pipeline;
        let finished = self
            .with_step()
            .all(|pipeline| dispatcher.states[pipeline.0].phase.load() == Phase::Finished);
        if !finished {
            return None;
        }
        self.finishing = false;
        Some(pipeline)
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

    /// Add `guard`, a region of the scope's input, to what is offered and not queued yet.
    pub(super) fn offer(&self, guard: &TileGuard) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        offered.region = Some(match offered.region.take() {
            Some(before) => before.union(guard),
            None => guard.clone(),
        });
    }

    /// Whether a nested loop among the inner pipelines holds a row the round gave it that its
    /// drive's source has delivered: the round has not run until that loop has queued and run it.
    /// A held row its source has not delivered waits for data from outside the round, so the
    /// round's step runs, leaves its position waiting for inputs, and the loop's publication of
    /// the row once the source delivers it brings the next request.
    fn members_hold_rows(&self) -> bool {
        self.members.iter().any(|member| match member {
            Member::Scope(child) => induction(child)
                .body_mut()
                .ready_rows()
                .is_some_and(|(ready, _)| !ready.is_empty()),
            Member::Chain(_) => false,
        })
    }

    /// For a nested loop, the rows it holds that its drive's source has delivered, and the rest:
    /// a row is ready where the source delivered it, and where what is left of it, closed over the
    /// scope's input, names no position, as a closing round gives a row's remainder past the
    /// positions its domain has. `None` where it holds no row or its source has offered nothing.
    fn ready_rows(&self) -> Option<(TileGuard, TileGuard)> {
        let input = self.driver_target().and_then(|target| {
            let target = target.read().unwrap_or_else(PoisonError::into_inner);
            target.as_ref().map(|(_, input)| input.clone())
        });
        let held = self.held.as_ref()?;
        let offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        let delivered = offered.region.as_ref()?;
        let rest = guard_minus(held, delivered);
        let rest = match input {
            Some(input) => rest.closed_over(&input),
            None => rest,
        };
        Some((guard_minus(held, &rest), rest))
    }

    /// Take the rows the loop around this nested loop gives it: they are queued once the drive's
    /// source has offered each whole ([`queue_offered`](Self::queue_offered)).
    pub(super) fn hold_row(&mut self, guard: &TileGuard) {
        self.rows_from_outer = true;
        self.held = Some(match self.held.take() {
            Some(before) => before.union(guard),
            None => guard.clone(),
        });
    }

    /// Mark this scope a nested loop's, whose rows come from the loop around it.
    pub(super) fn take_rows_from_outer(&mut self) {
        self.rows_from_outer = true;
    }

    /// Close the scope's pipeline once everything offered to it is queued.
    pub(super) fn close_offers(&self) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        offered.closing |= !offered.closed;
    }

    /// Queue what was offered on the scope's pipeline, and close the pipeline once asked, where
    /// `ready` says a request can run: a writer's attempt reads its store, which must be open.
    /// Whether it queued or closed anything.
    pub(super) fn queue_offered(&mut self, dispatcher: &Dispatcher, ready: bool) -> bool {
        let Some(pipeline) = self.attached.as_ref().map(|attached| attached.pipeline) else {
            return false;
        };
        // A nested loop queues each row given to it once its drive's source has delivered it.
        if self.rows_from_outer {
            let Some((ready_rows, rest)) = self.ready_rows() else {
                return false;
            };
            if ready_rows.is_empty() {
                return false;
            }
            // What the drive's source delivered stays delivered: a closing round gives the row
            // again, which reads it again.
            self.held = (!rest.is_empty()).then_some(rest);
            dispatcher.queue_for(pipeline, &ready_rows);
            return true;
        }
        // An offer comes from a push that also queues packages to the pipelines the drive pulls
        // its source through, which a worker may still be consuming: a request begun before
        // they have consumed them finds no position and closes over positions the drive will
        // emit. So the offer waits until every pipeline the scope's pipeline reads is quiescent.
        if !dispatcher.quiescent(dispatcher.infos[pipeline.0].reads.iter().copied()) {
            return false;
        }
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        // The pipeline stays open while a request is queued or running, which may leave positions
        // waiting for inputs, and while any wait: what an input brings queues the request that
        // runs them.
        let closing = offered.closing
            && offered.region.is_none()
            && dispatcher.outstanding(pipeline) == 0
            && offered.waiting.is_none();
        if !ready || (offered.region.is_none() && !closing) {
            return false;
        }
        let region = offered.region.take();
        offered.closing &= !closing;
        offered.closed |= closing;
        drop(offered);
        if let Some(region) = region {
            dispatcher.queue_for(pipeline, &region);
        }
        if closing {
            dispatcher.close(pipeline);
        }
        true
    }

    /// Whether anything offered is not queued yet.
    pub(super) fn has_offers(&self) -> bool {
        let offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        offered.region.is_some() || offered.closing
    }

    /// Clear every inner pipeline's entries.
    pub(super) fn unplace(&mut self) {
        for placement in self.placements.iter().flatten() {
            placement.set(None);
            placement.set_scope(None);
        }
        self.active = false;
    }

    /// Queue with `work` what pushes from outside the body brought its pipelines since the last
    /// round or attempt began (`Offered::grown`), so each reads what grew.
    pub(super) fn queue_grown(&self, work: &mut RoundWork) {
        let grown = std::mem::take(
            &mut self
                .offers
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .grown,
        );
        for (pipeline, guard) in grown {
            work.queue_round(pipeline, &guard);
        }
    }

    /// The positions of the scope's input a request left undecided, waiting for inputs: the next
    /// request runs them, and the scope's pipeline stays open while any wait.
    pub(super) fn waiting(&self) -> Option<TileGuard> {
        self.offers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .waiting
            .clone()
    }

    /// Set the positions waiting for inputs ([`waiting`](Self::waiting)): a push that reaches one
    /// of the scope's entries and no pipeline there takes offers them again
    /// (`Entry::wake`), so `entry`, the placement of an entry the body does not place, is marked
    /// the scope's too. A push that woke the scope while nothing waited ([`Offered::woken`])
    /// arrived before the positions waited, so it offers them once.
    pub(super) fn set_waiting(&self, waiting: Option<TileGuard>, entry: Option<&Placement>) {
        if let Some(entry) = entry {
            entry.set_scope(Some(self.offers.clone()));
        }
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(waiting) = &waiting
            && std::mem::take(&mut offered.woken)
        {
            offered.region = Some(match offered.region.take() {
                Some(before) => before.union(waiting),
                None => waiting.clone(),
            });
        }
        offered.waiting = waiting;
    }
}

/// A dropped body leaves no entry placed and no completion recorded at a pipeline of its run.
impl Drop for Body {
    fn drop(&mut self) {
        self.unplace();
        if let Some(target) = self.driver_target() {
            *target.write().unwrap_or_else(PoisonError::into_inner) = None;
        }
    }
}

struct Request {
    read: bool,
    emitted: bool,
    closing: bool,
    /// The last round's position is one the store could not decide: what the body read there is
    /// not final yet. The request ends with that position unreleased, and a push from a pipeline
    /// the scope reads brings the next request, which runs it again.
    undecided: bool,
    /// The positions the request runs: its package's, and those an earlier request left waiting
    /// for inputs.
    covers: TileGuard,
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
            rerun: None,
        }
    }
}

pub(super) struct InductionBorrow<'a>(crate::interpreter::tile_operators::StoreBorrow<'a>);

impl std::ops::Deref for InductionBorrow<'_> {
    type Target = InductionStoreProducer;
    fn deref(&self) -> &Self::Target {
        self.0
            .as_induction_store()
            .expect("a loop store has concrete induction state")
    }
}

impl std::ops::DerefMut for InductionBorrow<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
            .as_induction_store_mut()
            .expect("a loop store has concrete induction state")
    }
}

pub(super) fn induction(store: &StoreCell) -> InductionBorrow<'_> {
    InductionBorrow(store.write())
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

    pub(super) fn release_followers(
        &mut self,
        dispatcher: &Dispatcher,
        read: FollowersHold,
    ) -> bool {
        // A finish activates the body and holds its followers with no request open, and the step
        // must run before the scope finishes, so a finishing body releases them as a request does.
        let run = self.run();
        (run.request.is_some() || run.body.is_finishing())
            && run.body.release_followers(dispatcher, read)
    }

    /// The step's follower hold, read before a publication pass, or `None` before the scope is
    /// attached.
    pub(super) fn followers_hold(&self, dispatcher: &Dispatcher) -> Option<FollowersHold> {
        self.run().body.followers_hold(dispatcher)
    }

    /// Open the request `package`: the request it completes at once, and the first round's work.
    pub(super) fn begin_shared(
        &mut self,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) -> (Option<WorkPackage>, RoundWork) {
        self.activate(dispatcher);
        self.begin_package(package);
        self.queue_package_round(dispatcher)
    }

    pub(super) fn begin_shared_finish(&mut self, dispatcher: &Dispatcher) {
        assert!(
            !self.has_package(),
            "a scope finishes after completing its requests"
        );
        self.activate(dispatcher);
        let body = &mut self.run_mut().body;
        body.begin_finish();
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
        if let Some(entry) = self.base().placement.clone() {
            entry.set_scope(None);
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
    /// The scope's pipeline whose chain holds the drive (`TileProducer::next_position`).
    fn drive(&self) -> PipelineId {
        self.run().body.driver
    }

    /// Have the entry in front of the drive's source offer the scope a push of the source's keys
    /// as positions of the store's input: the drive reads its source by pull, so no push of the
    /// source reaches the scope's entry otherwise, and the scope would wait for each round until
    /// the source is whole.
    pub(super) fn decide_through_drive(&mut self) {
        let input = self.input_tiling(InputId::ONLY);
        let target = self
            .drive_target()
            .expect("a loop's drive offers its source's pushes");
        let offers = self.run().body.offers.clone();
        *target.write().unwrap_or_else(PoisonError::into_inner) = Some((offers, input));
    }

    /// Undo [`decide_through_drive`](Self::decide_through_drive): the drive's source's pushes
    /// offer the scope nothing.
    pub(super) fn forget_through_drive(&mut self) {
        if let Some(target) = self.drive_target() {
            *target.write().unwrap_or_else(PoisonError::into_inner) = None;
        }
    }

    /// Whether the drive's source's pushes offer the scope their keys.
    pub(super) fn decides_through_drive(&mut self) -> bool {
        self.drive_target().is_some_and(|target| {
            target
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_some()
        })
    }

    /// Where the drive's source's pushes are offered ([`CompletionTarget`]).
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

    /// The inner pipelines a closing round gives its row: each one no other inner pipeline feeds,
    /// and each nested loop. A pipeline that reads another inner pipeline takes the row from that
    /// pipeline's push, once the pipeline it reads has finished the row. A nested loop holds the
    /// row until its drive's source offers it, which that push does.
    fn closing_readers(&self, dispatcher: &Dispatcher) -> Vec<PipelineId> {
        let count = self.run().body.members.len();
        let inner: Vec<usize> = (0..count)
            .map(|local| self.pipeline(PipelineId(local)).0)
            .collect();
        (0..count)
            .map(PipelineId)
            .filter(|&pipeline| {
                matches!(self.run().body.members[pipeline.0], Member::Scope(_))
                    || !dispatcher.infos[self.pipeline(pipeline).0]
                        .reads
                        .iter()
                        .any(|read| inner.contains(read))
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
        crate::interpreter::notifications::notify_shared(&consumer, &region, &mut landing);
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
        let covers = match self.run().body.waiting() {
            Some(waiting) => package.guard.union(&waiting),
            None => package.guard.clone(),
        };
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
        // The store takes first what the body has decided since positions began to wait, so the
        // drive emits the next position past the ones now decided.
        if let Some(waiting) = self.run().body.waiting() {
            self.placed(|scope| scope.step_round(&waiting));
        }
        self.run_mut().request = Some(Request {
            read: rows,
            emitted: false,
            closing: false,
            undecided: false,
            covers,
            round: None,
            package,
        });
    }

    /// Keep `waiting`, the positions a request leaves undecided, waiting for inputs: a push that
    /// reaches the scope's body or the entry in front of the store's body once an input grows
    /// offers them again, and the request that offer brings runs them ([`Body::queue_offered`]).
    fn wait_for_inputs(&mut self, waiting: TileGuard) {
        let entry = self.base().placement.clone();
        self.run().body.set_waiting(Some(waiting), entry.as_ref());
    }

    /// End a request over `covers`: the positions of it the store has not decided wait for inputs
    /// while the drive's source can deliver more, and none wait once all are decided or the source
    /// is done. A request that ends before the source delivers a position leaves `covers`
    /// waiting, so the push that delivers one wakes the scope (`Entry::wake`) and offers them
    /// again; the drive's source entry queues nothing itself.
    fn keep_undecided(&mut self, covers: &TileGuard) {
        let undecided = guard_minus(covers, &self.input_released(InputId::ONLY));
        match undecided.is_empty() || self.terminal() {
            true => self.run().body.set_waiting(None, None),
            false => self.wait_for_inputs(undecided),
        }
    }

    pub(super) fn has_package(&self) -> bool {
        self.run().request.is_some()
    }

    /// The next round of the open request: the request, where it has no round left, and the
    /// round's work.
    pub(super) fn queue_package_round(
        &mut self,
        dispatcher: &Dispatcher,
    ) -> (Option<WorkPackage>, RoundWork) {
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
        if request.undecided {
            let waiting = guard_minus(&request.covers, &self.input_released(InputId::ONLY));
            self.wait_for_inputs(waiting);
            return (Some(request.package), RoundWork::default());
        }
        if request.closing {
            self.keep_undecided(&request.covers);
            return (Some(request.package), RoundWork::default());
        }
        // A round an earlier request left undecided runs again first: what it read has grown.
        if let Some(guard) = self.run_mut().rerun.take()
            && !guard_minus(&guard, &self.input_released(InputId::ONLY)).is_empty()
        {
            let starts = self.run().starts.clone();
            let mut work = self.placed(|store| store.round_on(dispatcher, &guard, &starts));
            self.run().body.queue_grown(&mut work);
            request.emitted = true;
            request.round = Some(guard);
            self.run_mut().request = Some(request);
            return (None, work);
        }
        loop {
            if !self.terminal()
                && let Some(position) = self.next_round_position()
                && request.covers.covers_path(&position)
            {
                let guard = Projection::of_path(&position).guard(&self.input_tiling(InputId::ONLY));
                let starts = self.run().starts.clone();
                let mut work = self.placed(|store| store.round_on(dispatcher, &guard, &starts));
                self.run().body.queue_grown(&mut work);
                request.emitted = true;
                request.round = Some(guard);
                self.run_mut().request = Some(request);
                return (None, work);
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
                && !guard_minus(&request.covers, &self.input_released(InputId::ONLY)).is_empty());
        if !closing {
            self.keep_undecided(&request.covers);
            return (Some(request.package), RoundWork::default());
        }
        let mut work = self.placed(|scope| {
            // A row's last position does not state the row's end. Render the drive once more
            // at no position so the closing round can release the row whole, including an
            // empty row. A flat request closes only positions the source emitted none of.
            if rows {
                scope.read_source();
            }
            scope.round_on(
                dispatcher,
                &request.covers,
                &scope.closing_readers(dispatcher),
            )
        });
        // What grew since the last round is read in this one too: a closing round runs its rows'
        // readers, a nested loop's among them, and a reader that has not read what grew would
        // offer the nested loop none of the positions it brings.
        self.run().body.queue_grown(&mut work);
        request.closing = true;
        request.round = Some(request.covers.clone());
        self.run_mut().request = Some(request);
        (None, work)
    }

    /// Step the queued round after its body and held pushes settle.
    pub(super) fn complete_round(&mut self) {
        let (guard, closing) = self
            .run_mut()
            .request
            .as_mut()
            .and_then(|request| Some((request.round.take()?, request.closing)))
            .expect("a loop steps one queued round");
        self.placed(|scope| scope.step_round(&guard));
        // A position round the store did not decide stays unreleased: running it again before
        // what the body read changes would decide nothing again.
        if !closing && !guard_minus(&guard, &self.input_released(InputId::ONLY)).is_empty() {
            self.run_mut()
                .request
                .as_mut()
                .expect("a loop steps one queued round")
                .undecided = true;
            self.run_mut().rerun = Some(guard);
        }
    }

    /// The body's work for one position or closing row, before the store steps it.
    fn round_on(
        &mut self,
        dispatcher: &Dispatcher,
        guard: &TileGuard,
        starts: &[PipelineId],
    ) -> RoundWork {
        let mut work = RoundWork::default();
        self.read_cycle_again();
        let (sources, readers): (Vec<PipelineId>, Vec<PipelineId>) = starts
            .iter()
            .partition(|&&start| dispatcher.is_source(self.pipeline(start)));
        for source in sources {
            work.notify(self.pipeline(source), guard);
        }
        for (reader, row) in self.row_for(guard, &readers) {
            // A reader whose input has released the whole row consumed it final, its end
            // included, and reads it no more: it is no longer there to read. A row released in
            // part is read again whole, for its end.
            let mut released = false;
            self.reach_local(reader, &mut |breaker, input| {
                released = guard_minus(&row, &breaker.input_released(input)).is_empty()
            });
            if released {
                continue;
            }
            // A nested loop whose pipeline reads another holds the row until its drive's source
            // has delivered it; any other reader takes it at once.
            match &self.run().body.members[reader.0] {
                Member::Scope(child)
                    if !dispatcher.infos[self.pipeline(reader).0].reads.is_empty() =>
                {
                    work.hold_round(child, &row)
                }
                _ => work.queue_round(self.pipeline(reader), &row),
            }
        }
        if self.run().body.is_attached() {
            self.run_mut().body.end_round_with(guard);
        }
        work
    }

    /// Step the store after the round's body and held pushes have settled. The store steps the
    /// positions of the round its input has decided; positions not decided yet stay unreleased,
    /// and the scope keeps them waiting for inputs ([`Body::waiting`]).
    fn step_round(&mut self, guard: &TileGuard) {
        self.consume_impl(InputId::ONLY, guard.clone());
    }
}

/// Call `call` with `member`'s breaker, the inner pipeline `pipeline`'s: in `store`'s chain, or
/// a nested loop's scope.
pub(super) fn reach_member(member: &Member, call: &mut Call<'_>) {
    match member {
        Member::Scope(store) => call(&mut *induction(store), InputId::ONLY),
        Member::Chain(handle) => call(
            &mut *handle.write().unwrap_or_else(PoisonError::into_inner),
            InputId::ONLY,
        ),
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
                Next::Finish { pipeline } => {
                    self.execution
                        .finish(&self.dispatcher, &mut reach, pipeline);
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
            let store = induction(&self.scope);
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
                pulls = input.base().reads.load(Ordering::Relaxed);
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

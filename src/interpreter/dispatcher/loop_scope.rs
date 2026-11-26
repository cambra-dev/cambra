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
}

/// One handler at a time chooses and settles this loop's rounds.
#[derive(Default)]
pub(super) struct LoopSchedule {
    phase: LoopPhase,
    round: Option<ActiveRound>,
    /// The position round a request ended with undecided: the next request runs it again first,
    /// since the drive has emitted its position already ([`complete_round`](InductionStoreProducer::complete_round)).
    rerun: Option<TileGuard>,
}

#[derive(Default, PartialEq, Eq)]
enum LoopPhase {
    #[default]
    New,
    Running,
    Draining,
    Finished,
}

impl LoopSchedule {
    pub(super) fn begin(
        &mut self,
        store: &StoreCell,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) {
        let (done, work) = induction(store).begin_shared(self, dispatcher, package);
        work.queue(dispatcher);
        induction(store).hold_followers(dispatcher);
        Self::complete(store, dispatcher, done);
    }

    pub(super) fn step(
        &mut self,
        store: &StoreCell,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) {
        let (request, outcome) = {
            let mut store = induction(store);
            #[cfg(test)]
            if let Some(probe) = &dispatcher.scope_step_probe {
                probe(package.pipeline);
            }
            store.complete_round(self)
        };
        dispatcher.acknowledge(package);
        let (done, work) = induction(store).queue_package_round(self, dispatcher, request, outcome);
        work.queue(dispatcher);
        induction(store).hold_followers(dispatcher);
        Self::complete(store, dispatcher, done);
    }

    fn complete(store: &StoreCell, dispatcher: &Dispatcher, done: Option<WorkPackage>) {
        scope::complete_request(dispatcher, done, |pushes| {
            let store = induction(store);
            if store.pushes_while_consuming() {
                pushes.push_final(&*store);
            }
        });
    }

    pub(super) fn has_request(&self) -> bool {
        self.round.is_some()
    }

    pub(super) fn step_guard(&self) -> Option<&TileGuard> {
        let active = self.round.as_ref()?;
        Some(match &active.kind {
            Round::Position(guard) => guard,
            Round::Closing => &active.request.covers,
        })
    }

    /// A child may retry between this loop's requests. Its follower hold must still settle.
    pub(super) fn publishing(&self) -> bool {
        matches!(self.phase, LoopPhase::Running | LoopPhase::Draining)
    }

    pub(super) fn take_finish(
        &mut self,
        body: &Body,
        dispatcher: &Dispatcher,
    ) -> Option<PipelineId> {
        if self.phase != LoopPhase::Draining {
            return None;
        }
        let pipeline = body.finished_pipeline(dispatcher)?;
        self.phase = LoopPhase::Finished;
        Some(pipeline)
    }
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
                // After the run's claims stop a notify queues nothing; the round ends with the run.
                RoundItem::Notify(pipeline, guard) => {
                    dispatcher.notify(pipeline, &guard);
                }
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

/// What a scope's input has offered it and the scope has not queued yet: a scope queues a request
/// only where it can run ([`Body::queue_offered`](loop_scope::Body::queue_offered)), and holds
/// the rest here.
#[derive(Default)]
pub struct Offered {
    intake: ScopeInput,
    close: IntakeClose,
    /// Per inner pipeline, what pushes from outside the body brought it since the last round or
    /// attempt began ([`Entry::wake`]): the next round or attempt queues it there, so the pipeline
    /// reads what grew.
    pub grown: Vec<(PipelineId, TileGuard)>,
    /// Positions the next request must revisit. Fresh input stays in the intake.
    retry: Option<Retry>,
    /// A wake that the next decision to park must observe.
    woken: bool,
}

/// Ordinary requests consume each offered region. A parent-fed loop retains delivery evidence
/// because the parent can give it the same row again in a closing round.
enum ScopeInput {
    Ordinary(Option<TileGuard>),
    Parent(Box<ParentRows>),
}

impl Default for ScopeInput {
    fn default() -> Self {
        Self::Ordinary(None)
    }
}

struct ParentRows {
    input: Tiling,
    held: Option<TileGuard>,
    delivered: Option<TileGuard>,
}

impl ParentRows {
    fn ready(&self) -> Option<(TileGuard, TileGuard)> {
        let held = self.held.as_ref()?;
        let rest = guard_minus(held, self.delivered.as_ref()?).closed_over(&self.input);
        Some((guard_minus(held, &rest), rest))
    }
}

#[derive(Default, PartialEq, Eq)]
enum IntakeClose {
    #[default]
    Open,
    AfterReads,
    Requested,
    Closed,
}

struct Retry {
    guard: TileGuard,
    phase: RetryPhase,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RetryPhase {
    /// Await input, or an ordinary request that can revisit the positions.
    Parked,
    /// A wake made the positions eligible for admission.
    Ready,
    /// A package has been queued to cover these positions.
    Queued,
}

impl Offered {
    pub(super) fn has_work(&self) -> bool {
        matches!(self.intake, ScopeInput::Ordinary(Some(_)))
            || self
                .retry
                .as_ref()
                .is_some_and(|retry| retry.phase == RetryPhase::Ready)
            || self.close == IntakeClose::Requested
    }

    pub(super) fn offer(&mut self, guard: TileGuard) {
        let region = match &mut self.intake {
            ScopeInput::Ordinary(pending) => pending,
            ScopeInput::Parent(rows) => &mut rows.delivered,
        };
        *region = Some(match region.take() {
            Some(before) => before.union(&guard),
            None => guard,
        });
    }

    pub(super) fn wake(&mut self) {
        if let Some(retry) = &mut self.retry
            && retry.phase == RetryPhase::Parked
        {
            retry.phase = RetryPhase::Ready;
        } else {
            self.woken = true;
        }
    }

    fn ready_retry(&mut self) -> Option<&mut Retry> {
        self.retry
            .as_mut()
            .filter(|retry| retry.phase == RetryPhase::Ready)
    }
}

/// A scope's [`Offered`], shared with the entry in front of its drive's source.
// shared-state-ok: the scope and the entry in front of its drive's source both hold it; what
// crosses it is a guard of the scope's input, never a tile.
pub type Offers = Arc<Mutex<Offered>>;

/// A scope's inner pipelines: a loop's body ([`InductionRun`]), or a transaction writer's
/// ([`WriterRun`](super::transaction_scope::WriterRun)). Planning builds them as a graph of their
/// own, which execution appends to the run's shared dispatcher between the scope's own pipeline
/// and its step (`Execution::attach_body` in `plan.rs`).
pub(super) struct Body {
    layout: BodyLayout,
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
    /// What the scope's input offered and the scope has not queued yet: the pushes of the drive's
    /// source, its live arrivals and its start ([`queue_offered`](Self::queue_offered)).
    pub(super) offers: Offers,
}

enum BodyLayout {
    Planned(Box<Dispatcher>),
    /// The dispatcher has taken the local graph and is attaching its nested scopes and step.
    Attaching,
    Attached(Attached),
}

/// Where a body sits in the run's shared dispatcher.
pub(super) struct Attached {
    /// The entries are placed at their global pipeline IDs.
    active: bool,
    /// The scope's own pipeline in the dispatcher around it, whose claims are its requests.
    pub(super) pipeline: PipelineId,
    /// The global id of the first inner pipeline; the others follow it in local order.
    base: usize,
    /// The pipeline that follows every inner one, whose claim ends a round or an attempt.
    pub(super) step: PipelineId,
    /// The follower hold of the inner pipelines and the step.
    pub(super) hold: HoldGroup,
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
            layout: BodyLayout::Planned(Box::new(graph)),
            members,
            placements,
            planned,
            driver,
            offers: Offers::default(),
        }
    }

    /// The planned graph, for execution to append to the run's dispatcher.
    pub(super) fn take_graph(&mut self) -> Dispatcher {
        let BodyLayout::Planned(graph) = std::mem::replace(&mut self.layout, BodyLayout::Attaching)
        else {
            panic!("a body's graph is appended once")
        };
        *graph
    }

    /// Record where execution appended the graph: after the scope's pipeline `pipeline`, from
    /// global id `base`, with the step `step`.
    pub(super) fn attach(
        &mut self,
        pipeline: PipelineId,
        base: usize,
        step: PipelineId,
        hold: HoldGroup,
    ) {
        debug_assert!(
            matches!(self.layout, BodyLayout::Attaching),
            "a body's graph is taken, then attached, once"
        );
        self.layout = BodyLayout::Attached(Attached {
            active: false,
            pipeline,
            base,
            step,
            hold,
        });
    }

    /// Where the body sits in the run's dispatcher.
    ///
    /// # Panics
    ///
    /// Before [`attach`](Self::attach): a body is reached through the handlers attaching installs.
    pub(super) fn attached(&self) -> &Attached {
        self.attachment()
            .expect("a body is reached once it is attached")
    }

    fn attachment(&self) -> Option<&Attached> {
        match &self.layout {
            BodyLayout::Attached(attached) => Some(attached),
            _ => None,
        }
    }

    pub(super) fn is_active(&self) -> bool {
        self.attachment().is_some_and(|attached| attached.active)
    }

    /// The global id of an attached body's inner pipeline.
    pub(super) fn global(&self, local: PipelineId) -> PipelineId {
        PipelineId(self.attached().base + local.0)
    }

    /// The global ids of the inner pipelines, none before the body is attached.
    pub(super) fn pipelines(&self) -> Vec<PipelineId> {
        match self.attachment() {
            Some(attached) => (attached.base..attached.base + self.members.len())
                .map(PipelineId)
                .collect(),
            None => Vec::new(),
        }
    }

    /// Place each inner pipeline's entries at its global id, except a source's. Whether this call
    /// activated the body: it does so once.
    pub(super) fn activate(&mut self, dispatcher: &Dispatcher) -> bool {
        let BodyLayout::Attached(attached) = &mut self.layout else {
            panic!("only an attached body activates")
        };
        if attached.active {
            return false;
        }
        attached.active = true;
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
        if !self.is_active() {
            return;
        }
        dispatcher.hold_followers(self.attached().hold);
    }

    /// A step reads the active round's guard. Its outstanding dispatcher claim prevents
    /// another admission until the handler settles the round and acknowledges the claim.
    pub(super) fn queue_step(&self, dispatcher: &Dispatcher, guard: &TileGuard) -> bool {
        let step = self.attached().step;
        if dispatcher.outstanding(step) != 0
            || !dispatcher.quiescent(self.pipelines().into_iter().map(|id| id.0))
            || dispatcher.followers_hold(self.attached().hold).0 & 1 == 1
            || self.children_have_work(dispatcher)
        {
            return false;
        }
        dispatcher.queue_for(step, guard);
        true
    }

    /// Close the inner sources, so the inner pipelines finish once they have read what is queued.
    pub(super) fn close_sources(&self, dispatcher: &Dispatcher) {
        for pipeline in self.pipelines() {
            if dispatcher.is_source(pipeline) {
                dispatcher.close(pipeline);
            }
        }
    }

    /// The scope pipeline once all its inner pipelines and its step have finished.
    pub(super) fn finished_pipeline(&self, dispatcher: &Dispatcher) -> Option<PipelineId> {
        let attached = self.attachment()?;
        (dispatcher.states[attached.step.0].phase.load() == Phase::Finished)
            .then_some(attached.pipeline)
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
        offered.offer(guard.clone());
    }

    /// An enclosing round waits for a child's delivered rows and woken retries to run.
    /// A held row still waiting for external input can span several rounds.
    fn children_have_work(&self, dispatcher: &Dispatcher) -> bool {
        self.members.iter().any(|member| match member {
            Member::Scope(child) => match child.try_write() {
                Ok(mut child) => {
                    let body = child
                        .as_induction_store_mut()
                        .expect("a nested loop")
                        .body_mut();
                    // Admission moves a held row into the request queue under this store.
                    // It may have moved since the enclosing body's quiescence check.
                    dispatcher.outstanding(body.attached().pipeline) != 0
                        || body.has_ready_row_or_retry()
                }
                Err(()) => true,
            },
            Member::Chain(_) => false,
        })
    }

    fn has_ready_row_or_retry(&self) -> bool {
        let offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        matches!(&offered.intake, ScopeInput::Parent(rows) if rows.ready().is_some_and(|(ready, _)| !ready.is_empty()))
            || offered
                .retry
                .as_ref()
                .is_some_and(|r| r.phase == RetryPhase::Ready)
    }

    /// Keep a parent row until the drive's source has delivered it.
    pub(super) fn hold_row(&mut self, guard: &TileGuard) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        let ScopeInput::Parent(rows) = &mut offered.intake else {
            unreachable!("only a nested scope accepts a parent row")
        };
        rows.held = Some(match rows.held.take() {
            Some(before) => before.union(guard),
            None => guard.clone(),
        });
    }

    pub(super) fn take_rows_from_outer(&mut self, input: Tiling) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        let ScopeInput::Ordinary(delivered) = &mut offered.intake else {
            unreachable!("a nested scope is attached once")
        };
        offered.intake = ScopeInput::Parent(Box::new(ParentRows {
            input,
            held: None,
            delivered: delivered.take(),
        }));
    }

    pub(super) fn close_after_reads(&self) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        if offered.close == IntakeClose::Open {
            offered.close = IntakeClose::AfterReads;
        }
    }

    /// Each read counts down after delivering its final output. A missed admission
    /// can observe the same last count on any later poll of this scope.
    fn intake(&self, dispatcher: &Dispatcher) -> std::sync::MutexGuard<'_, Offered> {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        if offered.close == IntakeClose::AfterReads
            && dispatcher.only_arrivals_remain(self.attached().pipeline)
        {
            offered.close = IntakeClose::Requested;
        }
        offered
    }

    /// Close the scope's pipeline once everything offered to it is queued.
    pub(super) fn close_offers(&self) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        if matches!(offered.close, IntakeClose::Open | IntakeClose::AfterReads) {
            offered.close = IntakeClose::Requested;
        }
    }

    /// Queue what was offered on the scope's pipeline, and close the pipeline once asked, where
    /// `ready` says a request can run: a writer's attempt reads its store, which must be open.
    /// Whether it queued or closed anything.
    pub(super) fn queue_offered(&mut self, dispatcher: &Dispatcher, ready: bool) -> bool {
        let Some(pipeline) = self.attachment().map(|attached| attached.pipeline) else {
            return false;
        };
        // An offer comes from a push that also queues packages to the pipelines the drive pulls
        // its source through, which a worker may still be consuming: a request begun before
        // they have consumed them finds no position and closes over positions the drive will
        // emit. So the offer waits until every pipeline the scope's pipeline reads is quiescent.
        let reads_ready = dispatcher.quiescent(dispatcher.infos[pipeline.0].reads.iter().copied());
        let mut offered = self.intake(dispatcher);
        let mut region = match &mut offered.intake {
            ScopeInput::Parent(rows) => rows.ready().and_then(|(ready, rest)| {
                if ready.is_empty() {
                    return None;
                }
                rows.held = (!rest.is_empty()).then_some(rest);
                Some(ready)
            }),
            ScopeInput::Ordinary(pending) if ready && reads_ready => pending.take(),
            ScopeInput::Ordinary(_) => return false,
        };
        // The pipeline stays open while a request is queued or running, which may leave positions
        // waiting for inputs, and while any wait: what an input brings queues the request that
        // runs them.
        let idle = dispatcher.outstanding(pipeline) == 0;
        let closing = matches!(offered.intake, ScopeInput::Ordinary(_))
            && offered.close == IntakeClose::Requested
            && idle
            && region.is_none()
            && offered.retry.is_none();
        // An ordinary request already queued on this ordered pipeline takes the retry when it
        // begins. Enqueueing a separate package behind it would revisit the same positions twice.
        if idle && let Some(retry) = offered.ready_retry() {
            region = Some(match region {
                Some(fresh) => fresh.union(&retry.guard),
                None => retry.guard.clone(),
            });
            retry.phase = RetryPhase::Queued;
        }
        if region.is_none() && !closing {
            return false;
        }
        if closing {
            offered.close = IntakeClose::Closed;
        }
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
    pub(super) fn has_offers(&self, dispatcher: &Dispatcher) -> bool {
        self.intake(dispatcher).has_work()
    }

    /// Clear every inner pipeline's entries.
    pub(super) fn unplace(&mut self) {
        for placement in self.placements.iter().flatten() {
            placement.set(None);
            placement.set_scope(None);
        }
        if let BodyLayout::Attached(attached) = &mut self.layout {
            attached.active = false;
        }
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

    /// The positions that waited for inputs when a request begins, which it runs
    /// in addition to the fresh positions named by its package.
    pub(super) fn take_waited(&self) -> Option<TileGuard> {
        self.offers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .retry
            .take()
            .map(|retry| retry.guard)
    }

    /// A peer changed the transaction store. Retry any parked positions. An attempt already
    /// in progress checks the store epoch when it settles.
    pub(super) fn offer_waiting(&self) {
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(retry) = &mut offered.retry
            && retry.phase == RetryPhase::Parked
        {
            retry.phase = RetryPhase::Ready;
        }
    }

    /// Set the positions waiting for inputs (`Offered::retry`): the first push that reaches one
    /// of the scope's entries and no pipeline there takes them and offers them again
    /// (`Entry::wake`), so `entry`, the placement of an entry the body does not place, is marked
    /// the scope's too. A push that woke the scope while nothing waited ([`Offered::woken`]) may
    /// have grown an input after the request read it, so the positions are offered once here.
    pub(super) fn set_waiting(&self, waiting: Option<TileGuard>, entry: Option<&Placement>) {
        if let Some(entry) = entry {
            entry.set_scope(Some(self.offers.clone()));
        }
        let mut offered = self.offers.lock().unwrap_or_else(PoisonError::into_inner);
        offered.retry = waiting.map(|guard| Retry {
            guard,
            phase: if std::mem::take(&mut offered.woken) {
                RetryPhase::Ready
            } else {
                RetryPhase::Parked
            },
        });
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

pub(super) struct Request {
    /// Whether the request has read the drive's source for newly delivered positions.
    read: bool,
    /// Whether the request has run a position round.
    emitted: bool,
    /// The positions the request runs: its package's, and those an earlier request left waiting
    /// for inputs.
    covers: TileGuard,
    /// Whether positions waited for inputs when the request began ([`Body::take_waited`]).
    waited: bool,
    package: WorkPackage,
}

/// A round whose body is running or whose step is queued.
struct ActiveRound {
    request: Request,
    kind: Round,
}

enum Round {
    Position(TileGuard),
    Closing,
}

/// What to do with a request after acknowledging its step package.
pub(super) enum RoundOutcome {
    Select,
    Park,
    End,
}

impl InductionRun {
    pub(super) fn new(body: Body, starts: Vec<PipelineId>) -> Self {
        Self { body, starts }
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

    /// Open the request `package`: the request it completes at once, and the first round's work.
    pub(super) fn begin_shared(
        &mut self,
        schedule: &mut LoopSchedule,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) -> (Option<WorkPackage>, RoundWork) {
        self.activate(dispatcher);
        let request = self.begin_package(schedule, package);
        self.queue_package_round(schedule, dispatcher, request, RoundOutcome::Select)
    }

    pub(super) fn begin_shared_finish(
        &mut self,
        schedule: &mut LoopSchedule,
        dispatcher: &Dispatcher,
    ) {
        assert!(
            !schedule.has_request()
                && matches!(schedule.phase, LoopPhase::New | LoopPhase::Running),
            "a scope finishes after completing its requests"
        );
        self.activate(dispatcher);
        let body = &mut self.run_mut().body;
        schedule.phase = LoopPhase::Draining;
        body.close_sources(dispatcher);
        dispatcher.close(body.attached().step);
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

    fn begin_package(&mut self, schedule: &mut LoopSchedule, package: WorkPackage) -> Request {
        assert!(
            !schedule.has_request()
                && matches!(schedule.phase, LoopPhase::New | LoopPhase::Running),
            "a loop completes one request before starting another"
        );
        let waited = self.run().body.take_waited();
        let covers = match &waited {
            Some(waited) => package.guard.union(waited),
            None => package.guard.clone(),
        };
        if schedule.phase == LoopPhase::New {
            // The drive reads before the opening step, so the step emits no position outside
            // a round. Each emitted position must run the body before the next store step.
            self.read_source();
            let none = self.input_tiling(InputId::ONLY).empty_guard();
            self.consume_impl(InputId::ONLY, none);
            schedule.phase = LoopPhase::Running;
        }
        let rows = !matches!(self.tiling(), Tiling::Store { .. });
        if rows {
            self.placed(|scope| scope.read_source());
        }
        // The store takes first what the body has decided since positions began to wait, so the
        // drive emits the next position past the ones now decided.
        if let Some(waited) = &waited {
            self.placed(|scope| scope.step_round(waited));
        }
        Request {
            read: rows,
            emitted: false,
            covers,
            waited: waited.is_some(),
            package,
        }
    }

    /// Keep `waiting`, the positions a request leaves undecided, waiting for inputs: a push that
    /// reaches the scope's body or the entry in front of the store's body once an input grows
    /// offers them again, and the request that offer brings runs them ([`Body::queue_offered`]).
    fn wait_for_inputs(&mut self, waiting: TileGuard) {
        let entry = self.base().placement.clone();
        self.run().body.set_waiting(Some(waiting), entry.as_ref());
    }

    /// End a request over `covers`; `waited` is whether positions waited for inputs when the
    /// request began. For a flat store, the positions of `covers` the store has not
    /// decided wait for inputs until the store is terminal: a request that ends before the
    /// drive's source delivers a position leaves its undecided positions waiting, so the push that
    /// delivers one wakes the scope (`Entry::wake`) and offers them again, since the drive's
    /// source entry queues nothing itself. A nested loop's rows wait only where positions waited
    /// before: the loop around it gives a row again with each round. None wait once all are
    /// decided.
    fn keep_undecided(&mut self, covers: &TileGuard, waited: bool) {
        let undecided = guard_minus(covers, &self.input_released(InputId::ONLY));
        let rows = !matches!(self.tiling(), Tiling::Store { .. });
        let done = match rows {
            true => !waited,
            false => self.terminal(),
        };
        match undecided.is_empty() || done {
            true => self.run().body.set_waiting(None, None),
            false => self.wait_for_inputs(undecided),
        }
    }

    /// The next round of the open request: the request, where it has no round left, and the
    /// round's work.
    pub(super) fn queue_package_round(
        &mut self,
        schedule: &mut LoopSchedule,
        dispatcher: &Dispatcher,
        mut request: Request,
        outcome: RoundOutcome,
    ) -> (Option<WorkPackage>, RoundWork) {
        match outcome {
            RoundOutcome::Select => {}
            RoundOutcome::Park => {
                let waiting = guard_minus(&request.covers, &self.input_released(InputId::ONLY));
                self.wait_for_inputs(waiting);
                return (Some(request.package), RoundWork::default());
            }
            RoundOutcome::End => {
                self.keep_undecided(&request.covers, request.waited);
                return (Some(request.package), RoundWork::default());
            }
        }
        let rows = !matches!(self.tiling(), Tiling::Store { .. });
        // A round an earlier request left undecided runs again first: what it read has grown.
        if let Some(guard) = schedule.rerun.take()
            && !guard_minus(&guard, &self.input_released(InputId::ONLY)).is_empty()
        {
            let starts = self.run().starts.clone();
            let mut work = self.placed(|store| store.round_on(dispatcher, &guard, &starts));
            self.run().body.queue_grown(&mut work);
            request.emitted = true;
            schedule.round = Some(ActiveRound {
                request,
                kind: Round::Position(guard),
            });
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
                schedule.round = Some(ActiveRound {
                    request,
                    kind: Round::Position(guard),
                });
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
            self.keep_undecided(&request.covers, request.waited);
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
        schedule.round = Some(ActiveRound {
            request,
            kind: Round::Closing,
        });
        (None, work)
    }

    /// Step the queued round after its body and held pushes settle.
    pub(super) fn complete_round(
        &mut self,
        schedule: &mut LoopSchedule,
    ) -> (Request, RoundOutcome) {
        let ActiveRound { request, kind } = schedule
            .round
            .take()
            .expect("a loop steps one queued round");
        let outcome = match kind {
            Round::Position(guard) => {
                self.placed(|scope| scope.step_round(&guard));
                if guard_minus(&guard, &self.input_released(InputId::ONLY)).is_empty() {
                    RoundOutcome::Select
                } else {
                    // Retry the exact position when a later request wakes its wider coverage.
                    schedule.rerun = Some(guard);
                    RoundOutcome::Park
                }
            }
            Round::Closing => {
                self.placed(|scope| scope.step_round(&request.covers));
                RoundOutcome::End
            }
        };
        (request, outcome)
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
        work
    }

    /// Step the store after the round's body and held pushes have settled. The store steps the
    /// positions of the round its input has decided; positions not decided yet stay unreleased,
    /// and the scope keeps them waiting for inputs (`Offered::retry`).
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
    use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::commit_operator::store_frontier;
    use crate::interpreter::operator_conversion::OperatorMap;
    use crate::interpreter::tile_operators::TileProducer;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{Position, Tile};

    #[test]
    fn a_closing_round_can_take_a_delivered_parent_row_again() {
        let compiled = Compiled::of(SUM);
        let mut scope = induction(&compiled.scope);
        let input = scope.input_tiling(InputId::ONLY);
        let body = scope.body_mut();
        let row = keys_between(0, 0);
        body.offer(&row);
        body.take_rows_from_outer(input);
        assert!(!body.queue_offered(&compiled.dispatcher, true));
        for _ in 0..2 {
            body.hold_row(&row);
            assert!(body.queue_offered(&compiled.dispatcher, true));
            assert!(!body.queue_offered(&compiled.dispatcher, true));
            let request = compiled.dispatcher.claim_of(PipelineId(0)).unwrap();
            assert_eq!(request.guard, row);
            compiled.dispatcher.acknowledge(request);
        }
    }

    #[test]
    fn a_parent_between_requests_releases_its_hold_for_a_woken_child() {
        let compiled = Compiled::of(indoc! {"
            out = test_sink()
            total := 0
            for x in [1, 2, 3]:
                for y in [1, 2]:
                    total += x * y
            out << total
        "});
        compiled.consume(keys_between(0, 0));
        let dispatcher = &compiled.dispatcher;
        let (hold, child) = {
            let mut parent = induction(&compiled.scope);
            let body = parent.body_mut();
            let child = body
                .members
                .iter()
                .find_map(|member| match member {
                    Member::Scope(child) => Some(child.clone()),
                    Member::Chain(_) => None,
                })
                .unwrap();
            (body.attached().hold, child)
        };
        let child_request = {
            let mut child = induction(&child);
            let body = child.body_mut();
            body.set_waiting(Some(keys_between(0, 0)), None);
            body.offers.lock().unwrap().wake();
            body.attached().pipeline
        };
        dispatcher.hold_followers(hold);
        for _ in 0..dispatcher.infos.len() {
            compiled.steps.poll(dispatcher);
            if let Some(package) = dispatcher.claim_of(child_request) {
                assert_eq!(dispatcher.outstanding(PipelineId(0)), 0);
                dispatcher.acknowledge(package);
                return;
            }
        }
        panic!("a ready child retry runs before the parent's next request");
    }

    #[rstest_log::rstest]
    #[case::ordinary(false)]
    #[case::parent_row(true)]
    fn a_wake_before_parking_and_one_after_admission_queue_one_retry(#[case] parent_row: bool) {
        let compiled = Compiled::of(SUM);
        let mut scope = induction(&compiled.scope);
        let input = scope.input_tiling(InputId::ONLY);
        let (entry, placement) = Entry::unplaced(input.clone());
        let body = scope.body_mut();
        if parent_row {
            body.take_rows_from_outer(input);
        }
        placement.set_scope(Some(body.offers.clone()));
        let waiting = keys_between(0, 0);
        entry.wake(&Projection::Everything);
        body.set_waiting(Some(waiting.clone()), None);
        assert!(body.queue_offered(&compiled.dispatcher, true));
        entry.wake(&Projection::Everything);
        assert!(!body.queue_offered(&compiled.dispatcher, true));
        assert_eq!(compiled.dispatcher.outstanding(PipelineId(0)), 1);
        let request = compiled
            .dispatcher
            .claim_of(PipelineId(0))
            .expect("one retry");
        assert_eq!(request.guard, waiting);
        assert_eq!(body.take_waited(), Some(waiting.clone()));
        body.set_waiting(Some(waiting), None);
        compiled.dispatcher.acknowledge(request);
        assert!(body.queue_offered(&compiled.dispatcher, true));
    }

    #[test]
    fn fresh_input_and_a_woken_retry_share_one_package() {
        let compiled = Compiled::of(SUM);
        let mut scope = induction(&compiled.scope);
        let (entry, placement) = Entry::unplaced(scope.input_tiling(InputId::ONLY));
        let body = scope.body_mut();
        let waiting = keys_between(0, 0);
        let fresh = keys_between(2, 2);
        body.set_waiting(Some(waiting.clone()), Some(&placement));
        entry.wake(&Projection::Everything);
        body.offer(&fresh);
        assert!(body.queue_offered(&compiled.dispatcher, true));
        entry.wake(&Projection::Everything);
        assert!(!body.queue_offered(&compiled.dispatcher, true));
        let request = compiled
            .dispatcher
            .claim_of(PipelineId(0))
            .expect("one request");
        assert_eq!(request.guard, fresh.union(&waiting));
        assert_eq!(body.take_waited(), Some(waiting));
        assert!(body.take_waited().is_none());
    }

    #[test]
    fn an_already_queued_ordinary_request_takes_the_woken_positions() {
        let compiled = Compiled::of(SUM);
        let mut scope = induction(&compiled.scope);
        let (entry, placement) = Entry::unplaced(scope.input_tiling(InputId::ONLY));
        let body = scope.body_mut();
        let waiting = keys_between(0, 0);
        let fresh = keys_between(1, 1);
        body.set_waiting(Some(waiting.clone()), Some(&placement));
        body.offer(&fresh);
        assert!(body.queue_offered(&compiled.dispatcher, true));
        entry.wake(&Projection::Everything);
        assert!(!body.queue_offered(&compiled.dispatcher, true));
        let request = compiled
            .dispatcher
            .claim_of(PipelineId(0))
            .expect("ordinary request");
        assert_eq!(request.guard, fresh);
        let active = scope.begin_package(&mut LoopSchedule::default(), request);
        assert!(active.waited);
        assert_eq!(active.covers, fresh.union(&waiting));
        assert_eq!(compiled.dispatcher.outstanding(PipelineId(0)), 1);
        assert!(scope.body_mut().take_waited().is_none());
    }

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
    /// its outer loop store.
    struct Compiled {
        _runs: ScopeRuns,
        _program: CompiledProgram,
        _ctx: GlobalContext,
        operators: OperatorMap,
        scope: StoreCell,
        dispatcher: Dispatcher,
        execution: Execution,
        steps: scope::ScopeSteps,
    }

    impl Compiled {
        fn of(source: &str) -> Self {
            Self::over(source, Dispatcher::new(vec![vec![]], usize::MAX))
        }

        fn over(source: &str, mut dispatcher: Dispatcher) -> Self {
            let mut ctx = GlobalContext::default();
            let _sink = ctx.register_test_sink("out");
            let loaded = LoadedProgram::test(source);
            let program = compile_program(&mut ctx, &loaded, Box::new(|| {}))
                .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
            let operators = ctx.take_operator_map();
            let mut roots = operators.operators().into_iter().filter_map(|fan| {
                let store = fan.store()?;
                let outer = matches!(store.read().tiling(), Tiling::Store { .. });
                outer.then_some(crate::interpreter::tile_operators::StoreRead {
                    fan: fan.id(),
                    store,
                })
            });
            let mut planner = Planner::default();
            planner.store_pipeline(roots.next().expect("one outer loop store"));
            assert!(roots.next().is_none(), "one outer loop store");
            let mut runs = ScopeRuns::new();
            let scope = planner.build_scope(0, usize::MAX, &mut runs);
            induction(&scope).begin_run();
            dispatcher.order(PipelineId(0));
            let mut scopes = vec![None; dispatcher.infos.len()];
            scopes[0] = Some(scope.clone());
            let execution = Execution::new(&scopes, &mut dispatcher);
            let steps = execution.scope_steps(&dispatcher);
            Self {
                steps,
                _runs: runs,
                _program: program,
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
                        self.steps.poll(&self.dispatcher),
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

    #[rstest_log::rstest]
    #[case::flat(SUM, 6)]
    #[case::nested(indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            for y in [1, 2]:
                total += x * y
        out << total
    "}, 18)]
    fn a_worker_runs_a_serial_feeder_and_finishes_its_dependent_loop(
        #[case] source: &str,
        #[case] expected: i64,
    ) {
        use crate::interpreter::{
            BaseType, ColumnValue,
            tile_operators::{MemoProducer, test_helpers::ProjectionSpy},
        };
        use std::sync::mpsc;
        use std::time::Duration;

        // A scalar feeder has one package. Its publication offers the three positions
        // of the outer loop. Only the background worker may claim, including all scope finishes.
        struct OfferRows(Offers);
        impl Consumer for OfferRows {
            fn notify(&self, _: &Projection, _: &mut Landing<'_>) {
                self.0.lock().unwrap().offer(keys_between(0, 2));
            }
        }
        let request = PipelineId(0);
        let feeder = PipelineId(1);
        let mut compiled = Compiled::over(
            source,
            Dispatcher::new(vec![vec![feeder.0], vec![]], usize::MAX),
        );
        compiled
            .execution
            .close_on_reads(&mut compiled.dispatcher, request);
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (input, _, _) =
            ProjectionSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
        let mut memo = MemoProducer::over(Box::new(input), &tiling);
        memo.base_mut().downstream = Some(Arc::new(OfferRows(
            induction(&compiled.scope).body_mut().offers.clone(),
        )));
        let handle: BreakerHandle = Arc::new(RwLock::new(memo));
        let workers = compiled
            .execution
            .worker_pool(&mut compiled.dispatcher, 2, |p| {
                assert_eq!(p, feeder.0);
                Some(workers::WorkerBreaker::Chain(handle.clone()))
            });
        let dispatcher = &compiled.dispatcher;
        assert!(dispatcher.infos[feeder.0].ordered);
        dispatcher.notify(feeder, &tiling.universal_guard());
        dispatcher.close(feeder);
        thread::scope(|threads| {
            let handles = workers.spawn(threads, dispatcher, false);
            let (done, result) = mpsc::channel();
            threads.spawn(move || {
                workers::WorkerPool::join(handles);
                let _ = done.send(());
            });
            let completed = result.recv_timeout(Duration::from_secs(5));
            dispatcher.stop_claims();
            completed.expect("the worker drains the scope without a coordinator finish claim");
        });
        assert!(dispatcher.states[request.0].phase.load() == Phase::Finished);
        assert!(!induction(&compiled.scope).body_mut().is_active());
        assert_eq!(compiled.value(), Value::Int(expected));
    }

    #[rstest_log::rstest]
    #[case::flat_seed(false, 0)]
    #[case::missed_close(true, 6)]
    fn a_worker_resumes_a_loop_while_an_unrelated_package_is_in_flight(
        #[case] finish_feeder: bool,
        #[case] expected: i64,
    ) {
        use std::sync::mpsc;
        use std::time::Duration;

        let request = PipelineId(0);
        let feeder = PipelineId(1);
        let peer = PipelineId(2);
        let mut compiled = Compiled::over(
            SUM,
            Dispatcher::new(vec![vec![feeder.0], vec![], vec![]], usize::MAX),
        );
        compiled
            .execution
            .close_on_reads(&mut compiled.dispatcher, request);
        let workers = compiled
            .execution
            .worker_pool(&mut compiled.dispatcher, 2, |_| None);
        let dispatcher = &compiled.dispatcher;

        // The coordinator holds an independent package from reservation through both
        // the worker's scope check and the observation of its result.
        dispatcher.notify(peer, &keys_between(0, 0));
        dispatcher.close(peer);
        let (Next::Package(WorkerPackage::Input(package)), (_, activity)) =
            workers.next(dispatcher, Some(peer), &|_| true)
        else {
            panic!("the coordinator takes the independent package");
        };
        assert_eq!(package.pipeline, peer);
        assert!(activity.is_some());

        if finish_feeder {
            compiled
                .execution
                .offer_request(request, &keys_between(0, 2));
            let _store = induction(&compiled.scope);
            dispatcher.close(feeder);
            dispatcher.begin_finish(feeder);
            dispatcher.finish(dispatcher.pushes(feeder));
            // Force the callback from the last read to miss the store.
            assert!(
                !compiled
                    .execution
                    .request_scope(request)
                    .try_queue_requests(dispatcher)
            );
        }

        dispatcher.start_visits();
        workers.begin_drain(dispatcher, false);
        let mut generation = Generation(dispatcher.changes());
        thread::scope(|threads| {
            let handles = workers.spawn(threads, dispatcher, false);
            let (done, result) = mpsc::channel();
            threads.spawn(move || {
                loop {
                    dispatcher.wait(generation);
                    generation = Generation(dispatcher.changes());
                    if dispatcher.stopped.load(Ordering::SeqCst) {
                        return;
                    }
                    if !finish_feeder
                        || dispatcher.states[request.0].phase.load() == Phase::Finished
                    {
                        let _ = done.send(());
                        return;
                    }
                }
            });
            let completed = result.recv_timeout(Duration::from_secs(5));
            dispatcher.stop_claims();
            workers::WorkerPool::join(handles);
            completed.expect("the worker progresses the scope before the peer returns");
        });
        // Before any positions arrive the published seed is 0. After the missed close
        // the scope must have consumed all three positions and finished with 6.
        assert_eq!(compiled.value(), Value::Int(expected));
        dispatcher.acknowledge(package);
        drop(activity);
        workers.end_drain();
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
    fn a_settled_loop_queues_one_step_until_the_coordinator_runs_it() {
        let compiled = Compiled::of(SUM);
        let whole = induction(&compiled.scope)
            .input_tiling(InputId::ONLY)
            .universal_guard();
        compiled.dispatcher.notify(PipelineId(0), &whole);
        let step = induction(&compiled.scope).body_mut().attached().step;
        for _ in 0..32 {
            if compiled.dispatcher.outstanding(step) != 0 {
                break;
            }
            compiled.tick();
        }
        assert_eq!(compiled.dispatcher.outstanding(step), 1);
        assert!(!compiled.steps.poll(&compiled.dispatcher));
        assert_eq!(compiled.dispatcher.outstanding(step), 1);
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

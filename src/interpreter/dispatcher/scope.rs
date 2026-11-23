//! Loop and transaction scopes: their request and step handlers, and the settlement of each
//! scope's body. See `src/interpreter/design-dispatcher.md`, "A loop in rounds".

use super::loop_scope::{Body, LoopSchedule, Member, induction};
use super::transaction_scope::{self, WriterPhase};
use super::*;
use crate::interpreter::tile_operators::{StoreBorrow, StoreCell};

/// A scope whose inner pipelines run on the run's shared dispatcher, between its request and
/// step handlers. Each scope's request and round or attempt state sits in a cell of its own,
/// which its request and step handlers advance one at a time.
pub(super) enum Scope {
    /// A loop: the store's rounds.
    Loop {
        store: StoreCell,
        // shared-state-ok: the loop's request and step handlers take turns advancing it; what
        // crosses it is the loop's request and round guards, never a tile.
        schedule: Mutex<LoopSchedule>,
    },
    /// One writer of a transaction store: its attempts.
    Writer {
        store: StoreCell,
        writer: usize,
        // shared-state-ok: the writer's request and step handlers take turns advancing it; what
        // crosses it is the writer's request and attempt guards, never a tile.
        phase: Mutex<WriterPhase>,
    },
}

fn scope_state<T>(state: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    state.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Land the scope's decision for the request `package` it completed, then acknowledge it.
pub(super) fn complete_request(
    dispatcher: &Dispatcher,
    package: Option<WorkPackage>,
    publish: impl FnOnce(&mut Pushes<'_>),
) {
    if let Some(package) = package {
        let mut pushes = dispatcher.pushes(package.pipeline);
        publish(&mut pushes);
        dispatcher.land(pushes);
        dispatcher.acknowledge(package);
    }
}

impl Scope {
    pub(super) fn reach(&self, call: &mut Call<'_>) {
        match self {
            Scope::Loop { store, .. } => call(&mut *induction(store), InputId::ONLY),
            Scope::Writer { store, writer, .. } => {
                let mut producer = transaction_scope::transaction(store);
                let input = producer.writer_input(*writer);
                call(&mut *producer, input);
            }
        }
    }

    /// Call `f` with the scope's inner pipelines.
    pub(super) fn with_body<R>(&self, f: impl FnOnce(&mut Body) -> R) -> R {
        f(self.body_in(&mut self.store().write()))
    }

    fn body_in<'a>(&self, store: &'a mut StoreBorrow<'_>) -> &'a mut Body {
        match self {
            Self::Loop { .. } => store
                .as_induction_store_mut()
                .expect("a loop store")
                .body_mut(),
            Self::Writer { writer, .. } => {
                &mut store
                    .as_transaction_store_mut()
                    .expect("a transaction store")
                    .writer_run_mut(*writer)
                    .body
            }
        }
    }

    /// Whether a request is open, whose claim is in flight until it completes.
    pub(super) fn has_request(&self) -> bool {
        match self {
            Scope::Loop { schedule, .. } => scope_state(schedule).has_request(),
            Scope::Writer { phase, .. } => scope_state(phase).has_request(),
        }
    }

    fn store(&self) -> &StoreCell {
        match self {
            Self::Loop { store, .. } | Self::Writer { store, .. } => store,
        }
    }

    /// A sweep can re-hold a body without waiting for a different scope's transition.
    /// A busy writer is held conservatively. Its next publication releases the version it sees.
    pub(super) fn hold_followers(
        &self,
        dispatcher: &Dispatcher,
        request: PipelineId,
        group: HoldGroup,
    ) {
        if dispatcher.states[request.0].phase.load() == Phase::Finished {
            return;
        }
        if let Self::Writer { phase, .. } = self
            && phase.try_lock().is_ok_and(|phase| !phase.open())
        {
            return;
        }
        dispatcher.hold_followers(group);
    }

    /// Open the request `package`, a claim of the scope's own pipeline.
    pub(super) fn begin(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Scope::Loop { store, schedule } => {
                scope_state(schedule).begin(store, dispatcher, package)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => scope_state(phase).begin(store, *writer, dispatcher, package),
        }
    }

    /// End the round or attempt whose step claimed `package`, and start the next or complete
    /// the request.
    pub(super) fn step(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Scope::Loop { store, schedule } => {
                scope_state(schedule).step(store, dispatcher, package)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => scope_state(phase).step(store, *writer, dispatcher, package),
        }
    }

    /// Begin the finish of the scope's pipeline: it drains the body, and its step's finish ends
    /// it ([`finish_step`](Self::finish_step)).
    pub(super) fn begin_finish(&self, dispatcher: &Dispatcher) {
        match self {
            Scope::Loop { store, schedule } => {
                let mut schedule = scope_state(schedule);
                induction(store).begin_shared_finish(&mut schedule, dispatcher);
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => {
                let mut phase = scope_state(phase);
                let work = transaction_scope::transaction(store)
                    .begin_transaction_finish(&mut phase, dispatcher, *writer);
                work.queue(dispatcher);
            }
        }
    }

    /// Finish the step `step` and then the scope's own pipeline, whose finish began first. The step
    /// reads every inner pipeline, so the body has finished. Answers the scope's pipeline, or
    /// `None` where the run has failed: a failed run records no finish ([`Dispatcher::finish`]),
    /// so the step has not finished.
    pub(super) fn finish_step(
        &self,
        dispatcher: &Dispatcher,
        step: PipelineId,
    ) -> Option<PipelineId> {
        dispatcher.finish(dispatcher.pushes(step));
        let finished = match self {
            Scope::Loop { store, schedule } => {
                let mut schedule = scope_state(schedule);
                schedule.take_finish(induction(store).body_mut(), dispatcher)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => {
                let mut phase = scope_state(phase);
                transaction_scope::transaction(store)
                    .writer_run_mut(*writer)
                    .take_finish(&mut phase, dispatcher)
            }
        };
        let Some(request) = finished else {
            assert!(
                dispatcher.failed.load(Ordering::SeqCst),
                "a scope's step finishes once the scope drains"
            );
            return None;
        };
        finish_with(dispatcher, &mut |_, call| self.reach(call), request);
        self.with_body(|body| body.unplace());
        Some(request)
    }

    /// Queue the requests offered to the scope where they can run: a loop's at once, a writer's
    /// once its store is open. Whether it queued or closed anything. An unrelated transition can be
    /// holding the store; the intake then stays for the next scope poll, including after its last
    /// read finished.
    pub(super) fn try_queue_requests(&self, dispatcher: &Dispatcher) -> bool {
        self.store()
            .try_write()
            .is_ok_and(|mut store| self.admit(dispatcher, &mut store))
    }

    fn admit(&self, dispatcher: &Dispatcher, store: &mut StoreBorrow<'_>) -> bool {
        match self {
            Self::Loop { .. } => self.body_in(store).queue_offered(dispatcher, true),
            Self::Writer { writer, .. } => store
                .as_transaction_store_mut()
                .expect("a transaction store")
                .queue_requests(dispatcher, *writer),
        }
    }
}

/// An ordered scope pipeline that any worker may claim.
pub(super) enum ScopePipeline {
    Request(Arc<Scope>),
    Step(Arc<Scope>),
    Seed(StoreCell, InputId),
}

impl ScopePipeline {
    /// The pipeline whose final publication landed. A request starts draining;
    /// its step makes the final publication once its body has finished.
    pub(super) fn finish(
        &self,
        dispatcher: &Dispatcher,
        pipeline: PipelineId,
        reach: &mut Reach<'_>,
    ) -> Option<PipelineId> {
        match self {
            Self::Request(scope) => {
                scope.begin_finish(dispatcher);
                None
            }
            Self::Step(scope) => scope.finish_step(dispatcher, pipeline),
            Self::Seed(..) => {
                finish_with(dispatcher, reach, pipeline);
                Some(pipeline)
            }
        }
    }

    pub(super) fn consume(
        &self,
        dispatcher: &Dispatcher,
        package: WorkPackage,
        reach: &mut Reach<'_>,
    ) {
        match self {
            Self::Request(scope) => scope.begin(dispatcher, package),
            Self::Step(scope) => scope.step(dispatcher, package),
            Self::Seed(..) => consume_with(dispatcher, reach, package),
        }
    }
}

/// A scope's settlement: its body's members, fixed when the plan attaches the body.
struct LocalSteps {
    scope: Arc<Scope>,
    request: PipelineId,
    step: PipelineId,
    base: usize,
    members: Vec<PublicationTarget>,
}

/// Where a scope publishes one inner pipeline's held output: a chain's breaker, or a nested loop.
enum PublicationTarget {
    Chain(BreakerHandle),
    Child(Arc<Scope>),
}

/// Every scope of a run, in groups of connected scopes: each group settles its scopes' bodies and
/// queues one step at a time.
#[derive(Default)]
pub(super) struct ScopeSteps {
    groups: Vec<StepGroup>,
}

struct StepGroup {
    scopes: Vec<LocalSteps>,
    // shared-state-ok: one claimant chooses the next step among connected scopes at a time.
    choosing: Mutex<()>,
}

impl ScopeSteps {
    /// Only scopes connected by reads, follows, containment or a shared store need to
    /// arbitrate their steps. A shared input alone does not connect its readers.
    pub(super) fn plan(dispatcher: &Dispatcher, scopes: impl Iterator<Item = Arc<Scope>>) -> Self {
        let scopes: Vec<_> = scopes
            .map(|scope| (scope.with_body(|body| body.attached().pipeline.0), scope))
            .collect();
        if scopes.is_empty() {
            return Self::default();
        }
        let mut upstream: Vec<Vec<usize>> = dispatcher
            .infos
            .iter()
            .map(|info| info.reads.iter().chain(&info.follows).copied().collect())
            .collect();
        for (p, info) in dispatcher.infos.iter().enumerate() {
            let first = info.pushes_with;
            if first != p {
                upstream[p].push(first);
                upstream[first].push(p);
            }
        }
        let mut stores = HashMap::new();
        let mut by_id = vec![None; upstream.len()];
        for (id, scope) in &scopes {
            by_id[*id] = Some(scope);
            scope.with_body(|body| {
                for p in body.pipelines().into_iter().chain([body.attached().step]) {
                    upstream[*id].push(p.0);
                    upstream[p.0].push(*id);
                }
            });
            if let Some(other) = stores.insert(Arc::as_ptr(scope.store()), *id) {
                upstream[*id].push(other);
                upstream[other].push(*id);
            }
        }
        let mut peers = vec![Vec::new(); upstream.len()];
        let mut seen = vec![usize::MAX; upstream.len()];
        for &(id, _) in &scopes {
            let mut stack = vec![id];
            while let Some(p) = stack.pop() {
                if seen[p] == id {
                    continue;
                }
                seen[p] = id;
                if p != id && by_id[p].is_some() {
                    peers[id].push(p);
                    peers[p].push(id);
                } else {
                    stack.extend(&upstream[p]);
                }
            }
        }

        let mut steps = Self::default();
        let mut grouped = vec![false; upstream.len()];
        for &(first, _) in &scopes {
            if grouped[first] {
                continue;
            }
            let mut connected = Vec::new();
            let mut stack = vec![first];
            while let Some(id) = stack.pop() {
                if std::mem::replace(&mut grouped[id], true) {
                    continue;
                }
                let scope = by_id[id].expect("a scope group member");
                connected.push(scope.with_body(|body| {
                    LocalSteps {
                        scope: scope.clone(),
                        request: body.attached().pipeline,
                        step: body.attached().step,
                        base: body.global(PipelineId(0)).0,
                        members: body
                            .members
                            .iter()
                            .enumerate()
                            .map(|(local, member)| match member {
                                Member::Chain(handle) => PublicationTarget::Chain(handle.clone()),
                                Member::Scope(_) => PublicationTarget::Child(
                                    by_id[body.global(PipelineId(local)).0]
                                        .expect("a nested loop's scope is attached")
                                        .clone(),
                                ),
                            })
                            .collect(),
                    }
                }));
                stack.extend(&peers[id]);
            }
            steps.groups.push(StepGroup {
                scopes: connected,
                choosing: Mutex::default(),
            });
        }
        steps
    }

    /// Settle each group's bodies and queue a step where a round or attempt has run. Whether any
    /// group changed anything.
    pub(super) fn poll(&self, dispatcher: &Dispatcher) -> bool {
        let mut advanced = false;
        for group in &self.groups {
            advanced |= group.poll(dispatcher);
        }
        advanced
    }
}

impl StepGroup {
    fn poll(&self, dispatcher: &Dispatcher) -> bool {
        if let [scope] = &self.scopes[..] {
            return scope.poll(dispatcher, true);
        }
        let Ok(_choosing) = self.choosing.try_lock() else {
            return false;
        };
        // Publish every body's held output before choosing a step. A queued or running
        // decision gets to land its input to peer scopes before the next decision.
        let mut published = false;
        for scope in &self.scopes {
            published |= scope.poll(dispatcher, false);
        }
        if published
            || self
                .scopes
                .iter()
                .any(|scope| !scope.ready_for_decision(dispatcher))
        {
            return published;
        }
        self.scopes
            .iter()
            .any(|scope| scope.try_queue_step(dispatcher))
    }
}

impl LocalSteps {
    fn with_schedule(&self, f: impl FnOnce(bool, Option<&TileGuard>) -> bool) -> bool {
        match self.scope.as_ref() {
            Scope::Loop { schedule, .. } => schedule
                .try_lock()
                .ok()
                .is_some_and(|state| f(state.publishing(), state.step_guard())),
            Scope::Writer { phase, .. } => phase
                .try_lock()
                .ok()
                .is_some_and(|state| f(state.open(), state.step_guard())),
        }
    }

    // A peer commit may move the snapshot used by every writer in the store. Let their
    // drivers and proposal pipelines consume the previous snapshot before advancing it.
    fn ready_for_decision(&self, dispatcher: &Dispatcher) -> bool {
        self.with_schedule(|_, _| {
            if dispatcher.ready_to_finish(self.request.0)
                || dispatcher.may_start_ordered_package(self.request)
                || dispatcher.outstanding(self.step) != 0
            {
                return false;
            }
            self.members.iter().enumerate().all(|(i, member)| {
                let p = self.base + i;
                matches!(member, PublicationTarget::Child(_))
                    || (!dispatcher.may_claim_from(p)
                        && !dispatcher.ready_to_finish(p)
                        && dispatcher.states[p].phase.load() != Phase::Finishing)
            })
        })
    }

    fn try_queue_step(&self, dispatcher: &Dispatcher) -> bool {
        self.with_schedule(|_, guard| guard.is_some_and(|guard| self.queue_step(dispatcher, guard)))
    }

    fn queue_step(&self, dispatcher: &Dispatcher, guard: &TileGuard) -> bool {
        self.scope
            .store()
            .try_write()
            .is_ok_and(|mut store| self.scope.body_in(&mut store).queue_step(dispatcher, guard))
    }

    fn poll(&self, dispatcher: &Dispatcher, queue: bool) -> bool {
        self.with_schedule(|publishing, guard| {
            self.settle(dispatcher, publishing, guard.filter(|_| queue))
        })
    }

    /// Open a flat loop's seed, admit what the scope was offered, and while the body runs publish
    /// what its members hold: once a pass publishes nothing, release the body's followers and
    /// queue the step. Whether anything changed.
    fn settle(&self, dispatcher: &Dispatcher, publishing: bool, guard: Option<&TileGuard>) -> bool {
        let Ok(mut store) = self.scope.store().try_write() else {
            return false;
        };
        // Only the loop's own inputs can affect its seed. The store and schedule
        // are exclusively held, so competing claimants cannot open it twice.
        if let Some(induction) = store.as_induction_store_mut()
            && dispatcher.states[self.request.0].phase.load() == Phase::Running
            && induction.initialize_seed_if(|| {
                dispatcher.quiescent(dispatcher.infos[self.request.0].reads.iter().copied())
            })
        {
            // Publishing a seed changes the store without enqueueing a package.
            dispatcher.wake_claimants();
            return true;
        }
        let admitted = self.scope.admit(dispatcher, &mut store);
        let body = self.scope.body_in(&mut store);
        if !publishing || !body.is_active() || dispatcher.outstanding(self.step) != 0 {
            return admitted;
        }
        let hold = body.attached().hold;
        let held = dispatcher.followers_hold(hold);
        if held.0 & 1 == 0 {
            return admitted || guard.is_some_and(|g| body.queue_step(dispatcher, g));
        }
        drop(store);
        // A nested request can span multiple publication passes. Its own schedule
        // decides when its output can be published to the enclosing body.
        if self.members.iter().enumerate().any(|(i, member)| {
            matches!(member, PublicationTarget::Chain(_))
                && dispatcher.may_claim_from(self.base + i)
        }) {
            return admitted;
        }
        let members = self.base..self.base + self.members.len();
        match try_push_held(dispatcher, members.map(PipelineId), |id, call| {
            match &self.members[id.0 - self.base] {
                PublicationTarget::Chain(handle) => {
                    let Ok(mut breaker) = handle.try_write() else {
                        return false;
                    };
                    call(&mut *breaker, InputId::ONLY);
                }
                PublicationTarget::Child(child) => {
                    let Scope::Loop { schedule, store } = child.as_ref() else {
                        unreachable!("a nested loop")
                    };
                    let Ok(state) = schedule.try_lock() else {
                        return false;
                    };
                    if !state.has_request() {
                        let Ok(mut store) = store.try_write() else {
                            return false;
                        };
                        call(
                            store.as_induction_store_mut().expect("a nested loop"),
                            InputId::ONLY,
                        );
                    }
                }
            }
            true
        }) {
            Publication::Busy => admitted,
            Publication::Published => true,
            Publication::Settled => {
                let released = dispatcher.release_followers_if(hold, held);
                let queued = guard.is_some_and(|g| self.queue_step(dispatcher, g));
                queued || released || admitted
            }
        }
    }
}

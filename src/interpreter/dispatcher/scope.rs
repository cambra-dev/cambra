//! Scope control pipelines, publication and admission of settled steps.
use super::loop_scope::{Body, LoopSchedule, Member, induction};
use super::transaction_scope::WriterPhase;
use super::*;
use crate::interpreter::tile_operators::{StoreBorrow, StoreCell};

/// A scope whose inner pipelines run on the run's shared dispatcher, between its request and
/// step handlers.
pub(super) enum Scope {
    /// A loop: the store's rounds.
    Loop {
        store: StoreCell,
        // shared-state-ok: request and step claims serialize this loop's scheduling metadata.
        schedule: Mutex<LoopSchedule>,
    },
    /// One writer of a transaction store: its attempts.
    Writer {
        store: StoreCell,
        writer: usize,
        // shared-state-ok: scope handlers take turns updating scheduling state for this writer.
        phase: Mutex<WriterPhase>,
    },
}

fn scope_state<T>(state: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    state.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Complete the retained request after publishing the scope's decision and releasing the store.
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
            Self::Loop {
                store,
                schedule: state,
            } => scope_state(state).begin(store, dispatcher, package),
            Self::Writer {
                store,
                writer,
                phase,
            } => scope_state(phase).begin(store, *writer, dispatcher, package),
        }
    }

    pub(super) fn step(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Self::Loop {
                store,
                schedule: state,
            } => scope_state(state).step(store, dispatcher, package),
            Self::Writer {
                store,
                writer,
                phase,
            } => scope_state(phase).step(store, *writer, dispatcher, package),
        }
    }

    pub(super) fn begin_finish(&self, dispatcher: &Dispatcher) {
        match self {
            Self::Loop {
                store,
                schedule: state,
            } => {
                let mut state = scope_state(state);
                induction(store).begin_shared_finish(&mut state, dispatcher);
            }
            Self::Writer {
                store,
                writer,
                phase,
            } => {
                let mut state = scope_state(phase);
                let work = transaction_scope::transaction(store)
                    .begin_transaction_finish(&mut state, dispatcher, *writer);
                work.queue(dispatcher);
            }
        }
    }

    /// The step reads every body member. Its unique finish claimant also
    /// publishes the enclosing request's final output after the body has drained.
    pub(super) fn finish_step(&self, dispatcher: &Dispatcher, step: PipelineId) -> PipelineId {
        dispatcher.finish(dispatcher.pushes(step));
        let finished = match self {
            Scope::Loop { store, schedule } => {
                let mut schedule = scope_state(schedule);
                let mut store = induction(store);
                let body = store.body_mut();
                schedule.take_finish(body, dispatcher)
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
        let request = finished.expect("a closed step finishes its draining scope");
        finish_with(dispatcher, &mut |_, call| self.reach(call), request);
        self.with_body(|body| body.unplace());
        request
    }

    /// Admit pending requests and publish what the body holds during shared settlement.
    pub(super) fn resume(
        &self,
        dispatcher: &Dispatcher,
        reach: &mut Reach<'_>,
        child_active: impl Fn(PipelineId) -> bool,
    ) -> bool {
        let mut progressed = false;
        if let Scope::Loop { store, .. } = self {
            progressed |= induction(store).initialize_seed();
        }
        // A scope's requests reach the scope, which queues them once they can run.
        if self.queue_requests(dispatcher) {
            return true;
        }
        // A loop publishes the inner pipelines a round settles; a writer, every inner pipeline.
        // The body's hold is read first: a worker's claim of the body after it holds the
        // followers again, so the release below fails rather than pass output this pass missed.
        let (pipelines, hold) = match self {
            Scope::Loop { store, schedule } => {
                let schedule = scope_state(schedule);
                let store = induction(store);
                (
                    store.settlement_pipelines(&schedule, child_active),
                    store.followers_hold(dispatcher),
                )
            }
            Scope::Writer { store, writer, .. } => {
                let transaction = transaction_scope::transaction(store);
                let run = transaction.writer_run(*writer);
                (run.body.pipelines(), run.body.followers_hold(dispatcher))
            }
        };
        let before = dispatcher.changes();
        push_held(dispatcher, reach, pipelines);
        // A change here is these pushes, or a worker's publication during the pass, which counts
        // as progress too: the coordinator claims again and reaches the same fixed point.
        if dispatcher.changes() != before {
            return true;
        }
        let released = hold.is_some_and(|hold| match self {
            Scope::Loop { store, schedule } => {
                let schedule = scope_state(schedule);
                induction(store).release_followers(&schedule, dispatcher, hold)
            }
            Scope::Writer { phase, .. } => {
                scope_state(phase).open()
                    && self.with_body(|body| body.release_followers(dispatcher, hold))
            }
        });
        progressed | released
    }

    /// Queue the requests offered to the scope where they can run: a loop's at once, a writer's
    /// once its store is open. Whether it queued or closed anything.
    fn queue_requests(&self, dispatcher: &Dispatcher) -> bool {
        self.admit(dispatcher, &mut self.store().write(), false)
    }

    /// An unrelated transition can be holding its store. Its intake remains available for
    /// the next pass. The coordinator rechecks finished reads at each settled boundary.
    pub(super) fn try_queue_requests(&self, dispatcher: &Dispatcher, close: bool) -> bool {
        self.store()
            .try_write()
            .is_ok_and(|mut store| self.admit(dispatcher, &mut store, close))
    }

    fn admit(&self, dispatcher: &Dispatcher, store: &mut StoreBorrow<'_>, close: bool) -> bool {
        match self {
            Self::Loop { .. } => {
                let body = self.body_in(store);
                if close {
                    body.close_offers();
                }
                body.queue_offered(dispatcher, true)
            }
            Self::Writer { writer, .. } => {
                let store = store
                    .as_transaction_store_mut()
                    .expect("a transaction store");
                if close {
                    store.writer_run_mut(*writer).body.close_offers();
                }
                store.queue_requests(dispatcher, *writer)
            }
        }
    }

    /// Queue the step of the open round or attempt where its work has run
    /// ([`Body::queue_step`]). Whether it queued it.
    pub(super) fn queue_step(&self, dispatcher: &Dispatcher) -> bool {
        let queue = |guard: &TileGuard| self.with_body(|body| body.queue_step(dispatcher, guard));
        match self {
            Scope::Loop { schedule, .. } => scope_state(schedule).step_guard().is_some_and(queue),
            Scope::Writer { phase, .. } => scope_state(phase).step_guard().is_some_and(queue),
        }
    }
}

/// An ordered scope pipeline that any worker may claim.
pub(super) enum ScopePipeline {
    Request {
        scope: Arc<Scope>,
        closes_on_reads: bool,
    },
    Step(Arc<Scope>),
    Seed(StoreCell, InputId),
}

impl ScopePipeline {
    pub(super) fn admit_after_read(&self, dispatcher: &Dispatcher, reader: PipelineId) {
        if let Self::Request {
            scope,
            closes_on_reads,
        } = self
        {
            scope.try_queue_requests(
                dispatcher,
                *closes_on_reads && dispatcher.only_arrivals_remain(reader),
            );
        }
    }

    /// The pipeline whose final publication landed. A request starts draining;
    /// its step makes the final publication once its body has finished.
    pub(super) fn finish(
        &self,
        dispatcher: &Dispatcher,
        pipeline: PipelineId,
        reach: &mut Reach<'_>,
    ) -> Option<PipelineId> {
        match self {
            Self::Request { scope, .. } => {
                scope.begin_finish(dispatcher);
                None
            }
            Self::Step(scope) => Some(scope.finish_step(dispatcher, pipeline)),
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
            Self::Request { scope, .. } => scope.begin(dispatcher, package),
            Self::Step(scope) => scope.step(dispatcher, package),
            Self::Seed(..) => consume_with(dispatcher, reach, package),
        }
    }
}

/// Publication for a body with independent inputs. The member handles are fixed at attachment.
/// The scope mutex serializes publication, step admission and the transition that consumes it.
struct LocalSteps {
    scope: Arc<Scope>,
    base: usize,
    members: Vec<BreakerHandle>,
}

#[derive(Default)]
pub(super) struct ScopeSteps {
    independent: Vec<LocalSteps>,
    shared: Vec<(PipelineId, Offers)>,
}

impl ScopeSteps {
    /// An isolated scope may publish and re-arm locally. Nested bodies, writers sharing a
    /// store and scopes connected by reads or follows settle in the fair shared pass.
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
        let mut request = vec![false; upstream.len()];
        for (id, scope) in &scopes {
            request[*id] = true;
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
        let mut coupled = vec![false; upstream.len()];
        let mut seen = vec![usize::MAX; upstream.len()];
        for &(id, _) in &scopes {
            let mut stack = vec![id];
            while let Some(p) = stack.pop() {
                if seen[p] == id {
                    continue;
                }
                seen[p] = id;
                if p != id && request[p] {
                    coupled[id] = true;
                    coupled[p] = true;
                } else {
                    stack.extend(&upstream[p]);
                }
            }
        }
        let mut steps = Self::default();
        for (id, scope) in scopes {
            if coupled[id] {
                steps
                    .shared
                    .push((PipelineId(id), scope.with_body(|body| body.offers.clone())));
            } else {
                let (base, members) = scope.with_body(|body| {
                    let handles = body
                        .members
                        .iter()
                        .map(|member| match member {
                            Member::Chain(handle) => handle.clone(),
                            Member::Scope(_) => {
                                unreachable!("a nested scope uses shared settlement")
                            }
                        })
                        .collect();
                    (body.global(PipelineId(0)).0, handles)
                });
                steps.independent.push(LocalSteps {
                    scope,
                    base,
                    members,
                });
            }
        }
        steps
    }

    /// A local retry must yield while a connected scope needs the fair settlement pass.
    pub(super) fn shared_work_pending(&self, dispatcher: &Dispatcher) -> bool {
        self.shared.iter().any(|(id, offers)| {
            dispatcher.outstanding(*id) != 0
                || dispatcher.states[id.0].phase.load() == Phase::Finishing
                || dispatcher.ready_to_finish(id.0)
                || scope_state(offers).has_work()
        })
    }

    pub(super) fn poll(&self, dispatcher: &Dispatcher) -> bool {
        if self.independent.is_empty() || self.shared_work_pending(dispatcher) {
            return false;
        }
        let mut advanced = false;
        for scope in &self.independent {
            advanced |= scope.poll(dispatcher);
        }
        advanced
    }
}

impl LocalSteps {
    fn poll(&self, dispatcher: &Dispatcher) -> bool {
        match self.scope.as_ref() {
            Scope::Loop {
                schedule: state, ..
            } => state
                .try_lock()
                .ok()
                .is_some_and(|state| self.settle(dispatcher, state.step_guard())),
            Scope::Writer { phase, .. } => phase
                .try_lock()
                .ok()
                .is_some_and(|phase| self.settle(dispatcher, phase.step_guard())),
        }
    }

    fn settle(&self, dispatcher: &Dispatcher, guard: Option<&TileGuard>) -> bool {
        let Ok(mut store) = self.scope.store().try_write() else {
            return false;
        };
        let admitted = self.scope.admit(dispatcher, &mut store, false);
        let Some(guard) = guard else { return admitted };
        let body = self.scope.body_in(&mut store);
        let step = body.attached().step;
        let hold = body.attached().hold;
        if dispatcher.outstanding(step) != 0 {
            return admitted;
        }
        let held = dispatcher.followers_hold(hold);
        if held.0 & 1 == 0 {
            return body.queue_step(dispatcher, guard) || admitted;
        }
        drop(store);
        let members = self.base..self.base + self.members.len();
        // Give already runnable body work its turn before inspecting breaker output.
        // A claim can still start after this scan, so each breaker is also tried below.
        if members.clone().any(|p| dispatcher.may_claim_from(p)) {
            return admitted;
        }
        match try_push_held(dispatcher, members.map(PipelineId), |id, call| {
            let handle = &self.members[id.0 - self.base];
            let mut breaker = match handle.try_write() {
                Ok(breaker) => breaker,
                Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
                Err(std::sync::TryLockError::WouldBlock) => return false,
            };
            call(&mut *breaker, InputId::ONLY);
            true
        }) {
            Publication::Busy => admitted,
            Publication::Published => true,
            Publication::Settled => {
                let released = dispatcher.release_followers_if(hold, held);
                let queued = self.scope.store().try_write().is_ok_and(|mut store| {
                    self.scope.body_in(&mut store).queue_step(dispatcher, guard)
                });
                queued || released || admitted
            }
        }
    }
}

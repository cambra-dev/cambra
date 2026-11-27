//! Loop and transaction scopes: their request and step handlers, and the settlement of each
//! scope's body. See `src/interpreter/design-dispatcher.md`, "A loop in rounds".

use super::loop_scope::{Body, LoopSchedule, Member, induction};
use super::transaction_scope::{self, WriterPhase};
use super::*;
use crate::interpreter::tile_operators::StoreCell;

/// A scope whose inner pipelines run on the run's shared dispatcher, between its request and
/// step handlers. Each scope's request and round or attempt state sits in a cell of its own,
/// which its request and step handlers advance one at a time.
pub(super) enum Scope {
    /// A loop: the store's rounds.
    Loop {
        store: StoreCell,
        // shared-state-ok: the loop's request and step handlers take turns advancing it; what
        // crosses it is the loop's request and round guards, never a tile.
        schedule: RefCell<LoopSchedule>,
    },
    /// One writer of a transaction store: its attempts.
    Writer {
        store: StoreCell,
        writer: usize,
        // shared-state-ok: the writer's request and step handlers take turns advancing it; what
        // crosses it is the writer's request and attempt guards, never a tile.
        phase: RefCell<WriterPhase>,
    },
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
        match self {
            Scope::Loop { store, .. } => f(induction(store).body_mut()),
            Scope::Writer { store, writer, .. } => f(&mut transaction_scope::transaction(store)
                .writer_run_mut(*writer)
                .body),
        }
    }

    /// Whether a request is open, whose claim is in flight until it completes.
    pub(super) fn has_request(&self) -> bool {
        match self {
            Scope::Loop { schedule, .. } => schedule.borrow().has_request(),
            Scope::Writer { phase, .. } => phase.borrow().has_request(),
        }
    }

    /// Hold back the pipelines that follow the body, while it runs: a writer's while a request or
    /// its finish is open.
    pub(super) fn hold_followers(&self, dispatcher: &Dispatcher) {
        match self {
            Scope::Loop { store, .. } => induction(store).hold_followers(dispatcher),
            Scope::Writer {
                store,
                writer,
                phase,
            } => {
                if phase.borrow().open() {
                    transaction_scope::transaction(store)
                        .writer_run_mut(*writer)
                        .body
                        .hold_followers(dispatcher);
                }
            }
        }
    }

    /// Open the request `package`, a claim of the scope's own pipeline.
    pub(super) fn begin(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Scope::Loop { store, schedule } => {
                schedule.borrow_mut().begin(store, dispatcher, package)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => phase
                .borrow_mut()
                .begin(store, *writer, dispatcher, package),
        }
    }

    /// End the round or attempt whose step claimed `package`, and start the next or complete
    /// the request.
    pub(super) fn step(&self, dispatcher: &Dispatcher, package: WorkPackage) {
        match self {
            Scope::Loop { store, schedule } => {
                schedule.borrow_mut().step(store, dispatcher, package)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => phase.borrow_mut().step(store, *writer, dispatcher, package),
        }
    }

    /// Begin the finish of the scope's pipeline: it drains the body, and its step's finish ends
    /// it ([`finish_step`](Self::finish_step)).
    pub(super) fn begin_finish(&self, dispatcher: &Dispatcher) {
        match self {
            Scope::Loop { store, schedule } => {
                let mut schedule = schedule.borrow_mut();
                induction(store).begin_shared_finish(&mut schedule, dispatcher);
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => {
                let mut phase = phase.borrow_mut();
                transaction_scope::transaction(store)
                    .begin_transaction_finish(&mut phase, dispatcher, *writer);
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
                let mut schedule = schedule.borrow_mut();
                schedule.take_finish(induction(store).body_mut(), dispatcher)
            }
            Scope::Writer {
                store,
                writer,
                phase,
            } => {
                let mut phase = phase.borrow_mut();
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
    /// once its store is open. Whether it queued or closed anything.
    pub(super) fn queue_requests(&self, dispatcher: &Dispatcher) -> bool {
        match self {
            Scope::Loop { .. } => self.with_body(|body| body.queue_offered(dispatcher, true)),
            Scope::Writer { store, writer, .. } => {
                transaction_scope::transaction(store).queue_requests(dispatcher, *writer)
            }
        }
    }

    /// Whether the body's held output is published and its follower hold settled, and the guard
    /// of the open round's or attempt's step.
    fn schedule(&self) -> (bool, Option<TileGuard>) {
        match self {
            Scope::Loop { schedule, .. } => {
                let schedule = schedule.borrow();
                (schedule.publishing(), schedule.step_guard().cloned())
            }
            Scope::Writer { phase, .. } => {
                let phase = phase.borrow();
                (phase.open(), phase.step_guard().cloned())
            }
        }
    }
}

/// A scope's settlement: its body's members, fixed when the plan attaches the body.
struct LocalSteps {
    scope: Rc<Scope>,
    request: PipelineId,
    step: PipelineId,
    base: usize,
    members: Vec<PublicationTarget>,
}

/// Where a scope publishes one inner pipeline's held output: a chain's breaker, or a nested loop.
enum PublicationTarget {
    Chain(BreakerHandle),
    Child(Rc<Scope>),
}

/// Every scope of a run, each settling its own body and queueing its own step.
#[derive(Default)]
pub(super) struct ScopeSteps {
    scopes: Vec<LocalSteps>,
}

impl ScopeSteps {
    /// The settlement of each of `scopes`, attached; a nested loop's scope among them.
    pub(super) fn plan(scopes: impl Iterator<Item = Rc<Scope>>) -> Self {
        let scopes: Vec<_> = scopes
            .map(|scope| (scope.with_body(|body| body.attached().pipeline.0), scope))
            .collect();
        let by_id: HashMap<_, _> = scopes.iter().map(|(id, scope)| (*id, scope)).collect();
        let scopes = scopes
            .iter()
            .map(|(_, scope)| {
                scope.with_body(|body| LocalSteps {
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
                            Member::Scope(_) => PublicationTarget::Child(Rc::clone(
                                by_id
                                    .get(&body.global(PipelineId(local)).0)
                                    .expect("a nested loop's scope is attached"),
                            )),
                        })
                        .collect(),
                })
            })
            .collect();
        Self { scopes }
    }

    /// Settle each scope's body and queue its step where its round or attempt has run. Whether
    /// any scope changed anything.
    pub(super) fn poll(&self, dispatcher: &Dispatcher) -> bool {
        let mut advanced = false;
        for scope in &self.scopes {
            advanced |= scope.settle(dispatcher);
        }
        advanced
    }
}

impl LocalSteps {
    /// Open a flat loop's seed, admit what the scope was offered, and while the body runs publish
    /// what its members hold: once a pass publishes nothing, release the body's followers and
    /// queue the step. Whether anything changed.
    fn settle(&self, dispatcher: &Dispatcher) -> bool {
        let (publishing, guard) = self.scope.schedule();
        // Only the loop's own inputs can affect its seed, so the seed opens once they have
        // consumed what they were queued.
        if let Scope::Loop { store, .. } = self.scope.as_ref()
            && dispatcher.states[self.request.0].phase.load() == Phase::Running
            && induction(store).initialize_seed_if(|| {
                dispatcher.quiescent(dispatcher.infos[self.request.0].reads.iter().copied())
            })
        {
            return true;
        }
        let admitted = self.scope.queue_requests(dispatcher);
        if !publishing
            || dispatcher.outstanding(self.step) != 0
            || !self.scope.with_body(|body| body.is_active())
        {
            return admitted;
        }
        if !self.scope.with_body(|body| body.followers_held()) {
            return admitted || guard.is_some_and(|guard| self.queue_step(dispatcher, &guard));
        }
        // A nested loop with an open request publishes through its own scope once the request
        // completes.
        let members = self.base..self.base + self.members.len();
        let published = push_held(
            dispatcher,
            &mut |id, call| match &self.members[id.0 - self.base] {
                PublicationTarget::Chain(handle) => call(&mut *handle.borrow_mut(), InputId::ONLY),
                PublicationTarget::Child(child) => {
                    if !child.has_request() {
                        child.reach(call);
                    }
                }
            },
            members.map(PipelineId),
        );
        if published {
            return true;
        }
        let released = self
            .scope
            .with_body(|body| body.release_followers(dispatcher));
        let queued = guard.is_some_and(|guard| self.queue_step(dispatcher, &guard));
        queued || released || admitted
    }

    fn queue_step(&self, dispatcher: &Dispatcher, guard: &TileGuard) -> bool {
        self.scope
            .with_body(|body| body.queue_step(dispatcher, guard))
    }
}

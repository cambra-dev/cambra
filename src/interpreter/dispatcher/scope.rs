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

    /// An unrelated transition can be holding its store. Its intake remains available for
    /// the next scope poll, including after its last read finished.
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
            Self::Request(scope) => scope.begin(dispatcher, package),
            Self::Step(scope) => scope.step(dispatcher, package),
            Self::Seed(..) => consume_with(dispatcher, reach, package),
        }
    }
}

/// The publication targets are fixed when the plan attaches the body.
struct LocalSteps {
    scope: Arc<Scope>,
    request: PipelineId,
    step: PipelineId,
    base: usize,
    members: Vec<PublicationTarget>,
}

enum PublicationTarget {
    Chain(BreakerHandle),
    Child(Arc<Scope>),
}

#[derive(Default)]
pub(super) struct ScopeSteps {
    groups: Vec<StepGroup>,
    /// Groups whose readiness can change when this pipeline makes progress.
    affected: Vec<Vec<usize>>,
    // shared-state-ok: group indices, claims and rotation cursors for this dispatcher run.
    work: Mutex<GroupWork>,
}

struct StepGroup {
    scopes: Vec<LocalSteps>,
}

#[derive(Default)]
struct GroupWork {
    phases: Vec<GroupPhase>,
    ready: VecDeque<(usize, usize)>,
    started: bool,
    /// Groups that could not inspect a busy handle. Recheck them once handlers have returned.
    verify: std::collections::BTreeSet<usize>,
}

enum GroupPhase {
    Idle { next: usize },
    Queued,
    Claimed { again: bool },
}

impl GroupWork {
    /// A wake during a claim survives its completion. Several wakes require one more visit.
    fn wake(&mut self, group: usize) -> bool {
        match &mut self.phases[group] {
            GroupPhase::Idle { next } => {
                self.ready.push_back((group, *next));
                self.phases[group] = GroupPhase::Queued;
                true
            }
            GroupPhase::Claimed { again } => {
                *again = true;
                false
            }
            GroupPhase::Queued => false,
        }
    }

    fn claim(&mut self) -> Option<(usize, usize)> {
        let (group, next) = self.ready.pop_front()?;
        self.phases[group] = GroupPhase::Claimed { again: false };
        Some((group, next))
    }

    fn complete(&mut self, group: usize, next: usize, advanced: bool) {
        let GroupPhase::Claimed { again } = self.phases[group] else {
            unreachable!("only the claimant completes a scope group")
        };
        self.phases[group] = GroupPhase::Idle { next };
        if advanced || again {
            self.wake(group);
        }
    }
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

        let mut steps = Self {
            affected: vec![Vec::new(); upstream.len()],
            ..Self::default()
        };
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
                                        .expect("a nested scope")
                                        .clone(),
                                ),
                            })
                            .collect(),
                    }
                }));
                stack.extend(&peers[id]);
            }
            // The same upstream walk includes body members, readers a seed waits for and
            // pipelines that can offer work to this group. Shared inputs can wake several groups.
            let group = steps.groups.len();
            let mut inputs: Vec<_> = connected.iter().map(|scope| scope.request.0).collect();
            while let Some(p) = inputs.pop() {
                if steps.affected[p].last() == Some(&group) {
                    continue;
                }
                steps.affected[p].push(group);
                inputs.extend(&upstream[p]);
            }
            steps.groups.push(StepGroup { scopes: connected });
            steps
                .work
                .get_mut()
                .unwrap()
                .phases
                .push(GroupPhase::Idle { next: 0 });
        }
        steps
    }

    pub(super) fn start(&self) {
        let mut work = self.work.lock().unwrap_or_else(PoisonError::into_inner);
        if !work.started {
            work.started = true;
            for group in 0..self.groups.len() {
                work.wake(group);
            }
        }
    }

    pub(super) fn wake(&self, dispatcher: &Dispatcher, pipeline: PipelineId) {
        let Some(groups) = self
            .affected
            .get(pipeline.0)
            .filter(|groups| !groups.is_empty())
        else {
            return;
        };
        let mut work = self.work.lock().unwrap_or_else(PoisonError::into_inner);
        let mut queued = false;
        for &group in groups {
            queued |= work.wake(group);
        }
        drop(work);
        if queued {
            dispatcher.wake_claimants();
        }
    }

    /// The activity reservation starts under the queue lock and covers publishing and requeueing.
    pub(super) fn settle_one<A>(
        &self,
        dispatcher: &Dispatcher,
        reserve: impl FnOnce() -> A,
    ) -> bool {
        if self.groups.is_empty() {
            return false;
        }
        let (claim, _activity) = {
            let mut work = self.work.lock().unwrap_or_else(PoisonError::into_inner);
            let Some(claim) = work.claim() else {
                return false;
            };
            (claim, reserve())
        };
        self.visit(dispatcher, claim, None);
        true
    }

    /// A nonblocking visit can miss a lock held by a reader outside the group. Once the run
    /// looks idle, retry these visits under the drain reservation before reporting quiescence.
    pub(super) fn verify_one(&self, dispatcher: &Dispatcher, generation: &Generation) -> bool {
        let claim = {
            let mut work = self.work.lock().unwrap_or_else(PoisonError::into_inner);
            if !work.ready.is_empty() {
                return true;
            }
            let Some(id) = work.verify.pop_first() else {
                return false;
            };
            let GroupPhase::Idle { next } = work.phases[id] else {
                work.verify.insert(id);
                return true;
            };
            work.phases[id] = GroupPhase::Claimed { again: false };
            (id, next)
        };
        self.visit(dispatcher, claim, Some(generation));
        true
    }

    fn visit(
        &self,
        dispatcher: &Dispatcher,
        (id, mut next): (usize, usize),
        quiet: Option<&Generation>,
    ) {
        let blocked = Cell::new(false);
        let advanced = self.groups[id].poll(dispatcher, &mut next, &blocked);
        let mut work = self.work.lock().unwrap_or_else(PoisonError::into_inner);
        work.complete(id, next, advanced);
        if blocked.get() || quiet.is_some_and(|generation| dispatcher.changed_since(generation)) {
            work.verify.insert(id);
        } else {
            work.verify.remove(&id);
        }
    }

    #[cfg(test)]
    pub(super) fn poll(&self, dispatcher: &Dispatcher) -> bool {
        // Hand-driven scope fixtures change their stores and queues outside the worker pool.
        let mut advanced = false;
        for group in 0..self.groups.len() {
            let mut work = self.work.lock().unwrap();
            work.wake(group);
            let (id, mut next) = work.claim().unwrap();
            drop(work);
            let changed = self.groups[id].poll(dispatcher, &mut next, &Cell::new(false));
            self.work.lock().unwrap().complete(id, next, false);
            advanced |= changed;
        }
        advanced
    }
}

impl StepGroup {
    fn poll(&self, dispatcher: &Dispatcher, next: &mut usize, blocked: &Cell<bool>) -> bool {
        if let [scope] = &self.scopes[..] {
            return scope.poll(dispatcher, true, blocked);
        }
        // Publish every body's held output before choosing a step. A queued or running
        // decision gets to land its input to peer scopes before the next decision.
        let mut published = false;
        for scope in &self.scopes {
            published |= scope.poll(dispatcher, false, blocked);
        }
        if published
            || self
                .scopes
                .iter()
                .any(|scope| !scope.ready_for_decision(dispatcher, blocked))
        {
            return published;
        }
        for index in (*next..self.scopes.len()).chain(0..*next) {
            if self.scopes[index].try_queue_step(dispatcher, blocked) {
                *next = (index + 1) % self.scopes.len();
                return true;
            }
        }
        false
    }
}

impl LocalSteps {
    fn with_schedule(
        &self,
        blocked: &Cell<bool>,
        f: impl FnOnce(bool, Option<&TileGuard>) -> bool,
    ) -> bool {
        match self.scope.as_ref() {
            Scope::Loop { schedule, .. } => schedule
                .try_lock()
                .inspect_err(|_| blocked.set(true))
                .ok()
                .is_some_and(|state| f(state.publishing(), state.step_guard())),
            Scope::Writer { phase, .. } => phase
                .try_lock()
                .inspect_err(|_| blocked.set(true))
                .ok()
                .is_some_and(|state| f(state.open(), state.step_guard())),
        }
    }

    // A peer commit may move the snapshot used by every writer in the store. Let their
    // drivers and proposal pipelines consume the previous snapshot before advancing it.
    fn ready_for_decision(&self, dispatcher: &Dispatcher, blocked: &Cell<bool>) -> bool {
        self.with_schedule(blocked, |_, _| {
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

    fn try_queue_step(&self, dispatcher: &Dispatcher, blocked: &Cell<bool>) -> bool {
        self.with_schedule(blocked, |_, guard| {
            guard.is_some_and(|guard| self.queue_step(dispatcher, guard, blocked))
        })
    }

    fn queue_step(&self, dispatcher: &Dispatcher, guard: &TileGuard, blocked: &Cell<bool>) -> bool {
        self.scope
            .store()
            .try_write()
            .inspect_err(|_| blocked.set(true))
            .is_ok_and(|mut store| self.scope.body_in(&mut store).queue_step(dispatcher, guard))
    }

    fn poll(&self, dispatcher: &Dispatcher, queue: bool, blocked: &Cell<bool>) -> bool {
        self.with_schedule(blocked, |publishing, guard| {
            self.settle(dispatcher, publishing, guard.filter(|_| queue), blocked)
        })
    }

    fn settle(
        &self,
        dispatcher: &Dispatcher,
        publishing: bool,
        guard: Option<&TileGuard>,
        blocked: &Cell<bool>,
    ) -> bool {
        let Ok(mut store) = self.scope.store().try_write() else {
            blocked.set(true);
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
        match try_push_held(
            dispatcher,
            members.map(PipelineId),
            |_| {},
            |id, call| {
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
            },
        ) {
            Publication::Busy => {
                blocked.set(true);
                admitted
            }
            Publication::Published => true,
            Publication::Settled => {
                let released = dispatcher.release_followers_if(hold, held);
                let queued = guard.is_some_and(|g| self.queue_step(dispatcher, g, blocked));
                queued || released || admitted
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wakes_during_a_claim_queue_exactly_one_more_visit() {
        let mut work = GroupWork {
            phases: vec![GroupPhase::Idle { next: 0 }, GroupPhase::Idle { next: 0 }],
            ..GroupWork::default()
        };
        assert!(work.wake(0));
        assert_eq!(work.claim(), Some((0, 0)));
        // The claimant has already inspected the scope. Two more inputs arrive before
        // it returns its cursor. A second worker can still claim the independent group.
        assert!(!work.wake(0));
        assert!(!work.wake(0));
        assert!(work.wake(1));
        assert_eq!(work.claim(), Some((1, 0)));
        assert_eq!(work.claim(), None);
        work.complete(1, 0, false);
        work.complete(0, 3, false);
        assert!(!work.wake(0), "an ordinary wake joins the queued retry");
        assert_eq!(work.claim(), Some((0, 3)));
        work.complete(0, 3, false);
        assert_eq!(work.claim(), None);
    }
}

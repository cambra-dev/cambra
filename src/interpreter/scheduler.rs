use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::ccl::FieldKey;
use crate::interpreter::CurryLevel;
use crate::interpreter::{
    Consumer, DataSourceDomainExtentImpl, Projection, dispatcher::Landing, dispatcher::Routes,
    tile_operators::Notified, value_probe::ProbeSlot,
};

/// A consumer handle shared by notification forwarders and deferred wakeups.
/// It carries notifications, not tile data.
pub type SharedConsumer = Rc<RefCell<dyn Consumer>>;

/// One operator's consumer, shared between its inputs, behind a gate: a [`Notified`] flag
/// set when a notification passes and cleared when the operator is pulled, and the region
/// passed since ([`Admission`]).
///
/// A notification carries no payload, so a second one that arrives before the operator has
/// been pulled, naming no key the ones passed since did not, says nothing they did not: they
/// have already reached every consumer downstream, and none of them has read this operator
/// since. One that names another key passes, since a consumer that acts on the region, as a
/// memo marks it dirty, has not heard of that key. Without the gate a change reaches a sink
/// once per path where notification paths branch and merge, and around a cycle it never
/// stops. A pull clears it whether or not it reads the input that notified, since a consumer
/// pulling the operator is what the notification asked for
/// (`src/interpreter/design-operators.md`, "The notification contract").
#[derive(Clone)]
pub struct GatedConsumer {
    shared: SharedConsumer,
    admission: Admission,
}

/// The gate of an operator's [`GatedConsumer`], for the operator's producer to take into its
/// base ([`ProducerBase::sharing`](crate::interpreter::tile_operators::ProducerBase::sharing)),
/// which clears it on every pull.
///
/// A gate no pull clears closes on the first notification, and from then on drops every
/// notification naming only keys that passed since, so the operator stops being woken for them
/// without any error. The token is not `Clone` and is
/// `#[must_use]`, so a `subscribe` that builds a shared consumer and leaves its gate unused does
/// not compile cleanly.
#[must_use = "a gate no pull clears drops every notification of keys that passed: pass it to \
              `ProducerBase::sharing`"]
pub struct Gate(pub(crate) Notified);

/// What a gate passes: the first notification after a pull, and after it one that names a key
/// nothing passed since that pull named. A pull clears the gate's flag, which starts the region
/// passed afresh. Clones share the flag and the region, so a forwarder reads what passed while
/// the consumer behind the gate is borrowed. The region is a union of what passed, not closed
/// over any tiling, so regions naming every tag of a tagged union whole do not make it
/// `Everything`: a later `Everything` passes once more, and the region is then `Everything`.
#[derive(Clone)]
pub(crate) struct Admission {
    gate: Notified,
    // shared-state-ok: the region a gate passed since the last pull, shared by the gate and the
    // forwarder that reads it on reentry; it names keys, never a tile.
    passed: Rc<RefCell<Projection>>,
}

impl Admission {
    /// An admission behind `gate`, which every pull of the operator clears.
    pub(crate) fn new(gate: Notified) -> Self {
        Admission {
            gate,
            passed: Rc::new(RefCell::new(Projection::Nothing)),
        }
    }

    /// Whether `arrived` passes, which records it as passed.
    pub(crate) fn admits(&self, arrived: &Projection) -> bool {
        let mut passed = self.passed.borrow_mut();
        if self.gate.mark_news() {
            *passed = arrived.clone();
            return true;
        }
        if arrived.minus(&passed) == Projection::Nothing {
            return false;
        }
        *passed = passed.union(arrived);
        true
    }

    /// Whether `arrived` would stop at the gate: the gate is closed, and what passed since the
    /// last pull names every key `arrived` names. Records nothing. A gate that passes every
    /// notification (`Notified::Always`) records nothing that says it was told, so it covers
    /// none.
    pub(crate) fn covers(&self, arrived: &Projection) -> bool {
        matches!(self.gate, Notified::Flag(_))
            && self.gate.is_set()
            && arrived.minus(&self.passed.borrow()) == Projection::Nothing
    }

    /// Clear the gate, as a pull of the operator does.
    pub(crate) fn reopen(&self) {
        self.gate.take();
    }
}

/// The consumer a gate guards: forwards a notification to `consumer` when the gate passes it.
struct Gated {
    admit: Admission,
    consumer: Box<dyn Consumer>,
}

impl Consumer for Gated {
    fn notify(&mut self, arrived: &Projection) {
        crate::interpreter::dispatcher::debug_assert_outside_a_run();
        debug_assert!(
            *arrived != Projection::Nothing,
            "no producer notifies of an empty region"
        );
        if self.admit.admits(arrived) {
            self.consumer.notify(arrived);
        }
    }

    /// A push passes the gate whatever it says, and leaves it as it is: every pushed region is a
    /// work package, which no pull replaces.
    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        self.consumer.push(region, landing);
    }

    fn route(&mut self, routes: &mut Routes) {
        self.consumer.route(routes);
    }
}

impl GatedConsumer {
    /// `consumer` behind `gate`, which the operator's producer must clear on every pull.
    pub fn new(consumer: Box<dyn Consumer>, gate: Notified) -> Self {
        let admission = Admission::new(gate);
        let shared: SharedConsumer = Rc::new(RefCell::new(Gated {
            admit: admission.clone(),
            consumer,
        }));
        Self { shared, admission }
    }

    /// The handle a wakeup queue holds or a producer re-arms.
    pub fn shared(&self) -> &SharedConsumer {
        &self.shared
    }

    /// Notify the operator's consumer now, through the gate.
    pub fn notify(&self, arrived: &Projection) {
        self.shared.borrow_mut().notify(arrived);
    }
}

/// Share one operator's consumer between several of its inputs.
///
/// An operator with more than one input has a single downstream consumer to wake,
/// so the handle has to be shared. This is the one way to build that handle. The
/// operator's producer takes the [`Gate`] into its base
/// ([`ProducerBase::sharing`](crate::interpreter::tile_operators::ProducerBase::sharing)).
pub fn shared_consumer(consumer: Box<dyn Consumer>) -> (GatedConsumer, Gate) {
    let gate = Notified::clear();
    (GatedConsumer::new(consumer, gate.clone()), Gate(gate))
}

/// A fresh `Box<dyn Consumer>` forwarding to `shared` — what `subscribe` wants for
/// an input whose notifications should reach the operator's own consumer.
///
/// The closure is not ceremony: a `Box<Rc<RefCell<dyn Consumer>>>` is not itself a
/// `Consumer`, because the blanket impl over `Rc<RefCell<C>>` needs a *sized* `C`,
/// and `dyn Consumer` is not. Wrapping the wake in a closure gives the blanket
/// impl something sized to bite on.
///
/// The consumer forwards every notification as [`Projection::Everything`] ([`widening`]): an
/// input's keys say nothing of the operator's own unless the operator's outermost keys are its
/// input's, which [`forwarding_consumer_keeping_keys`] is for, or its input's under a tag, which
/// [`forwarding_consumer_tagging`] is for.
pub fn forwarding_consumer(shared: &GatedConsumer, wakeups: &WakeupQueue) -> Box<dyn Consumer> {
    widening(forwarding_consumer_keeping_keys(shared, wakeups))
}

/// [`forwarding_consumer`] for an input whose outermost keys are the operator's: its region is
/// forwarded as it is.
pub fn forwarding_consumer_keeping_keys(
    shared: &GatedConsumer,
    wakeups: &WakeupQueue,
) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        gated: shared.clone(),
        wakeups: wakeups.clone(),
    })
}

/// [`forwarding_consumer`] for an arm of a tagged union, whose outermost keys are the arm's keys
/// under the arm's tag ([`tagging`]).
pub fn forwarding_consumer_tagging(
    shared: &GatedConsumer,
    wakeups: &WakeupQueue,
    tag: FieldKey,
) -> Box<dyn Consumer> {
    tagging(tag, forwarding_consumer_keeping_keys(shared, wakeups))
}

/// `consumer` behind a consumer that forwards every notification as [`Projection::Everything`].
///
/// An operator passes this to its input in place of its own consumer unless its outermost keys
/// are its input's: the input's region names the input's keys, which say nothing of the
/// operator's own.
pub fn widening(consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(Widening(consumer))
}

struct Widening(Box<dyn Consumer>);

impl Consumer for Widening {
    fn notify(&mut self, _arrived: &Projection) {
        self.0.notify(&Projection::Everything);
    }

    /// A change widens to every key. A decided region passes as every key where its source is
    /// wholly decided, and not at all otherwise: each output key depends on every input key.
    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        match region {
            Projection::Everything => self.0.push(region, landing),
            _ if landing.is_wholly_decided() => self.0.push(&Projection::Everything, landing),
            _ if landing.is_decided() => {}
            _ => landing.widened(|landing| self.0.push(&Projection::Everything, landing)),
        }
    }

    /// A change widens, and a decided region that is not whole passes as nothing.
    fn route(&mut self, routes: &mut Routes) {
        routes.widened(|routes| routes.deciding_part(|routes| self.0.route(routes)));
    }
}

/// `consumer` behind a consumer that widens like [`widening`] except for a decided region, which it
/// passes as `restate` names it: the region of the operator's keys each of whose values the input
/// region decides. An operator that re-keys its input knows which of its keys an input key
/// contributes to, as `Uncurry` pairs an outer key with each inner key beneath it, so a decided
/// region of its input decides that region of its own keys, which [`widening`] would hold back
/// until the input is wholly decided.
pub fn widening_restating_decided(
    restate: fn(&Projection) -> Projection,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(WideningRestatingDecided(restate, consumer))
}

struct WideningRestatingDecided(fn(&Projection) -> Projection, Box<dyn Consumer>);

impl Consumer for WideningRestatingDecided {
    fn notify(&mut self, _arrived: &Projection) {
        self.1.notify(&Projection::Everything);
    }

    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        match region {
            Projection::Everything => self.1.push(region, landing),
            _ if landing.is_decided() => self.1.push(&(self.0)(region), landing),
            _ => landing.widened(|landing| self.1.push(&Projection::Everything, landing)),
        }
    }

    /// A change widens, so the path widens.
    fn route(&mut self, routes: &mut Routes) {
        routes.widened(|routes| self.1.route(routes));
    }
}

/// [`restating`] for a lookup's collection operand: the rows a key of the operand names read that
/// key and also their input's value, so the decided region it passes names only part of what
/// those rows depend on ([`Routes::deciding_part`]).
pub fn restating_lookup(
    restate: Box<dyn Fn(&Projection) -> Projection>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(RestatingLookup(Restating(restate, consumer)))
}

struct RestatingLookup(Restating);

impl Consumer for RestatingLookup {
    fn notify(&mut self, arrived: &Projection) {
        self.0.notify(arrived);
    }

    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        self.0.push(region, landing);
    }

    fn route(&mut self, routes: &mut Routes) {
        routes.deciding_part(|routes| self.0.route(routes));
    }
}

/// `consumer` behind a consumer that passes each region on as `restate` names it, a change as a
/// decided region: an operator that keeps its input's keys under another spelling, as `Uncurry`
/// beneath a standing level names an outer and an inner key as one pair, restates both exactly.
pub fn restating(
    restate: Box<dyn Fn(&Projection) -> Projection>,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    Box::new(Restating(restate, consumer))
}

struct Restating(Box<dyn Fn(&Projection) -> Projection>, Box<dyn Consumer>);

impl Consumer for Restating {
    fn notify(&mut self, arrived: &Projection) {
        self.1.notify(&(self.0)(arrived));
    }

    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        self.1.push(&(self.0)(region), landing);
    }

    /// The path keeps the keys, under another spelling.
    fn route(&mut self, routes: &mut Routes) {
        self.1.route(routes);
    }
}

/// `consumer` behind a consumer that forwards each notification as the same keys under `tag`
/// ([`Projection::tagged`]): an arm of a tagged union passes this to the arm's input, since
/// the union's outermost keys are each arm's keys under the arm's tag.
pub fn tagging(tag: FieldKey, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(Tagging(tag, consumer))
}

struct Tagging(FieldKey, Box<dyn Consumer>);

impl Consumer for Tagging {
    fn notify(&mut self, arrived: &Projection) {
        self.1.notify(&arrived.tagged(&self.0));
    }

    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        self.1.push(&region.tagged(&self.0), landing);
    }

    /// The arm's keys under its tag are the union's keys, so the path keeps them.
    fn route(&mut self, routes: &mut Routes) {
        self.1.route(routes);
    }
}

/// What [`forwarding_consumer_keeping_keys`] returns: it passes each region on as it arrives,
/// through the operator's gate. A wrapper in front of it restates the region ([`widening`],
/// [`tagging`]).
struct Forwarding {
    gated: GatedConsumer,
    wakeups: WakeupQueue,
}

impl Consumer for Forwarding {
    /// A push is passed on at once, past the gate. A push climbs from one breaker to the next, so
    /// one that re-enters a consumer it is passing through has met a cycle, which fails the run.
    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        match self.gated.shared.try_borrow_mut() {
            Ok(mut consumer) => consumer.push(region, landing),
            Err(_) => landing.reentered(),
        }
    }

    fn route(&mut self, routes: &mut Routes) {
        match self.gated.shared.try_borrow_mut() {
            Ok(mut consumer) => consumer.route(routes),
            Err(_) => routes.reentered(),
        }
    }

    fn notify(&mut self, arrived: &Projection) {
        let GatedConsumer { shared, admission } = &self.gated;
        // A notification that re-enters a consumer already being notified is deferred to
        // the next drain of the wakeup queue. A recurrence's notification graph is cyclic,
        // and nesting closes a cycle through *two* inputs of one operator: the inner store
        // sits downstream of the enclosing body and its read feeds back into it, so one
        // upstream change reaches the body's `Zip` along both arms. Delivering the second
        // inside the first would re-enter the consumer. Dropping it would lose a change the
        // call in progress may already have pulled past: a cascade can contain a pull, and
        // a wake after one carries what arrived too late for it. Deferred, it is delivered
        // outside any cascade, where it cannot re-enter, and at worst wakes a consumer
        // whose next pull finds nothing new.
        //
        // A re-entering notification the gate would stop is dropped instead: nothing has
        // pulled the operator since the notifications that passed, and they name every key this
        // one does. Deferring it would deliver it again on the next drain, and around a cycle
        // again on every poll after. One naming a key that has not passed is deferred, and
        // delivered as `Everything`, since the wakeup queue holds handles and not regions.
        match shared.try_borrow_mut() {
            Ok(mut consumer) => consumer.notify(arrived),
            Err(_) if admission.covers(arrived) => {}
            Err(_) => self.wakeups.request(shared.clone()),
        }
    }
}

/// `consumer` behind a consumer that forwards each region of the input's keys at level `at` as
/// the same paths one level in, with a component beneath the keys above `at` that admits anything:
/// an inverse (`Converse`) at `at` passes this to its input, whose keys at `at` stand beneath the
/// values that become its keys there. Each input key stands beneath exactly one value, so the
/// region names exactly the paths it changed. A region of the keys above `at` is forwarded as it
/// is, since those levels stand.
pub fn one_level_in(at: CurryLevel, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(OneLevelIn { at, consumer })
}

struct OneLevelIn {
    at: CurryLevel,
    consumer: Box<dyn Consumer>,
}

impl OneLevelIn {
    /// `region` one level in, `None` where it names keys beneath level `at`.
    fn restated(&self, region: &Projection) -> Option<Projection> {
        match region {
            Projection::Keys { level, keys } if *level == self.at => Some(Projection::keys_at(
                CurryLevel::new(level.index() + 1),
                keys.with_level_inserted(level.index(), level.index()),
            )),
            Projection::Keys { level, .. } if *level > self.at => None,
            standing => Some(standing.clone()),
        }
    }
}

impl Consumer for OneLevelIn {
    fn notify(&mut self, arrived: &Projection) {
        let restated = self.restated(arrived).unwrap_or(Projection::Everything);
        self.consumer.notify(&restated);
    }

    /// A decided region of the standing levels passes as it is. One that names keys at or beneath
    /// level `at` passes as every key where its source is wholly decided, and not at all
    /// otherwise: which output keys an input row stands beneath depends on its values, which no
    /// region carries.
    fn push(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        if landing.is_decided() {
            match region {
                Projection::Keys { level, .. } if *level >= self.at => {
                    if landing.is_wholly_decided() {
                        self.consumer.push(&Projection::Everything, landing);
                    }
                }
                standing => self.consumer.push(standing, landing),
            }
            return;
        }
        match self.restated(region) {
            Some(restated) => self.consumer.push(&restated, landing),
            None => landing.widened(|landing| self.consumer.push(&Projection::Everything, landing)),
        }
    }

    /// The input's keys stand one level in, so the path keeps them. A decided region beneath the
    /// standing levels that is not whole passes as nothing.
    fn route(&mut self, routes: &mut Routes) {
        routes.deciding_part(|routes| self.consumer.route(routes));
    }
}

/// Deferred notifications delivered outside the current pull or notification cascade.
/// Consumers are deduplicated by handle identity. A request during a drain waits for the
/// next drain. See `src/interpreter/design-operators.md`, "The notification contract".
#[derive(Clone, Default)]
pub struct WakeupQueue(Rc<RefCell<Vec<SharedConsumer>>>);

impl WakeupQueue {
    /// Request that `consumer` be notified at the next
    /// [`Scheduler::check_for_notifications`] — i.e. once the current `get`
    /// stack has fully unwound.
    ///
    /// Inside a compiled program's dispatched run a request is dropped: nothing delivers it there,
    /// and the producers in pull mode the run pulls read again where a store steps
    /// (`tile_operators::read_again_toward`).
    pub fn request(&self, consumer: SharedConsumer) {
        if crate::interpreter::dispatcher::is_in_a_run() {
            return;
        }
        // Notifications request another read; repeated requests do not count separate changes.
        let mut queued = self.0.borrow_mut();
        if queued.iter().any(|waiting| Rc::ptr_eq(waiting, &consumer)) {
            return;
        }
        queued.push(consumer);
    }

    /// Notify every queued consumer of `Everything`, outside the cascade that queued it, and say
    /// whether one was queued: [`Scheduler::deliver`] does so. A request made during the drain
    /// waits for the next one ([`take`](Self::take)).
    fn deliver(&self) -> bool {
        let mut delivered = false;
        for consumer in self.take() {
            consumer.borrow_mut().notify(&Projection::Everything);
            delivered = true;
        }
        delivered
    }

    /// Take the currently-queued wakeups, leaving the queue empty. A wakeup
    /// fired during the drain may enqueue a fresh request (a still-converging
    /// producer re-arming); that lands in the now-empty queue and is delivered
    /// by the next drain, not this one.
    fn take(&self) -> Vec<SharedConsumer> {
        std::mem::take(&mut *self.0.borrow_mut())
    }

    /// Whether a wakeup is waiting for the next drain.
    pub(crate) fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }
}

/// Poll registered source handles and deliver source notifications and deferred wakeups.
/// See `src/interpreter/design-operators.md`, "The notification contract".
#[derive(Default)]
pub struct Scheduler {
    source_handles: HashMap<String, SourceHandle>,
    wakeups: WakeupQueue,
    probes: ProbeSlot,
    /// The source producers registered under each subscription still in progress,
    /// innermost last — see [`begin_source_producers`](Self::begin_source_producers).
    producer_frames: Vec<Vec<String>>,
    /// Sinks' pulls, run after the wakes that queued them in the same call.
    sink_pulls: WakeupQueue,
}

type SourceHandle = (
    Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    Vec<Weak<RefCell<dyn Consumer>>>,
);

impl Scheduler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Every registered source, by name.
    ///
    /// The scheduler already holds these to poll them; a reader of a source's
    /// retained window needs the same handles and has nowhere else to get them.
    pub fn sources(
        &self,
    ) -> impl Iterator<Item = (&str, &Rc<RefCell<dyn DataSourceDomainExtentImpl>>)> + '_ {
        self.source_handles
            .iter()
            .map(|(name, (handle, _))| (name.as_str(), handle))
    }

    /// The probe slot every producer subscribed under this scheduler holds.
    ///
    /// The scheduler carries it because every `subscribe` already receives
    /// the scheduler, so a producer takes the slot at construction with no
    /// ambient state.
    pub fn probes(&self) -> &ProbeSlot {
        &self.probes
    }

    /// Open a frame recording every producer that registers with a data source
    /// until the matching [`end_source_producers`](Self::end_source_producers).
    ///
    /// A source producer is attributed to whatever subscribed it, so the branch
    /// table can say which producers a branch holds: a fan-out records the
    /// producers its input chain registered, and a compilation the producers its
    /// outputs registered (`src/ccl/design/program-evolution.md`, "Routes across
    /// branches"). Frames nest, because a fan-out's input is subscribed from
    /// inside a compilation's.
    pub fn begin_source_producers(&mut self) {
        self.producer_frames.push(Vec::new());
    }

    /// Close the innermost frame and return the producers registered in it.
    ///
    /// The producers are also added to the enclosing frame, so a frame's record
    /// covers every producer registered below it, including those under a nested
    /// fan-out.
    pub fn end_source_producers(&mut self) -> Vec<String> {
        let producers = self
            .producer_frames
            .pop()
            .expect("`end_source_producers` closes a frame `begin_source_producers` opened");
        if let Some(outer) = self.producer_frames.last_mut() {
            outer.extend(producers.iter().cloned());
        }
        producers
    }

    /// Record that the producer named `producer` registered with a data source.
    ///
    /// A registration outside every frame is attributed to nothing. Only a
    /// subscription made outside a compilation does that, which a test that
    /// subscribes an operator by hand is.
    pub fn note_source_producer(&mut self, producer: String) {
        if let Some(frame) = self.producer_frames.last_mut() {
            frame.push(producer);
        }
    }

    /// Register `consumer` to be notified when `handle` has new data.
    ///
    /// The registration is **weak**, and the subscriber that made it owns the
    /// consumer. A registration lasts exactly as long as the producer it wakes,
    /// which is what a source handle outliving the graph subscribed to it
    /// requires: replacing a program drops the operators it rebuilt, pruning
    /// their registrations, while an operator carried across the replacement
    /// keeps waking as before. A strong registration would instead keep every
    /// operator any version ever subscribed alive and being notified.
    pub fn add_source_handle(
        &mut self,
        handle: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        consumer: Weak<RefCell<dyn Consumer>>,
    ) {
        let id = handle.borrow().get_id().to_string();
        if let Some(entry) = self.source_handles.get_mut(&id) {
            assert!(
                Rc::ptr_eq(&handle, &entry.0),
                "two sources are registered as `{id}`, so a poll of one wakes the \
other's subscribers",
            );
            entry.1.push(consumer);
        } else {
            self.source_handles.insert(id, (handle, vec![consumer]));
        }
    }

    /// Stop polling the source registered as `id`.
    ///
    /// Called when a version stops serving the endpoint behind it
    /// ([`SourceSinkRegistry::retire_routes_absent_from`](crate::ccl::context::SourceSinkRegistry)).
    /// A source handle outlives the version that opened it, and nothing else ever
    /// removes one, so without this the scheduler polls a retired route's source
    /// for the life of the process. It is also what lets the address be served
    /// again: a re-opened route mints a fresh source under the same id, which
    /// `add_source_handle` refuses to register alongside the stale one.
    pub fn forget_source(&mut self, id: &str) {
        self.source_handles.remove(id);
    }

    /// A handle to the deferred-wakeup queue, for producers that must request
    /// their own re-pull (see [`WakeupQueue`]). Obtained at `subscribe` time and
    /// stored, since `get` has no access to the scheduler.
    pub fn wakeup_queue(&self) -> WakeupQueue {
        self.wakeups.clone()
    }

    /// The queue a sink schedules its pull on. A pull queued while [`deliver`](Self::deliver)
    /// delivers its wakes runs in the same call, after them.
    pub fn sink_pull_queue(&self) -> WakeupQueue {
        self.sink_pulls.clone()
    }

    /// Pull what each source has received into its buffer, and return the
    /// consumers to wake, without waking them.
    ///
    /// No consumer is notified, so no `get` runs and nothing is released. A
    /// source's retained window read between this and [`deliver`](Self::deliver)
    /// holds this pass's arrivals. After `deliver`, a sink has pulled them and a
    /// `Memo` may have released them.
    pub fn poll_sources(&mut self) -> Delivery {
        let mut woken = Vec::new();
        for (source, consumers) in self.source_handles.values_mut() {
            // Prune first, so a source whose every subscriber is gone stops
            // accumulating dead registrations across program reloads.
            consumers.retain(|c| c.strong_count() > 0);
            if source.borrow_mut().check_for_new_data() {
                woken.extend(consumers.iter().filter_map(Weak::upgrade));
            }
        }
        Delivery(woken)
    }

    /// Notify the consumers a [`poll_sources`](Self::poll_sources) found data
    /// for, then the deferred wakeups, then run the sink pulls they queued, and say
    /// whether anything was delivered. A sink pulls here, once per call.
    pub fn deliver(&mut self, mut delivery: Delivery) -> bool {
        let mut delivered = false;
        for consumer in std::mem::take(&mut delivery.0) {
            consumer.borrow_mut().notify(&Projection::Everything);
            delivered = true;
        }
        // Take the queue after source delivery, outside its notification cascades.
        delivered |= self.wakeups.deliver();
        // Then pull every sink the wakes above reached, once each, so a change reaches a
        // sink in the call that delivers it.
        for pull in self.sink_pulls.take() {
            pull.borrow_mut().notify(&Projection::Everything);
            delivered = true;
        }
        delivered
    }

    /// [`poll_sources`](Self::poll_sources) then [`deliver`](Self::deliver), for
    /// a caller with nothing to do between them. Says whether anything was
    /// delivered.
    pub fn check_for_notifications(&mut self) -> bool {
        let delivery = self.poll_sources();
        self.deliver(delivery)
    }
}

/// Pending source notifications returned by [`Scheduler::poll_sources`].
/// Holds consumers strongly until delivery, even if their registrations are dropped meanwhile.
/// [`Scheduler::deliver`] consumes it. Dropping a nonempty delivery leaves arrivals unannounced
/// and triggers a debug assertion unless the thread is unwinding.
#[must_use = "a polled delivery must be passed to `Scheduler::deliver`"]
pub struct Delivery(Vec<SharedConsumer>);

impl Drop for Delivery {
    fn drop(&mut self) {
        // Skipped while unwinding: a second panic in `Drop` aborts.
        if !std::thread::panicking() {
            debug_assert!(
                self.0.is_empty(),
                "a Delivery of {} consumer(s) was dropped without `Scheduler::deliver`",
                self.0.len(),
            );
        }
    }
}

/// Delivers, then pulls, up to `laps` times: the alternation `src/main.rs` runs.
/// Returns the last tile. Without delivery, a [`Notified`]-gated producer answers from its
/// cache instead of reading its input again.
/// Stops early when `done` succeeds or, after the first lap, no notification was delivered,
/// the result is unchanged and both wakeup and sink-pull queues are empty.
/// With zero laps, return an empty tile.
/// See `src/interpreter/design-operators.md`, "The notification contract".
#[cfg(any(test, feature = "test-helpers"))]
pub fn pull_laps(
    scheduler: &mut Scheduler,
    producer: &mut dyn crate::interpreter::tile_operators::TileProducer,
    laps: usize,
    done: impl Fn(&crate::interpreter::Tile) -> bool,
) -> crate::interpreter::Tile {
    let guard = producer.tiling().universal_guard();
    let mut tile = producer.tiling().empty_tile();
    for lap in 0..laps {
        let pulls_before = cfg!(debug_assertions).then(|| pull_counts(&*producer));
        let delivered = scheduler.check_for_notifications();
        let pulled = producer.get(guard.clone());
        if done(&pulled) {
            return pulled;
        }
        // Nothing was delivered, the pull answered what the last one did, and it queued no
        // wakeup, so every operator saw what it saw before and nothing moves until an input
        // changes: the laps left would only repeat this one. A wakeup this pull queued is
        // delivered by the next lap's check, so that lap is not a repeat.
        if lap > 0
            && !delivered
            && pulled == tile
            && scheduler.wakeups.is_empty()
            && scheduler.sink_pulls.is_empty()
        {
            let ignored = pulls_before
                .map(|before| ignored_inputs(&*producer, &before))
                .unwrap_or_default();
            debug_assert!(
                ignored.is_empty(),
                "a run came to rest with an operator whose consumer it woke, and which that \
                 consumer pulled again without pulling the operator: every later notification \
                 from the operator's inputs is dropped. {ignored:?}"
            );
            return pulled;
        }
        tile = pulled;
    }
    tile
}

/// Hand `each` every producer reachable from `root` through
/// [`TileProducer::visit_input_producers`], once: a fan-out's input is reached from each of its
/// slots, and a recurrence's from inside itself.
#[cfg(any(test, feature = "test-helpers"))]
fn each_producer(
    root: &dyn crate::interpreter::tile_operators::TileProducer,
    each: &mut dyn FnMut(&dyn crate::interpreter::tile_operators::TileProducer),
) {
    fn walk(
        producer: &dyn crate::interpreter::tile_operators::TileProducer,
        seen: &mut std::collections::HashSet<String>,
        each: &mut dyn FnMut(&dyn crate::interpreter::tile_operators::TileProducer),
    ) {
        if !seen.insert(producer.name()) {
            return;
        }
        each(producer);
        producer.visit_input_producers(&mut |_, input| walk(input, seen, each));
    }
    walk(root, &mut std::collections::HashSet::new(), each);
}

/// How often each producer reachable from `root` has been pulled, by name.
#[cfg(any(test, feature = "test-helpers"))]
fn pull_counts(
    root: &dyn crate::interpreter::tile_operators::TileProducer,
) -> HashMap<String, u64> {
    let mut counts = HashMap::new();
    each_producer(root, &mut |producer| {
        counts.insert(producer.name(), producer.base().pulls);
    });
    counts
}

/// Each operator reachable from `root` whose gate ([`shared_consumer`]) is closed while a
/// producer that pulls it has been pulled since `before`, with that producer.
///
/// A gate closes when a notification passes and opens when the operator is pulled, so it rests
/// on a rule nothing else checks: a consumer woken by an operator pulls that operator. While it
/// has not, every later notification from the operator's inputs naming only keys that passed is
/// dropped. A consumer that no
/// longer reads the operator owes it nothing (a finished read, a settled seed, a recurrence
/// whose last reader retired), so only one still pulled counts, and an operator released whole
/// is never pulled again.
#[cfg(any(test, feature = "test-helpers"))]
fn ignored_inputs(
    root: &dyn crate::interpreter::tile_operators::TileProducer,
    before: &HashMap<String, u64>,
) -> Vec<String> {
    let mut ignored = Vec::new();
    each_producer(root, &mut |consumer| {
        if before.get(&consumer.name()) == Some(&consumer.base().pulls) {
            return;
        }
        consumer.visit_input_producers(&mut |role, input| {
            let closed = input.base().gate.as_ref().is_some_and(Notified::is_set);
            if closed && !input.obsolete_guard().is_universal() {
                ignored.push(format!("{} ({role} of {})", input.name(), consumer.name()));
            }
        });
    });
    ignored
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::interpreter::tile_operators::test_helpers::{RegionLog, keys_between};

    fn keys(first: u64, last: u64) -> Projection {
        Projection::of(&keys_between(first, last)).expect("keys name a projection")
    }

    /// Between pulls a gate passes a notification only for keys it has not passed since the last
    /// pull: one within what passed stops at the gate, one naming another key passes.
    #[test]
    fn a_closed_gate_passes_only_keys_it_has_not_passed_since_the_last_pull() {
        let (log, regions) = RegionLog::new();
        let (gated, gate) = shared_consumer(Box::new(log));
        gated.notify(&keys(0, 3));
        gated.notify(&keys(1, 2));
        gated.notify(&keys(10, 12));
        gated.notify(&keys(11, 12));
        assert_eq!(*regions.borrow_mut(), [keys(0, 3), keys(10, 12)]);
        assert!(gate.0.take());
        // The pull starts the region passed afresh: keys that passed only before it pass again.
        gated.notify(&keys(10, 12));
        gated.notify(&keys(1, 2));
        // A region naming some keys that passed and some that did not passes whole.
        gated.notify(&keys(2, 5));
        assert_eq!(
            *regions.borrow_mut(),
            [
                keys(0, 3),
                keys(10, 12),
                keys(10, 12),
                keys(1, 2),
                keys(2, 5)
            ]
        );
    }

    /// A forwarder sends `Everything` unless its operator's keys are its input's.
    #[test]
    fn a_forwarder_sends_everything_unless_it_keeps_keys() {
        let (log, regions) = RegionLog::new();
        let (gated, gate) = shared_consumer(Box::new(log));
        let wakeups = WakeupQueue::default();
        forwarding_consumer(&gated, &wakeups).notify(&keys(2, 4));
        assert!(gate.0.take());
        forwarding_consumer_keeping_keys(&gated, &wakeups).notify(&keys(2, 4));
        assert_eq!(*regions.borrow_mut(), [Projection::Everything, keys(2, 4)]);
    }

    /// A closure consumer takes the notification and ignores its region.
    #[test]
    fn a_closure_consumer_ignores_the_region() {
        let count = Rc::new(RefCell::new(0));
        let count_c = count.clone();
        let mut consumer: Box<dyn Consumer> = Box::new(move || *count_c.borrow_mut() += 1);
        consumer.notify(&keys(2, 4));
        consumer.notify(&Projection::Everything);
        assert_eq!(*count.borrow_mut(), 2);
    }

    /// `widening` sends `Everything` whatever region it is notified of.
    #[test]
    fn widening_sends_everything_for_any_region() {
        let (log, regions) = RegionLog::new();
        let mut consumer = widening(Box::new(log));
        consumer.notify(&keys(2, 4));
        consumer.notify(&Projection::Everything);
        assert_eq!(
            *regions.borrow_mut(),
            [Projection::Everything, Projection::Everything]
        );
    }

    /// A forwarder that keeps keys passes each region on as it is, `Everything` included, and
    /// carries nothing from one notification to the next.
    #[test]
    fn a_keeping_forwarder_passes_each_region_unchanged() {
        let (log, regions) = RegionLog::new();
        let (gated, gate) = shared_consumer(Box::new(log));
        let mut input = forwarding_consumer_keeping_keys(&gated, &WakeupQueue::default());
        let sent = [keys(2, 4), Projection::Everything, keys(6, 7)];
        for region in &sent {
            input.notify(region);
            assert!(gate.0.take());
        }
        assert_eq!(*regions.borrow_mut(), sent);
    }

    /// The walk at rest names an operator whose gate is closed while a producer that pulls it
    /// was pulled without pulling it, and only that: not while that producer has not been
    /// pulled, and not once the operator is released whole.
    #[test]
    fn a_woken_operator_its_consumer_pulled_past_is_named() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        use crate::interpreter::tile_operators::{ProducerBase, TileProducer};
        use crate::interpreter::{BaseType, Extent, Tile, TileGuard, Tiling};

        /// A producer that answers without pulling its input.
        struct PullsPast {
            base: ProducerBase,
            input: Box<dyn TileProducer>,
        }
        impl TileProducer for PullsPast {
            crate::interpreter::tile_operators::impl_producer_base!();
            fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
                visit("input", &*self.input);
            }

            fn visit_input_producers_mut(
                &mut self,
                visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
            ) {
                visit("input", &mut *self.input);
            }
            fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
                self.tiling().empty_tile()
            }
            fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
        }

        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (woken, gate) = shared_consumer(Box::new(|| {}));
        let mut input = TestTileProducer::new(tiling.empty_tile(), tiling.clone());
        input.base = ProducerBase::unowned(TestTileProducer::alloc_id(), &tiling).sharing(gate);
        let mut consumer = PullsPast {
            base: ProducerBase::unowned(PullsPast::alloc_id(), &tiling),
            input: Box::new(input),
        };
        let before = pull_counts(&consumer);
        woken.notify(&Projection::Everything);
        assert!(
            ignored_inputs(&consumer, &before).is_empty(),
            "the consumer has not been pulled since"
        );
        consumer.get(tiling.universal_guard());
        let ignored = ignored_inputs(&consumer, &before);
        assert_eq!(ignored.len(), 1, "{ignored:?}");
        assert!(
            ignored[0].contains(&format!("(input of {})", consumer.name())),
            "{ignored:?}"
        );
        consumer.input.release(tiling.universal_guard());
        assert!(
            ignored_inputs(&consumer, &before).is_empty(),
            "an operator released whole is pulled no more"
        );
    }

    /// A notification that re-enters a consumer still being notified reaches it later rather
    /// than being lost: the downstream here pulls on notify, and the cascade then reaches the
    /// second arm, whose data changed after the pull.
    #[test]
    fn a_reentrant_wake_after_a_pull_in_the_cascade_is_not_lost() {
        use std::cell::Cell;
        let data = Rc::new(Cell::new(0u32));
        let seen = Rc::new(Cell::new(0u32));
        let feedback: Rc<RefCell<Option<Box<dyn Consumer>>>> = Rc::new(RefCell::new(None));
        let (d, s, fb) = (data.clone(), seen.clone(), feedback.clone());
        let gate = Notified::clear();
        let pulled = gate.clone();
        let downstream: Box<dyn Consumer> = Box::new(move || {
            // The pull of the operator, which clears its gate as `TileProducer::get` does.
            pulled.take();
            s.set(d.get());
            // The rest of the cascade, once: arm B's data changes, and its notification
            // re-enters the operator this notification is still inside.
            let rest = fb.borrow_mut().take();
            if let Some(mut arm_b) = rest {
                d.set(d.get() + 1);
                arm_b.notify(&Projection::Everything);
            }
        });
        let shared = GatedConsumer::new(downstream, gate);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared, &scheduler.wakeup_queue());
        *feedback.borrow_mut() = Some(forwarding_consumer(&shared, &scheduler.wakeup_queue()));
        arm_a.notify(&Projection::Everything);
        scheduler.check_for_notifications();
        assert_eq!(
            seen.get(),
            data.get(),
            "the downstream never pulled what arm B delivered after its pull"
        );
    }

    /// A second notification before the operator is pulled says nothing the first did not, so
    /// it stops at the gate; the operator's pull lets the next one through.
    #[test]
    fn a_shared_consumer_passes_one_notification_per_pull() {
        use std::cell::Cell;
        let notified = Rc::new(Cell::new(0u32));
        let n = notified.clone();
        let (shared, gate) = shared_consumer(Box::new(move || n.set(n.get() + 1)));
        let scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared, &scheduler.wakeup_queue());
        let mut arm_b = forwarding_consumer(&shared, &scheduler.wakeup_queue());
        arm_a.notify(&Projection::Everything);
        arm_b.notify(&Projection::Everything);
        assert_eq!(
            notified.get(),
            1,
            "the second arm's notification passed an unpulled gate"
        );
        // The operator's pull, as `TileProducer::get` makes it.
        gate.0.take();
        arm_b.notify(&Projection::Everything);
        assert_eq!(
            notified.get(),
            2,
            "the pull did not let the next notification through"
        );
    }

    /// A notification that comes back around a cycle into the consumer it started from, with
    /// nothing pulled since, is dropped rather than deferred: the one in progress already says
    /// everything it would, and a deferred copy would go around again on every poll.
    #[test]
    fn a_reentrant_wake_with_no_pull_since_is_dropped() {
        use std::cell::Cell;
        let notified = Rc::new(Cell::new(0u32));
        let feedback: Rc<RefCell<Option<Box<dyn Consumer>>>> = Rc::new(RefCell::new(None));
        let (n, fb) = (notified.clone(), feedback.clone());
        let downstream: Box<dyn Consumer> = Box::new(move || {
            n.set(n.get() + 1);
            // The cycle: arm B's notification re-enters the operator this one is inside.
            let rest = fb.borrow_mut().take();
            if let Some(mut arm_b) = rest {
                arm_b.notify(&Projection::Everything);
            }
        });
        // Nothing pulls the operator here, so its gate is never cleared.
        let (shared, _gate) = shared_consumer(downstream);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared, &scheduler.wakeup_queue());
        *feedback.borrow_mut() = Some(forwarding_consumer(&shared, &scheduler.wakeup_queue()));
        arm_a.notify(&Projection::Everything);
        assert!(
            scheduler.wakeups.is_empty(),
            "the re-entrant notification was deferred"
        );
        scheduler.check_for_notifications();
        assert_eq!(notified.get(), 1);
    }

    /// A notification that re-enters the consumer it started from naming a key that did not pass
    /// since the last pull is deferred, not dropped: the consumer has not heard of that key.
    /// Delivered on the drain, it passes the gate, which then stops a copy naming nothing new.
    #[test]
    fn a_reentrant_wake_naming_a_new_key_is_deferred() {
        let arrivals = Rc::new(RefCell::new(Vec::new()));
        let feedback: Rc<RefCell<Option<Box<dyn Consumer>>>> = Rc::new(RefCell::new(None));
        struct Log {
            arrivals: Rc<RefCell<Vec<Projection>>>,
            feedback: Rc<RefCell<Option<Box<dyn Consumer>>>>,
        }
        impl Consumer for Log {
            fn notify(&mut self, arrived: &Projection) {
                self.arrivals.borrow_mut().push(arrived.clone());
                // The cycle: arm B's notification, of other keys, re-enters the operator this
                // one is inside.
                let rest = self.feedback.borrow_mut().take();
                if let Some(mut arm_b) = rest {
                    arm_b.notify(&keys(2, 3));
                }
            }
        }
        let downstream = Box::new(Log {
            arrivals: arrivals.clone(),
            feedback: feedback.clone(),
        });
        // Nothing pulls the operator here, so its gate is never cleared.
        let (shared, _gate) = shared_consumer(downstream);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer_keeping_keys(&shared, &scheduler.wakeup_queue());
        *feedback.borrow_mut() = Some(forwarding_consumer_keeping_keys(
            &shared,
            &scheduler.wakeup_queue(),
        ));
        arm_a.notify(&keys(0, 1));
        assert!(
            !scheduler.wakeups.is_empty(),
            "the re-entrant notification of a new key was dropped"
        );
        scheduler.check_for_notifications();
        assert_eq!(*arrivals.borrow(), vec![keys(0, 1), Projection::Everything]);
        arm_a.notify(&keys(2, 3));
        assert_eq!(
            arrivals.borrow().len(),
            2,
            "a notification within what passed stops at the gate"
        );
    }

    /// A pull that answers what the last one did but queues a wakeup is not quiescence: the
    /// wakeup is delivered by the next lap, and the producer it wakes answers anew.
    #[test]
    fn a_pull_that_queues_a_wakeup_is_not_quiescent() {
        use crate::interpreter::tile_operators::{ProducerBase, TileProducer};
        use crate::interpreter::{BaseType, ColumnValue, Extent, Tile, TileGuard, Tiling};
        struct WakesOnSecondPull {
            base: ProducerBase,
            pulls: usize,
            woken: Rc<RefCell<bool>>,
            queue: WakeupQueue,
        }
        impl TileProducer for WakesOnSecondPull {
            fn base(&self) -> &ProducerBase {
                &self.base
            }
            fn base_mut(&mut self) -> &mut ProducerBase {
                &mut self.base
            }
            fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
                self.pulls += 1;
                if self.pulls == 2 {
                    let woken = self.woken.clone();
                    self.queue
                        .request(Rc::new(RefCell::new(move || *woken.borrow_mut() = true)));
                }
                // Nothing until woken: a scalar holding a value is its whole answer, so the
                // pull before the wakeup answers what the first did by having none.
                let values = match *self.woken.borrow_mut() {
                    true => vec![2],
                    false => Vec::new(),
                };
                Tile::Scalar(ColumnValue::Ints(values))
            }
            fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
        }
        let mut scheduler = Scheduler::new();
        let mut producer = WakesOnSecondPull {
            base: ProducerBase::unowned(0, &Tiling::Scalar(Extent::Base(BaseType::Int))),
            pulls: 0,
            woken: Rc::new(RefCell::new(false)),
            queue: scheduler.wakeup_queue(),
        };
        let tile = pull_laps(&mut scheduler, &mut producer, 8, |t| {
            *t == Tile::Scalar(ColumnValue::Ints(vec![2]))
        });
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![2])));
    }

    /// A source with new data, and a consumer that counts its notifications.
    fn polled_source() -> (Scheduler, Rc<RefCell<u32>>, SharedConsumer) {
        use crate::{
            ccl::Type,
            interpreter::{BaseType, Extent, TestDataSource},
        };
        let mut source = TestDataSource::new(
            "src",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        source.set_has_data(true);
        let count = Rc::new(RefCell::new(0u32));
        let count_c = count.clone();
        let consumer: SharedConsumer = Rc::new(RefCell::new(move || *count_c.borrow_mut() += 1));
        let mut scheduler = Scheduler::new();
        scheduler.add_source_handle(Rc::new(RefCell::new(source)), Rc::downgrade(&consumer));
        (scheduler, count, consumer)
    }

    /// A poll takes the data in and wakes nobody; the delivery wakes the
    /// consumer. The gap between them is where a source window is sampled,
    /// with the arrivals present and no sink yet pulled.
    #[test]
    fn a_poll_wakes_no_consumer_until_it_is_delivered() {
        let (mut scheduler, count, _consumer) = polled_source();
        let delivery = scheduler.poll_sources();
        assert_eq!(*count.borrow_mut(), 0, "polling notifies nobody");
        scheduler.deliver(delivery);
        assert_eq!(*count.borrow_mut(), 1);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "dropped without `Scheduler::deliver`")]
    fn a_delivery_dropped_undelivered_is_refused() {
        let (mut scheduler, _count, _consumer) = polled_source();
        let delivery = scheduler.poll_sources();
        drop(delivery);
    }

    /// A requested wakeup is not delivered synchronously — only by the next
    /// `check_for_notifications` — and it is delivered exactly once (the queue is
    /// drained). This is the between-pulls delivery that lets a self-advancing
    /// producer request a re-pull without notifying from inside `get`.
    #[test]
    fn wakeup_is_deferred_and_delivered_once() {
        let mut scheduler = Scheduler::new();
        let count = Rc::new(RefCell::new(0u32));
        let count_c = count.clone();
        let consumer: Rc<RefCell<dyn Consumer>> =
            Rc::new(RefCell::new(move || *count_c.borrow_mut() += 1));

        scheduler.wakeup_queue().request(consumer);
        // Deferred: nothing fires until the scheduler is polled.
        assert_eq!(*count.borrow_mut(), 0);

        scheduler.check_for_notifications();
        assert_eq!(*count.borrow_mut(), 1);

        // Drained: a second poll with no new request delivers nothing.
        scheduler.check_for_notifications();
        assert_eq!(*count.borrow_mut(), 1);
    }

    /// A wakeup requested *during* delivery lands in the next drain, not the
    /// current one — one poll delivers one round, so the driver keeps control of
    /// pacing (a still-converging producer re-arming does not run to completion
    /// inside a single `check_for_notifications`).
    #[test]
    fn wakeup_requested_during_delivery_defers_to_next_poll() {
        let mut scheduler = Scheduler::new();
        let queue = scheduler.wakeup_queue();
        let log = Rc::new(RefCell::new(Vec::<&'static str>::new()));

        let log_b = log.clone();
        let b: Rc<RefCell<dyn Consumer>> =
            Rc::new(RefCell::new(move || log_b.borrow_mut().push("b")));

        // A logs "a" and, mid-delivery, requests B.
        let log_a = log.clone();
        let queue_c = queue.clone();
        let a: Rc<RefCell<dyn Consumer>> = Rc::new(RefCell::new(move || {
            log_a.borrow_mut().push("a");
            queue_c.request(b.clone());
        }));

        queue.request(a);
        scheduler.check_for_notifications(); // delivers A; A's request for B defers
        assert_eq!(*log.borrow_mut(), vec!["a"]);
        scheduler.check_for_notifications(); // now delivers B
        assert_eq!(*log.borrow_mut(), vec!["a", "b"]);
        scheduler.check_for_notifications(); // nothing left
        assert_eq!(*log.borrow_mut(), vec!["a", "b"]);
    }

    /// `one_level_in` at a nested level forwards a region of the inverted level's keys one level
    /// in, beneath any value, passes a region of the standing keys above as it is, and widens a
    /// region of the keys beneath.
    #[test]
    fn one_level_in_restates_the_inverted_level_and_passes_the_standing_one() {
        use crate::interpreter::{Predicate, Value};
        struct Record(Rc<RefCell<Vec<Projection>>>);
        impl Consumer for Record {
            fn notify(&mut self, arrived: &Projection) {
                self.0.borrow_mut().push(arrived.clone());
            }
        }
        let arrivals = Rc::new(RefCell::new(Vec::new()));
        let mut consumer = one_level_in(CurryLevel::new(1), Box::new(Record(arrivals.clone())));
        let point = |k: u64| Predicate::point(Value::UInt(k));
        let standing = Projection::keys_at(CurryLevel::OUTERMOST, point(4));
        let inverted = Predicate::qualified(point(4), point(7));
        let beneath = Predicate::qualified(Predicate::qualified(point(4), point(7)), point(1));
        consumer.notify(&standing);
        consumer.notify(&Projection::keys_at(CurryLevel::new(1), inverted.clone()));
        consumer.notify(&Projection::keys_at(CurryLevel::new(2), beneath));
        assert_eq!(
            *arrivals.borrow(),
            vec![
                standing,
                Projection::keys_at(CurryLevel::new(2), inverted.with_level_inserted(1, 1)),
                Projection::Everything,
            ]
        );
    }
}

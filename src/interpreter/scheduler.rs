use crate::interpreter::LockNow;
use std::{
    collections::HashMap,
    sync::Mutex,
    sync::{Arc, Weak},
};

use smol_str::SmolStr;

use crate::ccl::provenance::NodeId;
use crate::interpreter::{
    Consumer, DataSourceDomainExtentImpl, Projection,
    tile_operators::{Breaker, BreakerHandle, Notified},
    value_probe::ProbeSlot,
};

/// A consumer handle shared by notification forwarders and deferred wakeups.
/// It carries notifications, not tile data.
pub type SharedConsumer = Arc<Mutex<dyn Consumer>>;

/// One operator's consumer, shared between its inputs, behind a gate: a [`Notified`] that holds
/// the regions the notifications it passed named, and is cleared when the operator is pulled.
///
/// A notification whose region is inside what already passed says nothing the first did not: the
/// first has already reached every consumer downstream, and none of them has read this operator
/// since. Without the gate a change reaches a sink once per path where notification paths branch
/// and merge, and around a cycle it never stops. A region outside what passed is news, so a
/// notification for another part of the input is not lost behind one nobody pulled for. A pull
/// clears it whether or not it reads the input that notified, since a consumer pulling the
/// operator is what the notification asked for (`src/interpreter/design-operators.md`, "The
/// notification contract").
#[derive(Clone)]
pub struct GatedConsumer {
    shared: SharedConsumer,
    gate: Notified,
    /// Whether the consumer behind the gate never pulls, so the gate is [`Notified::Always`].
    region_driven: bool,
}

/// The gate of an operator's [`GatedConsumer`], for the operator's producer to take into its
/// base ([`ProducerBase::sharing`](crate::interpreter::tile_operators::ProducerBase::sharing)),
/// which clears it on every pull.
///
/// A gate no pull clears closes on the first notification and drops every one after it, so
/// the operator stops being woken without any error. The token is not `Clone` and is
/// `#[must_use]`, so a `subscribe` that builds a shared consumer and leaves its gate unused does
/// not compile cleanly.
#[must_use = "a gate no pull clears drops every notification after the first: pass it to \
              `ProducerBase::sharing`"]
pub struct Gate(pub(crate) Notified);

/// The consumer a gate guards: forwards a notification to `consumer` when the gate passes it.
/// The rounds of absorbed notifications a [`Gated`] delivers inside one notification before a
/// debug build says its consumer pulled inside `notify`.
const MAX_ABSORBED_ROUNDS: usize = 8;

struct Gated {
    admit: Notified,
    consumer: Box<dyn Consumer>,
    /// Whether `consumer` never pulls. Such a consumer has no gate, `admit` being
    /// [`Notified::Always`], so no region waits behind one: a consumer that pulls reads whatever
    /// arrived in its pull, and a region-driven one is notified of each.
    region_driven: bool,
    /// The thread that notified a consumer that pulls first. Such a cell is notified from one
    /// thread only, the scheduler's, which is what lets the notification in progress deliver a
    /// region that re-entered it: a region left by another thread could miss that delivery.
    owner: Option<std::thread::ThreadId>,
}

impl Consumer for Gated {
    fn notify(&mut self, arrived: &Projection) {
        debug_assert!(
            *arrived != Projection::Nothing,
            "no producer notifies of an empty region"
        );
        debug_assert!(
            !self.region_driven || matches!(self.admit, Notified::Always),
            "a region-driven consumer has no gate, or a closed one would hold its regions back"
        );
        if !self.region_driven {
            let here = std::thread::current().id();
            debug_assert_eq!(
                *self.owner.get_or_insert(here),
                here,
                "a cell whose consumer pulls was notified from two threads"
            );
        }
        // A notification that re-enters this consumer while it is being notified cannot be
        // delivered inside the first, so the forwarder leaves its region with the gate
        // ([`Notified::hold_pending`]) and the notification in progress delivers it when it returns,
        // through the gate, until nothing is left. Only a region outside what the gate passed
        // reaches the consumer, and the gate only grows until a pull, so a cycle of such
        // notifications ends inside the one that started it.
        //
        // That holds for a consumer that does not pull this operator inside `notify`: a sink
        // queues its pull, and a consumer that pulls does so after its wake returns. A pull
        // inside `notify` resets the gate, so a cascade that re-enters the cell each time would
        // pass the same region again every round, which the bound below catches in debug builds.
        // A consumer that obeys the rule cannot reset the gate, so each round needs a region
        // outside what has passed, and the cascade that makes them is finite.
        let mut region = arrived.clone();
        let mut rounds = 0;
        loop {
            if self.admit.mark_news_of(&region) {
                self.consumer.notify(&region);
            }
            region = self.admit.take_pending();
            if region == Projection::Nothing {
                break;
            }
            rounds += 1;
            debug_assert!(
                rounds <= MAX_ABSORBED_ROUNDS,
                "a consumer behind a gate pulled its operator inside `notify` and its cascade \
                 re-entered the cell each time: {rounds} rounds, the last of {region:?}"
            );
        }
    }

    fn region_driven(&self) -> bool {
        self.region_driven
    }
}

impl GatedConsumer {
    /// `consumer` behind `gate`, which the operator's producer must clear on every pull. A
    /// consumer that never pulls gets no gate to clear, so `gate` is replaced by
    /// [`Notified::Always`] for it. Private: [`shared_consumer`] builds the gate and hands its
    /// token to the caller, so no caller holds a clone the forwarder never reads.
    fn new(consumer: Box<dyn Consumer>, gate: Notified) -> Self {
        let region_driven = consumer.region_driven();
        let gate = if region_driven {
            Notified::Always
        } else {
            gate
        };
        let shared: SharedConsumer = Arc::new(Mutex::new(Gated {
            admit: gate.clone(),
            consumer,
            region_driven,
            owner: None,
        }));
        Self {
            shared,
            gate,
            region_driven,
        }
    }

    /// The handle a wakeup queue holds or a producer re-arms.
    pub fn shared(&self) -> &SharedConsumer {
        &self.shared
    }

    /// Notify the operator's consumer now, through the gate.
    pub fn notify(&self, arrived: &Projection) {
        self.shared.lock_now().notify(arrived);
    }
}

/// Share one operator's consumer between several of its inputs.
///
/// An operator with more than one input has a single downstream consumer to wake,
/// so the handle has to be shared. This is the one way to build that handle. The
/// operator's producer takes the [`Gate`] into its base
/// ([`ProducerBase::sharing`](crate::interpreter::tile_operators::ProducerBase::sharing)).
pub fn shared_consumer(consumer: Box<dyn Consumer>) -> (GatedConsumer, Gate) {
    let gated = GatedConsumer::new(consumer, Notified::clear());
    let gate = Gate(gated.gate.clone());
    (gated, gate)
}

/// A fresh `Box<dyn Consumer>` forwarding to `shared` — what `subscribe` wants for
/// an input whose notifications should reach the operator's own consumer.
///
/// The closure is not ceremony: a `Box<Arc<Mutex<dyn Consumer>>>` is not itself a
/// `Consumer`, because the blanket impl over `Arc<Mutex<C>>` needs a *sized* `C`,
/// and `dyn Consumer` is not. Wrapping the wake in a closure gives the blanket
/// impl something sized to bite on.
///
/// The consumer forwards every notification as [`Projection::Everything`]: an input's keys say
/// nothing of the operator's own unless the operator's outermost keys are its input's, which
/// [`forwarding_consumer_keeping_keys`] is for.
pub fn forwarding_consumer(shared: &GatedConsumer) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        gated: shared.clone(),
        route: Route::Widen,
    })
}

/// [`forwarding_consumer`] for an input whose outermost keys are the operator's: its region is
/// forwarded as it is.
pub fn forwarding_consumer_keeping_keys(shared: &GatedConsumer) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        gated: shared.clone(),
        route: Route::Keys,
    })
}

/// [`forwarding_consumer`] for an input that is a product the operator passes on: its region,
/// including a region of fields, is forwarded as it is.
pub fn forwarding_consumer_passing_regions(shared: &GatedConsumer) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        gated: shared.clone(),
        route: Route::Region,
    })
}

/// `consumer` behind a consumer for the record the operator selects the field `name` of: it
/// forwards a region of that field, sends nothing for a region of other fields only, and sends
/// `Everything` for any other region.
pub fn selecting_field(name: SmolStr, consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(SelectingField { name, consumer })
}

struct SelectingField {
    name: SmolStr,
    consumer: Box<dyn Consumer>,
}

impl Consumer for SelectingField {
    fn notify(&mut self, arrived: &Projection) {
        match arrived {
            Projection::Fields(fields) => {
                if let Some(region) = fields.get(&self.name) {
                    self.consumer.notify(region);
                }
            }
            _ => self.consumer.notify(&Projection::Everything),
        }
    }

    fn region_driven(&self) -> bool {
        self.consumer.region_driven()
    }
}

/// [`forwarding_consumer`] for the input that is the field `name` of the record the operator
/// makes of its inputs, whose fields are `names`: its region is forwarded as the region of that
/// field.
pub fn forwarding_consumer_into_field(
    shared: &GatedConsumer,
    name: SmolStr,
    names: Arc<[SmolStr]>,
) -> Box<dyn Consumer> {
    Box::new(Forwarding {
        gated: shared.clone(),
        route: Route::Field { name, names },
    })
}

/// `consumer` behind a consumer that forwards every notification as [`Projection::Everything`].
///
/// An operator passes this to its input in place of its own consumer unless its outermost keys
/// are its input's: the input's region names the input's keys, which say nothing of the
/// operator's own. The wrapper is as region-driven as `consumer`.
pub fn widening(consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(Widening(consumer))
}

struct Widening(Box<dyn Consumer>);

/// `consumer` behind a consumer that sends [`Projection::Everything`] for a region of fields and
/// any other region as it is.
///
/// An operator that keeps its input's keys passes this to its input: a region of fields names a
/// change inside a record, which only an operator that routes by field can place in its own
/// output, and the keys of the operator's output are not the fields of its input.
pub fn keys_only(consumer: Box<dyn Consumer>) -> Box<dyn Consumer> {
    Box::new(KeysOnly(consumer))
}

struct KeysOnly(Box<dyn Consumer>);

impl Consumer for KeysOnly {
    fn notify(&mut self, arrived: &Projection) {
        self.0.notify(&arrived.keys_only());
    }

    fn region_driven(&self) -> bool {
        self.0.region_driven()
    }
}

impl Consumer for Widening {
    fn notify(&mut self, _arrived: &Projection) {
        self.0.notify(&Projection::Everything);
    }

    fn region_driven(&self) -> bool {
        self.0.region_driven()
    }
}

/// What [`forwarding_consumer`] returns.
struct Forwarding {
    gated: GatedConsumer,
    route: Route,
}

/// What a forwarding consumer sends for the region its input notified.
enum Route {
    /// `Everything`.
    Widen,
    /// The region, with a region of fields widened to `Everything` ([`Projection::keys_only`]).
    Keys,
    /// The region as it is, a region of fields included.
    Region,
    /// The region as the region of one field of the record the operator makes of its inputs.
    Field {
        name: SmolStr,
        /// Every field of the record, so that a region of everything in each is everything.
        names: Arc<[SmolStr]>,
    },
}

impl Consumer for Forwarding {
    fn notify(&mut self, arrived: &Projection) {
        let GatedConsumer {
            shared,
            gate,
            region_driven,
        } = &self.gated;
        let region = match &self.route {
            Route::Widen => Projection::Everything,
            Route::Keys => arrived.keys_only(),
            Route::Region => arrived.clone(),
            Route::Field { name, names } => {
                Projection::fields(names.clone(), [(name.clone(), arrived.clone())])
            }
        };
        let region = &region;
        // Absorbing the notification of a consumer that never pulls into one in progress would
        // leave its region to a notification that may never return to it, so the forwarder
        // waits for the cell. The notification graph of a region-driven chain is acyclic, so a
        // cascade does not reach one cell twice, and a cell downstream of a region-driven
        // consumer is itself region-driven, so a thread that holds one such cell waits only for
        // cells further along. That orders the cells' locks and nothing else: the thread that
        // notifies must hold no lock that the cascade takes
        // (`src/interpreter/design-operators.md`, "The notification contract").
        if *region_driven {
            shared.lock_wait().notify(region);
            return;
        }
        // A notification that re-enters a consumer already being notified is absorbed into
        // the one in progress. A recurrence's notification graph is cyclic, and nesting closes a
        // cycle through *two* inputs of one operator: the inner store sits downstream of the
        // enclosing body and its read feeds back into it, so one upstream change reaches the
        // body's `Zip` along both arms. Delivering the second inside the first would re-enter
        // the consumer, and dropping it would lose a change the call in progress may already
        // have pulled past: a cascade can contain a pull, and a wake after one carries what
        // arrived too late for it. So the region is left with the gate, and the notification in
        // progress delivers it through the gate when it returns ([`Gated`]): a region inside
        // what passed is suppressed there, which is what ends the cycle, and one outside it,
        // as the region of another field of a record is, reaches the consumer. No wake is
        // queued and no pull is needed.
        match shared.try_lock_now() {
            Some(mut consumer) => consumer.notify(region),
            None => gate.hold_pending(region),
        }
    }

    fn region_driven(&self) -> bool {
        self.gated.region_driven
    }
}

/// Deferred notifications delivered outside the current pull or notification cascade.
/// Consumers are deduplicated by handle identity. A request during a drain waits for the
/// next drain. See `src/interpreter/design-operators.md`, "The notification contract".
#[derive(Clone, Default)]
pub struct WakeupQueue(Arc<Mutex<Vec<SharedConsumer>>>);

impl WakeupQueue {
    /// Request that `consumer` be notified at the next
    /// [`Scheduler::check_for_notifications`] — i.e. once the current `get`
    /// stack has fully unwound.
    pub fn request(&self, consumer: SharedConsumer) {
        // Notifications request another read; repeated requests do not count separate changes.
        let mut queued = self.0.lock_now();
        if queued.iter().any(|waiting| Arc::ptr_eq(waiting, &consumer)) {
            return;
        }
        queued.push(consumer);
    }

    /// Take the currently-queued wakeups, leaving the queue empty. A wakeup
    /// fired during the drain may enqueue a fresh request (a still-converging
    /// producer re-arming); that lands in the now-empty queue and is delivered
    /// by the next drain, not this one.
    fn take(&self) -> Vec<SharedConsumer> {
        std::mem::take(&mut *self.0.lock_now())
    }

    /// Whether a wakeup is waiting for the next drain.
    pub(crate) fn is_empty(&self) -> bool {
        self.0.lock_now().is_empty()
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
    /// The pipeline breakers by the operator that made each, registered when the breaker's
    /// producer is subscribed and held weakly: the producer owns the breaker. The dispatcher finds
    /// a breaker here.
    breakers: HashMap<NodeId, Weak<dyn Breaker>>,
}

/// A consumer registered for a source, and whether the outermost keys of what it wakes are the
/// source's keys.
struct SourceConsumer {
    consumer: Weak<Mutex<dyn Consumer>>,
    outermost_keys: bool,
}

type SourceHandle = (
    Arc<Mutex<dyn DataSourceDomainExtentImpl>>,
    Vec<SourceConsumer>,
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
    ) -> impl Iterator<Item = (&str, &Arc<Mutex<dyn DataSourceDomainExtentImpl>>)> + '_ {
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

    /// Register the breaker the producer of `operator` is, when it is subscribed. A second
    /// registration for the operator replaces the first: a reload subscribes an operator it
    /// carried forward while the previous producer is alive, and the producer subscribed last is
    /// the one a run drives.
    pub fn register_breaker(&mut self, operator: NodeId, handle: &BreakerHandle) {
        self.breakers.insert(operator, Arc::downgrade(handle));
    }

    /// The breaker the producer of `operator` is, if it registered one that is still alive.
    pub fn breaker(&self, operator: NodeId) -> Option<BreakerHandle> {
        self.breakers.get(&operator)?.upgrade()
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
    ///
    /// `outermost_keys` says that the outermost keys of what the consumer wakes are the source's
    /// keys, as an `IterateExtent` over the source's domain has. A consumer registered for a source
    /// inside a record or a union is woken with `Everything` when only keys are named
    /// ([`Scheduler::notify_source_consumers`]).
    pub fn add_source_handle(
        &mut self,
        handle: Arc<Mutex<dyn DataSourceDomainExtentImpl>>,
        consumer: Weak<Mutex<dyn Consumer>>,
        outermost_keys: bool,
    ) {
        let consumer = SourceConsumer {
            consumer,
            outermost_keys,
        };
        let id = handle.lock_now().get_id().to_string();
        if let Some(entry) = self.source_handles.get_mut(&id) {
            assert!(
                Arc::ptr_eq(&handle, &entry.0),
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

    /// Notify the consumers registered for the source named `source` that the keys `arrived`
    /// have changed, without polling it, and say whether a consumer was notified. `arrived` names
    /// the keys whose rows or readiness changed. A consumer whose outermost keys are not the
    /// source's, because the source sits inside a record or a union in its extent, is woken with
    /// `Everything`: the source's keys say nothing of its own.
    ///
    /// This is the hook for a thread that writes a source's rows and knows which keys it wrote,
    /// where `deliver` can say only that something changed. It is `pub`, and nothing calls it
    /// outside tests yet: no source reports its own arrival regions. The caller has written the
    /// rows and made their keys ready before it notifies, and holds no lock the cascade takes: the
    /// live source's state lock, the source's `Mutex`, the pool dispatcher's locks and the lock
    /// that parks idle workers. The source's `check_for_new_data` is not consulted, so a pending
    /// report of the same arrival is still delivered by the next poll, as `Everything`.
    pub fn notify_source_consumers(&mut self, source: &str, arrived: &Projection) -> bool {
        let Some((_, consumers)) = self.source_handles.get_mut(source) else {
            return false;
        };
        consumers.retain(|c| c.consumer.strong_count() > 0);
        let woken: Vec<(SharedConsumer, bool)> = consumers
            .iter()
            .filter_map(|c| Some((c.consumer.upgrade()?, c.outermost_keys)))
            .collect();
        for (consumer, outermost_keys) in &woken {
            let region = match outermost_keys {
                true => arrived,
                false => &Projection::Everything,
            };
            consumer.lock_now().notify(region);
        }
        !woken.is_empty()
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
            consumers.retain(|c| c.consumer.strong_count() > 0);
            if source.lock_wait().check_for_new_data() {
                woken.extend(consumers.iter().filter_map(|c| c.consumer.upgrade()));
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
            consumer.lock_now().notify(&Projection::Everything);
            delivered = true;
        }
        // Take the queue after source delivery, outside its notification cascades.
        // Requests created while this snapshot drains remain queued for the next drain.
        for consumer in self.wakeups.take() {
            consumer.lock_now().notify(&Projection::Everything);
            delivered = true;
        }
        // Then pull every sink the wakes above reached, once each, so a change reaches a
        // sink in the call that delivers it.
        self.pull_sinks() || delivered
    }

    /// Pull every sink that a wake queued a pull for, once each, and say whether there was one.
    /// [`deliver`](Self::deliver) ends with this, and a loop that serves a pool between the
    /// delivery and the pulls calls it after the pool's turn, which is where a sink behind a
    /// breaker is woken.
    pub fn pull_sinks(&mut self) -> bool {
        let mut pulled = false;
        for pull in self.sink_pulls.take() {
            pull.lock_now().notify(&Projection::Everything);
            pulled = true;
        }
        pulled
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
/// A gate closes when a notification passes and opens when the operator is pulled, so it rests on a
/// rule nothing else checks: a consumer woken by an operator pulls that operator. While it has not,
/// every later notification from the operator's inputs whose region is inside what passed is
/// suppressed. A consumer that no longer reads the operator owes it nothing (a finished read, a
/// settled seed, a recurrence whose last reader retired), so only one still pulled counts, and an
/// operator released whole is never pulled again.
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
    use smol_str::SmolStr;

    fn keys(first: u64, last: u64) -> Projection {
        Projection::of(&keys_between(first, last)).expect("keys name a projection")
    }

    /// A consumer that pulls is not notified of a region inside what passed since its last pull,
    /// and a pull opens the gate again.
    #[test]
    fn a_closed_gate_suppresses_a_region_inside_what_passed_for_a_consumer_that_pulls() {
        let (log, regions) = RegionLog::new(false);
        let (gated, gate) = shared_consumer(Box::new(log));
        gated.notify(&keys(0, 3));
        gated.notify(&keys(1, 2));
        assert_eq!(*regions.lock_now(), [keys(0, 3)]);
        assert!(gate.0.take());
        gated.notify(&keys(30, 31));
        assert_eq!(*regions.lock_now(), [keys(0, 3), keys(30, 31)]);
    }

    /// A region outside what the gate passed passes at once, and one inside it waits for a pull.
    #[test]
    fn a_gated_consumer_passes_a_region_outside_what_passed() {
        let (log, regions) = RegionLog::new(false);
        let (gated, _gate) = shared_consumer(Box::new(log));
        gated.notify(&keys(0, 3));
        gated.notify(&keys(10, 12));
        gated.notify(&keys(11, 11));
        assert_eq!(*regions.lock_now(), [keys(0, 3), keys(10, 12)]);
    }

    /// A consumer that never pulls has no gate to reopen, so every notification reaches it, whole
    /// and in order, through the forwarder of an operator's input.
    #[test]
    fn a_consumer_that_never_pulls_is_not_gated() {
        let (log, regions) = RegionLog::new(true);
        let (gated, _gate) = shared_consumer(Box::new(log));
        let mut input = forwarding_consumer_keeping_keys(&gated);
        assert!(input.region_driven());
        for region in [keys(0, 3), keys(4, 7), keys(8, 9)] {
            input.notify(&region);
        }
        assert_eq!(*regions.lock_now(), [keys(0, 3), keys(4, 7), keys(8, 9)]);
    }

    /// A forwarder sends `Everything` unless its operator's keys are its input's.
    #[test]
    fn a_forwarder_sends_everything_unless_it_keeps_keys() {
        let (log, regions) = RegionLog::new(true);
        let (gated, _gate) = shared_consumer(Box::new(log));
        forwarding_consumer(&gated).notify(&keys(2, 4));
        forwarding_consumer_keeping_keys(&gated).notify(&keys(2, 4));
        assert_eq!(*regions.lock_now(), [Projection::Everything, keys(2, 4)]);
    }

    /// A closure consumer takes the notification and ignores its region.
    #[test]
    fn a_closure_consumer_ignores_the_region() {
        let count = Arc::new(Mutex::new(0));
        let count_c = count.clone();
        let mut consumer: Box<dyn Consumer> = Box::new(move || *count_c.lock_now() += 1);
        consumer.notify(&keys(2, 4));
        consumer.notify(&Projection::Everything);
        assert_eq!(*count.lock_now(), 2);
    }

    /// `widening` sends `Everything` whatever region it is notified of.
    #[test]
    fn widening_sends_everything_for_any_region() {
        let (log, regions) = RegionLog::new(true);
        let mut consumer = widening(Box::new(log));
        consumer.notify(&keys(2, 4));
        consumer.notify(&Projection::Everything);
        assert_eq!(
            *regions.lock_now(),
            [Projection::Everything, Projection::Everything]
        );
    }

    fn fields_of(region: Projection) -> Projection {
        Projection::field_of(&["a", "b"], "a", region)
    }

    /// A region of fields becomes everything where an operator keeps its input's keys, and any
    /// other region passes.
    #[test]
    fn keys_only_widens_a_region_of_fields_and_passes_any_other() {
        let (log, regions) = RegionLog::new(true);
        let mut consumer = keys_only(Box::new(log));
        let sent = [
            fields_of(keys(2, 4)),
            keys(2, 4),
            Projection::Everything,
            fields_of(Projection::Everything),
        ];
        for region in &sent {
            consumer.notify(region);
        }
        assert_eq!(
            *regions.lock_now(),
            [
                Projection::Everything,
                keys(2, 4),
                Projection::Everything,
                Projection::Everything
            ]
        );
    }

    /// A forwarder that keeps keys widens a region of fields, and one that does not widens
    /// everything.
    #[test]
    fn a_forwarder_that_keeps_keys_widens_a_region_of_fields() {
        let (log, regions) = RegionLog::new(true);
        let (gated, gate) = shared_consumer(Box::new(log));
        forwarding_consumer_keeping_keys(&gated).notify(&fields_of(keys(2, 4)));
        assert!(gate.0.take());
        forwarding_consumer_keeping_keys(&gated).notify(&keys(2, 4));
        assert_eq!(*regions.lock_now(), [Projection::Everything, keys(2, 4)]);
    }

    /// How many of `regions` a fresh gate passes with no pull between them.
    fn passes(regions: &[Projection]) -> usize {
        let gate = Notified::clear();
        regions
            .iter()
            .filter(|region| gate.mark_news_of(region))
            .count()
    }

    /// With every region `Everything` a gate is the flag it was: the first passes and the rest
    /// wait for a pull. `a_shared_consumer_passes_one_notification_per_pull`,
    /// `a_reentrant_wake_with_no_pull_since_is_dropped` and
    /// `a_reentrant_wake_after_a_pull_in_the_cascade_is_not_lost` run the recurrence's cyclic
    /// graph through it.
    #[test]
    fn a_gate_passes_the_first_everything_and_holds_the_rest_until_a_pull() {
        let gate = Notified::clear();
        let passed: Vec<bool> = (0..4)
            .map(|_| gate.mark_news_of(&Projection::Everything))
            .collect();
        assert_eq!(passed, [true, false, false, false]);
        assert!(gate.take());
        assert!(gate.mark_news_of(&Projection::Everything));
    }

    #[test]
    fn disjoint_regions_both_pass() {
        assert_eq!(passes(&[keys(1, 2), keys(5, 6)]), 2);
    }

    /// The gate holds the union of what passed, so a region inside any of it is suppressed.
    #[test]
    fn a_region_inside_the_union_of_what_passed_is_suppressed() {
        assert_eq!(passes(&[keys(1, 2), keys(5, 6), keys(1, 2), keys(5, 6)]), 2);
    }

    #[test]
    fn a_region_inside_what_passed_is_suppressed() {
        assert_eq!(passes(&[keys(1, 6), keys(2, 3), keys(1, 6)]), 1);
    }

    #[test]
    fn a_region_that_overlaps_what_passed_without_being_inside_it_passes() {
        assert_eq!(passes(&[keys(1, 4), keys(3, 6)]), 2);
    }

    #[test]
    fn a_pull_resets_what_the_gate_held() {
        let gate = Notified::clear();
        assert!(gate.mark_news_of(&keys(1, 4)));
        assert!(!gate.mark_news_of(&keys(2, 3)));
        assert!(gate.take());
        assert!(gate.mark_news_of(&keys(2, 3)));
        assert!(gate.take());
        assert!(!gate.take());
    }

    #[test]
    fn everything_after_keys_passes_and_keys_after_everything_are_suppressed() {
        assert_eq!(passes(&[keys(1, 2), Projection::Everything]), 2);
        assert_eq!(passes(&[Projection::Everything, keys(1, 2)]), 1);
        assert_eq!(passes(&[keys(1, 2), Projection::Everything, keys(5, 6)]), 2);
    }

    #[test]
    fn fields_follow_the_same_containment_rule() {
        let fields =
            |name: &str, region: Projection| Projection::field_of(&["a", "b", "c"], name, region);
        assert_eq!(
            passes(&[fields("a", keys(1, 4)), fields("b", keys(1, 4))]),
            2
        );
        assert_eq!(
            passes(&[fields("a", keys(1, 4)), fields("a", keys(2, 3))]),
            1
        );
        assert_eq!(
            passes(&[fields("a", keys(1, 2)), fields("a", keys(5, 6))]),
            2
        );
        assert_eq!(
            passes(&[fields("a", Projection::Everything), fields("a", keys(1, 2))]),
            1
        );
    }

    /// A record's gate that has passed every field's region as everything holds everything, so a
    /// later notification of everything, such as one a cycle brings around, is suppressed. Without
    /// the record's names the held regions never added up to everything, and it passed.
    #[test]
    fn a_gate_that_passed_every_field_as_everything_suppresses_a_later_everything() {
        let all = ["a", "b", "c"];
        let gate = Notified::clear();
        let passed: Vec<bool> = all
            .iter()
            .map(|name| {
                gate.mark_news_of(&Projection::field_of(&all, name, Projection::Everything))
            })
            .collect();
        assert_eq!(passed, [true, true, true]);
        assert!(gate.covers(&Projection::Everything));
        assert!(!gate.mark_news_of(&Projection::Everything));
        assert!(!gate.mark_news_of(&Projection::field_of(&all, "a", keys(1, 2))));
    }

    /// Two inputs of a `MakeRecord` that each notify everything reach the consumer behind it as
    /// two notifications, one per field, and a third round of them reaches it as none.
    #[test]
    fn make_record_inputs_that_notify_everything_reach_a_consumer_once_per_field() {
        let names: Arc<[SmolStr]> = vec![SmolStr::new("_0"), SmolStr::new("_1")].into();
        let (log, regions) = RegionLog::new(false);
        let (shared, _gate) = shared_consumer(keys_only(Box::new(log)));
        let mut inputs: Vec<Box<dyn Consumer>> = names
            .iter()
            .map(|name| forwarding_consumer_into_field(&shared, name.clone(), names.clone()))
            .collect();
        for _round in 0..3 {
            for input in &mut inputs {
                input.notify(&Projection::Everything);
            }
        }
        assert_eq!(
            *regions.lock_now(),
            [Projection::Everything, Projection::Everything]
        );
    }

    /// The gate holds what it passed, not what was delivered: a consumer behind it that drops a
    /// region still closes the gate to that region, and the next pull opens it.
    #[test]
    fn a_region_the_consumer_behind_the_gate_drops_still_closes_the_gate_to_it() {
        let (log, regions) = RegionLog::new(false);
        let (gated, gate) = shared_consumer(selecting_field(SmolStr::new("a"), Box::new(log)));
        let other = Projection::field_of(&["a", "b"], "b", keys(1, 2));
        let wanted = Projection::field_of(&["a", "b"], "a", keys(1, 2));
        gated.notify(&other);
        gated.notify(&other);
        gated.notify(&wanted);
        assert_eq!(*regions.lock_now(), [keys(1, 2)]);
        assert!(gate.0.take());
    }

    /// A forwarder that keeps keys passes each region on as it is, `Everything` included, and
    /// carries nothing from one notification to the next.
    #[test]
    fn a_keeping_forwarder_passes_each_region_unchanged() {
        let (log, regions) = RegionLog::new(true);
        let (gated, gate) = shared_consumer(Box::new(log));
        let mut input = forwarding_consumer_keeping_keys(&gated);
        let sent = [keys(2, 4), Projection::Everything, keys(6, 7)];
        for region in &sent {
            input.notify(region);
            assert!(gate.0.take());
        }
        assert_eq!(*regions.lock_now(), sent);
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
        use crate::interpreter::SyncCell;
        let data = Arc::new(SyncCell::new(0u32));
        let seen = Arc::new(SyncCell::new(0u32));
        let feedback: Arc<Mutex<Option<Box<dyn Consumer>>>> = Arc::new(Mutex::new(None));
        let (d, s, fb) = (data.clone(), seen.clone(), feedback.clone());
        let gate = Notified::clear();
        let pulled = gate.clone();
        let downstream: Box<dyn Consumer> = Box::new(move || {
            // The pull of the operator, which clears its gate as `TileProducer::get` does.
            pulled.take();
            s.set(d.get());
            // The rest of the cascade, once: arm B's data changes, and its notification
            // re-enters the operator this notification is still inside.
            let rest = fb.lock_now().take();
            if let Some(mut arm_b) = rest {
                d.set(d.get() + 1);
                arm_b.notify(&Projection::Everything);
            }
        });
        let shared = GatedConsumer::new(downstream, gate);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared);
        *feedback.lock_now() = Some(forwarding_consumer(&shared));
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
        use crate::interpreter::SyncCell;
        let notified = Arc::new(SyncCell::new(0u32));
        let n = notified.clone();
        let (shared, gate) = shared_consumer(Box::new(move || n.set(n.get() + 1)));
        let mut arm_a = forwarding_consumer(&shared);
        let mut arm_b = forwarding_consumer(&shared);
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
    /// nothing pulled since, is absorbed into the one in progress and suppressed there: the one in
    /// progress already says everything it would, and nothing is queued to go around again.
    #[test]
    fn a_reentrant_wake_with_no_pull_since_is_absorbed_and_suppressed() {
        use crate::interpreter::SyncCell;
        let notified = Arc::new(SyncCell::new(0u32));
        let feedback: Arc<Mutex<Option<Box<dyn Consumer>>>> = Arc::new(Mutex::new(None));
        let (n, fb) = (notified.clone(), feedback.clone());
        let downstream: Box<dyn Consumer> = Box::new(move || {
            n.set(n.get() + 1);
            // The cycle: arm B's notification re-enters the operator this one is inside.
            let rest = fb.lock_now().take();
            if let Some(mut arm_b) = rest {
                arm_b.notify(&Projection::Everything);
            }
        });
        // Nothing pulls the operator here, so its gate is never cleared.
        let (shared, _gate) = shared_consumer(downstream);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared);
        *feedback.lock_now() = Some(forwarding_consumer(&shared));
        arm_a.notify(&Projection::Everything);
        assert!(
            scheduler.wakeups.is_empty(),
            "the re-entrant notification queued a wake"
        );
        scheduler.check_for_notifications();
        assert_eq!(notified.get(), 1);
    }

    /// The consumer, its log, and the slot of the arm that feeds the cell it is inside.
    type Reentering = (
        Box<dyn Consumer>,
        Arc<Mutex<Vec<Projection>>>,
        Arc<Mutex<Option<Box<dyn Consumer>>>>,
    );

    /// A downstream consumer that logs what it is notified of and, each time, notifies `reentry`
    /// through the arm that feeds the cell it is inside.
    fn reentering(reentry: Projection) -> Reentering {
        let log: Arc<Mutex<Vec<Projection>>> = Arc::default();
        let arm: Arc<Mutex<Option<Box<dyn Consumer>>>> = Arc::default();
        let (log_c, arm_c) = (log.clone(), arm.clone());
        let consumer: Box<dyn Consumer> =
            Box::new(RegionTap(Box::new(move |region: &Projection| {
                log_c.lock_now().push(region.clone());
                if let Some(arm) = arm_c.lock_now().as_mut() {
                    arm.notify(&reentry);
                }
            })));
        (consumer, log, arm)
    }

    /// A consumer from a function of the region.
    struct RegionTap(Box<dyn FnMut(&Projection) + Send>);

    impl Consumer for RegionTap {
        fn notify(&mut self, arrived: &Projection) {
            (self.0)(arrived)
        }
    }

    /// A cycle reaches both inputs of a `MakeRecord`: the region of field `a` passes, and the
    /// region of field `b` that re-enters inside it is outside what passed, so the notification in
    /// progress delivers it when it returns, and a consumer that selects `b` hears it.
    #[test]
    fn a_reentrant_region_of_another_field_is_not_lost() {
        let names: Arc<[SmolStr]> = vec![SmolStr::new("a"), SmolStr::new("b")].into();
        let of = |name: &str| Projection::field_of(&["a", "b"], name, keys(1, 2));
        let (downstream, log, arm) = reentering(keys(1, 2));
        let (shared, _gate) = shared_consumer(downstream);
        let mut input_a = forwarding_consumer_into_field(&shared, SmolStr::new("a"), names.clone());
        *arm.lock_now() = Some(forwarding_consumer_into_field(
            &shared,
            SmolStr::new("b"),
            names,
        ));
        input_a.notify(&keys(1, 2));
        assert_eq!(
            *log.lock_now(),
            [of("a"), of("b")],
            "the re-entrant region of `b` was lost or came late"
        );
    }

    /// A consumer that re-enters the cell it is inside every time it is notified: the region the
    /// gate passed covers what the next one carries, so the cycle ends inside the notification
    /// that started it, with no wake queued, and a later pull opens the gate again.
    #[test]
    fn a_cycle_that_keeps_reentering_ends_inside_the_notification_that_started_it() {
        let names: Arc<[SmolStr]> = vec![SmolStr::new("a"), SmolStr::new("b")].into();
        let (downstream, log, arm) = reentering(keys(1, 2));
        let (shared, gate) = shared_consumer(downstream);
        let mut scheduler = Scheduler::new();
        let mut input_a = forwarding_consumer_into_field(&shared, SmolStr::new("a"), names.clone());
        *arm.lock_now() = Some(forwarding_consumer_into_field(
            &shared,
            SmolStr::new("b"),
            names,
        ));
        input_a.notify(&keys(1, 2));
        for _ in 0..5 {
            scheduler.check_for_notifications();
            gate.0.take();
        }
        let heard = log.lock_now().clone();
        assert_eq!(heard.len(), 2, "{heard:?}");
        assert!(scheduler.wakeups.is_empty());
    }

    /// Two records on crossing cycles: `G` has fields `c`, `d`, and `H` has `a`, `b`. What is
    /// notified behind `G` notifies `G.d` and then `H.a`, and what is notified behind `H`
    /// notifies `H.b` and then `G.c`. A notification of `G.c` ends after a bounded number of
    /// notifications of each, with nothing queued, however many times the gates are pulled and
    /// the scheduler polled.
    #[test]
    fn two_records_on_crossing_cycles_settle_inside_one_notification() {
        type Arms = Arc<Mutex<Vec<Box<dyn Consumer>>>>;
        let g_names: Arc<[SmolStr]> = vec![SmolStr::new("c"), SmolStr::new("d")].into();
        let h_names: Arc<[SmolStr]> = vec![SmolStr::new("a"), SmolStr::new("b")].into();
        let counts: Arc<Mutex<(usize, usize)>> = Arc::default();
        let (g_arms, h_arms): (Arms, Arms) = (Arc::default(), Arc::default());
        let tap =
            |arms: Arms, count: fn(&mut (usize, usize)), counts: Arc<Mutex<(usize, usize)>>| {
                let consumer: Box<dyn Consumer> =
                    Box::new(RegionTap(Box::new(move |_: &Projection| {
                        count(&mut counts.lock_now());
                        for arm in arms.lock_now().iter_mut() {
                            arm.notify(&keys(1, 2));
                        }
                    })));
                consumer
            };
        let (g_shared, g_gate) = shared_consumer(tap(g_arms.clone(), |c| c.0 += 1, counts.clone()));
        let (h_shared, h_gate) = shared_consumer(tap(h_arms.clone(), |c| c.1 += 1, counts.clone()));
        let arm = |shared: &GatedConsumer, name: &str, names: &Arc<[SmolStr]>| {
            forwarding_consumer_into_field(shared, SmolStr::new(name), names.clone())
        };
        // G's downstream notifies G.d then H.a; H's notifies H.b then G.c.
        *g_arms.lock_now() = vec![arm(&g_shared, "d", &g_names), arm(&h_shared, "a", &h_names)];
        *h_arms.lock_now() = vec![arm(&h_shared, "b", &h_names), arm(&g_shared, "c", &g_names)];
        let mut seed = arm(&g_shared, "c", &g_names);
        seed.notify(&keys(1, 2));
        let mut scheduler = Scheduler::new();
        for _ in 0..20 {
            scheduler.check_for_notifications();
            g_gate.0.take();
            h_gate.0.take();
        }
        let (g, h) = *counts.lock_now();
        assert_eq!((g, h), (2, 2), "G and H were notified this many times");
        assert!(scheduler.wakeups.is_empty());
    }

    /// After a pull resets the gate, a region outside what passed before it passes, and one inside
    /// what passed since is suppressed.
    #[test]
    fn a_pull_leaves_the_gate_holding_nothing() {
        let gate = Notified::clear();
        assert!(gate.mark_news_of(&keys(1, 4)));
        assert!(gate.take());
        assert!(gate.mark_news_of(&keys(6, 6)));
        assert!(gate.mark_news_of(&keys(2, 3)));
        assert!(!gate.mark_news_of(&keys(6, 6)));
    }

    /// A gate that passed `Everything` suppresses a later one until a pull, and the pull of a gate
    /// that is clear has nothing to reset. A reader that saw `everything` before a pull began and
    /// is suppressed loses nothing: the pull reads after it, and the data it announced was
    /// written before it.
    #[test]
    fn a_pull_reopens_a_gate_that_passed_everything() {
        let gate = Notified::clear();
        assert!(gate.mark_news_of(&Projection::Everything));
        assert!(!gate.mark_news_of(&Projection::Everything));
        assert!(
            !gate.mark_news_of(&Projection::Nothing),
            "nothing is never news"
        );
        assert!(!Notified::clear().mark_news_of(&Projection::Nothing));
        assert!(gate.take());
        assert!(gate.mark_news_of(&Projection::Everything));
        assert!(gate.take());
        assert!(
            !gate.take(),
            "a pull of a gate that is clear has nothing to reset"
        );
        assert!(gate.mark_news_of(&keys(1, 2)));
    }

    /// A consumer that pulls its operator inside `notify` resets the gate, and a cascade that
    /// re-enters the cell each time then passes the same region again every round. The rule is
    /// that a consumer behind a gate does not pull inside `notify`; a debug build says so rather
    /// than loop.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "pulled its operator inside `notify`")]
    fn a_consumer_that_pulls_inside_notify_and_always_reenters_is_caught() {
        let names: Arc<[SmolStr]> = vec![SmolStr::new("a"), SmolStr::new("b")].into();
        let arm: Arc<Mutex<Option<Box<dyn Consumer>>>> = Arc::default();
        let gate_slot: Arc<Mutex<Option<Notified>>> = Arc::default();
        let (arm_c, gate_c) = (arm.clone(), gate_slot.clone());
        let consumer: Box<dyn Consumer> = Box::new(RegionTap(Box::new(move |_: &Projection| {
            // The pull inside `notify`, which opens the gate again.
            if let Some(gate) = gate_c.lock_now().as_ref() {
                gate.take();
            }
            if let Some(arm) = arm_c.lock_now().as_mut() {
                arm.notify(&keys(1, 2));
            }
        })));
        let (shared, gate) = shared_consumer(consumer);
        *gate_slot.lock_now() = Some(gate.0.clone());
        let mut input_a = forwarding_consumer_into_field(&shared, SmolStr::new("a"), names.clone());
        *arm.lock_now() = Some(forwarding_consumer_into_field(
            &shared,
            SmolStr::new("b"),
            names,
        ));
        input_a.notify(&keys(1, 2));
    }

    /// A cell whose consumer pulls is notified from one thread: the notification in progress
    /// delivers a region that re-entered it, which a region left by another thread could miss.
    #[cfg(debug_assertions)]
    #[test]
    fn a_cell_whose_consumer_pulls_notified_from_two_threads_is_caught() {
        let (shared, _gate) = shared_consumer(Box::new(|| {}));
        shared.notify(&keys(1, 2));
        let other = shared.clone();
        let outcome = std::thread::spawn(move || other.notify(&keys(5, 6))).join();
        assert!(
            outcome.is_err(),
            "the second thread's notification was accepted"
        );
    }

    /// The same cell, notified from its one thread any number of times, is fine.
    #[test]
    fn a_cell_whose_consumer_pulls_notified_from_one_thread_is_fine() {
        let (shared, _gate) = shared_consumer(Box::new(|| {}));
        shared.notify(&keys(1, 2));
        shared.notify(&keys(5, 6));
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
            woken: Arc<Mutex<bool>>,
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
                        .request(Arc::new(Mutex::new(move || *woken.lock_now() = true)));
                }
                // Nothing until woken: a scalar holding a value is its whole answer, so the
                // pull before the wakeup answers what the first did by having none.
                let values = match *self.woken.lock_now() {
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
            woken: Arc::new(Mutex::new(false)),
            queue: scheduler.wakeup_queue(),
        };
        let tile = pull_laps(&mut scheduler, &mut producer, 8, |t| {
            *t == Tile::Scalar(ColumnValue::Ints(vec![2]))
        });
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![2])));
    }

    /// A source with new data, and a consumer that counts its notifications.
    fn polled_source() -> (Scheduler, Arc<Mutex<u32>>, SharedConsumer) {
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
        let count = Arc::new(Mutex::new(0u32));
        let count_c = count.clone();
        let consumer: SharedConsumer = Arc::new(Mutex::new(move || *count_c.lock_now() += 1));
        let mut scheduler = Scheduler::new();
        scheduler.add_source_handle(
            Arc::new(Mutex::new(source)),
            Arc::downgrade(&consumer),
            true,
        );
        (scheduler, count, consumer)
    }

    /// A poll takes the data in and wakes nobody; the delivery wakes the
    /// consumer. The gap between them is where a source window is sampled,
    /// with the arrivals present and no sink yet pulled.
    #[test]
    fn a_poll_wakes_no_consumer_until_it_is_delivered() {
        let (mut scheduler, count, _consumer) = polled_source();
        let delivery = scheduler.poll_sources();
        assert_eq!(*count.lock_now(), 0, "polling notifies nobody");
        scheduler.deliver(delivery);
        assert_eq!(*count.lock_now(), 1);
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
        let count = Arc::new(Mutex::new(0u32));
        let count_c = count.clone();
        let consumer: Arc<Mutex<dyn Consumer>> =
            Arc::new(Mutex::new(move || *count_c.lock_now() += 1));

        scheduler.wakeup_queue().request(consumer);
        // Deferred: nothing fires until the scheduler is polled.
        assert_eq!(*count.lock_now(), 0);

        scheduler.check_for_notifications();
        assert_eq!(*count.lock_now(), 1);

        // Drained: a second poll with no new request delivers nothing.
        scheduler.check_for_notifications();
        assert_eq!(*count.lock_now(), 1);
    }

    /// A wakeup requested *during* delivery lands in the next drain, not the
    /// current one — one poll delivers one round, so the driver keeps control of
    /// pacing (a still-converging producer re-arming does not run to completion
    /// inside a single `check_for_notifications`).
    #[test]
    fn wakeup_requested_during_delivery_defers_to_next_poll() {
        let mut scheduler = Scheduler::new();
        let queue = scheduler.wakeup_queue();
        let log = Arc::new(Mutex::new(Vec::<&'static str>::new()));

        let log_b = log.clone();
        let b: Arc<Mutex<dyn Consumer>> = Arc::new(Mutex::new(move || log_b.lock_now().push("b")));

        // A logs "a" and, mid-delivery, requests B.
        let log_a = log.clone();
        let queue_c = queue.clone();
        let a: Arc<Mutex<dyn Consumer>> = Arc::new(Mutex::new(move || {
            log_a.lock_now().push("a");
            queue_c.request(b.clone());
        }));

        queue.request(a);
        scheduler.check_for_notifications(); // delivers A; A's request for B defers
        assert_eq!(*log.lock_now(), vec!["a"]);
        scheduler.check_for_notifications(); // now delivers B
        assert_eq!(*log.lock_now(), vec!["a", "b"]);
        scheduler.check_for_notifications(); // nothing left
        assert_eq!(*log.lock_now(), vec!["a", "b"]);
    }
}

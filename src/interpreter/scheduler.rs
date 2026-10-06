use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::interpreter::{Consumer, DataSourceDomainExtentImpl, value_probe::ProbeSlot};

/// A handle to the scheduler's **deferred-wakeup queue**.
///
/// The notification model is push-from-source: a source announces new data via
/// [`Scheduler::check_for_notifications`], which the driver calls *between*
/// pulls. But an operator that advances its own state one pull at a time — a
/// store recurrence closed through a cyclic feedback `FanOut` — has
/// more to compute after a partial pull with **no external trigger pending**,
/// and it cannot simply `notify()` from inside `get`: the notify graph is cyclic
/// (the feedback `FanOut`), so a synchronous notification during a `get`
/// re-enters an operator that is mid-`get` holding a `RefCell` borrow.
///
/// Instead such a producer calls [`WakeupQueue::request`] with its consumer. The
/// request is delivered by the next [`Scheduler::check_for_notifications`] — with
/// no `get`-borrow held anywhere — so the driver re-pulls without spinning and
/// without re-entering the graph mid-borrow.
///
/// The alternation is load-bearing rather than conventional: an operator holding a
/// cumulative cache answers from it while its input has said nothing
/// ([`crate::interpreter::tile_operators::Notified`]), so a caller that pulls without
/// delivering never reaches the operators below it. `pull_laps` is that alternation,
/// for tests.
///
/// A shareable consumer handle: a consumer the queue can hold and deliver later
/// (and that a producer can clone to re-arm on its next pull).
pub type SharedConsumer = Rc<RefCell<dyn Consumer>>;

/// Share one operator's consumer between several of its inputs.
///
/// An operator with more than one input has a single downstream consumer to wake,
/// so the handle has to be shared. This is the one way to build that handle.
pub fn shared_consumer(mut consumer: Box<dyn Consumer>) -> SharedConsumer {
    Rc::new(RefCell::new(move || consumer.notify()))
}

/// A fresh `Box<dyn Consumer>` forwarding to `shared` — what `subscribe` wants for
/// an input whose notifications should reach the operator's own consumer.
///
/// The closure is not ceremony: a `Box<Rc<RefCell<dyn Consumer>>>` is not itself a
/// `Consumer`, because the blanket impl over `Rc<RefCell<C>>` needs a *sized* `C`,
/// and `dyn Consumer` is not. Wrapping the wake in a closure gives the blanket
/// impl something sized to bite on.
pub fn forwarding_consumer(shared: &SharedConsumer, wakeups: &WakeupQueue) -> Box<dyn Consumer> {
    let shared = shared.clone();
    let wakeups = wakeups.clone();
    Box::new(move || {
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
        match shared.try_borrow_mut() {
            Ok(mut consumer) => consumer.notify(),
            Err(_) => wakeups.request(shared.clone()),
        }
    })
}

#[derive(Clone, Default)]
pub struct WakeupQueue(Rc<RefCell<Vec<SharedConsumer>>>);

impl WakeupQueue {
    /// Request that `consumer` be notified at the next
    /// [`Scheduler::check_for_notifications`] — i.e. once the current `get`
    /// stack has fully unwound.
    pub fn request(&self, consumer: SharedConsumer) {
        // A consumer already waiting is not queued twice. A wake is an edge, not a count,
        // and a drive re-arms on every pull it makes progress on, so the same consumer is
        // requested many times between drains.
        let mut queued = self.0.borrow_mut();
        if queued.iter().any(|waiting| Rc::ptr_eq(waiting, &consumer)) {
            return;
        }
        queued.push(consumer);
    }

    /// Take the currently-queued wakeups, leaving the queue empty. A wakeup
    /// fired during the drain may enqueue a fresh request (a still-converging
    /// producer re-arming); that lands in the now-empty queue and is delivered
    /// by the next drain, not this one.
    fn take(&self) -> Vec<SharedConsumer> {
        std::mem::take(&mut *self.0.borrow_mut())
    }

    /// Whether a wakeup is waiting for the next drain.
    #[cfg(any(test, feature = "test-helpers"))]
    fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }
}

/// Basic scheduler implementation.
///
/// Tracks [`IterateExtent`](crate::interpreter::tile_operators::IterateExtent)s that generate data from external sources (e.g.
/// data sources) and need to be polled for new data each tick, and carries the
/// [`WakeupQueue`] for producers that request their own re-pull.
#[derive(Default)]
pub struct Scheduler {
    source_handles: HashMap<String, SourceHandle>,
    wakeups: WakeupQueue,
    probes: ProbeSlot,
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
    /// for, then the deferred wakeups, and say whether anything was delivered.
    /// A sink pulls here.
    pub fn deliver(&mut self, mut delivery: Delivery) -> bool {
        let mut delivered = false;
        for consumer in std::mem::take(&mut delivery.0) {
            consumer.borrow_mut().notify();
            delivered = true;
        }
        // Deliver deferred wakeups now — outside any `get`, so a notification
        // that fans through the cyclic operator graph does not re-enter an
        // operator mid-borrow (see [`WakeupQueue`]). They follow the source
        // notifications because a wakeup is a notification too and can pull.
        for consumer in self.wakeups.take() {
            consumer.borrow_mut().notify();
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

/// The consumers a [`Scheduler::poll_sources`] found new data for, not yet
/// notified.
///
/// Holds them strongly from the poll to the delivery, so a consumer dropped in
/// between is still notified once. Dropping a `Delivery` without passing it to
/// [`Scheduler::deliver`] leaves the data buffered with no consumer woken, and a
/// sink-only program then stalls: `#[must_use]` catches a delivery that is
/// ignored, and `Drop` catches one that is bound and forgotten.
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

/// Deliver, then pull — `laps` times, stopping as soon as `done` accepts the tile or the
/// program is quiescent. Returns the last tile pulled.
///
/// The alternation `src/main.rs` runs, and the one a test should write. A lap runs on any
/// pull that reaches the store, so a loop that only pulls is not stalled by itself; what
/// it loses is the read. An operator holding a cumulative cache answers from that cache
/// while its input has said nothing ([`crate::interpreter::tile_operators::Notified`]),
/// so the pull stops there and never reaches the store at all. Delivering is what
/// re-enables the read.
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
        let delivered = scheduler.check_for_notifications();
        let pulled = producer.get(guard.clone());
        if done(&pulled) {
            return pulled;
        }
        // Nothing was delivered, the pull answered what the last one did, and it queued no
        // wakeup, so every operator saw what it saw before and nothing moves until an input
        // changes: the laps left would only repeat this one. A wakeup this pull queued is
        // delivered by the next lap's check, so that lap is not a repeat.
        if lap > 0 && !delivered && pulled == tile && scheduler.wakeups.is_empty() {
            return pulled;
        }
        tile = pulled;
    }
    tile
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A notification that re-enters a consumer still being notified reaches it later rather
    /// than being lost: the downstream here pulls on notify, as `SinkConsumer` does, and
    /// the cascade then reaches the second arm, whose data changed after the pull.
    #[test]
    fn a_reentrant_wake_after_a_pull_in_the_cascade_is_not_lost() {
        use std::cell::Cell;
        let data = Rc::new(Cell::new(0u32));
        let seen = Rc::new(Cell::new(0u32));
        let feedback: Rc<RefCell<Option<Box<dyn Consumer>>>> = Rc::new(RefCell::new(None));
        let (d, s, fb) = (data.clone(), seen.clone(), feedback.clone());
        let downstream: Box<dyn Consumer> = Box::new(move || {
            // The pull.
            s.set(d.get());
            // The rest of the cascade, once: arm B's data changes, and its notification
            // re-enters the operator this notification is still inside.
            let rest = fb.borrow_mut().take();
            if let Some(mut arm_b) = rest {
                d.set(d.get() + 1);
                arm_b.notify();
            }
        });
        let shared = shared_consumer(downstream);
        let mut scheduler = Scheduler::new();
        let mut arm_a = forwarding_consumer(&shared, &scheduler.wakeup_queue());
        *feedback.borrow_mut() = Some(forwarding_consumer(&shared, &scheduler.wakeup_queue()));
        arm_a.notify();
        scheduler.check_for_notifications();
        assert_eq!(
            seen.get(),
            data.get(),
            "the downstream never pulled what arm B delivered after its pull"
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
                let values = match *self.woken.borrow() {
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
        assert_eq!(*count.borrow(), 0, "polling notifies nobody");
        scheduler.deliver(delivery);
        assert_eq!(*count.borrow(), 1);
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
        assert_eq!(*count.borrow(), 0);

        scheduler.check_for_notifications();
        assert_eq!(*count.borrow(), 1);

        // Drained: a second poll with no new request delivers nothing.
        scheduler.check_for_notifications();
        assert_eq!(*count.borrow(), 1);
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
        assert_eq!(*log.borrow(), vec!["a"]);
        scheduler.check_for_notifications(); // now delivers B
        assert_eq!(*log.borrow(), vec!["a", "b"]);
        scheduler.check_for_notifications(); // nothing left
        assert_eq!(*log.borrow(), vec!["a", "b"]);
    }
}

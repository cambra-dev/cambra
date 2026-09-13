use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::interpreter::{Consumer, DataSourceDomainExtentImpl};

/// A handle to the scheduler's **deferred-wakeup queue**.
///
/// The notification model is push-from-source: a source announces new data via
/// [`Scheduler::check_for_notifications`], which the driver calls *between*
/// pulls. But an operator that advances its own state one round at a time — a
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
pub fn forwarding_consumer(shared: &SharedConsumer) -> Box<dyn Consumer> {
    let shared = shared.clone();
    Box::new(move || shared.borrow_mut().notify())
}

#[derive(Clone, Default)]
pub struct WakeupQueue(Rc<RefCell<Vec<SharedConsumer>>>);

impl WakeupQueue {
    /// Request that `consumer` be notified at the next
    /// [`Scheduler::check_for_notifications`] — i.e. once the current `get`
    /// stack has fully unwound.
    pub fn request(&self, consumer: SharedConsumer) {
        self.0.borrow_mut().push(consumer);
    }

    /// Take the currently-queued wakeups, leaving the queue empty. A request
    /// enqueued after this — by a source notification's synchronous pull, or by a
    /// still-converging producer re-arming during the drain — lands in the
    /// now-empty queue and is delivered by the next drain, which is the round it
    /// is asking for.
    fn take(&self) -> Vec<SharedConsumer> {
        std::mem::take(&mut *self.0.borrow_mut())
    }
}

// shared-state-ok: a counter, and what crosses it is a clock reading rather than
// a value — nothing in the graph reads data through it. A *round* is a span with
// no `get` in flight on this thread, which is a property of the thread and not of
// any one scheduler: two programs driven from the same loop share the points
// between their pulls.
thread_local! {
    // shared-state-ok: the counter itself, for the reason on the block above.
    static ROUND: Cell<u64> = const { Cell::new(0) };
}

/// Begin the next **delivery round**: the span between two
/// [`Scheduler::check_for_notifications`] calls, over which the graph holds one
/// consistent set of tiles.
///
/// A `get` is a read, not a step — two of them for the same region with no
/// release in between answer the same tile, which
/// [`TileProducer::get`](crate::interpreter::tile_operators::TileProducer::get)
/// asserts. A producer whose state advances with nothing external to trigger it
/// (a store draining its writers' proposals, a driver emitting the next attempt)
/// advances on this boundary rather than on whichever pull reached it first, and
/// answers the round's frozen tile for the rest of it.
/// [`RoundCache`](crate::interpreter::tile_operators::RoundCache) holds that
/// answer.
pub(crate) fn open_round() {
    ROUND.with(|r| r.set(r.get() + 1));
}

/// The delivery round in progress. See [`open_round`].
pub(crate) fn current_round() -> u64 {
    ROUND.with(Cell::get)
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

    pub fn check_for_notifications(&mut self) {
        // Open the round first: a source arrival and a deferred wakeup are both
        // state changes the graph may not observe mid-round, so everything this
        // call delivers belongs to the round it begins.
        open_round();
        // Take the queue before polling. A source's notification pulls
        // synchronously, and a producer re-arming during that pull is asking for
        // the *next* round — delivering it in this one would re-pull a graph that
        // has already answered for the round, spending the request on nothing.
        let deferred = self.wakeups.take();
        self.source_handles
            .values_mut()
            .for_each(|(source, consumers)| {
                // Prune first, so a source whose every subscriber is gone stops
                // accumulating dead registrations across program reloads.
                consumers.retain(|c| c.strong_count() > 0);
                if source.borrow_mut().check_for_new_data() {
                    for consumer in consumers.iter().filter_map(Weak::upgrade) {
                        consumer.borrow_mut().notify();
                    }
                }
            });
        // Deliver the deferred wakeups now — outside any `get`, so a notification
        // that fans through the cyclic operator graph does not re-enter an
        // operator mid-borrow (see [`WakeupQueue`]).
        for consumer in deferred {
            consumer.borrow_mut().notify();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

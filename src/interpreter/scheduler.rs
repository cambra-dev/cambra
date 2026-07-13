use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::interpreter::{Consumer, DataSourceDomainExtentImpl};

/// A handle to the scheduler's **deferred-wakeup queue**.
///
/// The notification model is push-from-source: a source announces new data via
/// [`Scheduler::check_for_notifications`], which the driver calls *between*
/// pulls. But an operator that advances its own state one pull at a time — the
/// mutation-loop [`Recurse`](crate::interpreter::tile_operators) cycle — has
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

#[derive(Clone, Default)]
pub struct WakeupQueue(Rc<RefCell<Vec<SharedConsumer>>>);

impl WakeupQueue {
    /// Request that `consumer` be notified at the next
    /// [`Scheduler::check_for_notifications`] — i.e. once the current `get`
    /// stack has fully unwound.
    pub fn request(&self, consumer: SharedConsumer) {
        self.0.borrow_mut().push(consumer);
    }

    /// Take the currently-queued wakeups, leaving the queue empty. A wakeup
    /// fired during the drain may enqueue a fresh request (a still-converging
    /// producer re-arming); that lands in the now-empty queue and is delivered
    /// by the next drain, not this one.
    fn take(&self) -> Vec<SharedConsumer> {
        std::mem::take(&mut *self.0.borrow_mut())
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
}

type SourceHandle = (
    Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    Vec<Box<dyn Consumer>>,
);

impl Scheduler {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_source_handle(
        &mut self,
        handle: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        consumer: Box<dyn Consumer>,
    ) {
        let id = handle.borrow().get_id().to_string();
        if let Some(entry) = self.source_handles.get_mut(&id) {
            assert!(Rc::ptr_eq(&handle, &entry.0));
            entry.1.push(consumer);
        } else {
            self.source_handles.insert(id, (handle, vec![consumer]));
        }
    }

    /// A handle to the deferred-wakeup queue, for producers that must request
    /// their own re-pull (see [`WakeupQueue`]). Obtained at `subscribe` time and
    /// stored, since `get` has no access to the scheduler.
    pub fn wakeup_queue(&self) -> WakeupQueue {
        self.wakeups.clone()
    }

    pub fn check_for_notifications(&mut self) {
        self.source_handles
            .values_mut()
            .for_each(|(source, consumers)| {
                if source.borrow_mut().check_for_new_data() {
                    consumers.iter_mut().for_each(|c| c.notify());
                }
            });
        // Deliver deferred wakeups now — outside any `get`, so a notification
        // that fans through the cyclic operator graph does not re-enter an
        // operator mid-borrow (see [`WakeupQueue`]).
        for consumer in self.wakeups.take() {
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

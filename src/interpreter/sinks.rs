//! Generic sink infrastructure: completion notification and the sink consumer.
//!
//! These types are independent of any particular data source (HTTP, stdin, etc.)
//! and are used by [`crate::ccl::context`] to wire compiled sink operators into
//! the scheduler.

use std::{
    cell::RefCell,
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
    },
};

use crate::interpreter::{
    Consumer, DataSink,
    scheduler::{SharedConsumer, WakeupQueue},
    tile_operators::TileProducer,
};

/// Shared slot for injecting the producer after `subscribe` returns.
///
/// [`SinkConsumer::new`] hands one clone to the consumer and returns the other
/// to the caller so it can be filled once [`crate::interpreter::tile_operators::TileOperator::subscribe`] completes.
pub type ProducerSlot = Rc<RefCell<Option<Box<dyn TileProducer>>>>;

// ---------------------------------------------------------------------------
// Completion notification
// ---------------------------------------------------------------------------

/// Signals one sink's completion to a shared done channel.
///
/// Each [`SinkConsumer`] holds one `DoneNotifier`.  When a terminal tile is
/// received, [`signal`](Self::signal) decrements the shared `remaining` counter;
/// the last sink to complete sends `()` on `tx`, firing `SinksHandle::done`.
pub struct DoneNotifier {
    /// Number of sinks that have not yet completed.
    remaining: Arc<AtomicUsize>,
    /// Fires `SinksHandle::done` when the last sink completes.
    tx: Sender<()>,
}

impl DoneNotifier {
    /// Record this sink's completion.  Sends on the shared channel iff this was the last one.
    pub fn signal(self) {
        if self.remaining.fetch_sub(1, Ordering::AcqRel) == 1 {
            let _ = self.tx.send(());
        }
    }

    /// Create `n` notifiers all wired to the same completion channel.
    pub fn create(n: usize) -> (Vec<Self>, Receiver<()>) {
        let (tx, rx) = mpsc::channel();
        let remaining = Arc::new(AtomicUsize::new(n));
        let notifiers = (0..n)
            .map(|_| Self {
                remaining: remaining.clone(),
                tx: tx.clone(),
            })
            .collect();
        (notifiers, rx)
    }
}

// ---------------------------------------------------------------------------
// Sink consumer
// ---------------------------------------------------------------------------

/// A [`Consumer`] that, on notification, schedules a pull of the wrapped producer on the
/// scheduler's sink pull queue
/// ([`Scheduler::sink_pull_queue`](crate::interpreter::Scheduler::sink_pull_queue)). The pull
/// passes the current tile to the paired [`DataSink`] and fires the [`DoneNotifier`] when a
/// terminal tile is received.
///
/// The pull is scheduled rather than made in [`notify`](Consumer::notify) because a change
/// reaches a sink once along every notification path from where it happened, and the queue
/// holds one pull however many arrive (`src/interpreter/design-operators.md`, "The
/// notification contract").
///
/// The producer reference is held in an `Option` that starts as `None` and is
/// filled after [`crate::interpreter::tile_operators::TileOperator::subscribe`] returns (solving the chicken-and-egg:
/// the consumer must exist before subscribe is called, but subscribe is what
/// creates the producer).
///
/// A pull scheduled *during* `subscribe` — an induction store notifies to start its
/// loop — waits on that queue until the scheduler next delivers, by which time the slot
/// is filled. Whoever fills the slot also pulls once at once ([`pull_now`](Self::pull_now),
/// from [`crate::ccl::context::compile_program`]).
pub struct SinkConsumer {
    /// The compiled responses producer, filled in after subscribe returns.
    producer: ProducerSlot,
    /// The pull a notification schedules: one `get` of the producer, handed to the sink.
    pull: SharedConsumer,
    /// Where a notification schedules [`pull`](Self::pull).
    wakeups: WakeupQueue,
}

impl SinkConsumer {
    /// Create a new consumer paired with `sink` and `done`.
    ///
    /// The returned consumer holds a shared handle to the `producer` slot. The
    /// caller fills it with the `TileProducer` returned by
    /// [`crate::interpreter::tile_operators::TileOperator::subscribe`] and then pulls
    /// once ([`pull_now`](Self::pull_now)).
    pub fn new(
        sink: Arc<dyn DataSink>,
        done: DoneNotifier,
        wakeups: WakeupQueue,
    ) -> (Self, ProducerSlot) {
        let slot: ProducerSlot = Rc::new(RefCell::new(None));
        let producer = slot.clone();
        let mut done = Some(done);
        let pull: SharedConsumer = Rc::new(RefCell::new(move || {
            if let Some(prod) = producer.borrow_mut().as_mut() {
                let guard = prod.tiling().universal_guard();
                let tile = prod.get(guard);
                sink.process(&tile);
                let is_terminal = tile.is_terminal();
                prod.release(tile.to_guard());
                if is_terminal && let Some(notifier) = done.take() {
                    notifier.signal();
                }
            }
        }));
        (
            Self {
                producer: slot.clone(),
                pull,
                wakeups,
            },
            slot,
        )
    }

    /// Pull now rather than when the scheduler next drains. Installing a version pulls it
    /// at once: the version a reload replaces hands its state to its successor, and one
    /// replaced before it was ever pulled has opened none to hand on.
    pub fn pull_now(&self) {
        self.pull.borrow_mut().notify();
    }

    /// Stop dispatching and release the producer chain behind this consumer.
    ///
    /// A [`DataSink`] outlives any one version of a program; the subscription
    /// that feeds it does not. Detaching is what ends a replaced version's
    /// dispatch, and it is not achieved by dropping the consumer alone: an
    /// operator carried across the replacement still holds the notification
    /// closure that reaches this consumer, so the replaced version would keep
    /// being woken and keep writing to a sink its successor now owns. Clearing
    /// the producer slot also drops the operators behind it, which is what lets
    /// the fan-outs they subscribed to see those subscriptions end.
    pub fn detach(&mut self) {
        *self.producer.borrow_mut() = None;
    }

    /// Call `f` with the sink's current producer, if it has been set.
    pub fn with_producer<F: FnOnce(&dyn TileProducer)>(&self, f: F) {
        if let Some(ref prod) = *self.producer.borrow() {
            f(prod.as_ref());
        }
    }
}

impl Consumer for SinkConsumer {
    /// Schedules one pull rather than pulling. A change reaches the sink once along every
    /// path from where it happened, and the queue holds a pull once however many arrive.
    fn notify(&mut self) {
        self.wakeups.request(self.pull.clone());
    }
}

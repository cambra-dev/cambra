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

use crate::interpreter::{Consumer, DataSink, tile_operators::TileProducer};

/// Shared slot for injecting the producer after `subscribe` returns.
///
/// [`SinkConsumer::new`] hands one clone to the consumer and returns the other
/// to the caller so it can be filled once [`TileOperator::subscribe`] completes.
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

/// A [`Consumer`] that, on each notification, pulls the current tile from the
/// wrapped producer, passes it to the paired [`DataSink`], and fires the
/// [`DoneNotifier`] when a terminal tile is received.
///
/// The producer reference is held in an `Option` that starts as `None` and is
/// filled after [`TileOperator::subscribe`] returns (solving the chicken-and-egg:
/// the consumer must exist before subscribe is called, but subscribe is what
/// creates the producer).
pub struct SinkConsumer {
    /// The compiled responses producer, filled in after subscribe returns.
    producer: ProducerSlot,
    /// The sink that dispatches responses.
    sink: Arc<dyn DataSink>,
    /// Fired once when this sink receives a terminal tile.  `None` after it fires.
    done: Option<DoneNotifier>,
}

impl SinkConsumer {
    /// Create a new consumer paired with `sink` and `done`.
    ///
    /// The returned consumer holds a shared handle to the `producer` slot; the
    /// caller should fill that slot with the `TileProducer` returned by
    /// [`TileOperator::subscribe`] before the first notification fires.
    pub fn new(sink: Arc<dyn DataSink>, done: DoneNotifier) -> (Self, ProducerSlot) {
        let slot: ProducerSlot = Rc::new(RefCell::new(None));
        (
            Self {
                producer: slot.clone(),
                sink,
                done: Some(done),
            },
            slot,
        )
    }

    /// Call `f` with the sink's current producer, if it has been set.
    pub fn with_producer<F: FnOnce(&dyn TileProducer)>(&self, f: F) {
        if let Some(ref prod) = *self.producer.borrow() {
            f(prod.as_ref());
        }
    }
}

impl Consumer for SinkConsumer {
    fn notify(&mut self) {
        if let Some(prod) = self.producer.borrow_mut().as_mut() {
            let guard = prod.tiling().universal_guard();
            let tile = prod.get(guard);
            self.sink.process(&tile);
            let is_terminal = tile.is_terminal();
            prod.release(tile.to_guard());
            if is_terminal && let Some(notifier) = self.done.take() {
                notifier.signal();
            }
        }
    }
}

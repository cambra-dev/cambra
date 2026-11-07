//! Generic sink infrastructure: completion notification and the sink consumer.
//!
//! These types are independent of any particular data source (HTTP, stdin, etc.)
//! and are used by [`crate::ccl::context`] to wire compiled sink operators into
//! dispatcher runs.

use crate::interpreter::Projection;
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
use crate::interpreter::{
    dispatcher::{Landing, PipelineId, Routes, pushed_guard},
    tile_operators::Tiling,
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

/// The dispatcher consumer of a program's sink output.
/// A region delivery queues work for its sink pipeline. After every pipeline finishes,
/// [`complete`](Self::complete) reconciles terminal output and signals [`DoneNotifier`].
/// The producer slot is filled after subscription returns.
pub struct SinkConsumer {
    /// The compiled responses producer, filled in after subscribe returns.
    producer: ProducerSlot,
    /// The sink that receives completed packages and the final terminal tile.
    sink: Arc<dyn DataSink>,
    done: Option<DoneNotifier>,
    /// The sink's pipeline in a dispatched run, and the tiling of the producer it pulls,
    /// which a push names regions of ([`place`](Self::place)).
    placed: Option<(PipelineId, Tiling)>,
}

impl SinkConsumer {
    /// Pair `sink` and `done` with an empty producer slot for the caller to fill after subscription.
    pub fn new(sink: Arc<dyn DataSink>, done: DoneNotifier) -> (Self, ProducerSlot) {
        let producer = Rc::new(RefCell::new(None));
        (
            Self {
                producer: producer.clone(),
                sink,
                done: Some(done),
                placed: None,
            },
            producer,
        )
    }

    /// Reconcile terminal output and signal completion after all sink pipelines finish.
    pub(crate) fn complete(&mut self) {
        if self.done.is_none() {
            return;
        }
        let mut slot = self.producer.borrow_mut();
        let producer = slot.as_mut().expect("a compiled sink holds its producer");
        let tile = producer
            .get(producer.tiling().universal_guard())
            .closed_over(producer.tiling());
        self.sink.process(&tile);
        producer.release(tile.to_guard());
        assert!(
            tile.is_terminal(),
            "a finished sink reconciles a terminal tile"
        );
        self.done
            .take()
            .expect("completion is signalled once")
            .signal();
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

    /// The slot holding the producer this consumer pulls, which a dispatched run walks.
    pub(crate) fn producer_slot(&self) -> &ProducerSlot {
        &self.producer
    }

    /// The sink this consumer hands its producer's answers to.
    pub(crate) fn sink(&self) -> Arc<dyn DataSink> {
        self.sink.clone()
    }

    /// Take the sink out of the pipeline it was placed in: a push that reaches it queues nothing.
    pub(crate) fn unplace(&mut self) {
        self.placed = None;
    }

    /// Place the sink in `pipeline` of a dispatched run, whose breaker pulls a producer of
    /// `input`: a push that reaches the sink queues for that pipeline what it names of `input`.
    pub(crate) fn place(&mut self, pipeline: PipelineId, input: Tiling) {
        self.placed = Some((pipeline, input));
    }
}

impl Consumer for SinkConsumer {
    /// Cache invalidation executes no sink; output delivery is scheduled by `notify`.
    fn invalidate(&mut self, _arrived: &Projection) {
        crate::interpreter::dispatcher::debug_assert_outside_a_run();
    }

    fn notify(&mut self, region: &Projection, landing: &mut Landing<'_>) {
        if let Some((pipeline, input)) = &self.placed
            && let Some(guard) = pushed_guard(region, input)
        {
            landing.queue(*pipeline, &guard);
        }
    }
    fn route(&mut self, routes: &mut Routes) {
        if let Some((pipeline, _)) = &self.placed {
            routes.reach(*pipeline);
        }
    }
}

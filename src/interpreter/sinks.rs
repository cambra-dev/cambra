//! Generic sink infrastructure: completion notification and the sink consumer.
//!
//! These types are independent of any particular data source (HTTP, stdin, etc.)
//! and are used by [`crate::ccl::context`] to wire compiled sink operators into
//! dispatcher runs.

use crate::interpreter::Projection;
use std::sync::PoisonError;
use std::sync::RwLock;
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicUsize, Ordering},
    mpsc::{self, Receiver, Sender},
};

use crate::interpreter::{Consumer, DataSink, Predicate, Tile, tile_operators::TileProducer};
use crate::interpreter::{
    dispatcher::{Landing, PipelineId, pushed_guard},
    tile_operators::Tiling,
};

/// Shared slot for injecting the producer after `subscribe` returns.
///
/// [`SinkConsumer::new`] hands one clone to the consumer and returns the other
/// to the caller so it can be filled once [`crate::interpreter::tile_operators::TileOperator::subscribe`] completes.
pub type ProducerSlot = Arc<RwLock<Option<Box<dyn TileProducer>>>>;

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
    /// The caller signals once.
    pub fn signal(&self) {
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
///
/// Every method takes `&self`: the compiled output and the operator graph share the consumer
/// (`CompiledOutput::sink_consumer`), and a notification takes no lock on it.
pub struct SinkConsumer {
    /// The compiled responses producer, filled in after subscribe returns.
    producer: ProducerSlot,
    /// The sink that receives completed packages and the final terminal tile.
    sink: Arc<dyn DataSink>,
    done: DoneNotifier,
    /// Whether [`complete`](Self::complete) has run, which signals `done` at most once.
    completed: AtomicBool,
    /// The sink's pipeline in a dispatched run, and the tiling of the producer it pulls,
    /// which a push names regions of ([`place`](Self::place)).
    // shared-state-ok: the planner writes the placement before a run and `notify` reads it; what
    // crosses it is a pipeline's index and a tiling, never a tile.
    placed: RwLock<Option<(PipelineId, Tiling)>>,
}

impl SinkConsumer {
    /// Pair `sink` and `done` with an empty producer slot for the caller to fill after subscription.
    pub fn new(sink: Arc<dyn DataSink>, done: DoneNotifier) -> (Self, ProducerSlot) {
        let producer = Arc::new(RwLock::new(None));
        (
            Self {
                producer: producer.clone(),
                sink,
                done,
                completed: AtomicBool::new(false),
                placed: RwLock::new(None),
            },
            producer,
        )
    }

    /// Reconcile terminal output and signal completion after all sink pipelines finish.
    pub(crate) fn complete(&self) {
        if self.completed.swap(true, Ordering::AcqRel) {
            return;
        }
        let mut slot = self
            .producer
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        let producer = slot.as_mut().expect("a compiled sink holds its producer");
        // A producer released whole answers nothing more, and the run's finish states what it
        // handed complete ([`pull_at_finish`]).
        let tile = pull_at_finish(&mut **producer);
        self.sink.process(&tile);
        producer.release(tile.to_guard());
        assert!(
            tile.is_terminal(),
            "a finished sink reconciles a terminal tile"
        );
        self.done.signal();
    }

    /// Release the producer chain owned by this consumer during version teardown.
    /// Operators retained by the replacement can still reference this consumer; clearing its
    /// slot prevents those references from retaining the retired producer graph. Paused or refused
    /// runs remove their placement separately with [`unplace`](Self::unplace).
    pub fn detach(&self) {
        *self
            .producer
            .write()
            .unwrap_or_else(PoisonError::into_inner) = None;
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
    pub(crate) fn unplace(&self) {
        *self.placed.write().unwrap_or_else(PoisonError::into_inner) = None;
    }

    /// Place the sink in `pipeline` of a dispatched run, whose breaker pulls a producer of
    /// `input`: a push that reaches the sink queues for that pipeline what it names of `input`.
    pub(crate) fn place(&self, pipeline: PipelineId, input: Tiling) {
        *self.placed.write().unwrap_or_else(PoisonError::into_inner) = Some((pipeline, input));
    }
}

impl Consumer for SinkConsumer {
    /// Cache invalidation executes no sink; output delivery is scheduled by `notify`.
    fn notify(&self, region: &Projection, landing: &mut Landing<'_>) {
        let queued = match &*self.placed.read().unwrap_or_else(PoisonError::into_inner) {
            Some((pipeline, input)) => pushed_guard(region, input).map(|guard| (*pipeline, guard)),
            None => None,
        };
        if let Some((pipeline, guard)) = queued {
            landing.queue(pipeline, &guard);
        }
    }
}

/// What a sink's or a `main` output's producer answers at the run's finish: its pull at the
/// universal guard, closed over its tiling. A producer its reader released whole has handed all it
/// holds, and the run has finished every pipeline, so where that pull does not state the producer
/// complete the finish states it complete with an empty collection that states every key
/// complete ([`complete_and_empty`]) (`src/interpreter/design-dispatcher.md`, "A widened
/// push").
pub(crate) fn pull_at_finish(producer: &mut dyn TileProducer) -> Tile {
    let tiling = producer.tiling().clone();
    let pulled = producer.get(tiling.universal_guard()).closed_over(&tiling);
    if pulled.is_terminal() || !producer.obsolete_guard().is_universal() {
        return pulled;
    }
    // The finish states complete only what the reads handed: a producer released whole answers
    // no key, and a key it holds no level beneath was complete once handed.
    debug_assert!(
        pulled.is_empty(),
        "a producer released whole answers no key at the finish: {pulled:?}"
    );
    complete_and_empty(&tiling).unwrap_or(pulled)
}

/// The tile of `tiling`, a collection, that holds nothing and states every key complete; `None`
/// where `tiling` is no collection.
fn complete_and_empty(tiling: &Tiling) -> Option<Tile> {
    match tiling.empty_tile() {
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            deleted,
            absent_keys,
            ..
        } => Some(Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate: Predicate::True,
            deleted,
            absent_keys,
        }),
        _ => None,
    }
}

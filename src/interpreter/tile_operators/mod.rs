//! Tile operator and producer types for the CCL dataflow graph.
//!
//! A [`TileOperator`] is a static descriptor of a computation node — it knows
//! its output [`Tiling`] and can create a live [`TileProducer`] via
//! [`TileOperator::subscribe`].  A [`TileProducer`] is the runtime counterpart:
//! it can answer `get` queries and accept `release` notifications.
//!
//! Operators and producers mirror each other: `FooOperator` / `FooProducer`
//! pairs appear throughout the module.
//!
//! The operators are grouped into submodules by cohesive operator+producer
//! cluster; this `mod.rs` carries the shared spine (the [`TileOperator`] /
//! [`TileProducer`] traits, `OperatorBase` and [`ProducerBase`] with their
//! `impl_*_base` macros, and [`TilePathStep`]) and re-exports every cluster so
//! consumers continue to reach items as `tile_operators::X`.

use smol_str::SmolStr;
use std::{
    collections::HashMap,
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicBool, Ordering},
    },
};

use log::trace;

pub use crate::interpreter::tiling::{
    CurryLevel, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
};
use crate::{
    ccl::provenance::NodeId,
    interpreter::operator_graph::{EdgeKind, InputEdgeSpec},
    interpreter::value_probe::ProbeSlot,
    interpreter::{
        ColumnValue, Consumer, Extent, Gate, GatedConsumer, Projection, Scheduler, Value,
        forwarding_consumer, forwarding_consumer_into_field, forwarding_consumer_keeping_keys,
        keys_only, selecting_field, validate_tile, widening,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

use crate::interpreter::LockNow;

mod aggregate;
mod combinators;
mod cycle_slot;
mod extract_final;
mod fan;
mod fanout;
#[cfg(test)]
mod forwarding_tests;
mod helpers;
mod iterate;
mod lookup;
mod map;
#[cfg(test)]
mod notification_scripts;
#[cfg(test)]
mod notification_sound;
mod reshape;
mod scalar;
mod union;

pub use aggregate::*;
pub use combinators::*;
pub use cycle_slot::*;
pub use extract_final::*;
pub use fan::*;
pub use fanout::*;
pub use helpers::*;
pub use iterate::*;
pub use lookup::*;
pub use map::*;
pub use reshape::*;
pub use scalar::*;
pub use union::*;

/// A source's rows, handed to the workers of a pool as morsels.
///
/// A worker asks for a morsel when it needs one, so no queue holds morsels between a source
/// and its workers. A morsel is named by a guard, never by its rows: the worker produces the
/// tile by pulling its own chain at the guard.
pub trait MorselSource: Send + Sync {
    /// The next morsel of at most `rows` rows. Each row is in exactly one claimed morsel,
    /// whichever threads claim.
    ///
    /// [`Claim::Exhausted`] is final. A claim that answers it happens after every claim that
    /// answered a morsel: the dispatcher finishes a pipeline once it has seen `Exhausted` and no
    /// outstanding morsel, and reads that count only because of this order. A source whose
    /// claims are updates of one atomic gets it from acquire-release updates, and one whose
    /// claims take a lock gets it from the lock.
    fn claim(&self, rows: u64) -> Claim;

    /// The keys `arrived` have been added to the source, and their rows are readable. `Everything`
    /// means every key that is ready to read, not every key of the source's extent: keys may
    /// arrive in any order, and a key that is not ready is not claimable. The caller wrote the
    /// rows and made their keys part of the source's yield predicate, the region ready to read,
    /// before it publishes the region, and publishes nothing after [`close`](Self::close). It
    /// holds no lock that the cascade of a notification takes, nor one the source takes. The yield
    /// predicate is not a tile's `domain_predicate`, which says that no further key arrives in a
    /// region. A source that holds every row from the start ignores it.
    fn publish(&self, _arrived: &Projection) {}

    /// No row will be added, and no region will be published after this call. Once every
    /// published row is claimed, `claim` answers [`Claim::Exhausted`]. A source that holds every
    /// row from the start ignores it.
    fn close(&self) {}
}

/// The answer to [`MorselSource::claim`].
pub enum Claim {
    /// The guard naming the morsel.
    Morsel(TileGuard),
    /// Nothing is claimable now, and a row may still arrive.
    Idle,
    /// Every row has been claimed and no row will arrive.
    Exhausted,
}

#[cfg(test)]
impl Claim {
    /// The morsel, or `None` for `Idle` and `Exhausted`.
    pub fn morsel(self) -> Option<TileGuard> {
        match self {
            Claim::Morsel(guard) => Some(guard),
            Claim::Idle | Claim::Exhausted => None,
        }
    }
}

/// Static descriptor of a computation node in the tile dataflow graph.
///
/// An operator knows its output [`Tiling`] and can instantiate a live
/// [`TileProducer`] by subscribing a [`Consumer`].  Operators are
/// constructed at compile time; producers are created on demand at runtime.
pub trait TileOperator: Send + Sync {
    /// Get the extent (type) of this operator.
    fn extent(&self) -> Extent {
        self.tiling().extent()
    }

    /// Return the [`Tiling`] that describes this operator's output shape.
    /// If the operator has unbound arguments, the tiling will be a curried function
    /// from inputs to the output.
    fn tiling(&self) -> &Tiling;

    /// This operator's identity, or `None` for a type that carries no
    /// `OperatorBase`.
    ///
    /// Production operators supply this through [`impl_operator_base`]. The
    /// default exists for test doubles, which need no identity: nothing folds
    /// them into a provenance table and nothing renders them in a pane.
    fn operator_id(&self) -> Option<NodeId> {
        None
    }

    /// State this operator's inputs to `visit`, in the order the graph holds
    /// them.
    ///
    /// The single statement of what an operator holds. The graph walk builds the
    /// operator pane from it, so an input stated nowhere is an edge the pane
    /// does not have and a subtree the pane may lose entirely.
    ///
    /// A visitor rather than a returned list because two inputs are reached
    /// through an `RwLock`: the read lock lives for the call and cannot outlive
    /// it. Required rather than defaulted so that a new operator states its
    /// inputs or fails to compile.
    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>));

    /// The concrete type's short name, e.g. `"MapResult"`.
    ///
    /// Split out of [`inspect`](Self::inspect) so a caller that wants only the
    /// name pays for the name: `inspect` recurses into upstream operators, so
    /// reading a label off it is quadratic in the depth of the graph.
    fn kind(&self) -> &'static str {
        short_type_name::<Self>()
    }

    /// The next operator on the path from this one to the chain a worker pool subscribes: an
    /// `ExtractAggregate` answers its fold, an `Aggregate` the input it folds, and every other
    /// operator `None`, which `run_main` never consults because `plan_main` admits only those
    /// two above the chain (`src/interpreter/design-parallel.md`, "A fold as the breaker").
    fn pool_input(&mut self) -> Option<&mut dyn TileOperator> {
        None
    }

    /// The rows this operator enumerates as morsels the workers of a pool claim, or `None` for
    /// an operator that is not a source the pool cuts. `IterateExtent` over a finite range
    /// answers one. See `src/interpreter/design-parallel.md`, "The dispatcher".
    fn morsel_source(&self) -> Option<Arc<dyn MorselSource>> {
        None
    }

    /// Constructs one producer for `consumer` over the requested `intent_guard` region.
    /// Its [`ProducerBase`] names this operator and holds `scheduler`'s probe slot.
    /// An input's producer comes from the input's own `subscribe`, which attributes it
    /// to that operator.
    /// See `src/interpreter/design-operators.md`, "The producer protocol".
    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer>;

    /// Render this operator and what it holds as an [`InspectNode`].
    ///
    /// The children are [`visit_inputs`](Self::visit_inputs)' `Value` edges, so
    /// an operator states what it holds once and this reads the same answer the
    /// graph walk does. `Share` edges are left out: a fan slot's edge to its
    /// fan input would draw the shared subtree once per branch, and following
    /// only `Value` edges is what makes this terminate without a cycle guard —
    /// they are acyclic, which `assert_graph_invariants` pins.
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new(self.kind()).with_tiling(self.tiling().to_string());
        if let Some(annotation) = self.inspect_annotation() {
            node = node.annotate(annotation);
        }
        let mut children = Vec::new();
        self.visit_inputs(&mut |spec| {
            if let EdgeKind::Value { .. } = spec.kind {
                children.push((spec.role.to_string(), spec.target.inspect(opts)));
            }
        });
        children
            .into_iter()
            .fold(node, |n, (role, child)| n.child(role, child))
    }

    /// An extra label beyond this operator's kind and tiling — a constant's
    /// value, a variant arm's tag. What it holds is not this: that is
    /// [`visit_inputs`](Self::visit_inputs).
    fn inspect_annotation(&self) -> Option<String> {
        None
    }

    /// If Some, represents an equality constraint between all or part of the domain
    /// and the result (i.e. the deepest codomain) of the output of this operator.
    /// Individual operators should override this when they are able to automatically detect this constraint.
    /// For example, [`IterateExtent`] always produces an identity function output, so it returns `Some([])`.
    /// Other operators like [`FanOut`] and [`Memo`] preserve structure, so they pass the value through from their
    /// input
    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        None
    }
}

/// Per-display-name instance counters, shared across all producer types.
///
/// Each key is the display name of a producer (e.g. `"MapApply"`, `"Memo"`),
/// and the value is the next ID to assign.  IDs start at 1.
// shared-state-ok: an ID allocator. What crosses it is a name, never a value: no
// operator reads anything another operator computed, so the producer graph still
// describes the whole dataflow.
static PRODUCER_COUNTERS: OnceLock<Mutex<HashMap<&'static str, usize>>> = OnceLock::new();

/// Subscribe `op` at its universal guard with a consumer that forwards to `shared`, the
/// consumer every input of one operator wakes
/// ([`shared_consumer`](crate::interpreter::shared_consumer)).
pub(crate) fn subscribe_forwarding(
    op: &mut dyn TileOperator,
    shared: &GatedConsumer,
    scheduler: &mut Scheduler,
) -> Box<dyn TileProducer> {
    op.subscribe(
        op.tiling().universal_guard(),
        forwarding_consumer(shared),
        scheduler,
    )
}

/// The consumer an operator passes an input: `consumer` itself where the operator's outermost keys
/// are the input's, so that the input's region reaches the operator's consumer as it is, and a
/// widening consumer where the operator re-keys or reads the input whole. The rule is the
/// operator's row of the projection table (`src/interpreter/design-operators.md`, "Projection
/// guards"): an input is kept iff the row pulls it at the projection.
pub(crate) fn consumer_keeping_keys_if(
    keeps_keys: bool,
    consumer: Box<dyn Consumer>,
) -> Box<dyn Consumer> {
    match keeps_keys {
        true => keys_only(consumer),
        false => widening(consumer),
    }
}

/// [`subscribe_forwarding`] for an input whose outermost keys are the operator's: the input's
/// region reaches the operator's consumer as it is.
pub(crate) fn subscribe_forwarding_keeping_keys(
    op: &mut dyn TileOperator,
    shared: &GatedConsumer,
    scheduler: &mut Scheduler,
) -> Box<dyn TileProducer> {
    op.subscribe(
        op.tiling().universal_guard(),
        forwarding_consumer_keeping_keys(shared),
        scheduler,
    )
}

/// [`subscribe_forwarding_keeping_keys`] where `keeps_keys`, and [`subscribe_forwarding`] where not.
pub(crate) fn subscribe_forwarding_keeping_keys_if(
    keeps_keys: bool,
    op: &mut dyn TileOperator,
    shared: &GatedConsumer,
    scheduler: &mut Scheduler,
) -> Box<dyn TileProducer> {
    match keeps_keys {
        true => subscribe_forwarding_keeping_keys(op, shared, scheduler),
        false => subscribe_forwarding(op, shared, scheduler),
    }
}

/// The concrete type's name with its module path stripped, e.g. `"MapResult"`.
///
/// Every caller wants the same name and each had its own copy:
/// [`TileOperator::kind`], [`TileProducer::name`], [`TileProducer::alloc_id`]'s
/// counter key, and the label `OperatorBase::new` records.
pub(crate) fn short_type_name<T: ?Sized>() -> &'static str {
    let full = std::any::type_name::<T>();
    debug_assert!(
        !full.contains('<'),
        "short_type_name splits on the last `::`, which for a generic type falls \
         inside the generic argument list and returns a fragment of it: {full}"
    );
    full.rsplit_once("::").map_or(full, |(_, tail)| tail)
}

/// Common identity and tiling state shared by every [`TileOperator`].
///
/// The operator-side counterpart of [`ProducerBase`], and it exists for the same
/// reason: every operator held a `tiling` field and a trivial accessor for it.
/// Identity rides here too, because construction is the only point every
/// operator type passes through — there is no shared constructor, so a
/// [`NodeId`] taken anywhere else would be a call site's responsibility to
/// remember.
///
/// The id is drawn from the same counter as an expression node's. Conversion
/// runs after every rewrite phase and mints no expression nodes, so every
/// operator id is greater than every expression id in the same compile, and the
/// two sets are disjoint. `src/ccl/design/provenance.md` owns why that matters.
pub(crate) struct OperatorBase {
    /// Identity, minted at construction. See the type's own docs for why here.
    pub(crate) id: NodeId,
    /// Output tiling for this operator.
    pub(crate) tiling: Tiling,
}

impl OperatorBase {
    /// Mint an identity for an operator and row it against the expression the
    /// ambient conversion recording names.
    ///
    /// Construction is the minting point because it is the only place every
    /// operator type passes through: there is no shared constructor, so every
    /// operator is built at its own call site.
    ///
    /// What the operator holds is not stated here. It is read off the built
    /// operator by [`TileOperator::visit_inputs`], so the two cannot disagree.
    pub(crate) fn new(tiling: Tiling) -> Self {
        let id = NodeId::fresh();
        crate::ccl::provenance::on_mint(id);
        Self { id, tiling }
    }
}

/// Implement [`TileOperator::tiling`] and [`TileOperator::operator_id`] for a
/// concrete operator that stores its shared state in a field named `base`.
///
/// Usage: place `impl_operator_base!();` inside the `impl TileOperator for Foo`
/// block in place of the boilerplate accessors.
macro_rules! impl_operator_base {
    () => {
        fn tiling(&self) -> &Tiling {
            &self.base.tiling
        }
        fn operator_id(&self) -> Option<$crate::ccl::provenance::NodeId> {
            Some(self.base.id)
        }
    };
}
// Re-exported within the crate so the cluster submodules can pull it in with
// `use super::impl_operator_base;`, avoiding a `#[macro_export]` that would leak
// it to the crate root.
pub(crate) use impl_operator_base;

/// Whether an input notification has arrived since the flag was last taken.
/// `subscribe` installs [`Self::consumer`] on the input before the producer exists;
/// an `Arc<AtomicBool>` connects the two and carries no tile values.
/// Each producer has one consumer, including each
/// `FanOut` slot. See `src/interpreter/design-operators.md`, "The notification contract".
/// [`Self::clear`] starts clear, so the first notification passes, including during `subscribe`.
/// [`ProducerBase::sharing`] clears it on every pull, even without reading the input.
///
/// A gate ([`Self::clear`]) also holds the region the notifications it passed named, so that a
/// notification is news unless its region is inside that union: with every region `Everything`
/// the first passes and the rest wait for a pull, as a flag does. The held region records what
/// was passed, not what was delivered. A downstream consumer may drop a region it has no use
/// for, and the gate then holds a region nobody acted on; that suppresses only a later
/// notification inside it, which that consumer would drop as well, and a pull resets it.
#[derive(Clone)]
pub enum Notified {
    /// The input's notification does not reach this producer, so every pull reads —
    /// what an operator whose `subscribe` installs no flag gets. It is also the gate of a
    /// region-driven consumer, which no pull would reopen and which a closed gate would
    /// deprive of its regions.
    Always,
    /// Set when the input notifies, cleared by a pull.
    // shared-state-ok: see the type doc.
    Flag(Arc<AtomicBool>),
    /// A gate: a flag, and the region the notifications passed since the last pull named.
    // shared-state-ok: see the type doc.
    Gate(Arc<GateState>),
}

/// What a [`Notified::Gate`] holds.
pub struct GateState {
    /// Whether a notification has passed since the last pull.
    set: AtomicBool,
    /// Whether that region is `Everything`, which every region is inside: the lock-free answer
    /// for the notifications that name nothing narrower.
    everything: AtomicBool,
    /// The regions held, which have no atomic form: they are interval sets or maps by field, and
    /// only this gate's notifications and pulls touch them.
    // shared-state-ok: see the type doc.
    held: Mutex<GateHeld>,
}

/// The regions a gate holds.
struct GateHeld {
    /// The union of the regions passed since the last pull.
    passed: Projection,
    /// The regions of notifications that re-entered the consumer behind the gate while it was
    /// being notified, which that notification delivers when it returns.
    pending: Projection,
}

impl GateState {
    /// Check, in debug builds, the state every critical section ends in: `set` is clear exactly
    /// where nothing is held, and `everything` is set exactly where everything is.
    fn check_at_rest(&self, held: &GateHeld) {
        debug_assert_eq!(
            self.set.load(Ordering::Relaxed),
            held.passed != Projection::Nothing,
            "a gate's flag and its held region disagree: {:?}",
            held.passed
        );
        debug_assert_eq!(
            self.everything.load(Ordering::Relaxed),
            held.passed == Projection::Everything,
            "a gate's everything flag and its held region disagree: {:?}",
            held.passed
        );
    }
}

impl Notified {
    /// A [`Flag`](Self::Flag) starting set, so the first pull can read before a notification.
    pub fn flag() -> Self {
        Self::Flag(Arc::new(AtomicBool::new(true)))
    }

    /// A live [`Gate`](Self::Gate), starting clear: the gate on an operator's shared consumer,
    /// or on a fan-out's branches, which has passed nothing on yet.
    pub fn clear() -> Self {
        Self::Gate(Arc::new(GateState {
            set: AtomicBool::new(false),
            everything: AtomicBool::new(false),
            held: Mutex::new(GateHeld {
                passed: Projection::Nothing,
                pending: Projection::Nothing,
            }),
        }))
    }

    /// Record that the input has new data, and say whether that is news: for a gate, unless a
    /// notification of `Everything` has passed since the last pull, which is
    /// [`mark_news_of`](Self::mark_news_of) for `Everything`. `Always` is always news.
    pub fn mark_news(&self) -> bool {
        self.mark_news_of(&Projection::Everything)
    }

    /// Record that the input has new data in `region`, and say whether that is news: for a
    /// gate, whether `region` is not inside what the notifications passed since the last pull
    /// named. `Always` is always news.
    pub fn mark_news_of(&self, region: &Projection) -> bool {
        match self {
            Self::Always => true,
            Self::Flag(c) => !c.swap(true, Ordering::AcqRel),
            Self::Gate(gate) => {
                if gate.everything.load(Ordering::Acquire) {
                    return false;
                }
                let mut held = gate.held.lock().expect("a gate's region is never poisoned");
                gate.check_at_rest(&held);
                let passed = &mut held.passed;
                if gate.set.load(Ordering::Acquire) && region.contained_in(passed) {
                    return false;
                }
                // One operator's notifications are all regions of keys or all regions of fields,
                // because its output is a collection or a record: a gate that is given both has
                // a wiring that is not one, and what it would hold of them is less than their
                // union.
                debug_assert!(
                    !matches!(
                        (&*passed, region),
                        (Projection::Keys(_), Projection::Fields(_))
                            | (Projection::Fields(_), Projection::Keys(_))
                    ),
                    "a gate was notified of keys and of fields: {passed:?}, {region:?}"
                );
                *passed = passed.passed_with(region);
                gate.everything
                    .store(*passed == Projection::Everything, Ordering::Release);
                gate.set.store(true, Ordering::Release);
                true
            }
        }
    }

    /// Record that a notification of `region` re-entered the consumer behind this gate while it
    /// was being notified, for that notification to deliver when it returns
    /// ([`take_pending`](Self::take_pending)). Only a gate holds regions.
    pub fn defer(&self, region: &Projection) {
        match self {
            Self::Gate(gate) => {
                let mut held = gate.held.lock().expect("a gate's region is never poisoned");
                held.pending = held.pending.union(region);
            }
            _ => unreachable!("only a gate holds a region to deliver later"),
        }
    }

    /// The regions [`defer`](Self::defer) recorded, and forget them: `Nothing` where none.
    pub fn take_pending(&self) -> Projection {
        match self {
            Self::Gate(gate) => {
                let mut held = gate.held.lock().expect("a gate's region is never poisoned");
                std::mem::replace(&mut held.pending, Projection::Nothing)
            }
            _ => Projection::Nothing,
        }
    }

    /// Whether a notification of `region` would be suppressed now, without recording anything: for
    /// a gate, a notification has passed since the last pull and its region is inside what
    /// passed. `Always` covers every region, and a flag covers any while it is set.
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn covers(&self, region: &Projection) -> bool {
        match self {
            Self::Always => true,
            Self::Flag(c) => c.load(Ordering::Acquire),
            Self::Gate(gate) => {
                let held = gate.held.lock().expect("a gate's region is never poisoned");
                gate.check_at_rest(&held);
                gate.set.load(Ordering::Acquire) && region.contained_in(&held.passed)
            }
        }
    }

    /// Whether the flag is set, without clearing it. `Always` reads set.
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn is_set(&self) -> bool {
        match self {
            Self::Always => true,
            Self::Flag(c) => c.load(Ordering::Acquire),
            Self::Gate(gate) => gate.set.load(Ordering::Acquire),
        }
    }

    /// Record that the input has new data.
    pub fn mark(&self) {
        match self {
            Self::Always => {}
            Self::Flag(c) => c.store(true, Ordering::Release),
            Self::Gate(_) => {
                self.mark_news();
            }
        }
    }

    /// Read and clear. `Always` reads set and stays set. A gate also forgets the region it held.
    ///
    /// A gate's pull begins here. Whenever the lock is free, `set` is clear exactly where the
    /// region held is `Nothing`, and `everything` is set exactly where it is `Everything`: every
    /// critical section ends in that state. So a pull that finds `set` clear has nothing to reset
    /// and returns without the lock, and one that finds it set clears `everything` before `set`
    /// and resets the region before it releases the lock, so a notification that takes the lock
    /// afterwards finds the gate clear and passes. A notification that read `everything` before
    /// the pull began is suppressed, which loses nothing: the pull reads after this returns, so
    /// it reads the data that notification announced. What orders that read after the write is
    /// the data's own synchronization, the producer's mutex in production, and not the atomics
    /// here.
    pub fn take(&self) -> bool {
        match self {
            Self::Always => true,
            Self::Flag(c) => c.swap(false, Ordering::AcqRel),
            Self::Gate(gate) => {
                if !gate.set.load(Ordering::Acquire) {
                    return false;
                }
                let mut held = gate.held.lock().expect("a gate's region is never poisoned");
                gate.check_at_rest(&held);
                gate.everything.store(false, Ordering::Release);
                let was_set = gate.set.swap(false, Ordering::AcqRel);
                held.passed = Projection::Nothing;
                was_set
            }
        }
    }

    /// An input consumer that sets this flag before forwarding the notification downstream.
    pub fn consumer(&self, downstream: Box<dyn Consumer>) -> Box<dyn Consumer> {
        Box::new(FlaggingConsumer {
            flag: self.clone(),
            downstream,
        })
    }
}

/// What [`Notified::consumer`] returns: sets the flag, then forwards the region unchanged.
struct FlaggingConsumer {
    flag: Notified,
    downstream: Box<dyn Consumer>,
}

impl Consumer for FlaggingConsumer {
    fn notify(&mut self, arrived: &Projection) {
        self.flag.mark();
        self.downstream.notify(arrived);
    }

    fn region_driven(&self) -> bool {
        self.downstream.region_driven()
    }
}

/// The regions an input has notified since they were last taken.
///
/// `subscribe` installs [`Self::consumer`] on the input before the producer exists;
/// an `Arc<Mutex<_>>` connects the two and carries no tile values. A region of fields names a
/// change inside a record, which a reader of keys cannot place, so it is recorded as
/// [`Projection::Everything`].
#[derive(Clone)]
pub struct Arrivals(
    // shared-state-ok: see the type doc.
    Arc<Mutex<Projection>>,
);

impl Arrivals {
    /// No region arrived yet.
    pub(crate) fn new() -> Self {
        Self(Arc::new(Mutex::new(Projection::Nothing)))
    }

    /// The union of the regions that arrived since the last call, which resets it.
    pub fn take(&self) -> Projection {
        std::mem::replace(&mut *self.0.lock_now(), Projection::Nothing)
    }

    /// Whether a region has arrived since the last [`take`](Self::take), which it leaves
    /// recorded.
    pub fn pending(&self) -> bool {
        *self.0.lock_now() != Projection::Nothing
    }

    /// An input consumer that records the region before forwarding it downstream.
    pub fn consumer(&self, downstream: Box<dyn Consumer>) -> Box<dyn Consumer> {
        Box::new(RecordingConsumer {
            arrivals: self.clone(),
            downstream,
        })
    }
}

/// What [`Arrivals::consumer`] returns: records the region, then forwards it unchanged.
struct RecordingConsumer {
    arrivals: Arrivals,
    downstream: Box<dyn Consumer>,
}

impl Consumer for RecordingConsumer {
    fn notify(&mut self, arrived: &Projection) {
        let mut held = self.arrivals.0.lock_now();
        *held = held.union(&arrived.keys_only());
        drop(held);
        self.downstream.notify(arrived);
    }

    fn region_driven(&self) -> bool {
        self.downstream.region_driven()
    }
}

/// One collection level of a tile, keyed in [`completion_view`]'s map by the record fields
/// walked through to reach it and its collection depth. `complete` is the
/// region of paths reaching this level the tile calls complete — its own statement, and
/// the one above read a level further in, since a complete key is complete beneath.
struct CompletionNode {
    complete: Predicate,
}

/// One key or value of a tile, at the path that reaches it, so two outputs compare entry by
/// entry. `complete` says whether the tile calls that path complete.
struct Entry {
    value: EntryValue,
    complete: bool,
}

/// What sits at an entry's path: a key, a value, or what a store or an aggregation answers
/// for one row. Compared by equality rather than by its `Debug` rendering, which prints a
/// record's fields in hash order and so differs between equal values.
#[derive(Debug, PartialEq)]
enum EntryValue {
    Key,
    Value(Option<Value>),
    Frontier(Option<crate::interpreter::Position>),
    Row(Tile),
}

type NodeKey = (Vec<SmolStr>, usize);
type EntryKey = (Vec<SmolStr>, Vec<Value>);

/// Flatten `tile` into its collection levels and the entries it holds.
fn completion_view(tile: &Tile) -> (HashMap<NodeKey, CompletionNode>, HashMap<EntryKey, Entry>) {
    fn walk(
        tile: &Tile,
        label: &[SmolStr],
        level: usize,
        rows: &[Option<Vec<Value>>],
        above: &Predicate,
        nodes: &mut HashMap<NodeKey, CompletionNode>,
        entries: &mut HashMap<EntryKey, Entry>,
    ) {
        match tile {
            Tile::DataFunction {
                row_starts,
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                // The rule `Tile::completion_at` states.
                let complete = match level {
                    0 => domain_predicate.clone(),
                    _ => above.descend(1).union(domain_predicate),
                };
                let starts = row_starts;
                let mut keys: Vec<Option<Vec<Value>>> = vec![None; domain.len()];
                for (row, path) in rows.iter().enumerate() {
                    let from = starts.get(row).copied().unwrap_or(domain.len());
                    let to = starts.get(row + 1).copied().unwrap_or(domain.len());
                    let Some(path) = path else { continue };
                    for (key, slot) in keys.iter_mut().enumerate().take(to).skip(from) {
                        if deleted.contains(key) {
                            continue;
                        }
                        let mut at = path.clone();
                        at.push(domain.index_at(key));
                        entries.insert(
                            (label.to_vec(), at.clone()),
                            Entry {
                                value: EntryValue::Key,
                                complete: complete.contains_path(&at),
                            },
                        );
                        *slot = Some(at);
                    }
                }
                walk(codomain, label, level + 1, &keys, &complete, nodes, entries);
                nodes.insert((label.to_vec(), level), CompletionNode { complete });
            }
            Tile::Record { fields, .. } => {
                for (field, field_tile) in fields {
                    let mut label = label.to_vec();
                    label.push(field.clone());
                    walk(field_tile, &label, level, rows, above, nodes, entries);
                }
            }
            Tile::Scalar(column) => {
                for (row, path) in rows.iter().enumerate() {
                    let Some(path) = path else { continue };
                    if row >= column.len() {
                        continue;
                    }
                    entries.insert(
                        (label.to_vec(), path.clone()),
                        Entry {
                            value: EntryValue::Value(Some(column.index_at(row))),
                            // A value at the root is the whole answer once it has arrived:
                            // a scalar holds no more than one.
                            complete: match level {
                                0 => true,
                                _ => above.contains_path(path),
                            },
                        },
                    );
                }
            }
            // A store's row is what it answers: its frontier, each key's seed, and each
            // key's value at every position it has decided. Its changelog is only how it
            // answers — reclaiming a released prefix keeps every carry source a live
            // position folds to, so the answers outside what was released do not move.
            Tile::Store {
                state,
                decided,
                frontier,
                ..
            } => {
                use crate::interpreter::commit_operator::{
                    store_decided_positions, store_frontier, store_seed_value, store_value_at,
                };
                use crate::interpreter::operator_conversion::store_key;
                let part = |name: &str| {
                    let mut l = label.to_vec();
                    l.push(SmolStr::new(name));
                    l
                };
                for (row, path) in rows.iter().enumerate() {
                    let Some(path) = path else { continue };
                    let one = tile.select_rows(&[row]);
                    // A store's seed is fixed for its whole life and a decided position's
                    // value never changes, so both are final wherever the store stands; its
                    // frontier only moves forward, which `completeness_violation`
                    // checks on its own.
                    let complete = true;
                    let entry = |value: EntryValue| Entry { value, complete };
                    entries.insert(
                        (part("frontier"), path.clone()),
                        Entry {
                            value: EntryValue::Frontier(store_frontier(&one)),
                            complete: false,
                        },
                    );
                    let Tile::Store {
                        decided: row_decided,
                        ..
                    } = &one
                    else {
                        unreachable!("a store's rows are stores")
                    };
                    let positions = store_decided_positions(row_decided, 0);
                    let names: Vec<SmolStr> = one.store_keys().cloned().collect();
                    for name in names {
                        let key = store_key(&crate::ccl::Label::from_runtime_key(&name));
                        // A store waiting for its seed has none yet; once it has one it
                        // keeps it.
                        let seed = store_seed_value(&one, &key);
                        entries.insert(
                            (part(&format!("seed.{name}")), path.clone()),
                            Entry {
                                complete: seed.is_some(),
                                value: EntryValue::Value(seed),
                            },
                        );
                        for position in &positions {
                            let mut at = path.clone();
                            at.push(position.value().clone());
                            entries.insert(
                                (part(&name), at),
                                entry(EntryValue::Value(store_value_at(&one, position, &key))),
                            );
                        }
                    }
                }
                // Each part of a store is also a collection over the store's rows, with a
                // statement of its own, and that statement is held to the contract like any
                // other collection's. A release of the store names its positions, which are
                // each part's keys, so a reclaimed prefix leaves every part as released.
                let Tile::Record { fields: logs, .. } = &**state else {
                    unreachable!("a store's state is a record of per-key changelogs")
                };
                for (name, log) in logs {
                    let label = part(&format!("#changelog.{name}"));
                    walk(log, &label, level, rows, above, nodes, entries);
                }
                walk(
                    decided,
                    &part("#decided"),
                    level,
                    rows,
                    above,
                    nodes,
                    entries,
                );
                walk(
                    frontier,
                    &part("#frontier"),
                    level,
                    rows,
                    above,
                    nodes,
                    entries,
                );
            }
            // An aggregation is one accumulator per row, compared row by row. Beneath no
            // level nothing is complete, and a row it has not reached holds nothing yet.
            other if level > 0 => {
                for (row, path) in rows.iter().enumerate().take(other.rows()) {
                    let Some(path) = path else { continue };
                    entries.insert(
                        (label.to_vec(), path.clone()),
                        Entry {
                            value: EntryValue::Row(other.select_rows(&[row])),
                            complete: above.contains_path(path),
                        },
                    );
                }
            }
            _ => {}
        }
    }
    let (mut nodes, mut entries) = (HashMap::new(), HashMap::new());
    walk(
        tile,
        &[],
        0,
        &[Some(Vec::new())],
        &Predicate::False,
        &mut nodes,
        &mut entries,
    );
    (nodes, entries)
}

/// Whether `guard` releases the root value under record fields `label` whole.
fn released_whole(guard: &TileGuard, label: &[SmolStr]) -> bool {
    match guard {
        g if g.is_universal() => true,
        TileGuard::Or(arms) => arms.iter().any(|arm| released_whole(arm, label)),
        TileGuard::Record(fields) => label
            .split_first()
            .and_then(|(field, rest)| fields.get(field).map(|g| released_whole(g, rest)))
            .unwrap_or(false),
        _ => false,
    }
}

/// The paths reaching collection level `level` under record fields `label` that `guard`
/// releases: a domain guard `d` codomain steps in names keys of level `d` and everything
/// beneath them.
fn released_at(guard: &TileGuard, label: &[SmolStr], level: usize) -> Predicate {
    fn walk(guard: &TileGuard, label: &[SmolStr], depth: usize, level: usize) -> Predicate {
        match guard {
            TileGuard::Or(arms) => arms
                .iter()
                .map(|arm| walk(arm, label, depth, level))
                .fold(Predicate::False, |all, one| all.union(&one)),
            TileGuard::Record(fields) => match label.split_first() {
                Some((field, rest)) => fields
                    .get(field)
                    .map_or(Predicate::False, |g| walk(g, rest, depth, level)),
                None => Predicate::False,
            },
            TileGuard::Function(FunctionGuard::Codomain(inner)) if depth < level => {
                walk(inner, label, depth + 1, level)
            }
            // The values of the level itself: a record field's cell, named at the rows its
            // leaf admits.
            TileGuard::Function(FunctionGuard::Codomain(inner)) if depth == level => {
                released_cells_at(inner, label)
            }
            TileGuard::Function(FunctionGuard::Domain(pred)) if depth <= level => {
                pred.descend(level - depth)
            }
            _ => Predicate::False,
        }
    }
    walk(guard, label, 0, level)
}

/// The paths whose value under record fields `label` `guard` names: a keyless leaf's rows.
fn released_cells_at(guard: &TileGuard, label: &[SmolStr]) -> Predicate {
    match guard {
        TileGuard::Or(arms) => arms
            .iter()
            .map(|arm| released_cells_at(arm, label))
            .fold(Predicate::False, |all, one| all.union(&one)),
        TileGuard::Record(fields) => match label.split_first() {
            Some((field, rest)) => fields
                .get(field)
                .map_or(Predicate::False, |g| released_cells_at(g, rest)),
            None => Predicate::False,
        },
        TileGuard::Scalar(pred) | TileGuard::Aggregation(pred) if label.is_empty() => {
            TileGuard::leaf_rows(pred).clone()
        }
        _ => Predicate::False,
    }
}

/// How `result` changes something `last` called complete, apart from removing what
/// `released` has released since: the two rules of `src/interpreter/design-operators.md`,
/// "The completeness contract". `None` where it changes nothing.
///
/// A statement covers every path at its level, including paths under rows that have not
/// arrived, so the second rule applies to them too: a key appearing under a row called
/// complete before it arrived breaks it.
fn completeness_violation(
    name: &str,
    last: &Tile,
    result: &Tile,
    released: &TileGuard,
) -> Option<String> {
    let (last_nodes, last_entries) = completion_view(last);
    let (result_nodes, result_entries) = completion_view(result);
    for ((label, level), node) in &last_nodes {
        let released_here = released_at(released, label, *level);
        let promised = node.complete.minus(&released_here);
        let kept = result_nodes
            .get(&(label.clone(), *level))
            .map_or(Predicate::False, |n| n.complete.clone());
        if !kept.subsumes(&promised) {
            return Some(format!(
                "{name} withdrew completion at level {level} of {label:?}: it called \
                 {promised:?} complete, and now calls only {kept:?} complete"
            ));
        }
    }
    // A root value is released by a release naming it whole, through the record fields that
    // reach it; a path beneath the root by one naming it.
    let is_released = |label: &Vec<SmolStr>, path: &Vec<Value>| match path.len() {
        0 => released_whole(released, label),
        n => released_at(released, label, n - 1).contains_path(path),
    };
    // A release lets a region leave the output, and nothing more: what a producer still
    // holds beneath a complete path, or adds beneath one, is checked whether or not a
    // consumer has since released it. Exempting those would hide exactly the broken
    // promise a consumer releases on.
    for ((label, path), entry) in &last_entries {
        if !entry.complete {
            continue;
        }
        match result_entries.get(&(label.clone(), path.clone())) {
            Some(now) if now.value == entry.value => {}
            None if is_released(label, path) => {}
            now => {
                return Some(format!(
                    "{name} changed {label:?} at {path:?}, which it had called complete: {:?} \
                     then {:?}, in {last:?} then {result:?}, having released {released:?}",
                    entry.value,
                    now.map(|n| &n.value)
                ));
            }
        }
    }
    // A store's frontier only moves forward: a position it has decided stays decided.
    for (key, entry) in &last_entries {
        let (
            EntryValue::Frontier(Some(then)),
            Some(Entry {
                value: EntryValue::Frontier(now),
                ..
            }),
        ) = (&entry.value, result_entries.get(key))
        else {
            continue;
        };
        if !now.as_ref().is_some_and(|now| now >= then) {
            return Some(format!(
                "{name} moved the frontier of {:?} at {:?} back: {then:?} then {now:?}",
                key.0, key.1
            ));
        }
    }
    for (label, path) in result_entries.keys() {
        if last_entries.contains_key(&(label.clone(), path.clone())) || path.is_empty() {
            continue;
        }
        // The collection an entry sits in: a key's own label, or for a value in a record's
        // field, the label that record's collection was reached by.
        let level = path.len() - 1;
        let was_complete = (0..=label.len())
            .rev()
            .find_map(|n| last_nodes.get(&(label[..n].to_vec(), level)))
            .is_some_and(|n| n.complete.contains_path(path));
        if was_complete {
            return Some(format!(
                "{name} added {label:?} at {path:?}, beneath a path it had called complete: \
                 {last:?} then {result:?}"
            ));
        }
    }
    None
}

/// Identity, output shape, release state and notification/probe handles for a producer.
pub struct ProducerBase {
    /// Instance-unique ID, allocated by [`TileProducer::alloc_id`].
    pub id: usize,
    /// The operator that built this producer. `None` only for a test double
    /// built with `ProducerBase::unowned`.
    pub node_id: Option<NodeId>,
    /// The probe slot of the scheduler this producer was subscribed under,
    /// written on every [`TileProducer::get`] while it holds a table.
    pub(crate) probes: ProbeSlot,
    /// Output tiling for this producer.
    pub tiling: Tiling,
    /// Obsolete region of the tiling
    pub obsolete_guard: TileGuard,
    /// The gate on the consumer this producer's operator shares between its inputs
    /// ([`shared_consumer`](crate::interpreter::scheduler::shared_consumer)), cleared by
    /// every pull. `None` for an operator that shares none.
    pub(crate) gate: Option<Notified>,
    /// How many times this producer has been pulled, for the debug check that a woken
    /// consumer pulls (`scheduler::pull_laps`).
    pub(crate) pulls: u64,
    /// The last tile `get` returned, for the debug check that the complete region never
    /// changes ([`completeness_violation`]). Debug builds only; `None` in release.
    pub(crate) last_output: Option<Tile>,
}

impl ProducerBase {
    /// Initialize a producer for `owner`'s operator.
    pub(crate) fn new(
        id: usize,
        tiling: &Tiling,
        owner: &OperatorBase,
        scheduler: &Scheduler,
    ) -> Self {
        Self {
            id,
            node_id: Some(owner.id),
            probes: scheduler.probes().clone(),
            tiling: tiling.clone(),
            obsolete_guard: tiling.empty_guard(),
            gate: None,
            pulls: 0,
            last_output: None,
        }
    }

    /// This producer's operator shares one consumer between its inputs
    /// ([`shared_consumer`](crate::interpreter::shared_consumer)), whose `gate` every pull
    /// clears. `None` for an operator that, in this subscription, shares none.
    pub(crate) fn sharing(mut self, gate: impl Into<Option<Gate>>) -> Self {
        self.gate = gate.into().map(|Gate(notified)| notified);
        self
    }

    /// A producer no operator built, for a test double constructing one
    /// directly. It names no operator and is never probed.
    #[cfg(test)]
    pub(crate) fn unowned(id: usize, tiling: &Tiling) -> Self {
        Self {
            id,
            node_id: None,
            probes: ProbeSlot::default(),
            tiling: tiling.clone(),
            obsolete_guard: tiling.empty_guard(),
            gate: None,
            pulls: 0,
            last_output: None,
        }
    }
}

/// Detach this producer's probe when it goes.
///
/// `LiveProgram::reload`'s teardown drops a replaced version's producers, so
/// their probes go with them, and the probe table never has to decide which
/// entries are still live. An operator the reload kept is not rebuilt, so its
/// producer is not dropped and its probe's readings continue across the swap.
impl Drop for ProducerBase {
    fn drop(&mut self) {
        self.probes.detach(self.node_id, self.id);
    }
}

/// Implement [`TileProducer::base`] and [`TileProducer::base_mut`] for a concrete
/// producer struct that stores its shared state in a field named `base: ProducerBase`.
///
/// Usage: place `impl_producer_base!();` inside the `impl TileProducer for Foo` block
/// in place of the two boilerplate accessor methods.
macro_rules! impl_producer_base {
    () => {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
    };
}
// Re-export the macro within the crate so the cluster submodules can pull it in
// with `use super::impl_producer_base;` — avoiding a `#[macro_export]` that would
// leak it to the crate root.
pub(crate) use impl_producer_base;

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer: Send {
    /// Return the shared identity/tiling state for this producer.
    fn base(&self) -> &ProducerBase;

    /// Return the shared identity/tiling state for this producer.
    fn base_mut(&mut self) -> &mut ProducerBase;

    /// Return the [`Tiling`] that describes this producer's output shape.
    fn tiling(&self) -> &Tiling {
        &self.base().tiling
    }

    /// Return the instance-unique numeric ID assigned at construction.
    fn producer_id(&self) -> usize {
        self.base().id
    }

    /// The [`NodeId`] of the operator that built this producer, or `None` for a
    /// producer built outside any [`TileOperator::subscribe`].
    ///
    /// One operator can build several producers — a `FanOut` slot is
    /// subscribed once per slot — so this identifies the operator and not the
    /// instance. [`producer_id`](Self::producer_id) is the instance.
    fn operator_id(&self) -> Option<NodeId> {
        self.base().node_id
    }

    /// Allocate the next instance ID for this producer type.
    ///
    /// The counter key is derived from `Self`'s type name with the `"Producer"`
    /// suffix stripped.  Call this from each producer's constructor to
    /// initialise its `id` field: `id: Self::alloc_id()`.
    fn alloc_id() -> usize
    where
        Self: Sized,
    {
        let raw: &'static str = short_type_name::<Self>();
        let key: &'static str = raw.strip_suffix("Producer").unwrap_or(raw);
        let map = PRODUCER_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut counters = map.lock().unwrap();
        let counter = counters.entry(key).or_insert(0);
        *counter += 1;
        *counter
    }

    /// Return the name of the concrete producer type, disambiguated by instance.
    ///
    /// The default implementation derives the display name from the concrete
    /// type name by stripping the `"Producer"` suffix, then appends `#<id>`.
    /// For example, `MapResultProducer` with id 3 → `"MapResult#3"`.
    fn name(&self) -> String {
        let raw = short_type_name::<Self>();
        let base = raw.strip_suffix("Producer").unwrap_or(raw);
        format!("{}#{}", base, self.producer_id())
    }

    /// Returns the current obsolete guard for this producer. The producer will
    /// never return any more data in the guarded region via `get`.
    fn obsolete_guard(&self) -> &TileGuard {
        &self.base().obsolete_guard
    }

    /// Call [`get_impl`](Self::get_impl), remove released scalar record cells, and check
    /// the result.
    /// Tiling conformance is asserted in every build; release, structural and completeness
    /// checks require debug assertions. Probe observations occur after those checks.
    /// A debug build also checks that the answer holds only what the projection guard names
    /// ([`Tile::within`]); an operator that forwards the projection to its input answers inside it because the input does, and any other cuts its own answer.
    /// See `src/interpreter/design-operators.md`, "The producer protocol".
    fn get(&mut self, projection_guard: TileGuard) -> Tile {
        // Cleared before the pull, so a notification arriving while it runs passes: the
        // pull may already have read past the input that sent it.
        if let Some(gate) = &self.base().gate {
            gate.take();
        }
        self.base_mut().pulls += 1;
        let asked = cfg!(debug_assertions).then(|| projection_guard.clone());
        let mut result = self.get_impl(projection_guard);
        // Released scalar cells are removed while their enclosing rows remain open;
        // see `src/interpreter/design-operators.md`, "The release contract".
        if let Some(cells) = self.obsolete_guard().released_cells() {
            result.remove_guarded(cells);
        }
        // A duplicate scalar delivery can append cells without identifying the repeated
        // positions. Check every released region here, not just universal releases.
        // See `src/interpreter/design-operators.md`, "The release contract".
        debug_assert!(
            !result.contains_guarded(self.obsolete_guard()),
            "{} returned data it had released: {result:?} overlaps {:?}",
            self.name(),
            self.obsolete_guard(),
        );
        trace!(
            "{} produced {:?} for tiling {}",
            self.name(),
            result,
            self.tiling()
        );
        debug_assert!(validate_tile(&result), "Invalid tile: {result:?}");
        if let Some(asked) = &asked {
            // A guard that is not a projection is left to a producer that restates projections,
            // which panics on it in `get_impl`; one that is, bounds the answer.
            if let Ok(projection) = Projection::of(asked)
                && let Err(outside) = result.within(&projection)
            {
                panic!(
                    "{} answered a pull at {asked:?} with {result:?}, but {outside}",
                    self.name()
                );
            }
        }
        if cfg!(debug_assertions) {
            // A pull states completeness only for the region it returns, so the last output
            // is compared inside that region: a producer asked for one region after another
            // withdraws nothing it said of the first.
            let region = asked.as_ref().and_then(|asked| Projection::of(asked).ok());
            let last_in_region = self.base().last_output.as_ref().map(|last| {
                let mut last = last.clone();
                if let Some(region) = &region {
                    last.restrict_to(region, self.tiling());
                }
                last
            });
            if let Some(last) = &last_in_region
                && let Some(violation) =
                    completeness_violation(&self.name(), last, &result, self.obsolete_guard())
            {
                panic!(
                    "{violation}\nin the producer tree:\n{}",
                    crate::pretty_tree::render_with_max_depth(
                        &self.inspect(&VizOptions::default()),
                        Some(6)
                    )
                );
            }
            // The statement a later pull is held to holds each region's last answer: this pull
            // replaces its own region and leaves the others as they were.
            let stated = match (&region, self.base_mut().last_output.take()) {
                (Some(Projection::Nothing), Some(last)) => last,
                (Some(region @ Projection::Keys(_)), Some(mut last)) => {
                    last.restrict_to(&Projection::Everything.minus(region), self.tiling());
                    let mut answered = result.clone();
                    answered.restrict_to(region, self.tiling());
                    last.merge(answered);
                    last
                }
                _ => result.clone(),
            };
            self.base_mut().last_output = Some(stated);
        }
        assert!(
            result.check_from(self.tiling()),
            "{} produced {result:?}, which does not tile as {}",
            self.name(),
            self.tiling()
        );
        // After `get_impl` rather than around it: `get_impl` pulls this
        // producer's inputs, whose own `get` locks the same probe table, and a
        // lock held across that call overlaps the inner one.
        let base = self.base();
        base.probes.observe_named(
            base.node_id,
            base.id,
            || self.name(),
            &result,
            &base.obsolete_guard,
        );
        result
    }

    /// Produce the tile for `projection_guard`, honoring accumulated releases and completeness.
    /// The [`get`](Self::get) wrapper supplies validation, not general projection or reclamation.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile;

    /// Permanently release a region after checking its shape and normalizing it.
    /// Accumulate the region in [`obsolete_guard`](Self::obsolete_guard); call
    /// [`release_impl`](Self::release_impl) with the normalized argument only if accumulation
    /// changes the stored guard. See `src/interpreter/design-operators.md`, "The release contract".
    fn release(&mut self, obsolete_guard: TileGuard) {
        trace!("{} release: {obsolete_guard:?}", self.name());
        assert!(
            obsolete_guard.check_from(self.tiling()),
            "{obsolete_guard:?} vs {:?}",
            self.tiling()
        );
        // Released in canonical form (`TileGuard::flatten_or`), so a region naming everything
        // beneath some keys reaches `release_impl` as those keys.
        let obsolete_guard = TileGuard::flatten_or(vec![obsolete_guard]);
        let new_guard = self.base().obsolete_guard.union(&obsolete_guard);
        if new_guard != self.base().obsolete_guard {
            self.base_mut().obsolete_guard = new_guard;
            self.release_impl(obsolete_guard);
        }
    }

    /// Honor or reject the normalized release argument, already included in the obsolete guard.
    /// Reclaim local state and forward releases according to this operator's input usage.
    /// Ignoring an unsupported guard does not cancel the wrapper's accumulated promise.
    fn release_impl(&mut self, obsolete_guard: TileGuard);

    /// What this producer keeps of its own between pulls ([`ProducerStateInfo`]).
    ///
    /// A producer that keeps nothing past a pull answers the default, which holds nothing.
    /// What its inputs keep is theirs to report.
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::default()
    }

    /// Inspect this producer as an [`InspectNode`] for visualization.
    ///
    /// Always includes name and tiling, and impls can add children with `add_inspect_children`.
    /// A producer holding state records its [`state_info`](Self::state_info) on the node.
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let node = InspectNode::new(self.name()).with_tiling(self.tiling().to_string());
        let node = match self.state_info().values {
            0 => node,
            held => node.with_held_values(held),
        };
        self.add_inspect_children(node, opts)
    }

    /// Hand `visit` each producer this one pulls, with the role it plays. It is what
    /// [`add_inspect_children`](Self::add_inspect_children) lists by default, and what
    /// `scheduler::pull_laps`'s debug check that a woken
    /// consumer pulls walks. A producer that pulls nothing visits nothing.
    fn visit_input_producers(&self, _visit: &mut dyn FnMut(&str, &dyn TileProducer)) {}

    /// Hook for adding any children to the InspectNode: by default, each producer
    /// [`visit_input_producers`](Self::visit_input_producers) visits, under its role.
    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let mut children = Vec::new();
        self.visit_input_producers(&mut |role, input| {
            children.push((role.to_string(), input.inspect(opts)));
        });
        children
            .into_iter()
            .fold(node, |node, (role, child)| node.child(role, child))
    }
}

/// Values retained by one producer between pulls, excluding its inputs' retained state.
/// The unit is values, not bytes.
/// See `src/interpreter/design-operators.md`, "What a producer holds".
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProducerStateInfo {
    /// The values held: a cached tile's cells ([`Tile::cell_count`]), an accumulator's, or a
    /// store's changelog entries, decided positions and seeds.
    pub values: usize,
}

impl ProducerStateInfo {
    /// `values` held.
    pub fn holding(values: usize) -> Self {
        ProducerStateInfo { values }
    }
}

/// A producer that participates in a cyclic operator graph as an **append-only,
/// position-stable sequencing source** — the commit operator's recurrence (and
/// the changelog induction store) rely on this contract:
///
/// 1. Its output tile is append-only along the sequencing domain: a value once
///    emitted at a position is never changed (only `release` shrinks the view).
/// 2. Positions are absolute and never shift; a released prefix may be compacted
///    away, but the live suffix keeps its position values.
/// 3. Because a released prefix desyncs a fanned slot, a stateful sequencing
///    producer is wired with exactly one consumer (the cycle uses
///    [`FanOut::new_cyclic`] around the *operator*; the producer itself is never
///    fanned). Fanning one is a wiring bug, not a user error.
/// 4. `release` is the acknowledgment: a released prefix signals the region is
///    committed/consumed, and the producer advances its append/compaction cursor
///    in response.
///
/// Implementing this trait is a deliberate statement that the producer obeys the
/// contract above. Invariant (2)'s position-stability is maintained *by
/// construction* (the engine/window appends immutable positions and only
/// compacts released prefixes); [`Self::debug_assert_position_invariant`] does
/// not re-derive it. It cheaply checks the producer's own append/compaction
/// **bookkeeping** — the per-cursor/per-writer state whose desync is how a
/// compaction or wiring bug would actually manifest — in debug builds.
pub(crate) trait CyclicSequencingProducer: TileProducer {
    /// Debug-only check of the append/compaction bookkeeping backing the
    /// append-only / position-stable invariant (contract item 2), called from
    /// the producer's `get` path — e.g. that per-writer cursors stay aligned
    /// with the writer set. A failure is a compaction or wiring bug, not a user
    /// error; a no-op in release builds.
    fn debug_assert_position_invariant(&self);
}

/// Represents a step on a path through a Tile structure
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TilePathStep {
    /// A step into a specific field of a Record
    Record(SmolStr),
    /// A step into the codomain of a function
    Codomain,
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::{
        InspectNode, ProducerBase, Tile, TileGuard, TileOperator, TileProducer, Tiling, VizOptions,
    };
    use crate::interpreter::{ColumnValue, FunctionGuard, LockNow, Predicate, Projection, Value};
    use bit_set::BitSet;
    use intervalsets::{Interval, IntervalSet};
    use std::sync::{Arc, Mutex};

    /// The projection guard naming the keys `[first, last]` of the outermost collection.
    pub(crate) fn keys_between(first: u64, last: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
            IntervalSet::from(Interval::closed(Value::UInt(first), Value::UInt(last))),
        )))
    }

    /// `values` as a collection of integers keyed by position `0..`, stating `complete` of its
    /// whole domain or only of the positions it holds.
    pub(crate) fn ints_by_position(values: &[i64], complete: bool) -> Tile {
        let domain_predicate = match (complete, values.len()) {
            (true, _) => Predicate::True,
            (false, 0) => Predicate::False,
            (false, n) => Predicate::at_or_below(Value::UInt(n as u64 - 1)),
        };
        Tile::data_function(
            ColumnValue::UInts((0..values.len() as u64).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(values.to_vec()))),
            domain_predicate,
            BitSet::new(),
        )
    }

    /// The `(position, value)` entries of a collection of integers keyed by position, in key
    /// order, whatever order the tile holds them in. A row the tile marks deleted is not an
    /// entry, as it is to a consumer.
    pub(crate) fn int_entries(tile: &Tile) -> Vec<(u64, i64)> {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = tile
        else {
            panic!("a collection, got {tile:?}");
        };
        let (ColumnValue::UInts(keys), Tile::Scalar(ColumnValue::Ints(values))) =
            (domain, codomain.as_ref())
        else {
            panic!("positions to integers, got {tile:?}");
        };
        let mut entries: Vec<(u64, i64)> = keys
            .iter()
            .copied()
            .zip(values.iter().copied())
            .enumerate()
            .filter(|(row, _)| !deleted.contains(*row))
            .map(|(_, entry)| entry)
            .collect();
        entries.sort_unstable();
        entries
    }

    /// Assert that a producer answers a projection as the whole of its answer cut to it. `make`
    /// builds the same producer twice: one is pulled at `guard`, the other at the universal
    /// guard, and the second's tile is cut to `guard` and compared. Both are compacted and
    /// ordered by key where the keys are scalars, since a producer may order its rows as it likes.
    pub(crate) fn assert_conforms(make: impl Fn() -> Box<dyn TileProducer>, guard: TileGuard) {
        let normal = |mut tile: Tile| {
            tile.compact();
            // Pairs and other record keys keep the order the producer gave them.
            match &tile {
                Tile::DataFunction {
                    domain: ColumnValue::Records(_),
                    ..
                } => tile,
                _ => crate::interpreter::sort_function_by_domain(tile),
            }
        };
        let mut projected = make();
        let answer = normal(projected.get(guard.clone()));
        let mut whole = make();
        let mut expected = whole.get(whole.tiling().universal_guard());
        expected.restrict_to(&guard.projection("assert_conforms"), whole.tiling());
        assert_eq!(
            answer,
            normal(expected),
            "a pull at {guard:?} is the whole answer cut to it"
        );
    }

    /// A [`TileProducer`] that **conforms to projection**: it answers a fixed tile minus what
    /// has been released, cut to the projection guard it is pulled with. It logs every
    /// projection and every release it receives, which is how a test sees the guard an
    /// operator restated for its input.
    ///
    /// Pull it after releasing, never over a region already pulled and kept: the double is
    /// itself held to the completeness contract.
    pub(crate) struct ProjectionSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        /// The tile it answers from instead of `tile`, which a test rewrites between pulls to
        /// grow its input.
        script: Option<Arc<Mutex<Tile>>>,
        pub(crate) pulled: GuardLog,
        pub(crate) released: GuardLog,
    }

    /// The two logs of a [`ProjectionSpy`]: the projection guards it was pulled with, and the
    /// guards released to it.
    pub(crate) type GuardLog = Arc<Mutex<Vec<TileGuard>>>;

    impl ProjectionSpy {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, GuardLog, GuardLog) {
            let pulled = GuardLog::default();
            let released = GuardLog::default();
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    script: None,
                    pulled: pulled.clone(),
                    released: released.clone(),
                },
                pulled,
                released,
            )
        }
    }

    impl TileProducer for ProjectionSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            self.pulled.lock_now().push(projection_guard.clone());
            let mut tile = match &self.script {
                Some(script) => script.lock_now().clone(),
                None => self.tile.clone(),
            };
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            let projection = projection_guard.projection("ProjectionSpy");
            tile.restrict_to(&projection, self.tiling());
            tile
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.lock_now().push(obsolete_guard);
        }
    }

    /// An operator over a fixed tile whose producers are [`ProjectionSpy`]s sharing one pair of
    /// logs, so a test can build a fan-out or a memo over it and read what reaches the input.
    pub(crate) struct ProjectionSpyOp {
        tile: Tile,
        tiling: Tiling,
        pulled: GuardLog,
        released: GuardLog,
    }

    impl ProjectionSpyOp {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, GuardLog, GuardLog) {
            let (pulled, released) = (GuardLog::default(), GuardLog::default());
            (
                Self {
                    tile,
                    tiling,
                    pulled: pulled.clone(),
                    released: released.clone(),
                },
                pulled,
                released,
            )
        }
    }

    impl TileOperator for ProjectionSpyOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            mut consumer: Box<dyn super::Consumer>,
            _scheduler: &mut super::Scheduler,
        ) -> Box<dyn TileProducer> {
            consumer.notify(&Projection::Everything);
            let (mut spy, _, _) = ProjectionSpy::new(self.tile.clone(), self.tiling.clone());
            spy.pulled = self.pulled.clone();
            spy.released = self.released.clone();
            Box::new(spy)
        }
    }

    /// A test helper TileProducer that returns a pre-determined tile.
    /// Useful for testing TileOperators by injecting tiles directly.
    pub(crate) struct TestTileProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
    }

    impl TestTileProducer {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> Self {
            Self {
                base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                tile,
            }
        }
    }

    /// A collection of `Int` keyed by `keys`, each key holding its own value, with `decided`
    /// stated complete.
    pub(crate) fn int_column(keys: Vec<u64>, decided: Predicate) -> Tile {
        let values = keys.iter().map(|&key| key as i64).collect();
        Tile::data_function(
            ColumnValue::from_uints(keys),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            decided,
            BitSet::new(),
        )
    }

    /// A [`TileProducer`] that answers each pull with the tile its shared cell holds, cut to
    /// the projection and minus what has been released to it, so a test can change its input
    /// between pulls. What a producer states on one pull
    /// constrains what it may answer on the next (`src/interpreter/design-operators.md`,
    /// "The completeness contract"), which a fixed tile cannot exercise.
    pub(crate) struct ScriptedProducer {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Arc<Mutex<Tile>>,
    }

    impl ScriptedProducer {
        /// The producer, and the cell a test writes the next pull's answer into.
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, Arc<Mutex<Tile>>) {
            let cell = Arc::new(Mutex::new(tile));
            let producer = Self {
                base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                tile: cell.clone(),
            };
            (producer, cell)
        }
    }

    impl TileProducer for ScriptedProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
            let mut tile = self.tile.lock_now().clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            let projection = projection_guard.projection("ScriptedProducer");
            tile.restrict_to(&projection, self.tiling());
            tile
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// An operator whose producer is a [`ScriptedProducer`] over a cell the test keeps, so a
    /// test can feed a growing input through a real consumer. The producer answers the cell
    /// minus what has been released to it.
    pub(crate) struct ScriptedOp {
        cell: Arc<Mutex<Tile>>,
        tiling: Tiling,
    }

    impl ScriptedOp {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, Arc<Mutex<Tile>>) {
            let cell = Arc::new(Mutex::new(tile));
            (
                Self {
                    cell: cell.clone(),
                    tiling,
                },
                cell,
            )
        }
    }

    impl TileOperator for ScriptedOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            mut consumer: Box<dyn super::Consumer>,
            _scheduler: &mut super::Scheduler,
        ) -> Box<dyn TileProducer> {
            consumer.notify(&Projection::Everything);
            Box::new(ScriptedProducer {
                base: ProducerBase::unowned(ScriptedProducer::alloc_id(), &self.tiling),
                tile: self.cell.clone(),
            })
        }
    }

    /// A consumer that logs the region of each notification it receives. `driven` is its
    /// [`Consumer::region_driven`].
    pub(crate) struct RegionLog {
        regions: Arc<Mutex<Vec<Projection>>>,
        driven: bool,
    }

    impl RegionLog {
        pub(crate) fn new(driven: bool) -> (Self, Arc<Mutex<Vec<Projection>>>) {
            let regions = Arc::new(Mutex::new(Vec::new()));
            (
                Self {
                    regions: regions.clone(),
                    driven,
                },
                regions,
            )
        }
    }

    impl super::Consumer for RegionLog {
        fn notify(&mut self, arrived: &Projection) {
            self.regions.lock_now().push(arrived.clone());
        }

        fn region_driven(&self) -> bool {
            self.driven
        }
    }

    /// A consumer that acts on the region and never pulls is not gated, so the consumer that
    /// records the region before it says what the consumer behind it says.
    #[test]
    fn a_recording_consumer_is_region_driven_as_its_downstream_is() {
        let arrivals = super::Arrivals::new();
        for driven in [true, false] {
            let (log, _) = RegionLog::new(driven);
            assert_eq!(
                arrivals.consumer(Box::new(log)).region_driven(),
                driven,
                "downstream driven: {driven}"
            );
        }
    }

    /// The consumer a [`NotifyingOp`] was subscribed with, which a test notifies through.
    pub(crate) type InputConsumer = Arc<Mutex<Option<Box<dyn super::Consumer>>>>;

    /// An operator over a fixed tile that keeps the consumer it is subscribed with, so a test
    /// notifies an operator above it from where the operator's input would.
    pub(crate) struct NotifyingOp {
        tile: Tile,
        tiling: Tiling,
        consumer: InputConsumer,
        script: Option<Arc<Mutex<Tile>>>,
        pulled: GuardLog,
    }

    impl NotifyingOp {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, InputConsumer) {
            let consumer = InputConsumer::default();
            (
                Self {
                    tile,
                    tiling,
                    consumer: consumer.clone(),
                    script: None,
                    pulled: GuardLog::default(),
                },
                consumer,
            )
        }

        /// An operator whose producer answers what the returned cell holds, cut to the guard it
        /// is pulled with, so a test grows its input between pulls, and the log of the guards
        /// it was pulled with.
        pub(crate) fn scripted(
            tile: Tile,
            tiling: Tiling,
        ) -> (Self, InputConsumer, Arc<Mutex<Tile>>, GuardLog) {
            let (mut op, consumer) = Self::new(tile.clone(), tiling);
            let cell = Arc::new(Mutex::new(tile));
            op.script = Some(cell.clone());
            let pulled = op.pulled.clone();
            (op, consumer, cell, pulled)
        }
    }

    impl TileOperator for NotifyingOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(super::InputEdgeSpec<'_>)) {}

        fn tiling(&self) -> &Tiling {
            &self.tiling
        }

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn super::Consumer>,
            _scheduler: &mut super::Scheduler,
        ) -> Box<dyn TileProducer> {
            *self.consumer.lock_now() = Some(consumer);
            let (mut spy, _, _) = ProjectionSpy::new(self.tile.clone(), self.tiling.clone());
            spy.script = self.script.clone();
            spy.pulled = self.pulled.clone();
            Box::new(spy)
        }
    }

    /// Notify through the consumer a [`NotifyingOp`] was subscribed with.
    pub(crate) fn notify_input(consumer: &InputConsumer, arrived: &Projection) {
        consumer
            .lock_now()
            .as_mut()
            .expect("the operator was subscribed")
            .notify(arrived);
    }

    /// A store's parts are collections held to the contract like any other: a decided set
    /// stated `True` that gains a position has added a key beneath a complete path. The same
    /// growth under a statement naming only what is decided passes.
    #[test]
    fn a_store_part_growing_beneath_its_own_statement_is_reported() {
        use crate::interpreter::commit_operator::{CommitEngine, full_store_tiling};
        use crate::interpreter::operator_conversion::store_key;
        use crate::interpreter::{BaseType, Extent, FunctionGuard, Position, Predicate, Value};
        use std::collections::HashMap;
        let tiling = full_store_tiling(
            Extent::Base(BaseType::UInt),
            HashMap::from([("acc".into(), Tiling::Scalar(Extent::Base(BaseType::Int)))]),
        );
        let mut engine = CommitEngine::unopened();
        let step = |engine: &mut CommitEngine, p: u64| {
            let writes = HashMap::from([(
                store_key(&crate::ccl::Label::new("acc")),
                Value::Int(p as i64),
            )]);
            engine.step(Position::new(Value::UInt(p)), Some(writes));
            engine.render_full_store_tile(&tiling)
        };
        let last = step(&mut engine, 0);
        let result = step(&mut engine, 1);
        let released = TileGuard::Function(FunctionGuard::Domain(Predicate::False));
        assert_eq!(
            super::completeness_violation("honest", &last, &result, &released),
            None
        );

        let claim_all = |mut tile: Tile| {
            if let Tile::Store { decided, .. } = &mut tile
                && let Tile::DataFunction {
                    domain_predicate, ..
                } = &mut **decided
            {
                *domain_predicate = Predicate::True;
            }
            tile
        };
        let message = super::completeness_violation(
            "claims_all",
            &claim_all(last.clone()),
            &claim_all(result.clone()),
            &released,
        )
        .expect("a decided set stated whole while it grows is reported");
        assert!(
            message.contains("#decided")
                && message.contains("beneath a path it had called complete"),
            "{message}"
        );
    }

    /// A value in a record's field filled in beneath a key already called complete is an
    /// addition beneath a complete path, which the completeness contract forbids.
    #[test]
    fn a_record_field_filled_beneath_a_complete_key_is_reported() {
        use crate::interpreter::{ColumnValue, Predicate};
        use bit_set::BitSet;
        use std::collections::HashMap;
        let with_n = |n: ColumnValue| {
            // Built directly rather than through `Tile::data_function`, which a tile holding
            // a complete key with an empty field need not pass: this is the check's input.
            Tile::DataFunction {
                row_starts: vec![0],
                domain: ColumnValue::UInts(vec![0]),
                codomain: Box::new(Tile::record(HashMap::from([
                    ("n".into(), Tile::Scalar(n)),
                    (
                        "xs".into(),
                        Tile::grouped(
                            vec![0],
                            ColumnValue::UInts(vec![]),
                            Box::new(Tile::Scalar(ColumnValue::UInts(vec![]))),
                            Predicate::False,
                            BitSet::new(),
                        ),
                    ),
                ]))),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
            }
        };
        let last = with_n(ColumnValue::Ints(vec![]));
        let result = with_n(ColumnValue::Ints(vec![5]));
        let violation = super::completeness_violation(
            "a_record_field",
            &last,
            &result,
            &TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
        )
        .expect("an addition beneath a complete key is reported");
        assert!(
            violation.contains("beneath a path it had called complete"),
            "{violation}"
        );
    }

    /// A stream of `0..8` whose answer holds the keys `from..=to` and states `stated` complete.
    fn answered(from: u64, to: u64, stated: (u64, u64)) -> (Tile, Tiling) {
        use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Value};
        use bit_set::BitSet;
        let region = |first: u64, last: u64| {
            Predicate::intervals(IntervalSet::from(Interval::closed(
                Value::UInt(first),
                Value::UInt(last),
            )))
        };
        let tile = Tile::data_function(
            ColumnValue::from_uints((from..=to).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                (from..=to).map(|key| key as i64).collect(),
            ))),
            region(stated.0, stated.1),
            BitSet::new(),
        );
        let tiling = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        (tile, tiling)
    }

    /// A producer pulled at one region after another keeps what it stated of each: a pull of a
    /// disjoint region between two pulls of the first withdraws nothing, and answering the first
    /// again as it did passes.
    #[test]
    fn a_producer_asked_for_two_regions_in_turn_may_repeat_its_first_answer() {
        use crate::interpreter::tile_operators::test_helpers::{ScriptedProducer, keys_between};
        let (first, tiling) = answered(0, 3, (0, 3));
        let (mut producer, answer) = ScriptedProducer::new(first.clone(), tiling);
        producer.get(keys_between(0, 3));
        *answer.lock_now() = answered(4, 7, (4, 7)).0;
        producer.get(keys_between(4, 7));
        *answer.lock_now() = first;
        producer.get(keys_between(0, 3));
    }

    /// An input that states a region complete, answers a pull of another region, and then
    /// retracts the first when it is pulled there again has broken the contract, though the
    /// pull before the retraction was at the other region.
    #[test]
    #[should_panic(expected = "withdrew completion")]
    fn a_producer_that_retracts_a_region_after_a_pull_of_another_is_reported() {
        use crate::interpreter::tile_operators::test_helpers::{ScriptedProducer, keys_between};
        let (first, tiling) = answered(0, 3, (0, 3));
        let (mut producer, answer) = ScriptedProducer::new(first, tiling);
        producer.get(keys_between(0, 3));
        *answer.lock_now() = answered(4, 7, (4, 7)).0;
        producer.get(keys_between(4, 7));
        *answer.lock_now() = answered(0, 3, (0, 1)).0;
        producer.get(keys_between(0, 3));
    }

    /// A [`TileProducer`] that answers with a fixed tile, less what it has been released, and
    /// records every release guard it is handed, for asserting that a release *propagates*.
    pub(crate) struct ReleaseSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        pub(crate) released: Arc<Mutex<Vec<TileGuard>>>,
    }

    impl ReleaseSpy {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, Arc<Mutex<Vec<TileGuard>>>) {
            let released = Arc::new(Mutex::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    released: released.clone(),
                },
                released,
            )
        }
    }

    impl TileProducer for ReleaseSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.lock_now().push(obsolete_guard);
        }
    }

    impl TileProducer for TestTileProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// A [`TileProducer`] that **honors** the release contract: it answers with a
    /// fixed tile minus everything released so far, and logs each guard handed to
    /// it.
    ///
    /// Use this over [`ReleaseSpy`] whenever a test pulls again *after* releasing.
    /// A double that re-answers released rows is itself the contract violation, so
    /// the assertion in [`TileProducer::get`] fires on the double before the
    /// behavior under test is ever reached.
    pub(crate) struct QuietSpy {
        pub(crate) base: ProducerBase,
        pub(crate) tile: Tile,
        pub(crate) released: Arc<Mutex<Vec<TileGuard>>>,
    }

    impl QuietSpy {
        pub(crate) fn new(tile: Tile, tiling: Tiling) -> (Self, Arc<Mutex<Vec<TileGuard>>>) {
            let released = Arc::new(Mutex::new(Vec::new()));
            (
                Self {
                    base: ProducerBase::unowned(Self::alloc_id(), &tiling),
                    tile,
                    released: released.clone(),
                },
                released,
            )
        }
    }

    impl TileProducer for QuietSpy {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            let mut tile = self.tile.clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile.compact();
            tile
        }

        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.released.lock_now().push(obsolete_guard);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Consumer, InputEdgeSpec, OperatorBase, ProducerBase, Scheduler, Tile, TileGuard,
        TileOperator, TileProducer, Tiling,
    };
    use crate::interpreter::{Extent, types::BaseType, types::ColumnValue};

    fn int_tiling() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    struct OneRow {
        base: ProducerBase,
    }

    impl TileProducer for OneRow {
        impl_producer_base!();

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::Scalar(ColumnValue::Ints(vec![7]))
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    struct Leaf {
        base: OperatorBase,
    }

    impl TileOperator for Leaf {
        impl_operator_base!();

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(OneRow {
                base: ProducerBase::new(
                    OneRow::alloc_id(),
                    &self.base.tiling,
                    &self.base,
                    scheduler,
                ),
            })
        }
    }

    /// A producer subscribed before probing is switched on is probed once it
    /// is, under its operator's id: probes attach on demand, not at build.
    #[test]
    fn a_producer_is_probed_under_its_operator_once_its_scheduler_enables_probing() {
        let mut op = Leaf {
            base: OperatorBase::new(int_tiling()),
        };
        let mut scheduler = Scheduler::new();
        let mut producer = op.subscribe(
            int_tiling().universal_guard(),
            Box::new(|| {}),
            &mut scheduler,
        );
        assert_eq!(producer.operator_id(), op.operator_id());

        producer.get(int_tiling().universal_guard());
        assert!(!scheduler.probes().is_enabled());

        scheduler.probes().enable();
        producer.get(int_tiling().universal_guard());
        let keys: Vec<_> = scheduler
            .probes()
            .with_table(|table| table.probe_keys().collect())
            .expect("probing is on");
        assert_eq!(keys, vec![(op.operator_id(), producer.producer_id())]);

        drop(producer);
        assert_eq!(
            scheduler
                .probes()
                .with_table(|table| table.probe_keys().count()),
            Some(0),
            "dropping a producer detaches its probe",
        );
    }
}

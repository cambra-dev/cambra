use log::trace;
use std::{
    cell::{Cell, RefCell},
    rc::{Rc, Weak},
};

use super::*;
use crate::interpreter::operator_graph::{share, value};
use crate::{
    interpreter::{
        Consumer, Position, Projection, Scheduler,
        scheduler::{
            GatedConsumer, WakeupQueue, forwarding_consumer_keeping_keys, shared_consumer,
        },
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Re-entrancy bookkeeping for cyclic op graphs.  Stored in
/// [`FanOutShared::reentrancy`] only for fan-outs constructed via
/// [`FanOut::new_cyclic`]; non-cyclic fan-outs leave it `None` and pay
/// none of the cyclic-mode overhead.
///
/// A fan-out is "cyclic" iff one of its slots feeds (transitively)
/// back into its own input.  In practice this is the commit store's
/// recurrence: one slot feeds back into the store's own input and the
/// body's prior-value reads (`get_prev_txn`) close the cycle.  In that setup,
/// subscribing or pulling one slot can synchronously trigger the same
/// operation on a sibling slot — the re-entrancy state below catches
/// that and serves from the cache instead of recursively re-entering the
/// inner producer.
struct FanOutReentrancy {
    /// Cache of the most-recently-returned tile from the inner producer,
    /// used to serve re-entrant `FanOutProducer::get_impl` calls.
    ///
    /// **Replace, not merge**: typical inner producers ([`Memo`] in
    /// particular) already return cumulative tiles, so each non-reentrant
    /// pull supplants the previous cache rather than appending to it.
    cached_tile: Tile,
    /// Re-entrancy guard for the inner subscribe path.  `FanOutSlot::subscribe`
    /// of one slot can transitively trigger `subscribe` on a sibling
    /// (e.g. an induction loop's drive subscribes to its store slot while
    /// the store is subscribing the body that reads the drive).
    /// The re-entrant call sees this set, skips the inner subscribe (the
    /// outer call is doing it), and just returns a `FanOutProducer`.
    subscribing_inner: bool,
}

/// Mutable state shared across all slots from the same [`FanOut`] and all
/// [`FanOutProducer`]s it creates.  Wrapping this in `Rc<RefCell<...>>` and
/// creating it eagerly in [`FanOut::new`] ensures that every slot produced by
/// [`FanOut::slot`] shares the same object from the start — even before any
/// [`TileOperator::subscribe`] call has initialised the inner producer.
struct FanOutShared {
    /// Instance ID shared by all [`FanOutProducer`]s from the same fan-out group.
    id: usize,
    /// Inner producer, set on the first [`FanOutSlot::subscribe`] call.
    ///
    /// In cyclic mode (see [`FanOutReentrancy`]), this is also **taken out**
    /// during the inner pull in `FanOutProducer::get_impl` so that
    /// re-entrant calls from cyclic op graphs can detect re-entrance by
    /// finding `None` and fall back to the cached tile.
    producer: Option<Box<dyn TileProducer>>,
    /// Every consumer registered via [`FanOutSlot::subscribe`], in order.
    ///
    /// Stored as `Rc<RefCell<...>>` so that the notification closure can clone the
    /// handles, release the `shared` borrow, and then call each consumer without
    /// holding `shared` across the notification.  This prevents a re-entrant panic
    /// when a consumer (e.g. `SinkConsumer`) calls back into `FanOutProducer::get_impl`,
    /// which itself needs `shared.borrow_mut()`.
    consumers: Vec<Rc<RefCell<Box<dyn Consumer>>>>,
    /// Per-subscriber release guards; intersected before passing upstream.
    release_guards: Vec<TileGuard>,
    /// What every subscriber had agreed to release the last time one released,
    /// and so what this fan-out has already passed upstream.
    ///
    /// A subscriber registering from now on starts here rather than at nothing.
    /// The region is gone: the fan-out told its input it would not be read again,
    /// so the input is free to have dropped it and a late subscriber that claimed
    /// to still want it would hold the intersection back at a frontier no one is
    /// waiting on. Within one version every subscription is made before any data
    /// flows, so this is the empty guard and seeding from it changes nothing;
    /// across a version handover it is what a rebuilt subscriber inherits from the
    /// one it replaces.
    released: TileGuard,
    /// The highest position [`released`](Self::released) has ever named, for an
    /// output whose domain is a monotone `UInt` iteration position.
    ///
    /// Kept alongside the guard rather than read off it, because the guard loses
    /// the number at the end: a consumer that finishes an iteration releases the
    /// whole domain, and a universal release names no position. This watermark
    /// only ever rises, so it still says where the iteration got to after that
    /// last release.
    ///
    /// [`released`]: FanOutShared::released
    released_position: Option<Position>,
    /// Each subscriber's slot number, parallel to [`release_guards`] and
    /// [`consumers`].
    ///
    /// The [`FanOutProducer`] a subscription handed out owns the strong side, so
    /// a dead entry means that subscriber's producer has been dropped. Its slot
    /// is then skipped: it neither blocks the release intersection nor gets
    /// notified.
    ///
    /// A `Cell<usize>` rather than a bare token because the slot number *is* the
    /// subscription's identity, and [`compact`](Self::compact) renumbers. A
    /// producer reads its index out of the cell it shares with this entry, so
    /// dropping dead slots stays compatible with addressing a guard by index:
    /// the survivors are told their new numbers. Without that the list would
    /// grow by one dead slot per replaced subscriber on every reload, forever,
    /// and both the notify walk and the release intersection scan it.
    ///
    /// [`release_guards`]: FanOutShared::release_guards
    /// [`consumers`]: FanOutShared::consumers
    subscribers: Vec<Weak<Cell<usize>>>,
    /// Re-entrancy bookkeeping for cyclic op graphs.  `None` for non-cyclic
    /// fan-outs (the overwhelming majority); `Some` only when constructed
    /// via [`FanOut::new_cyclic`].
    reentrancy: Option<FanOutReentrancy>,
    /// The name of every producer [`producer`](Self::producer)'s chain
    /// registered with a data source when it was subscribed.
    ///
    /// The chain is subscribed once and owned here, so these producers live as
    /// long as this fan-out does. What a program branch that holds this fan-out
    /// holds of each source is read off it ([`FanOut::source_producers`]).
    source_producers: Vec<String>,
    /// Set when the input's notification is passed to the branches, cleared when a branch
    /// pulls. A second one before that says nothing the first did not, so it stops here, as
    /// it does at an operator's shared consumer (`crate::interpreter::GatedConsumer`).
    forwarded: Notified,
}

impl FanOutShared {
    /// The slots whose subscriber still exists, in subscription order.
    fn live_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.subscribers
            .iter()
            .enumerate()
            .filter(|(_, s)| s.strong_count() > 0)
            .map(|(i, _)| i)
    }

    /// Drop every slot whose subscriber is gone, renumbering the survivors.
    ///
    /// Each surviving producer learns its new index through the `Cell` it shares
    /// with its entry in [`subscribers`](Self::subscribers), so the three
    /// parallel vectors stay bounded by the number of live subscriptions rather
    /// than by the number ever made.
    ///
    /// Safe only when no producer is mid-pull, since a renumber between a
    /// producer reading its index and using it would address another
    /// subscriber's guard. [`FanOut::reopen`] is the one caller, and it runs at a
    /// version handover with the graph already torn down.
    fn compact(&mut self) {
        // Upgrade once: `keep` and the renumbering must agree on which slots are
        // live, and reading liveness twice would let them disagree.
        let live: Vec<_> = self.subscribers.iter().map(Weak::upgrade).collect();
        if live.iter().all(Option::is_some) {
            return;
        }
        for (next, cell) in live.iter().flatten().enumerate() {
            cell.set(next);
        }
        let keep: Vec<bool> = live.iter().map(Option::is_some).collect();
        retain_flagged(&mut self.subscribers, &keep);
        retain_flagged(&mut self.consumers, &keep);
        retain_flagged(&mut self.release_guards, &keep);
        debug_assert_eq!(
            self.consumers.len(),
            self.subscribers.len(),
            "consumers stay parallel to subscribers"
        );
        debug_assert_eq!(
            self.release_guards.len(),
            self.subscribers.len(),
            "release guards stay parallel to subscribers"
        );
    }
}

/// Keep the elements of `v` whose flag in `keep` is set, in order.
fn retain_flagged<T>(v: &mut Vec<T>, keep: &[bool]) {
    debug_assert_eq!(v.len(), keep.len(), "one flag per element");
    let mut flags = keep.iter();
    v.retain(|_| *flags.next().unwrap_or(&false));
}

/// The consumer a fan-out installs on its input: it forwards the input's region to every live
/// slot's consumer. One notification passes between pulls and the next is dropped with its region,
/// which a slot consumer that pulls does not need, since its pull reads whatever arrived.
struct FanOutInput {
    shared: Weak<RefCell<FanOutShared>>,
}

impl Consumer for FanOutInput {
    fn notify(&mut self, arrived: &Projection) {
        // Clone the consumer handles while holding a short borrow, then release the borrow before
        // calling notify(). This prevents a re-entrant panic when a consumer (e.g. SinkConsumer)
        // calls FanOutProducer::get_impl(), which needs shared.borrow_mut() for the same Rc.
        let Some(shared_rc) = self.shared.upgrade() else {
            return;
        };
        let consumers = {
            let shared = shared_rc.borrow();
            if !shared.forwarded.mark_news() {
                return;
            }
            shared
                .live_indices()
                .map(|i| shared.consumers[i].clone())
                .collect::<Vec<_>>()
        };
        for c in &consumers {
            c.borrow_mut().notify(arrived);
        }
    }
}

/// RAII guard for the cyclic `FanOut` `subscribing_inner` flag.  Created
/// when we set the flag `true` to drive the inner `subscribe`; its `Drop`
/// resets the flag to `false`.  This makes the path panic-safe — if
/// `input.subscribe(...)` unwinds, the flag is still reset so a later
/// (re-)subscribe attempt doesn't get silently skipped.
struct SubscribingInnerGuard<'a> {
    shared: &'a Rc<RefCell<FanOutShared>>,
}

impl<'a> Drop for SubscribingInnerGuard<'a> {
    fn drop(&mut self) {
        if let Some(re) = self.shared.borrow_mut().reentrancy.as_mut() {
            re.subscribing_inner = false;
        }
    }
}

/// RAII guard for the cyclic `FanOut`'s "producer taken out" pattern in
/// `FanOutProducer::get_impl`.  Owns the temporarily-extracted inner
/// producer and on `Drop` puts it back into `shared.producer`, so a
/// panic from the inner `producer.get(...)` doesn't leave
/// `shared.producer = None` forever (which would break every later
/// pull on this fan-out).
struct TakenProducerGuard<'a> {
    shared: &'a Rc<RefCell<FanOutShared>>,
    /// Wrapped in `Option` so the destructor can `take()` the producer
    /// and move it back into `shared` (you can't move out of `&mut self`
    /// fields in `Drop`, but `Option::take` swaps the value).
    producer: Option<Box<dyn TileProducer>>,
}

impl<'a> Drop for TakenProducerGuard<'a> {
    fn drop(&mut self) {
        if let Some(producer) = self.producer.take() {
            self.shared.borrow_mut().producer = Some(producer);
        }
    }
}

/// Allows for creating multiple TileOperators that all point to the same
/// underlying operator.  Call [`FanOut::slot`] to get additional handles;
/// subscribing to any handle will reuse the same inner producer.
pub struct FanOut {
    // shared-state-ok: the fan-out's own input operator, shared with the slots
    // that are views of this one operator. It holds an *operator*, not values
    // passed between operators — the same reason `CycleSlot` is legitimate.
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that slots produced by
    /// [`FanOut::slot`] always share the same object.
    shared: Rc<RefCell<FanOutShared>>,
    /// Whether any slots have been created yet.
    // shared-state-ok: construction-time bookkeeping of the `FanOut` itself, not a
    // channel between operators — it records that `slot` has been called, and no
    // value ever passes through it.
    used: RefCell<bool>,
}

impl FanOut {
    /// Construct a new `FanOut` wrapping `input`.  Use this for ordinary
    /// (non-cyclic) op graphs; the resulting fan-out doesn't pay any
    /// cyclic-mode overhead.  If a slot of this fan-out ends up
    /// feeding back into its own input (e.g. a store recurrence closing
    /// through the fan-out), use [`FanOut::new_cyclic`] instead.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_with_reentrancy(input, None)
    }

    /// Construct a cyclic [`FanOut`].  Sets up the re-entrancy bookkeeping
    /// (a cached tile snapshot + a subscribe-in-progress flag) needed when
    /// a slot of this fan-out transitively feeds back into its own input.
    ///
    /// The cost relative to [`FanOut::new`] is one `Tile` clone per pull
    /// (to refresh the cache), so non-cyclic users should stick with `new`.
    /// Called for the stores a recurrence is built around — the commit store and
    /// the induction store. The slot that closes the cycle is a
    /// [`recurrence_slot`](Self::recurrence_slot), not a
    /// [`slot`](Self::slot).
    pub fn new_cyclic(input: Box<dyn TileOperator>) -> Self {
        let cached_tile = input.tiling().empty_tile();
        Self::new_with_reentrancy(
            input,
            Some(FanOutReentrancy {
                cached_tile,
                subscribing_inner: false,
            }),
        )
    }

    fn new_with_reentrancy(
        input: Box<dyn TileOperator>,
        reentrancy: Option<FanOutReentrancy>,
    ) -> Self {
        let tiling = input.tiling().clone();
        let shared = Rc::new(RefCell::new(FanOutShared {
            id: FanOutProducer::alloc_id(),
            producer: None,
            consumers: Vec::new(),
            release_guards: Vec::new(),
            released: tiling.empty_guard(),
            released_position: None,
            subscribers: Vec::new(),
            reentrancy,
            forwarded: Notified::clear(),
            source_producers: Vec::new(),
        }));
        Self {
            input: Rc::new(RefCell::new(input)),
            tiling,
            shared,
            used: RefCell::new(false),
        }
    }

    /// Return a new slot handle on this fan-out.  All slots share the same
    /// inner producer and consumer list; subscribing to any of them is
    /// equivalent.
    ///
    /// This is the handle for a reader downstream of the fan-out, and it owns
    /// the fan-out. An operator that this fan-out's own input chain contains
    /// takes a [`recurrence_slot`](Self::recurrence_slot) instead — see
    /// [`FanHold`].
    pub fn slot(&self) -> Box<dyn TileOperator> {
        self.slot_holding(FanHold::Reader {
            shared: self.shared.clone(), // shares the Rc — always connected
            input: self.input.clone(),
        })
    }

    /// A slot for an operator that this fan-out's own input chain contains.
    ///
    /// A store's driver and its writer read the store they are part of, to
    /// recover each position's prior value. Such a reader must not own the
    /// fan-out — see [`FanHold`].
    pub fn recurrence_slot(&self) -> Box<dyn TileOperator> {
        self.slot_holding(FanHold::Recurrence {
            shared: Rc::downgrade(&self.shared),
            input: Rc::downgrade(&self.input),
        })
    }

    fn slot_holding(&self, hold: FanHold) -> Box<dyn TileOperator> {
        let result = FanOutSlot {
            hold,
            base: OperatorBase::new(self.tiling.clone()),
            primary: !*self.used.borrow(),
        };
        *self.used.borrow_mut() = true;
        Box::new(result)
    }

    pub fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    /// The operator this fan-out reads.
    ///
    /// For a caller that wants the subgraph rather than a place in it: a slot
    /// is minted fresh on every call, so reaching the input through one would
    /// answer about a node that did not exist a moment ago.
    pub fn with_input<R>(&self, f: impl FnOnce(&dyn TileOperator) -> R) -> R {
        f(&**self.input.borrow())
    }

    /// The tile this fan-out most recently served, for a cyclic fan-out;
    /// `None` for an ordinary one, which keeps no memo.
    ///
    /// Reads the cyclic-mode memo rather than pulling the input, so it is safe
    /// wherever the graph is not mid-traversal and observes exactly what the
    /// fan's consumers last saw. A store's value is carried on its fan, so this
    /// is how a version replacing this program reads what its variables hold
    /// without a second channel out of the operator.
    pub fn cached_tile(&self) -> Option<Tile> {
        self.shared
            .borrow()
            .reentrancy
            .as_ref()
            .map(|r| r.cached_tile.clone())
    }

    /// Whether every subscriber has released everything this fan-out could
    /// offer.
    ///
    /// Such a fan-out answers empty from here on: it has told its input that
    /// nothing will be read again, and a `Memo` input drops what it holds in
    /// response. A version replacing another reads this where it would take an
    /// operator over, and what it does with the answer depends on what it wants
    /// the operator for. A binding is what a name reads, so one standing behind a
    /// spent operator is rebuilt: keeping it binds the name to nothing. An
    /// iteration input is taken instead — a recurrence continuing over it wants
    /// the position it reached, which
    /// [`released_position`](Self::released_position) reports as well from a
    /// spent operator as from a live one, and a spent one is what a finished
    /// iteration looks like. The handover carries such an operator either way: a
    /// store that can no longer produce still holds the value its variables hand
    /// on.
    pub fn released_in_full(&self) -> bool {
        self.shared.borrow().released.is_universal()
    }

    /// The last position this fan-out's subscribers have collectively released,
    /// for an output that is a function of a position domain.
    ///
    /// What a version keeping this fan-out has to know in order to place a
    /// recurrence over it. The producer beneath it will offer positions above
    /// this and no others, so a drive told to start anywhere else either decides
    /// a position a second time or waits for one that has gone.
    ///
    /// `None` when nothing has been released, and when the output is not
    /// position-domained — the two are the same answer to the caller, which has
    /// no position to start above either way. A consumer that finished the
    /// iteration is not one of those cases: the position it got to is retained
    /// past the universal release that closed it
    /// ([`FanOutShared::released_position`]).
    pub fn released_position(&self) -> Option<Position> {
        self.shared.borrow().released_position.clone()
    }

    /// Whether every live slot has released the same region.
    ///
    /// A subscriber added now starts at the intersection over the live slots,
    /// and [`released_position`](Self::released_position) is read off the same
    /// intersection, so when the slots disagree neither is where any one reader
    /// stopped (`src/ccl/design/program-evolution.md`, "Routes across
    /// branches").
    pub fn live_slots_agree(&self) -> bool {
        let shared = self.shared.borrow();
        let mut guards = shared.live_indices().map(|i| &shared.release_guards[i]);
        let Some(first) = guards.next() else {
            return true;
        };
        guards.all(|g| g == first)
    }

    /// The name of every producer registered with a data source from inside
    /// this fan-out's input chain, nested fan-outs included, when the chain was
    /// subscribed. Empty before the first subscription.
    pub fn source_producers(&self) -> Vec<String> {
        self.shared.borrow().source_producers.clone()
    }

    /// Reopen this fan-out for a fresh set of slots, keeping the inner
    /// producer and everything it has accumulated.
    ///
    /// For carrying one operator across a program reload. Only the
    /// [`inspect`](TileOperator::inspect) bookkeeping resets: which slot
    /// renders the input subtree and which renders a back-reference. The
    /// subscriptions need no attention, because each is tied to the life of the
    /// producer it handed out ([`FanOutShared::subscribers`]) — a subscriber the
    /// reload dropped stops counting on its own, and one the reload carried
    /// forward keeps its guard.
    pub fn reopen(&self) {
        *self.used.borrow_mut() = false;
        self.shared.borrow_mut().compact();
    }
}

/// How a handle holds the fan-out it belongs to.
///
/// A downstream reader owns it: the fan-out's state and its input chain must
/// outlive everything that reads them. A recurrence does not, because the
/// operator doing the reading sits *inside* the input chain the fan-out owns —
/// a store's body reading the store's own prior value. Owning it from there
/// closes a cycle through `FanOutShared::producer` that keeps the whole
/// subgraph alive for the life of the process, which across a program reload
/// means every retired version's operators are retained and the release
/// records their producers hold are never handed back.
///
/// Reading through a `Weak` is sound in that position because the read happens
/// only while the fan-out is pulling the chain the reader is part of, so the
/// fan-out is alive for the whole of it.
#[derive(Clone)]
enum FanHold {
    /// A downstream reader's handle, which owns the fan-out.
    Reader {
        shared: Rc<RefCell<FanOutShared>>,
        // shared-state-ok: the fan-out's own input operator, the same handle as
        // [`FanOut::input`] — a slot is a view of one fan-out, not a second
        // one. It holds an *operator*, not values passed between operators.
        input: Rc<RefCell<Box<dyn TileOperator>>>,
    },
    /// A recurrence's handle on a fan-out whose input chain contains it.
    Recurrence {
        shared: Weak<RefCell<FanOutShared>>,
        input: Weak<RefCell<Box<dyn TileOperator>>>,
    },
}

/// Why a recurrence's `Weak` is always upgradable where it is read.
const DEAD_RECURRENCE: &str = "a recurrence reads the fan-out whose input chain it sits in, and \
     that read happens only while the fan-out is pulling that chain";

impl FanHold {
    fn shared(&self) -> Rc<RefCell<FanOutShared>> {
        match self {
            FanHold::Reader { shared, .. } => shared.clone(),
            FanHold::Recurrence { shared, .. } => shared.upgrade().expect(DEAD_RECURRENCE),
        }
    }

    /// Read the fan-out's input operator. The cell never leaves `FanHold`, so
    /// the one place an operator handle is shared is the `Reader` field.
    fn with_input<R>(&self, f: impl FnOnce(&dyn TileOperator) -> R) -> R {
        match self {
            FanHold::Reader { input, .. } => f(&**input.borrow()),
            FanHold::Recurrence { input, .. } => {
                f(&**input.upgrade().expect(DEAD_RECURRENCE).borrow())
            }
        }
    }

    /// Subscribe to the fan-out's input operator, the one use that needs it
    /// mutably.
    fn subscribe_input(
        &self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        match self {
            FanHold::Reader { input, .. } => {
                input
                    .borrow_mut()
                    .subscribe(intent_guard, consumer, scheduler)
            }
            FanHold::Recurrence { input, .. } => input
                .upgrade()
                .expect(DEAD_RECURRENCE)
                .borrow_mut()
                .subscribe(intent_guard, consumer, scheduler),
        }
    }
}

struct FanOutSlot {
    // shared-state-ok: the same operator handle as [`FanOut::input`] and the same
    // mutable state as [`FanOut::shared`] — a slot is a view of one fan-out,
    // not a second one. Operators and their bookkeeping, not values.
    hold: FanHold,
    /// The tiling is the fan-out's, forwarded to every slot of it.
    base: OperatorBase,
    /// True for the first handle returned by [`FanOut::slot`], false for subsequent ones.
    /// The primary renders its input subtree in inspect; copies emit a back-reference.
    primary: bool,
}

impl FanOutSlot {
    fn shared(&self) -> Rc<RefCell<FanOutShared>> {
        self.hold.shared()
    }
}

impl TileOperator for FanOutSlot {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        self.hold.with_input(|op| visit(share(op)));
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = self.shared().borrow().id;
        if self.primary {
            InspectNode::new(format!("FanOut#{id}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.hold.with_input(|op| op.inspect(opts)))
        } else {
            InspectNode::leaf(format!("→ FanOut#{id}"))
        }
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Register the consumer and reserve its release-guard slot. The slot
        // number lives in the cell the producer holds, so `compact` can renumber.
        let slot = Rc::new(Cell::new(0usize));
        let shared_rc = self.shared();
        {
            let mut shared = shared_rc.borrow_mut();
            slot.set(shared.consumers.len());
            shared.consumers.push(Rc::new(RefCell::new(consumer)));
            let carried = shared.released.clone();
            shared.release_guards.push(carried);
            shared.subscribers.push(Rc::downgrade(&slot));
        } // borrow released here before we might call input.subscribe

        // Decide whether *this* call should drive the inner subscribe.
        // `producer.is_none()` is the standard "first subscription" check;
        // in cyclic mode, `!reentrancy.subscribing_inner` makes the path
        // re-entrancy-safe: a sibling-slot subscribe triggered from
        // inside the inner subscribe call sees the flag set and just
        // returns a producer (the outer call will populate `producer`
        // before anyone pulls).
        let should_subscribe = {
            let mut shared = shared_rc.borrow_mut();
            if shared.producer.is_some() {
                false
            } else if let Some(re) = shared.reentrancy.as_mut() {
                if re.subscribing_inner {
                    false
                } else {
                    re.subscribing_inner = true;
                    true
                }
            } else {
                true
            }
        };

        // Drive the inner subscribe (first non-reentrant subscriber only).
        // We must not hold a borrow of `shared` during `input.subscribe`
        // because that call may synchronously fire the notification closure,
        // which itself borrows `shared`.
        if should_subscribe {
            // RAII: any path out of this block (success or panic) resets
            // `subscribing_inner` to `false`.  Without the guard, a panic
            // from `input.subscribe(...)` would leave the flag set
            // forever and silently skip every future subscribe attempt
            // on this fan-out.
            let _guard = SubscribingInnerGuard { shared: &shared_rc };
            let shared_weak = Rc::downgrade(&shared_rc);
            scheduler.begin_source_producers();
            let inner = self.hold.subscribe_input(
                intent_guard,
                Box::new(FanOutInput {
                    shared: shared_weak,
                }),
                scheduler,
            );
            let producers = scheduler.end_source_producers();
            let mut shared = shared_rc.borrow_mut();
            shared.producer = Some(inner);
            shared.source_producers = producers;
            drop(shared);
            // `_guard` drops here, resetting `subscribing_inner`.
        }

        Box::new(FanOutProducer {
            // The fan-out's own id rather than a fresh one, so every slot's
            // producer reads as the same `FanOut#n`. `ProbeTable` keys on
            // `(node_id, producer_id)`, and that stays unique here because each
            // slot is its own operator with its own `NodeId` — the first
            // component separates them, not the second. Subscribing one slot
            // twice would land both producers in one slot; nothing does, and
            // `FanOut::slot` mints a fresh slot per call.
            base: ProducerBase::new(shared_rc.borrow().id, self.tiling(), &self.base, scheduler),
            // The producer a subscription hands out holds the fan-out the same
            // way this slot does: a recurrence's producer must not own it
            // either.
            hold: self.hold.clone(),
            slot,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.hold.with_input(|op| op.result_correlation())
    }
}

struct FanOutProducer {
    base: ProducerBase,
    /// Shared state (consumers + release guards), held the same way the slot
    /// this producer came from holds it — see [`FanHold`].
    hold: FanHold,
    /// This producer's index into `shared.consumers` and `shared.release_guards`,
    /// and the token that keeps its slot counted for as long as the producer
    /// exists — one object, since the index *is* the subscription's identity.
    /// Written by [`FanOutShared::compact`]. See [`FanOutShared::subscribers`].
    // shared-state-ok: which slot this subscription owns — bookkeeping between a
    // producer and the fan-out it subscribed to, not a back channel for data. No
    // tile, tile guard, or program value passes through it; a producer only reads
    // it to index its own release guard, which it would have done with a plain
    // `usize` if dead slots never had to be reclaimed.
    slot: Rc<Cell<usize>>,
}

impl FanOutProducer {
    /// This producer's current slot number.
    fn index(&self) -> usize {
        self.slot.get()
    }

    fn shared(&self) -> Rc<RefCell<FanOutShared>> {
        self.hold.shared()
    }
}

impl TileProducer for FanOutProducer {
    impl_producer_base!();

    /// The fan-out's input, which every slot pulls through the shared state. Nothing is
    /// visited while a pull holds that state, or after a recurrence's fan-out has gone.
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let shared = match &self.hold {
            FanHold::Reader { shared, .. } => Some(shared.clone()),
            FanHold::Recurrence { shared, .. } => shared.upgrade(),
        };
        if let Some(shared) = shared
            && let Ok(shared) = shared.try_borrow()
            && let Some(input) = &shared.producer
        {
            visit("input", &**input);
        }
    }

    /// No children: a fan-out's input is one producer however many slots read it, so a
    /// slot does not list it.
    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    /// A cyclic fan-out's cached snapshot, shared by every slot, so counted at the first.
    fn state_info(&self) -> ProducerStateInfo {
        if self.index() != 0 {
            return ProducerStateInfo::default();
        }
        let shared = self.shared();
        let shared = shared.borrow();
        ProducerStateInfo::holding(
            shared
                .reentrancy
                .as_ref()
                .map_or(0, |re| re.cached_tile.cell_count()),
        )
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        if self.index() == 0 {
            let node = InspectNode::new(self.name()).with_tiling(self.tiling().to_string());
            let node = match self.state_info().values {
                0 => node,
                held => node.with_held_values(held),
            };
            node.child(
                "input",
                self.shared()
                    .borrow()
                    .producer
                    .as_ref()
                    .unwrap()
                    .inspect(opts),
            )
        } else {
            InspectNode::leaf(format!("→ {}", self.name()))
        }
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        let shared_rc = self.shared();
        // Reopened before the pull, as an operator's gate is (`TileProducer::get`), and so by
        // a pull that reads nothing.
        shared_rc.borrow().forwarded.take();
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let cyclic = shared_rc.borrow().reentrancy.is_some();
        // A sibling that re-enters mid-pull is answered from the cache of the last completed
        // pull, which has to cover whatever region that sibling asks for: a cyclic fan-out reads
        // its input whole.
        let projection_guard = match cyclic {
            true => self.tiling().universal_guard(),
            false => projection.guard(self.tiling()),
        };
        // In cyclic mode, take the inner producer out during the pull so
        // sibling-slot re-entrance can detect re-entrance by finding
        // `producer == None` and serve from the cached tile.  In
        // non-cyclic mode, the producer stays in `shared` and we pull
        // through a regular borrow.
        let mut result = if cyclic {
            let producer_opt = shared_rc.borrow_mut().producer.take();
            if let Some(producer) = producer_opt {
                // RAII: put the producer back into `shared` on any exit
                // path (success or panic).  Without this guard, a panic
                // from `producer.get(...)` would leave `shared.producer
                // = None` forever, silently breaking every subsequent
                // pull on this fan-out.
                let mut guard = TakenProducerGuard {
                    shared: &shared_rc,
                    producer: Some(producer),
                };
                let tile = guard.producer.as_mut().unwrap().get(projection_guard);
                trace!("{} received {tile:?}", self.name());
                // Refresh the re-entrancy cache before the guard drops.
                // We replace (not merge) — inner producers like `Memo`
                // already return cumulative tiles, so each pull
                // supplants the previous cached snapshot.
                shared_rc
                    .borrow_mut()
                    .reentrancy
                    .as_mut()
                    .unwrap()
                    .cached_tile = tile.clone();
                tile
                // `guard` drops here, restoring `shared.producer`.
            } else {
                // Re-entrant pull: another slot's outer `get_impl` is
                // currently holding the producer.  Serve the latest known
                // emission instead of re-entering the inner producer (which
                // would alias `&mut`).
                let cached = shared_rc
                    .borrow()
                    .reentrancy
                    .as_ref()
                    .unwrap()
                    .cached_tile
                    .clone();
                trace!("{} serving cached (re-entrant): {cached:?}", self.name());
                cached
            }
        } else {
            shared_rc
                .borrow_mut()
                .producer
                .as_mut()
                .unwrap()
                .get(projection_guard)
        };

        // Filter by the stored obsolete guard. Because upstream retains data according to the
        // intersection of all obsolete guards, it may have more data than this specific consumer
        // is interested in.
        let guard = shared_rc.borrow().release_guards[self.index()].clone();
        trace!("{} removing {guard:?} from {result:?}", self.name());
        result.remove_guarded(guard);
        result.restrict_to(&projection, self.tiling());
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let shared_rc = self.shared();
        let mut shared = shared_rc.borrow_mut();
        // Union with the existing stored guard so that the accumulated set of
        // delivered data grows monotonically.  Replacing (instead of union-ing)
        // would forget previously-released ranges, causing FanOutSlot to
        // re-deliver data that a consumer has already released.
        let index = self.index();
        let accumulated = shared.release_guards[index].union(&obsolete_guard);
        trace!(
            "{} slot {index} accumulate {:?} + {obsolete_guard:?} = {accumulated:?}",
            self.name(),
            shared.release_guards[index]
        );
        shared.release_guards[index] = accumulated;
        // Only live subscribers constrain the release. A subscriber whose
        // producer has been dropped never releases again, so counting its guard
        // would hold the intersection wherever that subscriber left it and the
        // input would retain everything from there on.
        let intersection = shared
            .live_indices()
            .fold(self.tiling().universal_guard(), |acc, i| {
                acc.intersect(&shared.release_guards[i])
            });
        trace!(
            "{} releasing: {intersection:?} from slots {:?} live {:?}",
            self.name(),
            shared.release_guards,
            shared.live_indices().collect::<Vec<_>>()
        );
        // The match is total for a fan-out a recurrence reads, rather than a
        // shape test with a fallthrough. Every function tiling's empty and
        // universal guards are `Function(Domain(_))` (`Tiling::empty_guard`,
        // including a nested one), which supplies both the seed each
        // `release_guards` entry starts at and this fold's identity; `Domain` is
        // closed under the union and intersection applied to it; and both drives
        // release only `Domain` to an iteration source — `InductionDriver`
        // constructs it at each of its two release sites, and `TransactDriver`
        // forwards to its trigger only inside the same match. A `Codomain` guard
        // arriving here would fail the intersect rather than land in the `else`
        // ([`FunctionGuard::intersect`] has no mixed arm), so the position cannot
        // be silently lost.
        if let TileGuard::Function(FunctionGuard::Domain(pred)) = &intersection
            && let Some(position) = pred.max_released_position()
        {
            shared.released_position = shared.released_position.clone().max(Some(position));
        }
        shared.released = intersection.clone();
        // In cyclic mode the inner producer can be temporarily taken out
        // by a sibling-slot `get_impl`; skip the inner release in that
        // case (the next non-reentrant release will recompute and
        // forward).  Non-cyclic mode always has `producer = Some(_)`.
        if let Some(producer) = shared.producer.as_mut() {
            producer.release(intersection);
        } else {
            debug_assert!(
                shared.reentrancy.is_some(),
                "non-cyclic FanOut's producer should never be absent during release"
            );
        }
    }
}

/// An operator that logically forwards data from its input to its
/// consumer, but caches it so that the data doesn't have to be recomputed.
/// This involves storing the current Tile, merging new Tiles in as they arrive,
/// and immediately releasing upstream according to the received Tiles.
pub struct Memo {
    pub input: Box<dyn TileOperator>,
    /// The tiling is `input`'s, forwarded unchanged.
    base: OperatorBase,
}

impl Memo {
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for Memo {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let arrivals = Arrivals::new();
        let (consumer, gate) = shared_consumer(consumer);
        Box::new(MemoProducer::new(
            ProducerBase::new(
                MemoProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            self.input.subscribe(
                intent_guard,
                arrivals.consumer(forwarding_consumer_keeping_keys(
                    &consumer,
                    &scheduler.wakeup_queue(),
                )),
                scheduler,
            ),
            arrivals,
            consumer,
            scheduler.wakeup_queue(),
        ))
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

pub(crate) struct MemoProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    cached_tile: Tile,
    /// The region of the input the cache may not hold the answer for: what the memo has not
    /// read, and what its input has notified since it was read.
    ///
    /// A pull answers from the cache over a region outside this one, and reads the input over a
    /// region inside it. A pull at part of it reads that part: the rest stays until a pull reads
    /// it. The input's silence says nothing about a region never pulled, so it starts as
    /// [`Everything`](Projection::Everything).
    dirty: Projection,
    /// The regions the input has notified since the last pull, which fold into
    /// [`dirty`](Self::dirty) at the next one.
    arrivals: Arrivals,
    /// Set once this producer has released its input **universally**, which it
    /// does as soon as the input hands over a complete tile.
    ///
    /// Once everything the input will ever produce is cached, pulling it again
    /// is pointless work: a conforming input answers empty for a region it has
    /// released, which merges to nothing. So skipping the pull is an optimization: a
    /// release build always takes it, and a debug build once it has probed the drained
    /// input — see [`Self::get_impl`].
    upstream_drained: bool,
    /// Whether a pull nothing notified has re-read the input since the last read, which only
    /// a debug build does. The probe asks whether the input changed without notifying; until
    /// the memo reads again, a second probe asks what the first answered.
    gate_probed: bool,
    /// Whether the drained input has been pulled since it last notified, which only a debug
    /// build reads. A probe asks whether the input still answers empty for what it released;
    /// until the input notifies, the answer cannot have changed.
    drain_probed: bool,
    /// Whether [`BreakingProducer::consume_impl`] has run: a consuming memo answers from its
    /// cache and never pulls its input.
    consuming: bool,
    /// This memo's consumer, woken through [`wakeups`](Self::wakeups) when a pull nothing
    /// notified finds data the cache did not hold.
    ///
    /// A memo answers from its cache until its input notifies, so every consumer downstream
    /// counts on its output changing only after a notification. A pull taken without one, a
    /// drained input a debug build still probes, can still find new data, and then the
    /// change reaches no one: a sibling memo over the same input has already answered from
    /// its own cache and will keep doing so.
    consumer: GatedConsumer,
    wakeups: WakeupQueue,
}

impl MemoProducer {
    /// A memo over `input` with an empty cache that has read nothing: every region starts dirty.
    /// `arrivals` records what the input notifies, and `wakeups` carries the consumer's wakes.
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        arrivals: Arrivals,
        consumer: GatedConsumer,
        wakeups: WakeupQueue,
    ) -> Self {
        let cached_tile = base.tiling.empty_tile();
        Self {
            base,
            input,
            cached_tile,
            dirty: Projection::Everything,
            arrivals,
            upstream_drained: false,
            gate_probed: false,
            drain_probed: false,
            consuming: false,
            consumer,
            wakeups,
        }
    }

    /// A memo over `input` that nothing subscribed, for a test that builds a chain by hand.
    #[cfg(test)]
    pub(crate) fn over(input: Box<dyn TileProducer>, tiling: &Tiling) -> Self {
        Self::new(
            ProducerBase::unowned(Self::alloc_id(), tiling),
            input,
            Arrivals::new(),
            shared_consumer(Box::new(|| {})).0,
            WakeupQueue::default(),
        )
    }

    /// The cache cut to `projection`: it holds whatever was read, which can be more than the
    /// pull asks for.
    fn answer(&self, projection: &Projection) -> Tile {
        let mut tile = self.cached_tile.clone();
        tile.restrict_to(projection, self.tiling());
        tile
    }
}

impl MemoProducer {
    /// Pull the input at `projection_guard`, merge the answer into the cache, and release the
    /// input at what the answer states. `must_read` is whether the region was dirty: a read of a
    /// clean region that finds data the cache lacked wakes the memo's consumer.
    fn read_input(
        &mut self,
        projection_guard: TileGuard,
        projection: &Projection,
        must_read: bool,
    ) {
        self.gate_probed = false;
        self.dirty = self.dirty.minus(projection);
        let mut input = self.input.get(projection_guard);
        trace!("{} received {input:?}", self.name());
        let upstream_obsolete = input.to_guard();
        input.compact();
        // The release must cover the plain values merged into the cache; see
        // `src/interpreter/design-operators.md`, "The release contract".
        // Open-group keys and join-shaped values may remain; the check excludes plain values.
        #[cfg(debug_assertions)]
        {
            let mut unreleased = input.clone();
            unreleased.remove_guarded(upstream_obsolete.clone());
            unreleased.compact();
            debug_assert!(
                !unreleased.holds_a_plain_value(),
                "{} merged values it cannot release: {unreleased:?} is left after releasing \
                 {upstream_obsolete:?} from {input:?}",
                self.name(),
            );
        }
        trace!("{} releasing {upstream_obsolete:?}", self.name());
        // A pull of an input already drained is the probe.
        self.drain_probed = self.upstream_drained;
        // Latch: once the input has handed over everything, a later pull answering
        // empty (as a conforming input does for a region it released) must not
        // read as "not drained after all".
        self.upstream_drained |= upstream_obsolete.is_universal();
        self.input.release(upstream_obsolete);
        trace!(
            "{} merging {input:?} into {:?}",
            self.name(),
            self.cached_tile
        );
        if must_read {
            self.cached_tile.merge(input);
        } else {
            let before = self.cached_tile.clone();
            self.cached_tile.merge(input);
            if self.cached_tile != before {
                self.wakeups.request(self.consumer.shared().clone());
            }
        }
    }
}

impl BreakingProducer for MemoProducer {
    /// Reads the input at `guard` whether or not the cache holds the region, since the caller
    /// asks for the pipeline to run, and leaves the memo consuming. The consumer is woken when
    /// the read changes the cache: the notification that made the region dirty may have been
    /// answered by a pull of the cache before this consume.
    fn consume_impl(&mut self, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        self.consuming = true;
        let projection = guard.projection(&self.name());
        if projection == Projection::Nothing || self.upstream_drained {
            return;
        }
        self.dirty = self.dirty.union(&self.arrivals.take());
        self.read_input(guard, &projection, false);
    }

    fn input(&self) -> &dyn TileProducer {
        &*self.input
    }

    /// The region the cached tile states. A release removes rows and leaves the statement as it
    /// was, which `finalize` takes into account.
    fn held(&self) -> TileGuard {
        self.cached_tile.to_guard()
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = guard.projection(&self.name());
        self.dirty = self.dirty.union(&self.arrivals.take());
        self.answer(&projection)
    }
}

impl TileProducer for MemoProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.cached_tile.cell_count())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        // Everything the input will ever produce is already cached, so the pull below can
        // only return what was released — which a conforming input answers empty, merging to
        // nothing. A release build skips it.
        //
        // A debug build probes instead, once after the input drains and again after each
        // notification of a region the pull reads. A `Memo` sits above most scalar producers, so never pulling a drained
        // input would shield every one of them from the release-contract assertion in
        // `TileProducer::get`; the probe makes an input that answers with released data trip
        // that assertion at the input, where the defect is, instead of corrupting the cache
        // here. Probing on every pull adds nothing, since until the input notifies a second
        // probe asks what the first answered, and it re-reads a subgraph once per path to it,
        // which grows with the nesting of the fan-outs over it.
        //
        // `cfg!` rather than `#[cfg]` so both configurations stay compiled.
        self.dirty = self.dirty.union(&self.arrivals.take());
        // The cache may not hold this region: it was never read, or the input has notified
        // since.
        let must_read = self.dirty.intersect(&projection) != Projection::Nothing;
        if self.upstream_drained && (!cfg!(debug_assertions) || (self.drain_probed && !must_read)) {
            return self.answer(&projection);
        }
        // The cache is cumulative, so over a region outside `dirty` it is already the answer,
        // empty or not, and pulling walks the subtree below to merge nothing. `dirty` starts as
        // everything, so the first pull of a region reads: a demand read taken outside the
        // delivery loop, a store's init op reading a seed or a completion read, arrives before
        // anything has notified. Every later change to the input notifies (the notification
        // contract), so an empty cache over a region the input has not notified since is the
        // input's answer. Under a fan-out the cache is what keeps each branch's pull from
        // re-reading the shared input, which on a first lap is mostly empty. A drained input is
        // left to the rule above rather than gated here, which is what keeps that rule's debug
        // probe: gating a drained input would shield it in every build.
        if !must_read && !self.upstream_drained {
            // The gate trusts the notification contract, so a debug build checks it, once
            // per read: an input that changed without notifying answers something new.
            if cfg!(debug_assertions) && !self.gate_probed && self.wakeups.is_empty() {
                self.gate_probed = true;
                let mut probe = self.input.get(projection_guard);
                probe.compact();
                let mut merged = self.cached_tile.clone();
                merged.merge(probe.clone());
                // A notification that landed during the probe, from another thread writing rows
                // before notifying, is the notification the probe asks for: it has not been
                // taken yet, so the rows are not news the contract missed.
                debug_assert!(
                    self.arrivals.pending() || holds_the_same(&merged, &self.cached_tile),
                    "{}'s input {} changed without notifying: {probe:?} is new to {:?}",
                    self.name(),
                    self.input.name(),
                    self.cached_tile,
                );
            }
            return self.answer(&projection);
        }
        self.read_input(projection_guard, &projection, must_read);
        self.answer(&projection)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Remove any released data from the cached tile since the consumer
        // is no longer interested.
        self.cached_tile.remove_guarded(obsolete_guard.clone());
        // Compact so that logically-deleted entries are physically gone.
        self.cached_tile.compact();
        // Also release upstream to handle the case where the consumer releases
        // data that was never produced.
        self.input.release(obsolete_guard.clone());
        trace!("{} now has cached {:?}", self.name(), self.cached_tile);
    }
}

/// Whether `a` and `b` hold the same cells and state the same completeness at every level,
/// whatever each statement is spelled as.
fn holds_the_same(a: &Tile, b: &Tile) -> bool {
    let statements = |tile: &Tile| {
        let mut levels = Vec::new();
        tile.clone().map_level_predicates(&mut |_, pred| {
            levels.push(pred.clone());
            pred.clone()
        });
        levels
    };
    let (ours, theirs) = (statements(a), statements(b));
    a.cell_count() == b.cell_count()
        && ours.len() == theirs.len()
        && ours
            .iter()
            .zip(&theirs)
            .all(|(x, y)| x.subsumes(y) && y.subsumes(x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::{Cell, RefCell};
    use std::collections::VecDeque;
    use std::rc::Rc;

    use bit_set::BitSet;

    use crate::interpreter::tile_operators::test_helpers::QuietSpy;
    use crate::interpreter::tile_operators::{Constant, Scheduler};
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};

    /// Reopening a fan-out drops the slots whose subscribers are gone and tells
    /// each survivor its new number, so the parallel slot vectors are bounded by
    /// the live subscriptions rather than by every subscription ever made.
    ///
    /// The renumbering is the whole point: a producer addresses its release guard
    /// by index, so a compaction that moved guards without telling the producers
    /// would hand one subscriber another's guard. This drops the *first* of two
    /// subscribers for that reason — the survivor has to move from slot 1 to slot
    /// 0 and keep the guard it released.
    #[test]
    fn reopening_a_fan_out_drops_dead_slots_and_renumbers_the_rest() {
        let extent = Extent::Base(BaseType::Int);
        let fan = FanOut::new(Box::new(Constant::new(Value::Int(1), extent.clone())));
        let mut sched = Scheduler::new();
        let tiling = Tiling::Scalar(extent);

        let first = fan
            .slot()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        let mut second = fan
            .slot()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        assert_eq!(fan.shared.borrow().subscribers.len(), 2);

        // Distinguish the survivor's guard from the empty one the dead slot holds.
        let mine = TileGuard::Scalar(Predicate::True);
        second.release(mine.clone());
        drop(first);

        fan.reopen();

        let shared = fan.shared.borrow();
        assert_eq!(shared.subscribers.len(), 1, "the dead slot is gone");
        assert_eq!(shared.consumers.len(), 1, "consumers stay parallel");
        assert_eq!(shared.release_guards.len(), 1, "guards stay parallel");
        drop(shared);
        assert_eq!(
            fan.shared.borrow().release_guards[0],
            mine,
            "the survivor's guard moved with it, and it reads its new slot"
        );
    }

    /// A subscriber that registers after the fan-out has released starts having
    /// released the same, because that data is gone: the fan-out told its input
    /// it would not be read again.
    ///
    /// Within one version every subscription is made before any data flows, so
    /// this only bites across a version handover — which is exactly when it has
    /// to, since the subscriber registering is the one replacing the subscriber
    /// that released.
    #[test]
    fn a_late_subscriber_starts_at_what_the_fan_out_has_released() {
        let extent = Extent::Base(BaseType::Int);
        let fan = FanOut::new(Box::new(Constant::new(Value::Int(1), extent.clone())));
        let mut sched = Scheduler::new();
        let tiling = Tiling::Scalar(extent);

        let mut first = fan
            .slot()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        assert!(
            !fan.released_in_full(),
            "nothing has released, so the fan-out still has its value to give"
        );
        first.release(TileGuard::Scalar(Predicate::True));
        drop(first);
        fan.reopen();

        assert!(
            fan.released_in_full(),
            "the one subscriber released everything, so the fan-out can only answer empty"
        );
        let late = fan
            .slot()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        assert_eq!(
            fan.shared.borrow().release_guards[0],
            TileGuard::Scalar(Predicate::True),
            "the late subscriber inherits the release rather than starting at nothing"
        );
        drop(late);
    }

    /// A `TileOperator` whose producer hands over one scripted tile per pull and
    /// empties afterwards. It counts pulls, and keeps the consumer its subscriber
    /// installed so a test can fire a notification the way the scheduler would.
    /// An input that changes only when it notifies, as the notification contract has it:
    /// its first tile stands from the start, each [`notify`] brings the next, and a pull
    /// takes the tile standing, leaving nothing new until the next notification.
    struct Scripted {
        base: OperatorBase,
        tiles: Rc<RefCell<VecDeque<Tile>>>,
        pulls: Rc<Cell<usize>>,
        notifier: Notifier,
    }

    struct ScriptedProducer {
        base: ProducerBase,
        tiles: Rc<RefCell<VecDeque<Tile>>>,
        pulls: Rc<Cell<usize>>,
        standing: Rc<Cell<bool>>,
        /// What the last tile called complete, which a pull with nothing new still states.
        complete: Option<Predicate>,
    }

    impl Scripted {
        /// The operator, the pull counter, and a handle that fires the consumer the
        /// memo installs on it.
        fn new(tiles: Vec<Tile>, tiling: &Tiling) -> (Self, Rc<Cell<usize>>, Notifier) {
            let pulls = Rc::new(Cell::new(0usize));
            let notifier = Notifier {
                consumer: Rc::new(RefCell::new(None)),
                standing: Rc::new(Cell::new(true)),
            };
            (
                Self {
                    base: OperatorBase::new(tiling.clone()),
                    tiles: Rc::new(RefCell::new(tiles.into())),
                    pulls: pulls.clone(),
                    notifier: notifier.clone(),
                },
                pulls,
                notifier,
            )
        }
    }

    /// The consumer a [`Scripted`] input was handed, so a test can notify with it, and
    /// whether a tile stands to be taken.
    #[derive(Clone)]
    struct Notifier {
        consumer: Rc<RefCell<Option<Box<dyn Consumer>>>>,
        standing: Rc<Cell<bool>>,
    }

    /// Bring the input's next tile, and notify.
    fn notify(notifier: &Notifier) {
        notifier.standing.set(true);
        notifier
            .consumer
            .borrow_mut()
            .as_mut()
            .expect("the memo installed a consumer on its input")
            .notify(&Projection::Everything);
    }

    impl TileOperator for Scripted {
        impl_operator_base!();

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            *self.notifier.consumer.borrow_mut() = Some(consumer);
            Box::new(ScriptedProducer {
                base: ProducerBase::unowned(ScriptedProducer::alloc_id(), self.tiling()),
                tiles: self.tiles.clone(),
                pulls: self.pulls.clone(),
                standing: self.notifier.standing.clone(),
                complete: None,
            })
        }
    }

    impl TileProducer for ScriptedProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.pulls.set(self.pulls.get() + 1);
            let next = match self.standing.replace(false) {
                true => self.tiles.borrow_mut().pop_front(),
                false => None,
            };
            match (next, &self.complete) {
                (Some(tile), _) => {
                    if let Tile::DataFunction {
                        domain_predicate, ..
                    } = &tile
                    {
                        self.complete = Some(domain_predicate.clone());
                    }
                    tile
                }
                (None, Some(complete)) => {
                    let Tile::DataFunction {
                        row_starts,
                        domain,
                        codomain,
                        deleted,
                        ..
                    } = self.tiling().empty_tile()
                    else {
                        unreachable!("a tile that stated completeness is a collection")
                    };
                    Tile::grouped(row_starts, domain, codomain, complete.clone(), deleted)
                }
                (None, None) => self.tiling().empty_tile(),
            }
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// The pulls a debug build adds to a gated memo's first gated pull, to check its input
    /// changed only by notifying.
    fn probe() -> usize {
        usize::from(cfg!(debug_assertions))
    }

    /// A tiling whose tiles can be **incomplete**, so a memo over one never reaches
    /// `upstream_drained` and the gate is what the test observes.
    fn partial_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// One row at `key`, under a domain predicate that claims only the prefix up to
    /// it — so the tile is not the whole function and the input is not drained.
    fn one_row(key: u64, value: i64) -> Tile {
        Tile::data_function(
            ColumnValue::UInts(vec![key]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![value]))),
            Predicate::at_or_below(Value::UInt(key)),
            BitSet::new(),
        )
    }

    /// A fan-out passes its input's notification to its branches once until a branch pulls:
    /// a second one before that says nothing the first did not.
    #[test]
    fn a_fan_out_passes_one_notification_per_pull() {
        let tiling = partial_tiling();
        let (input, _pulls, notifier) = Scripted::new(vec![one_row(0, 7)], &tiling);
        let fan = FanOut::new(Box::new(input));
        let mut sched = Scheduler::new();
        let counts: Vec<Rc<Cell<u32>>> = (0..2).map(|_| Rc::new(Cell::new(0))).collect();
        let mut producers: Vec<Box<dyn TileProducer>> = counts
            .iter()
            .map(|count| {
                let count = count.clone();
                fan.slot().subscribe(
                    tiling.universal_guard(),
                    Box::new(move || count.set(count.get() + 1)),
                    &mut sched,
                )
            })
            .collect();
        notify(&notifier);
        notify(&notifier);
        let seen = || counts.iter().map(|c| c.get()).collect::<Vec<_>>();
        assert_eq!(
            seen(),
            [1, 1],
            "the second notification reached the branches unpulled"
        );
        producers[0].get(tiling.universal_guard());
        notify(&notifier);
        assert_eq!(
            seen(),
            [2, 2],
            "a branch's pull did not let the next notification through"
        );
    }

    /// A sink under a diamond, one memoized input fanned out to both fields of a record, is
    /// pulled once per scheduler call: the change reaches the record along both branches, and the
    /// record's gate passes one notification, which schedules the sink's one pull.
    #[test]
    fn a_sink_under_a_diamond_is_pulled_once_per_scheduler_call() {
        use crate::interpreter::DataSink;
        use crate::interpreter::sinks::{DoneNotifier, SinkConsumer};
        use crate::interpreter::tile_operators::MakeRecord;
        use std::sync::{Arc, Mutex};

        /// How many tiles the sink was handed.
        #[derive(Default)]
        struct Counting(Mutex<usize>);
        impl DataSink for Counting {
            fn process(&self, _tile: &Tile) {
                *self.0.lock().unwrap() += 1;
            }
        }

        let tiling = partial_tiling();
        let (input, _pulls, notifier) = Scripted::new(vec![one_row(0, 7), one_row(1, 8)], &tiling);
        let fan = FanOut::new(Box::new(Memo::new(Box::new(input))));
        let mut record = MakeRecord::new(vec![fan.slot(), fan.slot()]);
        let mut sched = Scheduler::new();
        let sink = Arc::new(Counting::default());
        let (done, _finished) = DoneNotifier::create(1);
        let (consumer, slot) = SinkConsumer::new(
            sink.clone(),
            done.into_iter().next().expect("one notifier"),
            sched.sink_pull_queue(),
        );
        let universal = record.tiling().universal_guard();
        let producer = record.subscribe(universal, Box::new(consumer), &mut sched);
        *slot.borrow_mut() = Some(producer);
        let processed = || *sink.0.lock().unwrap();

        for call in 1..=2 {
            notify(&notifier);
            sched.check_for_notifications();
            assert_eq!(
                processed(),
                call,
                "the sink was pulled {} times",
                processed()
            );
        }
    }

    /// A memo shared by two branches of a fan-out reads its input once per notification: the
    /// second branch's pull, and every pull after until the input notifies, is answered
    /// from the cache, empty or not.
    #[test]
    fn a_memo_under_a_fan_out_reads_its_input_once_per_notification() {
        let tiling = partial_tiling();
        let (input, pulls, notifier) =
            Scripted::new(vec![tiling.empty_tile(), one_row(0, 7)], &tiling);
        let fan = FanOut::new(Box::new(Memo::new(Box::new(input))));
        let mut sched = Scheduler::new();
        let mut branches: Vec<Box<dyn TileProducer>> = (0..2)
            .map(|_| {
                fan.slot()
                    .subscribe(tiling.universal_guard(), Box::new(|| {}), &mut sched)
            })
            .collect();
        let pull_both = |branches: &mut Vec<Box<dyn TileProducer>>| {
            for branch in branches.iter_mut() {
                branch.get(tiling.universal_guard());
            }
        };

        pull_both(&mut branches);
        pull_both(&mut branches);
        assert_eq!(
            pulls.get(),
            1 + probe(),
            "the empty cache answers both branches, twice over, from one read"
        );
        notify(&notifier);
        pull_both(&mut branches);
        assert_eq!(
            pulls.get(),
            2 + 2 * probe(),
            "a notification allows one more read, and a debug build one more probe"
        );
    }

    /// A memo whose input has said nothing since its last pull answers from the
    /// cache without reading the input; a notification re-enables the read.
    ///
    /// This is the gate `MemoProducer::get_impl` applies, and it is what makes a
    /// pull cost the graph's traffic rather than its size.
    #[test]
    fn a_memo_reads_its_input_only_after_its_input_notifies() {
        let tiling = partial_tiling();
        let (input, pulls, notifier) = Scripted::new(vec![one_row(0, 7)], &tiling);
        let mut memo = Memo::new(Box::new(input));
        let mut sched = Scheduler::new();
        let mut producer = memo.subscribe(tiling.universal_guard(), Box::new(|| {}), &mut sched);

        let first = producer.get(tiling.universal_guard());
        assert_eq!(pulls.get(), 1, "the first pull reads its input");
        assert!(!first.is_empty(), "the first pull fills the cache");

        let gated = producer.get(tiling.universal_guard());
        assert_eq!(
            gated, first,
            "a gated pull answers the tile it just answered"
        );
        assert_eq!(
            pulls.get(),
            1 + probe(),
            "nothing notified, so the input is not read, but by a debug build's probe"
        );

        notify(&notifier);
        let after = producer.get(tiling.universal_guard());
        assert_eq!(after, first, "the input had nothing new to add");
        assert_eq!(
            pulls.get(),
            2 + probe(),
            "a notification re-enables the read"
        );
    }

    /// A debug build probes a drained input once, then answers from the cache until the input
    /// notifies, which allows one more probe. A release build never pulls a drained input.
    #[test]
    fn a_drained_memo_probes_its_input_once_per_notification() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let complete = Tile::Scalar(ColumnValue::Ints(vec![7]));
        let (input, pulls, notifier) = Scripted::new(vec![complete.clone()], &tiling);
        let mut memo = Memo::new(Box::new(input));
        let mut sched = Scheduler::new();
        let mut producer = memo.subscribe(tiling.universal_guard(), Box::new(|| {}), &mut sched);
        let probes = |n: usize| if cfg!(debug_assertions) { 1 + n } else { 1 };

        assert_eq!(producer.get(tiling.universal_guard()), complete);
        assert_eq!(
            pulls.get(),
            1,
            "the first pull reads the input, which drains"
        );
        assert_eq!(producer.get(tiling.universal_guard()), complete);
        assert_eq!(
            pulls.get(),
            probes(1),
            "a debug build probes the drained input once"
        );
        assert_eq!(producer.get(tiling.universal_guard()), complete);
        assert_eq!(
            pulls.get(),
            probes(1),
            "nothing notified, so the probe is not repeated"
        );
        notify(&notifier);
        assert_eq!(producer.get(tiling.universal_guard()), complete);
        assert_eq!(
            pulls.get(),
            probes(2),
            "a notification allows one more probe"
        );
    }

    /// An **empty** cache is gated like any other once the input has been read: the first
    /// pull reads, because the flag starts set, and from then on the input's next change
    /// notifies. The input here yields nothing on the first pull and the row on the second.
    #[test]
    fn a_memo_with_an_empty_cache_reads_its_input_after_a_notification() {
        let tiling = partial_tiling();
        let (input, pulls, notifier) =
            Scripted::new(vec![tiling.empty_tile(), one_row(0, 7)], &tiling);
        let mut memo = Memo::new(Box::new(input));
        let mut sched = Scheduler::new();
        let mut producer = memo.subscribe(tiling.universal_guard(), Box::new(|| {}), &mut sched);

        assert!(
            producer.get(tiling.universal_guard()).is_empty(),
            "the input had nothing yet"
        );
        assert_eq!(pulls.get(), 1, "the first pull reads its input");

        assert!(
            producer.get(tiling.universal_guard()).is_empty(),
            "nothing notified, so the empty cache is the answer"
        );
        assert_eq!(
            pulls.get(),
            1 + probe(),
            "nothing notified, so the input is not read, but by a debug build's probe"
        );

        notify(&notifier);
        assert!(
            !producer.get(tiling.universal_guard()).is_empty(),
            "the notification re-enables the read, which finds the row"
        );
        assert_eq!(pulls.get(), 2 + probe());
    }

    /// A `Memo` releases its input universally as soon as the input hands over a
    /// complete tile, and from then on the cache is the value: repeated pulls
    /// answer the same single scalar.
    ///
    /// This has to hold in both build configurations, because a debug build probes the
    /// drained input (see [`MemoProducer::get_impl`]); this memo listens to no notification,
    /// so it probes on every pull. The input — honoring the release it was just handed —
    /// answers empty, which merges to nothing. Were the input to answer with the released
    /// value again, `merge` would append it: a `Tile::Scalar`'s positions are
    /// implicit, so it cannot tell "this position again" from "one more position",
    /// and one value would silently become two, then three.
    #[test]
    fn memo_holds_one_value_across_repeated_pulls() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (upstream, _released) =
            QuietSpy::new(Tile::Scalar(ColumnValue::Ints(vec![-5])), tiling.clone());
        let mut memo = MemoProducer::new(
            ProducerBase::unowned(MemoProducer::alloc_id(), &tiling),
            Box::new(upstream),
            Arrivals::new(),
            shared_consumer(Box::new(|| {})).0,
            WakeupQueue::default(),
        );

        for pull in 1..=3 {
            let tile = memo.get(tiling.universal_guard());
            assert_eq!(
                tile,
                Tile::Scalar(ColumnValue::Ints(vec![-5])),
                "pull {pull}: the cache holds the one drained value, not one copy per pull"
            );
        }
        assert!(
            memo.upstream_drained,
            "the complete tile should have been released universally on the first pull"
        );
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::Scheduler;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, InputConsumer, NotifyingOp, ProjectionSpy, ProjectionSpyOp, int_entries,
        ints_by_position, keys_between, notify_input,
    };
    use crate::interpreter::{BaseType, Extent};

    const ROWS: u64 = 8;

    fn ints() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// A fan-out over a stream of `0..ROWS`, with two slots subscribed, and the input's logs.
    fn two_slots() -> (Box<dyn TileProducer>, Box<dyn TileProducer>, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).collect();
        let (input, pulled, _) = ProjectionSpyOp::new(ints_by_position(&values, true), ints());
        let fan = FanOut::new(Box::new(input));
        let mut sched = Scheduler::new();
        let first = fan
            .slot()
            .subscribe(ints().empty_guard(), Box::new(|| {}), &mut sched);
        let second = fan
            .slot()
            .subscribe(ints().empty_guard(), Box::new(|| {}), &mut sched);
        (first, second, pulled)
    }

    /// `xs ▷ map(c)` fans a stream into two consumers that each read their own morsels. Each
    /// slot's answer is its own morsel, and the shared input is pulled at the region of the slot
    /// that pulls it: a producer states completeness only for the region it returns, so a pull of
    /// one region withdraws nothing it said of another.
    #[test]
    fn slots_read_their_own_morsels_through_one_input() {
        let (mut first, mut second, pulled) = two_slots();

        let one = first.get(keys_between(0, 3));
        assert_eq!(int_entries(&one), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

        let two = second.get(keys_between(4, 7));
        assert_eq!(int_entries(&two), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);

        let pulled = pulled.borrow();
        assert_eq!(pulled[0], keys_between(0, 3));
        assert_eq!(
            pulled[1],
            keys_between(4, 7),
            "the second pull is the second slot's morsel alone"
        );
    }

    /// A slot pulled at `Nothing` before any other asks pulls nothing upstream, and the input
    /// stays untouched until a slot wants a region.
    #[test]
    fn a_slot_that_asks_for_nothing_pulls_nothing() {
        let (mut first, _second, pulled) = two_slots();
        let tile = first.get(ints().empty_guard());
        assert!(int_entries(&tile).is_empty());
        assert!(pulled.borrow().is_empty());
    }

    /// A slot that asks for everything after another took a morsel gets everything, and the
    /// morsel's slot is still answered at its own region afterwards.
    #[test]
    fn a_later_universal_pull_reads_everything_and_the_first_slot_keeps_its_region() {
        let (mut first, mut second, pulled) = two_slots();
        first.get(keys_between(0, 1));
        let all = second.get(ints().universal_guard());
        assert_eq!(int_entries(&all).len(), ROWS as usize);
        assert_eq!(*pulled.borrow().last().unwrap(), ints().universal_guard());

        let again = first.get(keys_between(0, 1));
        assert_eq!(int_entries(&again), vec![(0, 0), (1, 1)]);
    }

    /// A `Memo` over a stream, built by hand and pulled by hand.
    fn memo_over_stream() -> (MemoProducer, GuardLog, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).collect();
        let (upstream, pulled, released) =
            ProjectionSpy::new(ints_by_position(&values, true), ints());
        let memo = MemoProducer::over(Box::new(upstream), &ints());
        (memo, pulled, released)
    }

    /// A memo reads its input over the morsel it is asked for and releases only that, so the
    /// input keeps the rest for the next morsel. The answer is the morsel, not the cache.
    #[test]
    fn a_memo_reads_and_releases_one_morsel_at_a_time() {
        let (mut memo, pulled, released) = memo_over_stream();

        let first = memo.get(keys_between(0, 3));
        assert_eq!(int_entries(&first), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
        assert_eq!(pulled.borrow()[0], keys_between(0, 3));
        assert_eq!(released.borrow()[0], keys_between(0, 3));
        memo.release(keys_between(0, 3));

        let second = memo.get(keys_between(4, 7));
        assert_eq!(int_entries(&second), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);
        assert_eq!(pulled.borrow()[1], keys_between(4, 7));
    }

    /// A region the memo has read is answered from the cache with no pull, even once the
    /// input is silent. A region it has not read pulls the input, and the answer joins the
    /// cache.
    #[test]
    fn a_memo_answers_a_read_region_from_its_cache_and_reads_a_new_one() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.get(keys_between(0, 3));
        memo.release(keys_between(0, 1));

        let kept = memo.get(keys_between(2, 3));
        assert_eq!(int_entries(&kept), vec![(2, 2), (3, 3)]);
        // A debug build probes a silent input once, at the same region.
        assert!(
            pulled.borrow()[1..]
                .iter()
                .all(|guard| *guard == keys_between(2, 3)),
            "a read region reaches the input only as a probe: {:?}",
            pulled.borrow()
        );

        let wider = memo.get(keys_between(2, 5));
        assert_eq!(
            *pulled.borrow().last().unwrap(),
            keys_between(2, 5),
            "an unread region reaches the input"
        );
        assert_eq!(wider_keys(&wider), vec![2, 3, 4, 5]);
    }

    /// A memo consumed whole answers every pull as a memo in pull mode does, from its cache.
    #[test]
    fn a_consuming_memo_answers_as_a_lazy_one_does() {
        let (mut lazy, _, _) = memo_over_stream();
        let (mut consuming, _, _) = memo_over_stream();
        consuming.consume_impl(ints().universal_guard());
        assert_eq!(consuming.finalize(), ints().universal_guard());

        for guard in [
            ints().universal_guard(),
            keys_between(0, 3),
            keys_between(2, 5),
            ints().empty_guard(),
        ] {
            assert_eq!(
                consuming.get(guard.clone()),
                lazy.get(guard.clone()),
                "a pull at {guard:?}"
            );
        }
    }

    /// `consume_impl` pulls the input at its guard and releases it at what the answer stated, and
    /// nothing after it reaches the input.
    #[test]
    fn a_consuming_memo_pulls_the_input_once_and_releases_it_whole() {
        let (mut memo, pulled, released) = memo_over_stream();
        memo.consume_impl(ints().universal_guard());
        assert_eq!(*pulled.borrow(), vec![ints().universal_guard()]);
        assert_eq!(*released.borrow(), vec![ints().universal_guard()]);

        for _ in 0..3 {
            memo.get(keys_between(0, 3));
            memo.get(ints().universal_guard());
        }
        assert_eq!(
            pulled.borrow().len(),
            1,
            "a consuming memo's offer pulls nothing, even in a debug build"
        );
    }

    /// A memo consumed at a region answers that region from its cache and pulls nothing for the
    /// rest: the statement of its cache says which region it answers.
    #[test]
    fn a_memo_consumed_in_part_answers_that_part_and_pulls_no_more() {
        let (mut memo, pulled, released) = memo_over_stream();
        memo.consume_impl(keys_between(0, 3));
        assert_eq!(*pulled.borrow(), vec![keys_between(0, 3)]);
        assert_eq!(*released.borrow(), vec![keys_between(0, 3)]);

        let part = memo.get(keys_between(0, 3));
        assert_eq!(int_entries(&part), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
        let rest = memo.get(keys_between(4, 7));
        assert!(int_entries(&rest).is_empty(), "the rest is not consumed");
        assert_eq!(pulled.borrow().len(), 1, "and it is not pulled either");
    }

    /// Consuming a memo whose input has already drained pulls nothing.
    #[test]
    fn a_memo_whose_input_has_drained_consumes_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.get(ints().universal_guard());
        let pulls = pulled.borrow().len();
        memo.consume_impl(ints().universal_guard());
        assert_eq!(memo.finalize(), ints().universal_guard());
        assert_eq!(pulled.borrow().len(), pulls);
    }

    /// A pipeline finalizes after its input has stated everything complete, and a memo consumed
    /// in part has not had that. The check is an `assert!`, since it guards the protocol between
    /// the driver and the breaker and a release build runs the same driver.
    #[test]
    #[should_panic(expected = "finalizes after its input has stated everything complete")]
    fn finalize_before_the_input_has_drained_panics() {
        let (mut memo, _, _) = memo_over_stream();
        memo.consume_impl(keys_between(0, 3));
        memo.finalize();
    }

    /// `finalize` queues no wake. A consume that finds nothing new, on a memo whose input has
    /// drained, queues none either, so the queue is empty throughout.
    #[test]
    fn finalize_queues_no_wake() {
        let (mut memo, _, _) = memo_over_stream();
        memo.get(ints().universal_guard());
        assert!(
            memo.wakeups.is_empty(),
            "the first read is what was notified"
        );
        memo.consume_impl(ints().universal_guard());
        memo.finalize();
        assert!(memo.wakeups.is_empty());
    }

    /// The guard one memo finalizes is the guard the memo that reads it consumes: the whole
    /// tiling less what the first released, which the second pulls and releases at.
    #[test]
    fn a_memo_consumes_the_guard_the_memo_before_it_finalized() {
        let (mut first, _, _) = memo_over_stream();
        let (mut second, pulled, released) = memo_over_stream();
        first.consume_impl(ints().universal_guard());
        first.release(keys_between(0, 3));
        let handed = first.finalize();
        assert_ne!(
            handed,
            ints().universal_guard(),
            "the released keys are not handed on"
        );
        second.consume_impl(handed.clone());
        assert_eq!(*pulled.borrow(), vec![handed.clone()]);
        assert_eq!(*released.borrow(), vec![handed]);
        let rest = second.get(ints().universal_guard());
        assert_eq!(int_entries(&rest), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);
    }

    /// A pull at `Nothing` consumes nothing.
    #[test]
    fn consuming_nothing_pulls_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.consume_impl(ints().empty_guard());
        assert!(pulled.borrow().is_empty());
        assert!(int_entries(&memo.get(ints().universal_guard())).is_empty());
    }

    /// A pull at `Nothing` answers empty and touches neither the cache nor the input.
    #[test]
    fn a_memo_asked_for_nothing_reads_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        let tile = memo.get(ints().empty_guard());
        assert!(int_entries(&tile).is_empty());
        assert!(pulled.borrow().is_empty());
    }

    /// A `Memo` subscribed over an input whose rows a test writes, with the consumer the input
    /// notifies through and the log of the guards the input was pulled with.
    fn memo_over_growing_input() -> (
        Box<dyn TileProducer>,
        InputConsumer,
        Rc<RefCell<Tile>>,
        GuardLog,
    ) {
        let (input, notifier, rows, pulled) =
            NotifyingOp::scripted(ints_by_position(&[], false), ints());
        let memo = Memo::new(Box::new(input)).subscribe(
            ints().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        );
        (memo, notifier, rows, pulled)
    }

    /// The rows of `keys`, each holding its own key, stated incomplete.
    fn rows_at(keys: std::ops::RangeInclusive<u64>) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(keys.clone().collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                keys.map(|key| key as i64).collect(),
            ))),
            Predicate::False,
            bit_set::BitSet::new(),
        )
    }

    fn notify_keys(notifier: &InputConsumer, from: u64, to: u64) {
        notify_input(
            notifier,
            &Projection::of(&keys_between(from, to)).expect("a region of keys"),
        );
    }

    /// A notification names the keys it changed, and the memo reads the input again over those
    /// keys only: a region it read before and that stayed silent is answered from the cache.
    #[test]
    fn a_memo_rereads_only_the_keys_its_input_notified() {
        let (mut memo, notifier, rows, _) = memo_over_growing_input();
        memo.get(keys_between(0, 2));
        memo.get(keys_between(3, 5));

        // Rows land at 3..=5 and the input says so; none land at 0..=2.
        *rows.borrow_mut() = rows_at(3..=5);
        notify_keys(&notifier, 3, 5);
        let silent = memo.get(keys_between(0, 2));
        assert!(int_entries(&silent).is_empty(), "{silent:?}");
        let notified = memo.get(keys_between(3, 5));
        assert_eq!(int_entries(&notified), vec![(3, 3), (4, 4), (5, 5)]);
    }

    /// A notification of everything, which a chain that re-keys delivers, makes every region
    /// the memo has read stale.
    #[test]
    fn a_memo_rereads_every_region_when_its_input_notifies_everything() {
        let (mut memo, notifier, rows, _) = memo_over_growing_input();
        memo.get(keys_between(0, 2));
        memo.get(keys_between(3, 5));

        *rows.borrow_mut() = rows_at(0..=5);
        notify_input(&notifier, &Projection::Everything);
        assert_eq!(
            int_entries(&memo.get(keys_between(0, 2))),
            vec![(0, 0), (1, 1), (2, 2)]
        );
        assert_eq!(
            int_entries(&memo.get(keys_between(3, 5))),
            vec![(3, 3), (4, 4), (5, 5)]
        );
    }

    /// A region nothing has read reaches the input, whatever the input has notified: the rows
    /// that were there from the start are read by the first pull of them.
    #[test]
    fn a_memo_reads_a_region_nothing_has_read() {
        let (mut memo, notifier, rows, _) = memo_over_growing_input();
        *rows.borrow_mut() = rows_at(6..=7);
        notify_keys(&notifier, 0, 2);
        assert_eq!(
            int_entries(&memo.get(keys_between(6, 7))),
            vec![(6, 6), (7, 7)]
        );
    }

    /// A pull of a region read and not notified since answers from the cache: the input is
    /// pulled to read it and, in a debug build, once to probe it, and no more.
    #[test]
    fn a_memo_answers_a_clean_region_from_the_cache() {
        let (mut memo, _, _, pulled) = memo_over_growing_input();
        for _ in 0..4 {
            memo.get(keys_between(0, 2));
        }
        assert!(
            pulled.borrow().len() <= 2,
            "a read and a probe at most: {:?}",
            pulled.borrow()
        );
    }

    /// An input whose second pull, the memo's probe, lands rows and notifies, as another thread
    /// writing rows and then notifying does between the memo taking its arrivals and probing.
    #[cfg(debug_assertions)]
    struct LandsDuringProbe {
        base: ProducerBase,
        pulls: usize,
        arrivals: Arrivals,
    }

    #[cfg(debug_assertions)]
    impl TileProducer for LandsDuringProbe {
        impl_producer_base!();

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.pulls += 1;
            if self.pulls == 2 {
                self.arrivals
                    .consumer(Box::new(|| {}))
                    .notify(&Projection::Everything);
            }
            match self.pulls {
                1 => ints_by_position(&[], false),
                _ => rows_at(0..=3),
            }
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    /// The rows land and the notification is recorded while the probe runs, so it is waiting
    /// when the probe compares: the rows are the change it announces, not one that came without
    /// it. The next pull takes the notification and reads them.
    #[cfg(debug_assertions)]
    #[test]
    fn the_probe_tolerates_rows_whose_notification_has_not_been_taken_yet() {
        let arrivals = Arrivals::new();
        let mut memo = MemoProducer::new(
            ProducerBase::unowned(MemoProducer::alloc_id(), &ints()),
            Box::new(LandsDuringProbe {
                base: ProducerBase::unowned(LandsDuringProbe::alloc_id(), &ints()),
                pulls: 0,
                arrivals: arrivals.clone(),
            }),
            arrivals,
            shared_consumer(Box::new(|| {})).0,
            WakeupQueue::default(),
        );
        memo.get(keys_between(0, 3));
        assert!(int_entries(&memo.get(keys_between(0, 3))).is_empty());
        assert_eq!(
            int_entries(&memo.get(keys_between(0, 3))),
            vec![(0, 0), (1, 1), (2, 2), (3, 3)]
        );
    }

    fn wider_keys(tile: &Tile) -> Vec<u64> {
        int_entries(tile).into_iter().map(|(k, _)| k).collect()
    }

    /// A notification of everything stands for news anywhere the memo has read. A pull at one
    /// region reads that region only, so the news for the other stays pending until it is pulled.
    #[test]
    fn a_pull_at_one_region_leaves_the_news_for_another_region_pending() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;

        let (input, rows) = ScriptedProducer::new(ints_by_position(&[], false), ints());
        let mut memo = MemoProducer::new(
            ProducerBase::unowned(MemoProducer::alloc_id(), &ints()),
            Box::new(input),
            Arrivals::new(),
            shared_consumer(Box::new(|| {})).0,
            WakeupQueue::default(),
        );
        memo.get(keys_between(0, 3));
        memo.get(keys_between(4, 7));

        // The input answers each region with its own rows once they land.
        let rows_at = |keys: std::ops::RangeInclusive<u64>| {
            Tile::data_function(
                ColumnValue::from_uints(keys.clone().collect()),
                Box::new(Tile::Scalar(ColumnValue::Ints(
                    keys.map(|key| key as i64).collect(),
                ))),
                Predicate::False,
                bit_set::BitSet::new(),
            )
        };
        *rows.borrow_mut() = rows_at(0..=3);
        memo.arrivals
            .consumer(Box::new(|| {}))
            .notify(&Projection::Everything);
        memo.get(keys_between(0, 3));
        memo.release(keys_between(0, 3));

        *rows.borrow_mut() = rows_at(4..=7);
        let later = memo.get(keys_between(4, 7));
        assert_eq!(int_entries(&later), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);
    }

    /// `xs ▷ map(converse(xs))`: each position of a stream is mapped to the positions that hold
    /// its value, which is a group-by read back at the stream. The stream is memoized and fanned
    /// to both the argument leg and, through `Converse`, the function leg.
    ///
    /// `Converse` reads the stream whole, so the shared input is widened to the whole stream
    /// once the function leg pulls it; the morsel's answer is cut at the map.
    #[test]
    fn a_morsel_of_a_map_over_a_converse_of_the_same_memoized_stream() {
        use crate::interpreter::CurryLevel;
        use crate::interpreter::tile_operators::{Converse, MapResult};

        let values = [0i64, 1, 0, 1, 2, 2, 0, 1];
        let (stream, pulled, _) = ProjectionSpyOp::new(ints_by_position(&values, true), ints());
        let fan = FanOut::new(Box::new(Memo::new(Box::new(stream))));
        let by_value = Converse::new(fan.slot());
        let mut map = MapResult::new_at(fan.slot(), Box::new(by_value), CurryLevel::new(1));
        let guard = map.tiling().universal_guard();
        let mut sched = Scheduler::new();
        let mut producer = map.subscribe(guard, Box::new(|| {}), &mut sched);

        let morsel = producer.get(keys_between(2, 3));
        let Tile::DataFunction { domain, .. } = &morsel else {
            panic!("a collection, got {morsel:?}")
        };
        assert_eq!(
            (0..domain.len())
                .map(|i| domain.index_at(i))
                .collect::<Vec<_>>(),
            vec![Value::UInt(2), Value::UInt(3)]
        );
        // Position 2 holds value 0, shared with positions 0 and 6; position 3 holds 1, shared
        // with 1 and 7.
        let Tile::DataFunction {
            row_starts,
            domain: members,
            ..
        } = domain_codomain(&morsel)
        else {
            panic!("a group per position, got {morsel:?}")
        };
        assert_eq!(*row_starts, vec![0, 3]);
        assert_eq!(*members, ColumnValue::UInts(vec![2, 0, 6, 3, 1, 7]));
        // stream, and the shared input is pulled at what both have asked.
        assert_eq!(
            *pulled.borrow(),
            vec![keys_between(2, 3), ints().universal_guard()]
        );
    }

    fn domain_codomain(tile: &Tile) -> &Tile {
        let Tile::DataFunction { codomain, .. } = tile else {
            panic!("a collection, got {tile:?}")
        };
        codomain
    }
}

/// A consuming memo over an input that grows, is released and is notified: what it holds, what it
/// finalizes and what reaches the input, each against a model of the rows written and released.
#[cfg(test)]
mod consuming_tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::interpreter::tile_operators::Scheduler;
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Released, Rng, Shared, Step, entries, growing_source,
        ints, keys_of, keys_predicate, predicate, rows_of, same_region, source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{Predicate, Value};

    /// A memo over `source`, and the consumer its input notifies through.
    fn memo_over(source: &Shared) -> (MemoProducer, Box<dyn Consumer>) {
        let arrivals = Arrivals::new();
        let notifier = arrivals.consumer(Box::new(|| {}));
        let memo = MemoProducer::new(
            ProducerBase::unowned(MemoProducer::alloc_id(), &ints()),
            Box::new(Input::over(source)),
            arrivals,
            shared_consumer(Box::new(|| {})).0,
            WakeupQueue::default(),
        );
        (memo, notifier)
    }

    /// What the memo's cached tile states complete.
    fn statement(memo: &MemoProducer) -> Predicate {
        let Tile::DataFunction {
            domain_predicate, ..
        } = &memo.cached_tile
        else {
            panic!("a collection, got {:?}", memo.cached_tile)
        };
        domain_predicate.clone()
    }

    // ------------------------------------------------------------------------------------
    // The input notifies a region, and the memo consumes it
    // ------------------------------------------------------------------------------------

    /// A consume at the keys an input notified merges what the input answered for them, states
    /// complete those keys and no others, and releases the input at them.
    #[test]
    fn a_notified_region_of_keys_is_what_the_memo_consumes() {
        let source = source(0..10);
        let (mut memo, mut notifier) = memo_over(&source);
        let region = Keys(2, 5);

        notifier.notify(&region.projection());
        assert!(memo.arrivals.pending());
        memo.consume_impl(region.guard());

        assert!(!memo.arrivals.pending(), "the notification is taken");
        assert_eq!(entries(&memo.cached_tile), rows_of(2..=5));
        let stated = statement(&memo);
        assert!(same_region(&stated, &keys_predicate(2, 5)), "{stated:?}");
        for outside in [0, 1, 6, 9] {
            assert!(!stated.contains(&Value::UInt(outside)), "key {outside}");
        }
        assert_eq!(source.borrow().pulled, vec![region.guard()]);
        assert_eq!(source.borrow().released, vec![region.guard()]);
    }

    /// A second region disjoint from the first joins the cache, which then states both.
    #[test]
    fn a_second_disjoint_region_joins_the_cache() {
        let source = source(0..10);
        let (mut memo, mut notifier) = memo_over(&source);
        for region in [Keys(1, 2), Keys(7, 9)] {
            notifier.notify(&region.projection());
            memo.consume_impl(region.guard());
        }
        assert_eq!(entries(&memo.cached_tile), rows_of([1, 2, 7, 8, 9]));
        let stated = statement(&memo);
        let both = keys_predicate(1, 2).union(&keys_predicate(7, 9));
        assert!(same_region(&stated, &both), "{stated:?}");
        assert!(
            !stated.contains(&Value::UInt(5)),
            "a key between is not stated"
        );
        assert_eq!(
            source.borrow().released,
            vec![keys_between(1, 2), keys_between(7, 9)]
        );
    }

    /// A region that overlaps the first is answered for the keys the input still holds, and the
    /// cache states the union.
    #[test]
    fn an_overlapping_region_adds_only_the_keys_the_input_still_holds() {
        let source = source(0..10);
        let (mut memo, mut notifier) = memo_over(&source);
        for region in [Keys(2, 5), Keys(4, 8)] {
            notifier.notify(&region.projection());
            memo.consume_impl(region.guard());
        }
        assert_eq!(entries(&memo.cached_tile), rows_of(2..=8));
        let stated = statement(&memo);
        assert!(same_region(&stated, &keys_predicate(2, 8)), "{stated:?}");
        assert_eq!(
            source.borrow().released,
            vec![keys_between(2, 5), keys_between(4, 8)],
            "the input is released at each guard consumed"
        );
    }

    /// `Everything` notified and consumed drains the input: the cache states the universe, and
    /// `finalize` names all of it.
    #[test]
    fn everything_notified_and_consumed_finalizes_the_universe() {
        let source = source(0..10);
        let (mut memo, mut notifier) = memo_over(&source);
        notifier.notify(&Projection::Everything);
        memo.consume_impl(All.guard());
        assert_eq!(entries(&memo.cached_tile), rows_of(0..10));
        assert!(same_region(&statement(&memo), &Predicate::True));
        assert_eq!(memo.finalize(), ints().universal_guard());
    }

    /// `Nothing` notified is not recorded, and consuming nothing reads nothing.
    #[test]
    fn nothing_notified_is_consumed_as_nothing() {
        let source = source(0..10);
        let (mut memo, mut notifier) = memo_over(&source);
        notifier.notify(&Projection::Nothing);
        assert!(!memo.arrivals.pending());
        memo.consume_impl(ints().empty_guard());
        assert!(source.borrow().pulled.is_empty());
        assert!(entries(&memo.cached_tile).is_empty());
    }

    /// A growing input states complete only the keys it holds, so the release leaves a key it
    /// has not answered, and a row that arrives there later is merged and released.
    #[test]
    fn a_key_the_input_withheld_is_merged_by_a_later_consume() {
        let source = growing_source([0, 1, 2, 4, 5]);
        let (mut memo, _) = memo_over(&source);
        memo.consume_impl(Keys(0, 5).guard());
        let first = predicate(&source.borrow().released[0]);
        assert!(first.contains(&Value::UInt(2)));
        assert!(
            !first.contains(&Value::UInt(3)),
            "the input did not answer key 3"
        );

        source.borrow_mut().rows.insert(3, value(3));
        memo.consume_impl(Keys(0, 5).guard());
        assert_eq!(entries(&memo.cached_tile), rows_of(0..=5));
        let second = predicate(source.borrow().released.last().unwrap());
        assert!(second.contains(&Value::UInt(3)));
    }

    /// An offer at a region nothing consumed states nothing complete there.
    #[test]
    fn an_offer_at_a_region_never_consumed_states_nothing() {
        let (mut memo, _) = memo_over(&source(0..10));
        memo.consume_impl(Keys(0, 3).guard());
        let Tile::DataFunction {
            domain_predicate, ..
        } = memo.get(Keys(6, 8).guard())
        else {
            panic!("a collection")
        };
        assert!(domain_predicate.intersect(&keys_predicate(6, 8)).is_false());
    }

    /// A consume after the output was released at a region merges nothing there: the input does
    /// not answer the region again.
    #[test]
    fn a_consume_after_a_release_merges_nothing_released() {
        let source = source(0..10);
        let (mut memo, _) = memo_over(&source);
        memo.consume_impl(Keys(0, 3).guard());
        memo.release(Keys(0, 3).guard());
        memo.consume_impl(Keys(0, 3).guard());
        assert!(entries(&memo.cached_tile).is_empty());
        assert!(entries(&memo.get(Keys(0, 3).guard())).is_empty());
    }

    /// A release of the whole output leaves nothing held, and a release of every key of the
    /// universe leaves exactly the keys beyond it.
    #[test]
    fn finalize_after_releasing_everything_or_every_key_is_exact() {
        let (mut memo, _) = memo_over(&source(0..10));
        memo.consume_impl(All.guard());
        memo.release(All.guard());
        assert_eq!(memo.finalize(), ints().empty_guard());

        let (mut memo, _) = memo_over(&source(0..10));
        memo.consume_impl(All.guard());
        memo.release(Keys(0, KEYS - 1).guard());
        assert!(same_region(
            &predicate(&memo.finalize()),
            &Predicate::True.minus(&keys_predicate(0, KEYS - 1))
        ));
    }

    /// A release of nothing changes neither the cache nor what `finalize` returns.
    #[test]
    fn a_release_of_nothing_changes_nothing() {
        let (mut memo, _) = memo_over(&source(0..10));
        memo.consume_impl(All.guard());
        let before = (entries(&memo.cached_tile), memo.finalize());
        memo.release(ints().empty_guard());
        assert_eq!((entries(&memo.cached_tile), memo.finalize()), before);
    }

    // ------------------------------------------------------------------------------------
    // What finalize returns
    // ------------------------------------------------------------------------------------

    /// A drained memo finalizes the whole of what it consumed.
    #[test]
    fn finalize_names_everything_consumed() {
        let source = source(0..10);
        let (mut memo, _) = memo_over(&source);
        memo.consume_impl(All.guard());
        assert_eq!(memo.finalize(), ints().universal_guard());
    }

    /// A release of a sub-region leaves the rest: the guard excludes exactly the keys released.
    #[test]
    fn finalize_excludes_what_was_released() {
        let source = source(0..10);
        let (mut memo, _) = memo_over(&source);
        memo.consume_impl(All.guard());
        memo.release(keys_between(2, 3));
        let guard = memo.finalize();
        assert!(same_region(
            &predicate(&guard),
            &Predicate::True.minus(&keys_predicate(2, 3))
        ));
        assert_eq!(
            entries(&memo.cached_tile),
            rows_of([0, 1, 4, 5, 6, 7, 8, 9])
        );
    }

    /// Rows added after a first consume, and consumed, are in the guard; the released keys are
    /// still out of it.
    #[test]
    fn finalize_includes_rows_added_and_consumed_later_and_still_excludes_released_ones() {
        let source = source(0..6);
        let (mut memo, mut notifier) = memo_over(&source);
        memo.consume_impl(keys_between(0, 5));
        memo.release(keys_between(2, 3));

        source.borrow_mut().rows.insert(9, value(9));
        notifier.notify(&Keys(6, 11).projection());
        memo.consume_impl(All.guard());

        let guard = keys_of(&memo.finalize());
        assert_eq!(guard, (0..KEYS).filter(|k| ![2, 3].contains(k)).collect());
        assert!(guard.contains(&9), "the row added later");
        assert_eq!(entries(&memo.cached_tile), rows_of([0, 1, 4, 5, 9]));
    }

    /// An input that has stated everything complete and holds no row leaves a cache that states
    /// the universe and holds nothing: its guard is the universe.
    #[test]
    fn finalize_of_a_memo_over_an_empty_input_is_the_universe() {
        let source = source([]);
        let (mut memo, _) = memo_over(&source);
        memo.consume_impl(All.guard());
        assert!(entries(&memo.cached_tile).is_empty());
        assert_eq!(memo.finalize(), ints().universal_guard());
    }

    /// A memo that was not consumed has a cache that states nothing, and a pipeline does not
    /// finalize before its input has drained.
    #[test]
    #[should_panic(expected = "finalizes after its input has stated everything complete")]
    fn finalize_before_the_first_consume_panics() {
        let (mut memo, _) = memo_over(&source(0..3));
        memo.finalize();
    }

    /// A cache of outermost keys has no exact difference with a release named beneath the keys,
    /// so `finalize` names the gap rather than answering another region.
    #[test]
    #[should_panic(expected = "the guard algebra has no difference")]
    fn guard_minus_of_a_shape_without_a_spelling_panics() {
        let beneath = TileGuard::Function(FunctionGuard::Codomain(Box::new(Keys(1, 2).guard())));
        guard_minus(&ints().universal_guard(), &beneath);
    }

    /// A memo of groups released beneath its keys holds a region the guard algebra cannot take
    /// exactly out of what it stated, so `finalize` names the gap.
    #[test]
    #[should_panic(expected = "the guard algebra has no difference")]
    fn a_release_beneath_the_groups_of_a_memo_has_no_difference() {
        use crate::interpreter::tile_operators::growing::{NestedInput, nested_tiling};
        let mut memo =
            MemoProducer::over(Box::new(NestedInput::over(&source(0..4))), &nested_tiling());
        memo.consume_impl(nested_tiling().universal_guard());
        memo.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            Keys(0, 1).guard(),
        ))));
        memo.finalize();
    }

    // ------------------------------------------------------------------------------------
    // Wakes
    // ------------------------------------------------------------------------------------

    /// A consumer of a consuming memo is woken by the input's notification, as a memo's in pull mode
    /// is; `consume_impl` and `finalize` queue no wake of their own for a read the notification
    /// announced.
    #[test]
    fn the_consumer_of_a_consuming_memo_is_woken_by_the_input_notification() {
        use crate::interpreter::scheduler::forwarding_consumer_keeping_keys;

        let woken = Rc::new(Cell::new(0));
        let counted = woken.clone();
        let (consumer, gate) = shared_consumer(Box::new(move || counted.set(counted.get() + 1)));
        let mut sched = Scheduler::new();
        let wakeups = sched.wakeup_queue();
        let arrivals = Arrivals::new();
        let mut notifier = arrivals.consumer(forwarding_consumer_keeping_keys(&consumer, &wakeups));
        let (mut memo, _) = memo_over(&source(0..4));
        memo.arrivals = arrivals;
        memo.consumer = consumer;
        memo.wakeups = wakeups;
        // A pull of the memo reopens the gate the notification closed, as it does in a program.
        memo.base = ProducerBase::unowned(MemoProducer::alloc_id(), &ints()).sharing(gate);

        notifier.notify(&All.projection());
        sched.check_for_notifications();
        assert_eq!(
            woken.get(),
            1,
            "the input's notification reaches the consumer"
        );

        memo.consume_impl(All.guard());
        sched.check_for_notifications();
        assert_eq!(
            woken.get(),
            1,
            "the gate is closed until the consumer pulls"
        );
        memo.get(All.guard());
        memo.finalize();
        assert!(memo.wakeups.is_empty(), "finalize queues no wake");
    }

    /// A consumer woken by the input's notification pulls a consuming memo before the driver
    /// consumes the keys notified: it is answered from the rows consumed so far, and the consume
    /// that merges the new rows wakes it again, since no later notification will.
    #[test]
    fn a_consumer_that_pulled_between_the_notification_and_the_consume_is_woken_by_the_consume() {
        use crate::interpreter::scheduler::forwarding_consumer_keeping_keys;

        let woken = Rc::new(Cell::new(0));
        let counted = woken.clone();
        let (consumer, gate) = shared_consumer(Box::new(move || counted.set(counted.get() + 1)));
        let mut sched = Scheduler::new();
        let wakeups = sched.wakeup_queue();
        let arrivals = Arrivals::new();
        let mut notifier = arrivals.consumer(forwarding_consumer_keeping_keys(&consumer, &wakeups));
        let (mut memo, _) = memo_over(&source(0..4));
        memo.arrivals = arrivals;
        memo.consumer = consumer;
        memo.wakeups = wakeups;
        // A pull of the memo reopens the gate the notification closed, as it does in a program.
        memo.base = ProducerBase::unowned(MemoProducer::alloc_id(), &ints()).sharing(gate);

        memo.consume_impl(Keys(0, 1).guard());
        notifier.notify(&Keys(2, 3).projection());
        sched.check_for_notifications();
        assert_eq!(woken.get(), 1, "the notification wakes the consumer");

        let pulled = memo.get(All.guard());
        assert_eq!(
            entries(&pulled),
            rows_of([0, 1]),
            "the rows consumed so far"
        );

        memo.consume_impl(Keys(2, 3).guard());
        sched.check_for_notifications();
        assert_eq!(woken.get(), 2, "the rows the consume merged are announced");
    }

    // ------------------------------------------------------------------------------------
    // Interleavings of consumes, releases, new rows and notifications
    // ------------------------------------------------------------------------------------

    /// A consuming memo and a twin in pull mode over growing inputs that receive the same script,
    /// and the model the consuming memo is held to. The input notifies both memos of every row
    /// and of its close, as its notification contract asks; a `Notify` step is a notification
    /// with no change behind it.
    struct Run {
        consuming: MemoProducer,
        consuming_notifier: Box<dyn Consumer>,
        consuming_source: Shared,
        lazy: MemoProducer,
        lazy_notifier: Box<dyn Consumer>,
        lazy_source: Shared,
        input: InputModel,
        /// What the memo's output was released at.
        memo_released: Released,
        memo_released_predicate: Predicate,
        /// What the answers the memo merged state complete, together.
        stated: Predicate,
        /// The keys the cache holds.
        cache: BTreeSet<u64>,
        /// Whether an answer stated everything complete, after which the memo reads no more.
        drained: bool,
        /// The seed, the iteration, the initial rows and the steps so far, for a failure.
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let (consuming_source, lazy_source) = (
                growing_source(initial.iter().copied()),
                growing_source(initial.iter().copied()),
            );
            let (consuming, consuming_notifier) = memo_over(&consuming_source);
            let (lazy, lazy_notifier) = memo_over(&lazy_source);
            Self {
                consuming,
                consuming_notifier,
                consuming_source,
                lazy,
                lazy_notifier,
                lazy_source,
                input: InputModel::new(initial),
                memo_released: Released::default(),
                memo_released_predicate: Predicate::False,
                stated: Predicate::False,
                cache: BTreeSet::new(),
                drained: false,
                trace,
            }
        }

        fn notify(&mut self, region: Projection) {
            self.consuming_notifier.notify(&region);
            self.lazy_notifier.notify(&region);
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        for source in [&self.consuming_source, &self.lazy_source] {
                            source.borrow_mut().rows.insert(key, value(key));
                        }
                        self.notify(Keys(key, key).projection());
                    }
                }
                Notify(region) => self.notify(region.projection()),
                Close => {
                    self.input.closed = true;
                    for source in [&self.consuming_source, &self.lazy_source] {
                        source.borrow_mut().closed = true;
                    }
                    self.notify(Projection::Everything);
                }
                Consume(region) => {
                    self.consuming.consume_impl(region.guard());
                    if !self.drained {
                        let (answered, stated) = self.input.pull(region);
                        self.cache.extend(answered);
                        self.stated = self.stated.union(&stated);
                        self.drained = self.input.closed && matches!(region, All);
                    }
                }
                Release(region) => {
                    self.consuming.release(region.guard());
                    self.lazy.release(region.guard());
                    if !self.memo_released.covers(region) {
                        let keys = region.keys();
                        self.cache.retain(|key| !keys.contains(key));
                        self.memo_released.add(region);
                        self.memo_released_predicate = self
                            .memo_released_predicate
                            .union(&predicate(&region.guard()));
                        self.input.release(region);
                    }
                }
            }
        }

        /// The consuming memo and the input against the model.
        fn check(&mut self) {
            let trace = &self.trace;
            assert_eq!(
                entries(&self.consuming.cached_tile),
                rows_of(self.cache.iter().copied()),
                "{trace}: the cache"
            );
            self.input.check(&self.consuming_source, trace);
            if self.input.drained() {
                let guard = predicate(&self.consuming.finalize());
                let expected = self.stated.minus(&self.memo_released_predicate);
                assert!(
                    same_region(&guard, &expected),
                    "{trace}: finalize is {guard:?}, not what was stated less what was released \
                     {expected:?}"
                );
            }
        }

        /// Close the input, consume everything, and compare what the consuming memo offers with
        /// what the twin in pull mode answers for the same script.
        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            for guard in [
                ints().universal_guard(),
                keys_between(0, 3),
                keys_between(4, 7),
                keys_between(2, 9),
            ] {
                assert_eq!(
                    entries(&self.consuming.get(guard.clone())),
                    entries(&self.lazy.get(guard.clone())),
                    "{}: offer at {guard:?}",
                    self.trace
                );
            }
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            run.finish();
        }
    }

    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Notify, Release};

    /// Sequences that interleave a consume of part of the input, a release of part of the output
    /// and of what the input holds, rows added before and after a release, at keys the input has
    /// not answered, inside a released region and after the input closes.
    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[
                Consume(Keys(0, 3)),
                Add(3),
                Consume(Keys(0, 3)),
                Add(8),
                Consume(Keys(4, 11)),
            ],
            &[
                Consume(Keys(0, 3)),
                Release(Keys(1, 2)),
                Add(9),
                Consume(Keys(4, 11)),
                Close,
                Consume(All),
            ],
            &[
                Add(2),
                Consume(Keys(0, 3)),
                Add(3),
                Notify(Keys(0, 3)),
                Consume(Keys(0, 3)),
            ],
            &[
                Release(Keys(5, 6)),
                Add(5),
                Add(6),
                Add(7),
                Consume(Keys(4, 8)),
            ],
            &[
                Consume(Keys(0, 5)),
                Consume(Keys(3, 8)),
                Release(Keys(4, 6)),
                Close,
                Consume(All),
            ],
            &[Release(Keys(0, 11)), Add(3), Close, Consume(All)],
            &[
                Close,
                Consume(All),
                Add(4),
                Release(Keys(0, 1)),
                Consume(Keys(0, 6)),
            ],
            &[
                Consume(Keys(2, 5)),
                Release(Keys(2, 5)),
                Add(3),
                Consume(Keys(2, 5)),
            ],
            &[
                Consume(Keys(6, 8)),
                Add(7),
                Add(10),
                Release(Keys(7, 10)),
                Consume(Keys(6, 11)),
            ],
            &[Close, Consume(Keys(0, 3)), Release(All), Consume(All)],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    /// Three hundred sequences of fourteen steps each, from a seed of the memo's own. A release
    /// names keys the cache holds half the time.
    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..14 {
                let step = rng.step_among(&run.cache, true);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}

use log::trace;
use std::{
    cell::{Cell, RefCell},
    rc::{Rc, Weak},
};

use super::*;
use crate::{
    interpreter::{Consumer, Scheduler},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Re-entrancy bookkeeping for cyclic op graphs.  Stored in
/// [`FanOutShared::reentrancy`] only for fan-outs constructed via
/// [`FanOut::new_cyclic`]; non-cyclic fan-outs leave it `None` and pay
/// none of the cyclic-mode overhead.
///
/// A fan-out is "cyclic" iff one of its branches feeds (transitively)
/// back into its own input.  In practice this is the commit store's
/// recurrence: one branch feeds back into the store's own input and the
/// body's prior-value reads (`get_prev_txn`) close the cycle.  In that setup,
/// subscribing or pulling one branch can synchronously trigger the same
/// operation on a sibling branch — the re-entrancy state below catches
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
    /// Re-entrancy guard for the inner subscribe path.  `FanOutBranch::subscribe`
    /// of one branch can transitively trigger `subscribe` on a sibling
    /// (e.g. an induction loop's drive subscribes to its store branch while
    /// the store is subscribing the body that reads the drive).
    /// The re-entrant call sees this set, skips the inner subscribe (the
    /// outer call is doing it), and just returns a `FanOutProducer`.
    subscribing_inner: bool,
}

/// Mutable state shared across all branches from the same [`FanOut`] and all
/// [`FanOutProducer`]s it creates.  Wrapping this in `Rc<RefCell<...>>` and
/// creating it eagerly in [`FanOut::new`] ensures that every branch produced by
/// [`FanOut::branch`] shares the same object from the start — even before any
/// [`TileOperator::subscribe`] call has initialised the inner producer.
struct FanOutShared {
    /// Instance ID shared by all [`FanOutProducer`]s from the same fan-out group.
    id: usize,
    /// Inner producer, set on the first [`FanOutBranch::subscribe`] call.
    ///
    /// In cyclic mode (see [`FanOutReentrancy`]), this is also **taken out**
    /// during the inner pull in `FanOutProducer::get_impl` so that
    /// re-entrant calls from cyclic op graphs can detect re-entrance by
    /// finding `None` and fall back to the cached tile.
    producer: Option<Box<dyn TileProducer>>,
    /// Every consumer registered via [`FanOutBranch::subscribe`], in order.
    ///
    /// Stored as `Rc<RefCell<...>>` so that the notification closure can clone the
    /// handles, release the `shared` borrow, and then call each consumer without
    /// holding `shared` across the notification.  This prevents a re-entrant panic
    /// when a consumer (e.g. `SinkConsumer`) calls back into `FanOutProducer::get_impl`,
    /// which itself needs `shared.borrow_mut()`.
    consumers: Vec<Rc<RefCell<Box<dyn Consumer>>>>,
    /// Per-subscriber release guards; intersected before passing upstream.
    release_guards: Vec<TileGuard>,
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
    /// grow by one dead slot per replaced subscriber on every update, forever,
    /// and both the notify walk and the release intersection scan it.
    ///
    /// [`release_guards`]: FanOutShared::release_guards
    /// [`consumers`]: FanOutShared::consumers
    subscribers: Vec<Weak<Cell<usize>>>,
    /// Re-entrancy bookkeeping for cyclic op graphs.  `None` for non-cyclic
    /// fan-outs (the overwhelming majority); `Some` only when constructed
    /// via [`FanOut::new_cyclic`].
    reentrancy: Option<FanOutReentrancy>,
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
/// underlying operator.  Call [`FanOut::branch`] to get additional handles;
/// subscribing to any handle will reuse the same inner producer.
pub struct FanOut {
    // shared-state-ok: the fan-out's own input operator, shared with the branches
    // that are views of this one operator. It holds an *operator*, not values
    // passed between operators — the same reason `CycleSlot` is legitimate.
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that branches produced by
    /// [`FanOut::branch`] always share the same object.
    shared: Rc<RefCell<FanOutShared>>,
    /// Whether any branches have been created yet.
    // shared-state-ok: construction-time bookkeeping of the `FanOut` itself, not a
    // channel between operators — it records that `branch` has been called, and no
    // value ever passes through it.
    used: RefCell<bool>,
}

impl FanOut {
    /// Construct a new `FanOut` wrapping `input`.  Use this for ordinary
    /// (non-cyclic) op graphs; the resulting fan-out doesn't pay any
    /// cyclic-mode overhead.  If a branch of this fan-out ends up
    /// feeding back into its own input (e.g. a store recurrence closing
    /// through the fan-out), use [`FanOut::new_cyclic`] instead.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_with_reentrancy(input, None)
    }

    /// Construct a cyclic [`FanOut`].  Sets up the re-entrancy bookkeeping
    /// (a cached tile snapshot + a subscribe-in-progress flag) needed when
    /// a branch of this fan-out transitively feeds back into its own input.
    ///
    /// The cost relative to [`FanOut::new`] is one `Tile` clone per pull
    /// (to refresh the cache).  The mutation-loop body fan-out is the only
    /// caller today; non-cyclic users should stick with `new`.
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
            subscribers: Vec::new(),
            reentrancy,
        }));
        Self {
            input: Rc::new(RefCell::new(input)),
            tiling,
            shared,
            used: RefCell::new(false),
        }
    }

    /// Return a new branch handle on this fan-out.  All branches share the same
    /// inner producer and consumer list; subscribing to any of them is
    /// equivalent.
    pub fn branch(&self) -> Box<dyn TileOperator> {
        let result = FanOutBranch {
            input: self.input.clone(),
            tiling: self.tiling.clone(),
            shared: self.shared.clone(), // shares the Rc — always connected
            primary: !*self.used.borrow(),
        };
        *self.used.borrow_mut() = true;
        Box::new(result)
    }

    pub fn tiling(&self) -> &Tiling {
        &self.tiling
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

    /// Reopen this fan-out for a fresh set of branches, keeping the inner
    /// producer and everything it has accumulated.
    ///
    /// For carrying one operator across a program update. Only the
    /// [`inspect`](TileOperator::inspect) bookkeeping resets: which branch
    /// renders the input subtree and which renders a back-reference. The
    /// subscriptions need no attention, because each is tied to the life of the
    /// producer it handed out ([`FanOutShared::subscribers`]) — a subscriber the
    /// update dropped stops counting on its own, and one the update carried
    /// forward keeps its guard.
    pub fn reopen(&self) {
        *self.used.borrow_mut() = false;
        self.shared.borrow_mut().compact();
    }
}

struct FanOutBranch {
    // shared-state-ok: the same operator handle as [`FanOut::input`] — a branch is
    // a view of one fan-out, not a second one. An operator, not a value.
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that branches produced by
    /// [`FanOut::branch`] always share the same object.
    shared: Rc<RefCell<FanOutShared>>,
    /// True for the first handle returned by [`FanOut::branch`], false for subsequent ones.
    /// The primary renders its input subtree in inspect; copies emit a back-reference.
    primary: bool,
}

impl TileOperator for FanOutBranch {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = self.shared.borrow().id;
        if self.primary {
            InspectNode::new(format!("FanOut#{id}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.input.borrow().inspect(opts))
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
        {
            let mut shared = self.shared.borrow_mut();
            slot.set(shared.consumers.len());
            shared.consumers.push(Rc::new(RefCell::new(consumer)));
            shared.release_guards.push(self.tiling.empty_guard());
            shared.subscribers.push(Rc::downgrade(&slot));
        } // borrow released here before we might call input.subscribe

        // Decide whether *this* call should drive the inner subscribe.
        // `producer.is_none()` is the standard "first subscription" check;
        // in cyclic mode, `!reentrancy.subscribing_inner` makes the path
        // re-entrancy-safe: a sibling-branch subscribe triggered from
        // inside the inner subscribe call sees the flag set and just
        // returns a producer (the outer call will populate `producer`
        // before anyone pulls).
        let should_subscribe = {
            let mut shared = self.shared.borrow_mut();
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
            let _guard = SubscribingInnerGuard {
                shared: &self.shared,
            };
            let shared_rc = self.shared.clone();
            let inner = self.input.borrow_mut().subscribe(
                intent_guard,
                Box::new(move || {
                    // Clone the consumer handles while holding a short borrow,
                    // then release the borrow before calling notify().  This
                    // prevents a re-entrant panic when a consumer (e.g.
                    // SinkConsumer) calls FanOutProducer::get_impl(), which
                    // needs shared.borrow_mut() for the same Rc.
                    let consumers = {
                        let shared = shared_rc.borrow();
                        shared
                            .live_indices()
                            .map(|i| shared.consumers[i].clone())
                            .collect::<Vec<_>>()
                    };
                    for c in &consumers {
                        c.borrow_mut().notify();
                    }
                }),
                scheduler,
            );
            self.shared.borrow_mut().producer = Some(inner);
            // `_guard` drops here, resetting `subscribing_inner`.
        }

        Box::new(FanOutProducer {
            base: ProducerBase::new(self.shared.borrow().id, &self.tiling),
            shared: self.shared.clone(),
            slot,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.borrow().result_correlation()
    }
}

struct FanOutProducer {
    base: ProducerBase,
    /// Shared state (consumers + release guards).
    shared: Rc<RefCell<FanOutShared>>,
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
}

impl TileProducer for FanOutProducer {
    impl_producer_base!();

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        if self.index() == 0 {
            InspectNode::new(self.name())
                .with_tiling(self.tiling().to_string())
                .child(
                    "input",
                    self.shared
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
        // In cyclic mode, take the inner producer out during the pull so
        // sibling-branch re-entrance can detect re-entrance by finding
        // `producer == None` and serve from the cached tile.  In
        // non-cyclic mode, the producer stays in `shared` and we pull
        // through a regular borrow.
        let cyclic = self.shared.borrow().reentrancy.is_some();
        let mut result = if cyclic {
            let producer_opt = self.shared.borrow_mut().producer.take();
            if let Some(producer) = producer_opt {
                // RAII: put the producer back into `shared` on any exit
                // path (success or panic).  Without this guard, a panic
                // from `producer.get(...)` would leave `shared.producer
                // = None` forever, silently breaking every subsequent
                // pull on this fan-out.
                let mut guard = TakenProducerGuard {
                    shared: &self.shared,
                    producer: Some(producer),
                };
                let tile = guard.producer.as_mut().unwrap().get(projection_guard);
                trace!("{} received {tile:?}", self.name());
                // Refresh the re-entrancy cache before the guard drops.
                // We replace (not merge) — inner producers like `Memo`
                // already return cumulative tiles, so each pull
                // supplants the previous cached snapshot.
                self.shared
                    .borrow_mut()
                    .reentrancy
                    .as_mut()
                    .unwrap()
                    .cached_tile = tile.clone();
                tile
                // `guard` drops here, restoring `shared.producer`.
            } else {
                // Re-entrant pull: another branch's outer `get_impl` is
                // currently holding the producer.  Serve the latest known
                // emission instead of re-entering the inner producer (which
                // would alias `&mut`).
                let cached = self
                    .shared
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
            self.shared
                .borrow_mut()
                .producer
                .as_mut()
                .unwrap()
                .get(projection_guard)
        };

        // Filter by the stored obsolete guard. Because upstream retains data according to the
        // intersection of all obsolete guards, it may have more data than this specific consumer
        // is interested in.
        let guard = self.shared.borrow().release_guards[self.index()].clone();
        trace!("{} removing {guard:?} from {result:?}", self.name());
        result.remove_guarded(guard);
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let mut shared = self.shared.borrow_mut();
        // Union with the existing stored guard so that the accumulated set of
        // delivered data grows monotonically.  Replacing (instead of union-ing)
        // would forget previously-released ranges, causing FanOutBranch to
        // re-deliver data that a consumer has already released.
        let index = self.index();
        let accumulated = shared.release_guards[index].union(&obsolete_guard);
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
        trace!("{} releasing: {intersection:?}", self.name());
        // In cyclic mode the inner producer can be temporarily taken out
        // by a sibling-branch `get_impl`; skip the inner release in that
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
    pub tiling: Tiling,
}

impl Memo {
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self { input, tiling }
    }
}

impl TileOperator for Memo {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(MemoProducer {
            base: ProducerBase::new(MemoProducer::alloc_id(), &self.tiling),
            input: self.input.subscribe(intent_guard, consumer, scheduler),
            cached_tile: self.tiling().empty_tile(),
            upstream_drained: false,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

struct MemoProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    cached_tile: Tile,
    /// Set once this producer has released its input **universally**, which it
    /// does as soon as the input hands over a complete tile.
    ///
    /// Once everything the input will ever produce is cached, pulling it again
    /// is pointless work: a conforming input answers empty for a region it has
    /// released, which merges to nothing. So skipping the pull is an
    /// *optimization*, and only release builds take it — see [`Self::get_impl`].
    upstream_drained: bool,
}

impl TileProducer for MemoProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        // Everything the input will ever produce is already cached, so the pull
        // below can only return what was released — which a conforming input
        // answers empty, merging to nothing. Skipping it saves the work.
        //
        // Debug builds deliberately do *not* skip it. A `Memo` sits above most
        // scalar producers, so short-circuiting here would shield every one of
        // them from ever being pulled after a universal release — the exact
        // state the release-contract assertion in `TileProducer::get` exists to
        // check. Keeping the pull in debug turns this cache from a shield into a
        // probe: an input that answers with released data trips the assertion at
        // the input, where the defect is, instead of corrupting the cache here.
        //
        // `cfg!` rather than `#[cfg]` so both configurations stay compiled.
        if self.upstream_drained && !cfg!(debug_assertions) {
            return self.cached_tile.clone();
        }
        let mut input = self.input.get(projection_guard);
        trace!("{} received {input:?}", self.name());
        let upstream_obsolete = input.to_guard();
        input.compact();
        trace!("{} releasing {upstream_obsolete:?}", self.name());
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
        self.cached_tile.merge(input);
        self.cached_tile.clone()
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

#[cfg(test)]
mod tests {
    use super::*;
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
            .branch()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        let mut second = fan
            .branch()
            .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut sched);
        assert_eq!(fan.shared.borrow().subscribers.len(), 2);

        // Distinguish the survivor's guard from the empty one the dead slot holds.
        let mine = TileGuard::Scalar(true);
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

    /// A `Memo` releases its input universally as soon as the input hands over a
    /// complete tile, and from then on the cache is the value: repeated pulls
    /// answer the same single scalar.
    ///
    /// This has to hold in both build configurations, because only release builds
    /// skip the upstream pull (see [`MemoProducer::get_impl`]). A debug build
    /// re-pulls, and the input — honoring the release it was just handed — answers
    /// empty, which merges to nothing. Were the input to answer with the released
    /// value again, `merge` would append it: a `Tile::Scalar`'s positions are
    /// implicit, so it cannot tell "this position again" from "one more position",
    /// and one value would silently become two, then three.
    #[test]
    fn memo_holds_one_value_across_repeated_pulls() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (upstream, _released) =
            QuietSpy::new(Tile::Scalar(ColumnValue::Ints(vec![-5])), tiling.clone());
        let mut memo = MemoProducer {
            base: ProducerBase::new(MemoProducer::alloc_id(), &tiling),
            input: Box::new(upstream),
            cached_tile: tiling.empty_tile(),
            upstream_drained: false,
        };

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

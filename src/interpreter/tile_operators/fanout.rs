#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::Announce as _;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ConsumeInPipeline as _;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::SharedCounter as Cell;
use log::trace;
use std::sync::PoisonError;
use std::sync::RwLock;
use std::sync::{Arc, Weak};

use super::*;
use crate::ccl::provenance::NodeId;
use crate::interpreter::Prefix;
use crate::interpreter::operator_graph::{share, value};
use crate::{
    interpreter::{
        Consumer, Position, Projection, SubscribeContext, notifications::shared_consumer,
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
/// [`FanOutProducer`]s it creates.  Wrapping this in `Arc<RwLock<...>>` and
/// creating it eagerly in [`FanOut::new`] ensures that every slot produced by
/// [`FanOut::slot`] shares the same object from the start — even before any
/// [`TileOperator::subscribe`] call has initialised the inner producer.
pub(crate) struct FanOutShared {
    /// Instance ID shared by all [`FanOutProducer`]s from the same fan-out group.
    id: usize,
    /// Inner producer, set on the first [`FanOutSlot::subscribe`] call.
    producer: Option<Inner>,
    /// Every consumer registered via [`FanOutSlot::subscribe`], in order.
    ///
    /// Stored as shared handles so that the notification closure can clone them,
    /// release the `shared` read, and then call each consumer without
    /// holding `shared` across the notification. This prevents a re-entrant deadlock
    /// when a consumer (e.g. `SinkConsumer`) calls back into `FanOutProducer::get_impl`,
    /// which itself takes the `shared` write lock.
    consumers: Vec<SharedConsumer>,
    /// Per-subscriber release guards; intersected before passing upstream.
    release_guards: Vec<TileGuard>,
    /// Per subscriber, what its reader released, together with what the reader it replaces had
    /// released by the same measure, parallel to [`release_guards`](Self::release_guards). Each
    /// release through the slot grows it ([`FanOutProducer::release`]).
    ///
    /// It differs from the release guard by what the fan-out reclaimed past a slot that died
    /// before a handover, which the guard a replacement starts at adds and this record does not.
    /// The dead slot's reader never received those rows, so a replacement announces only this
    /// record's keys ([`Unannounced`]), and so does the replacement of that replacement.
    own: Vec<TileGuard>,
    /// Per subscriber, the keys its predecessor's [`own`](Self::own) record names whole that its
    /// reader has not released itself, which [`AnnounceInherited`] adds to each region delivered
    /// to the reader ([`Unannounced`]). `None` once the reader has released all of them, and for
    /// a subscriber whose predecessor released no key whole.
    unannounced: Vec<Option<Unannounced>>,
    /// Whether each subscriber reads through a [`recurrence_slot`](FanOut::recurrence_slot),
    /// parallel to [`consumers`](Self::consumers): an operator inside the store's cycle, which a
    /// push skips.
    recurrence: Vec<bool>,
    current_values: Vec<bool>,
    /// What every slot [`counted_indices`](Self::counted_indices) names, and every retired slot,
    /// had agreed to release the last time one released, and so what this fan-out has already
    /// passed upstream.
    ///
    /// It decides what the input may reclaim and nothing else. A subscriber starts at the
    /// release of the reader it replaces ([`retired`](Self::retired)), and at this region only
    /// where it replaces none: the region is gone, so a subscriber claiming to want it would
    /// hold the intersection back at a frontier no one is waiting on. Within one version every
    /// subscription is made before any data flows, so this is the empty guard then.
    released: TileGuard,
    /// The reader each slot serves, parallel to [`release_guards`](Self::release_guards): the
    /// nodes of the terms whose conversion minted it, across the versions that kept the reader
    /// and were held at the fan-out's last alias or compaction ([`FanOut::alias_readers`]).
    /// Empty for a slot no version replaces a reader through, and for one whose versions are
    /// all gone, which no compilation can name as a predecessor.
    readers: Vec<Vec<Named>>,
    /// The last position each slot's releases have named as a prefix, parallel to
    /// [`release_guards`](Self::release_guards), for an output whose domain is ordered.
    ///
    /// Kept beside the guard rather than read off it, because a drive that finishes releases
    /// the whole domain, and a universal release names no position. It rises only on a release
    /// that is itself a prefix ([`Predicate::as_prefix_in`]), so a release of keys absent above
    /// the drive's cursor does not move it.
    positions: Vec<Option<Position>>,
    /// The slots a version handover found dead, with the readers they served, so that a
    /// subscriber replacing one starts at that reader's release
    /// ([`FanOutSlot::subscribe`]). They hold the reclamation intersection back until the
    /// handover settles ([`FanOut::settle_handover`]), so nothing a replacement still reads is
    /// reclaimed in between.
    retired: Vec<RetiredSlot>,
    /// Whether a version handover is open: from [`FanOut::reopen`] until
    /// [`FanOut::settle_handover`]. While it is, a slot that dies keeps its guard in the
    /// reclamation intersection where it served a reader
    /// ([`counted_indices`](Self::counted_indices)). A replacement for that reader may subscribe
    /// later in the same handover and start at that guard.
    handing_over: bool,
    /// Each subscriber's slot number, parallel to every other per-slot vector of
    /// this struct: [`consumers`], [`release_guards`], [`own`](Self::own),
    /// [`unannounced`](Self::unannounced), [`recurrence`](Self::recurrence),
    /// `current_values`, [`readers`](Self::readers) and
    /// [`positions`](Self::positions). [`compact`](Self::compact) drops a slot
    /// from each of them.
    ///
    /// The [`FanOutProducer`] a subscription handed out owns the strong side, so
    /// a dead entry means that subscriber's producer has been dropped. Its slot
    /// is then skipped: it is not notified, and it holds the release intersection
    /// back only while a handover is open and it served a reader
    /// ([`counted_indices`](Self::counted_indices)).
    ///
    /// A `Cell<usize>` rather than a bare token because the slot number is the
    /// subscription's identity, and [`compact`](Self::compact) renumbers. A
    /// producer reads its index out of the cell it shares with this entry, so
    /// dropping dead slots stays compatible with addressing a guard by index:
    /// the survivors are told their new numbers. Without that the list would
    /// grow by one dead slot per replaced subscriber on every reload, forever,
    /// and both the notify walk and the release intersection scan it.
    ///
    /// [`release_guards`]: FanOutShared::release_guards
    /// [`consumers`]: FanOutShared::consumers
    subscribers: Vec<Weak<std::sync::atomic::AtomicUsize>>,
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
}

/// The reader a fan-out slot serves across a reload: the node of the term whose conversion minted
/// the slot. A slot minted in a new version for a term that corresponds to one in the version it
/// replaces starts at the release of that term's slot (`src/ccl/design/program-evolution.md`,
/// "Where a rebuilt reader picks up"). A term mints at most one slot of a fan-out a reload can
/// keep, which subscribing asserts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlotReader {
    node: NodeId,
}

impl SlotReader {
    /// The slot the term at `node` mints.
    pub fn new(node: NodeId) -> Self {
        Self { node }
    }
}

/// One compiled version of a program, alive while an operator map of it is held: by the branch
/// that runs it, or by a compilation that replaces it, from the offer until the handover settles.
/// A fan-out drops the names a version gave its readers once that version is not held, at its
/// next alias or compaction ([`FanOut::alias_readers`]).
#[derive(Clone, Default)]
pub struct Version(Arc<()>);

/// A name that a version gives the reader of a slot ([`FanOutShared::readers`]).
#[derive(Clone)]
struct Named {
    reader: SlotReader,
    version: Weak<()>,
}

impl Named {
    fn new(reader: SlotReader, version: &Version) -> Self {
        Self {
            reader,
            version: Arc::downgrade(&version.0),
        }
    }
}

/// Drop the names of `names` whose version no operator map holds any more.
fn drop_dead_names(names: &mut Vec<Named>) {
    names.retain(|named| named.version.strong_count() > 0);
}

/// Whether a slot with the names `names` serves `reader`.
fn serves(names: &[Named], reader: SlotReader) -> bool {
    names.iter().any(|named| named.reader == reader)
}

/// A slot a version handover found dead ([`FanOutShared::retired`]).
struct RetiredSlot {
    readers: Vec<Named>,
    /// What the slot holds back in the reclamation intersection, and what a replacement starts
    /// at: the slot's release guard and, for a slot that died before the handover, what the
    /// fan-out reclaimed since.
    guard: TileGuard,
    /// The slot's [`FanOutShared::own`] record.
    own: TileGuard,
    position: Option<Position>,
}

/// What the slot that served a reader released ([`FanOutShared::release_of`]).
struct SlotRelease<'a> {
    /// The guard a replacement for the reader starts at.
    guard: &'a TileGuard,
    /// What the reader and the readers it replaced released ([`FanOutShared::own`]). It differs
    /// from [`guard`](Self::guard) where a slot in that line died before a handover: the
    /// fan-out may have reclaimed rows past it since, which no reader in the line received.
    own: &'a TileGuard,
    /// The last position the reader released as a prefix ([`FanOutShared::positions`]).
    position: &'a Option<Position>,
}

impl FanOutShared {
    /// What the slot that served `reader` released, live, dead or retired.
    fn release_of(&self, reader: SlotReader) -> Option<SlotRelease<'_>> {
        let in_slots = (0..self.readers.len())
            .find(|&i| serves(&self.readers[i], reader))
            .map(|i| SlotRelease {
                guard: &self.release_guards[i],
                own: &self.own[i],
                position: &self.positions[i],
            });
        in_slots.or_else(|| {
            self.retired
                .iter()
                .find(|r| serves(&r.readers, reader))
                .map(|r| SlotRelease {
                    guard: &r.guard,
                    own: &r.own,
                    position: &r.position,
                })
        })
    }

    /// Drop every name whose version is no longer held, from every slot and every retired slot.
    fn drop_dead_names(&mut self) {
        for names in self
            .readers
            .iter_mut()
            .chain(self.retired.iter_mut().map(|r| &mut r.readers))
        {
            drop_dead_names(names);
        }
    }

    /// The slots whose subscriber still exists, in subscription order.
    fn live_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.subscribers
            .iter()
            .enumerate()
            .filter(|(_, s)| s.strong_count() > 0)
            .map(|(i, _)| i)
    }

    /// The slots whose guards constrain what the input may reclaim: every live slot, and while a
    /// handover is open every dead slot that served a reader. A slot under an operator the new
    /// version declined dies when the offer is released
    /// ([`OpConversionContext::release_offer`]), and a replacement for its reader may subscribe
    /// after that.
    ///
    /// [`OpConversionContext::release_offer`]: crate::interpreter::operator_conversion::OpConversionContext::release_offer
    fn counted_indices(&self) -> impl Iterator<Item = usize> + '_ {
        self.subscribers
            .iter()
            .enumerate()
            .filter(|&(i, s)| {
                s.strong_count() > 0 || (self.handing_over && !self.readers[i].is_empty())
            })
            .map(|(i, _)| i)
    }

    /// Drop every slot whose subscriber is gone, renumbering the survivors.
    ///
    /// Each surviving producer learns its new index through the `Cell` it shares
    /// with its entry in [`subscribers`](Self::subscribers), so the per-slot
    /// vectors stay bounded by the number of live subscriptions rather than by
    /// the number ever made.
    ///
    /// Safe only when no producer is mid-pull, since a renumber between a
    /// producer reading its index and using it would address another
    /// subscriber's guard. [`FanOut::reopen`] and [`FanOut::settle_handover`] are the
    /// callers, and they run at a version handover with the graph already torn down.
    ///
    /// It also drops the reader names of every version no operator map holds any more.
    fn compact(&mut self) {
        self.drop_dead_names();
        // Upgrade once: `keep` and the renumbering must agree on which slots are
        // live, and reading liveness twice would let them disagree.
        let live: Vec<_> = self.subscribers.iter().map(Weak::upgrade).collect();
        if live.iter().all(Option::is_some) {
            return;
        }
        for (next, cell) in live.iter().flatten().enumerate() {
            cell.store(next, std::sync::atomic::Ordering::Relaxed);
        }
        let keep: Vec<bool> = live.iter().map(Option::is_some).collect();
        // A dead slot that served a reader is what that reader's replacement starts at.
        for (at, kept) in keep.iter().enumerate() {
            if !kept && !self.readers[at].is_empty() {
                // A slot that died before the handover stopped counting toward the
                // intersection, which may have moved past it since, and those rows are gone.
                self.retired.push(RetiredSlot {
                    readers: std::mem::take(&mut self.readers[at]),
                    guard: self.release_guards[at].union(&self.released),
                    own: self.own[at].clone(),
                    position: self.positions[at].clone(),
                });
            }
        }
        retain_flagged(&mut self.subscribers, &keep);
        retain_flagged(&mut self.consumers, &keep);
        retain_flagged(&mut self.release_guards, &keep);
        retain_flagged(&mut self.own, &keep);
        retain_flagged(&mut self.unannounced, &keep);
        retain_flagged(&mut self.recurrence, &keep);
        retain_flagged(&mut self.readers, &keep);
        retain_flagged(&mut self.positions, &keep);
        retain_flagged(&mut self.current_values, &keep);
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
        debug_assert_eq!(
            self.own.len(),
            self.subscribers.len(),
            "own release records stay parallel to subscribers"
        );
        debug_assert_eq!(
            self.unannounced.len(),
            self.subscribers.len(),
            "unannounced keys stay parallel to subscribers"
        );
    }
}

fn try_unpoison<T>(result: std::sync::TryLockResult<T>) -> Result<T, ()> {
    match result {
        Ok(guard) => Ok(guard),
        Err(std::sync::TryLockError::Poisoned(error)) => Ok(error.into_inner()),
        Err(std::sync::TryLockError::WouldBlock) => Err(()),
    }
}

/// A fan-out's input producer, as [`FanOutShared::producer`] holds it.
enum Inner {
    /// An ordinary fan-out's input, which a slot pulls under the fan-out's shared state.
    Owned(Box<dyn TileProducer>),
    /// A cyclic fan-out's input, a store, in a cell of its own. A slot pulls it under that
    /// cell's read alone, with the fan-out's shared state free, so a pull that re-enters
    /// through the store's recurrence finds the cell borrowed and is answered from the snapshot,
    /// and the store can publish its snapshot through the shared state while it steps itself
    /// ([`Cycle`]).
    // shared-state-ok: a cyclic fan-out's input producer, held apart from the fan-out's state
    // so the two read separately; what crosses it is the producer, never a tile passed
    // between operators.
    Store(StoreCell),
}

/// The cell a cyclic fan-out holds its store in ([`Inner::Store`]), which a planner reaches.
// shared-state-ok: the name of the cell `Inner::Store` holds, which a planner reaches to drive
// the store as a pipeline breaker; what crosses it is the producer, never a tile.
pub(crate) type StoreCell = Arc<Store>;

/// A cyclic store and releases waiting for its current mutable operation to end.
pub(crate) struct Store {
    // shared-state-ok: the store producer owned by its cyclic fan-out, never a tile channel.
    producer: RwLock<Box<dyn TileProducer>>,
    // shared-state-ok: the accumulated release region, never tiles.
    pending_release: RwLock<Option<TileGuard>>,
}

impl Store {
    fn new(producer: Box<dyn TileProducer>) -> Self {
        Self {
            producer: RwLock::new(producer),
            pending_release: RwLock::new(None),
        }
    }

    pub(crate) fn read(&self) -> StoreRef<'_> {
        self.try_read()
            .expect("a store is not mutably borrowed while read")
    }

    pub(crate) fn try_read(&self) -> Result<StoreRef<'_>, ()> {
        Ok(StoreRef {
            producer: Some(try_unpoison(self.producer.try_read())?),
            store: self,
        })
    }

    pub(crate) fn write(&self) -> StoreBorrow<'_> {
        StoreBorrow {
            producer: Some(
                self.producer
                    .write()
                    .unwrap_or_else(PoisonError::into_inner),
            ),
            pending_release: &self.pending_release,
        }
    }

    pub(crate) fn try_write(&self) -> Result<StoreBorrow<'_>, ()> {
        Ok(StoreBorrow {
            producer: Some(try_unpoison(self.producer.try_write())?),
            pending_release: &self.pending_release,
        })
    }

    fn release(&self, guard: TileGuard) {
        let mut pending = self
            .pending_release
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        *pending = Some(match pending.take() {
            Some(before) => before.union(&guard),
            None => guard,
        });
        drop(pending);
        // An available store settles now; a borrowed store settles when its operation ends.
        drop(self.try_write());
    }
}

/// A read of the store: the releases deferred while it was read settle once the last read ends.
pub(crate) struct StoreRef<'a> {
    producer: Option<std::sync::RwLockReadGuard<'a, Box<dyn TileProducer>>>,
    store: &'a Store,
}

impl std::ops::Deref for StoreRef<'_> {
    type Target = Box<dyn TileProducer>;
    fn deref(&self) -> &Self::Target {
        self.producer.as_deref().expect("the store is borrowed")
    }
}

impl Drop for StoreRef<'_> {
    fn drop(&mut self) {
        drop(self.producer.take());
        if !std::thread::panicking() {
            drop(self.store.try_write());
        }
    }
}

/// A mutable store operation: the releases deferred while it ran settle when it ends.
pub(crate) struct StoreBorrow<'a> {
    producer: Option<std::sync::RwLockWriteGuard<'a, Box<dyn TileProducer>>>,
    pending_release: &'a RwLock<Option<TileGuard>>,
}

impl std::ops::Deref for StoreBorrow<'_> {
    type Target = dyn TileProducer;
    fn deref(&self) -> &Self::Target {
        self.producer
            .as_deref()
            .expect("the store is borrowed")
            .as_ref()
    }
}

impl std::ops::DerefMut for StoreBorrow<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.producer
            .as_deref_mut()
            .expect("the store is borrowed")
            .as_mut()
    }
}

impl Drop for StoreBorrow<'_> {
    fn drop(&mut self) {
        if self.producer.is_none() {
            return;
        }
        // A failed operation leaves the pending release for a subsequent successful read.
        if std::thread::panicking() {
            return;
        }
        loop {
            let mut pending = self
                .pending_release
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            let Some(guard) = pending.take() else {
                // Hand off atomically: a new release either joins this drain or
                // observes an unlocked producer and starts its own drain.
                drop(self.producer.take());
                return;
            };
            drop(pending);
            self.producer.as_deref_mut().unwrap().release(guard);
        }
    }
}

/// A cyclic fan-out as a reader slot of it names it to a planner (`TileProducer::store_read`).
pub struct StoreRead {
    /// The fan-out's id, which every slot's producer names.
    pub(crate) fan: usize,
    /// The store, the fan-out's input.
    pub(crate) store: StoreCell,
}

/// A store's handle on the cyclic fan-out whose input it is ([`TileProducer::enter_cycle`]).
/// It does what a pull of the fan-out does around the store's own step: it publishes the snapshot
/// a re-entrant pull is answered from, and it names the fan-out its recurrence slots read, so the
/// store can have the operators inside its cycle read again before a step.
#[derive(Clone)]
pub struct Cycle {
    shared: Weak<RwLock<FanOutShared>>,
    domain: Option<Extent>,
}

impl Cycle {
    /// The consumers of the fan-out's live reader slots, which the store's pushes reach.
    pub(crate) fn readers(&self) -> Vec<SharedConsumer> {
        reader_consumers(&self.shared)
    }

    /// The id of the fan-out, which its recurrence slots answer ([`TileProducer::recurrence_of`]).
    pub(crate) fn fan(&self) -> usize {
        self.shared
            .upgrade()
            .expect(DEAD_RECURRENCE)
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .id
    }

    /// Make `tile` the snapshot a re-entrant pull of the fan-out is answered from, as a
    /// completed pull of the store does.
    pub(crate) fn publish(&self, tile: &Tile) {
        let shared = self.shared.upgrade().expect(DEAD_RECURRENCE);
        {
            let mut state = shared.write().unwrap_or_else(PoisonError::into_inner);
            state
                .reentrancy
                .as_mut()
                .expect("a store's fan-out is cyclic")
                .cached_tile = tile.clone();
            if state.live_indices().any(|i| state.current_values[i])
                && let Some(frontier) = crate::interpreter::commit_operator::store_frontier(tile)
            {
                let prefix = crate::interpreter::tiling::domain_prefix_over(
                    vec![frontier.into_value()],
                    std::slice::from_ref(self.domain.as_ref().expect("a flat store has a domain")),
                );
                let current: Vec<usize> = state
                    .live_indices()
                    .filter(|&i| state.current_values[i])
                    .collect();
                for i in current {
                    state.release_guards[i] = state.release_guards[i].union(&prefix);
                }
            }
        }
        release_shared(&shared);
    }
}

/// Keep the elements of `v` whose flag in `keep` is set, in order.
fn retain_flagged<T>(v: &mut Vec<T>, keep: &[bool]) {
    debug_assert_eq!(v.len(), keep.len(), "one flag per element");
    let mut flags = keep.iter();
    v.retain(|_| *flags.next().unwrap_or(&false));
}

/// The consumer a fan-out installs on its input: it forwards each region to every live slot.
struct FanOutInput {
    shared: Weak<RwLock<FanOutShared>>,
}

impl Consumer for FanOutInput {
    /// A delivered region reaches every live reader slot's consumer.
    /// It skips a recurrence slot: the operators inside a store's cycle read the store in pull
    /// mode, within its own pipeline.
    fn notify(
        &self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        for c in &reader_consumers(&self.shared) {
            crate::interpreter::notifications::notify_shared(c, region, landing);
        }
    }
}

/// The consumers of the live reader slots, which a push reaches, and none of a recurrence slot. A
/// clone of each handle, so no read of the fan-out is held while a push climbs past.
fn reader_consumers(fan: &Weak<RwLock<FanOutShared>>) -> Vec<SharedConsumer> {
    let Some(shared_rc) = fan.upgrade() else {
        return Vec::new();
    };
    let shared = shared_rc.read().unwrap_or_else(PoisonError::into_inner);
    shared
        .live_indices()
        .filter(|&i| !shared.recurrence[i])
        .map(|i| shared.consumers[i].clone())
        .collect()
}

/// RAII guard for the cyclic `FanOut` `subscribing_inner` flag.  Created
/// when we set the flag `true` to drive the inner `subscribe`; its `Drop`
/// resets the flag to `false`.  This makes the path panic-safe — if
/// the inner `subscribe` unwinds, the flag is still reset so a later
/// (re-)subscribe attempt doesn't get silently skipped.
struct SubscribingInnerGuard<'a> {
    shared: &'a Arc<RwLock<FanOutShared>>,
}

impl<'a> Drop for SubscribingInnerGuard<'a> {
    fn drop(&mut self) {
        if let Some(re) = self
            .shared
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .reentrancy
            .as_mut()
        {
            re.subscribing_inner = false;
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
    input: Arc<dyn TileOperator>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that slots produced by
    /// [`FanOut::slot`] always share the same object.
    shared: Arc<RwLock<FanOutShared>>,
    /// Whether any slots have been created yet.
    // shared-state-ok: construction-time bookkeeping of the `FanOut` itself, not a
    // channel between operators — it records that `slot` has been called, and no
    // value ever passes through it.
    used: RwLock<bool>,
}

impl FanOut {
    /// Construct a new `FanOut` wrapping `input`.  Use this for ordinary
    /// (non-cyclic) op graphs; the resulting fan-out doesn't pay any
    /// cyclic-mode overhead.  If a slot of this fan-out ends up
    /// feeding back into its own input (e.g. a store recurrence closing
    /// through the fan-out), use [`FanOut::new_cyclic`] instead.
    pub fn new(input: Arc<dyn TileOperator>) -> Self {
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
    pub fn new_cyclic(input: Arc<dyn TileOperator>) -> Self {
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
        input: Arc<dyn TileOperator>,
        reentrancy: Option<FanOutReentrancy>,
    ) -> Self {
        let tiling = input.tiling().clone();
        let shared = Arc::new(RwLock::new(FanOutShared {
            id: FanOutProducer::alloc_id(),
            producer: None,
            consumers: Vec::new(),
            release_guards: Vec::new(),
            own: Vec::new(),
            unannounced: Vec::new(),
            recurrence: Vec::new(),
            current_values: Vec::new(),
            released: tiling.empty_guard(),
            readers: Vec::new(),
            positions: Vec::new(),
            retired: Vec::new(),
            handing_over: false,
            subscribers: Vec::new(),
            reentrancy,

            source_producers: Vec::new(),
        }));
        Self {
            input,
            tiling,
            shared,
            used: RwLock::new(false),
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
    pub fn slot(&self) -> Arc<dyn TileOperator> {
        self.slot_holding(
            FanHold::Reader {
                shared: self.shared.clone(), // shares the Arc — always connected
                input: self.input.clone(),
            },
            false,
            None,
        )
    }

    /// A slot for the reader `reader`, which starts at the release of `predecessor`'s slot,
    /// the slot of the reader it replaces in the version before, where this fan-out holds one
    /// ([`FanOutSlot::subscribe`]).
    ///
    /// For a reader of a fan-out a reload can keep: a binding, a store or an iteration input
    /// ([`OperatorMap`](crate::interpreter::operator_conversion::OperatorMap)).
    pub fn slot_read_by(
        &self,
        reader: SlotReader,
        predecessor: Option<SlotReader>,
        version: &Version,
    ) -> Arc<dyn TileOperator> {
        self.slot_holding(
            FanHold::Reader {
                shared: self.shared.clone(),
                input: self.input.clone(),
            },
            false,
            Some((Named::new(reader, version), predecessor)),
        )
    }

    /// A slot for an operator that this fan-out's own input chain contains.
    ///
    /// A store's driver and its writer read the store they are part of, to
    /// recover each position's prior value. Such a reader must not own the
    /// fan-out — see [`FanHold`].
    pub fn recurrence_slot(&self) -> Arc<dyn TileOperator> {
        self.slot_holding(
            FanHold::Recurrence {
                shared: Arc::downgrade(&self.shared),
                input: Arc::downgrade(&self.input),
            },
            false,
            None,
        )
    }

    /// A flat store read that retains each key's current value without retaining its history.
    pub(crate) fn current_slot(&self) -> Arc<dyn TileOperator> {
        assert!(
            matches!(self.tiling, Tiling::Store { .. }),
            "current-value retention reads a flat store"
        );
        self.slot_holding(
            FanHold::Reader {
                shared: self.shared.clone(),
                input: self.input.clone(),
            },
            true,
            None,
        )
    }

    fn slot_holding(
        &self,
        hold: FanHold,
        current_values: bool,
        reader: Option<(Named, Option<SlotReader>)>,
    ) -> Arc<dyn TileOperator> {
        let result = FanOutSlot {
            hold,
            current_values,
            base: OperatorBase::new(self.tiling.clone()),
            primary: !std::mem::replace(
                &mut *self.used.write().unwrap_or_else(PoisonError::into_inner),
                true,
            ),
            reader,
        };
        Arc::new(result)
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
        f(&*self.input)
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
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .reentrancy
            .as_ref()
            .map(|r| r.cached_tile.clone())
    }

    /// The id every slot's producer of this fan-out names.
    #[cfg(test)]
    pub(crate) fn id(&self) -> usize {
        self.shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .id
    }

    /// A cyclic fan-out's store, which a test drives as a pipeline breaker. `None` for an
    /// ordinary fan-out, and before the store is subscribed.
    #[cfg(test)]
    pub(crate) fn store(&self) -> Option<StoreCell> {
        match &self
            .shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .producer
        {
            Some(Inner::Store(cell)) => Some(cell.clone()),
            _ => None,
        }
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
    /// [`released_position_of`](Self::released_position_of) reports as well from a
    /// spent operator as from a live one, and a spent one is what a finished
    /// iteration looks like. The handover carries such an operator either way: a
    /// store that can no longer produce still holds the value its variables hand
    /// on.
    pub fn released_in_full(&self) -> bool {
        self.shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .released
            .is_universal()
    }

    /// The last position the slot that served `reader` released as a prefix, for an output
    /// that is a function of an ordered domain.
    ///
    /// What a version keeping this fan-out has to know to place a recurrence over it where
    /// `reader` is the recurrence's predecessor: a drive told to start anywhere else either
    /// decides a position a second time or waits for one that has gone.
    ///
    /// `None` when that slot released no prefix, when no slot served `reader`, and when the
    /// output is not position-domained, which are one answer to the caller: there is no
    /// position to start above. A drive that finished the iteration is not one of those cases:
    /// the position it got to is kept past the universal release that closed it
    /// ([`FanOutShared::positions`]).
    pub fn released_position_of(&self, reader: SlotReader) -> Option<Position> {
        let shared = self.shared.read().unwrap_or_else(PoisonError::into_inner);
        shared.release_of(reader).and_then(|r| r.position.clone())
    }

    /// The most names one slot of this fan-out answers to, over its live, dead and retired
    /// slots.
    #[cfg(test)]
    pub(crate) fn most_names_of_a_slot(&self) -> usize {
        let shared = self.shared.read().unwrap_or_else(PoisonError::into_inner);
        shared
            .readers
            .iter()
            .chain(shared.retired.iter().map(|r| &r.readers))
            .map(Vec::len)
            .max()
            .unwrap_or(0)
    }

    /// What the slot that served `reader` released, live, dead or retired; `None` where no
    /// slot served it.
    pub fn released_by(&self, reader: SlotReader) -> Option<TileGuard> {
        let shared = self.shared.read().unwrap_or_else(PoisonError::into_inner);
        shared.release_of(reader).map(|r| r.guard.clone())
    }

    /// Record that the readers this fan-out's slots served under the nodes `renamed` maps from
    /// are also the readers at the nodes it maps to: a version that keeps a reader, inside a
    /// kept region, keeps its slot, and the version after it names that reader by the kept
    /// version's nodes ([`OpConversionContext::keep_region`]). `version` is the version that names
    /// them so. The slot answers to the names of every version still held, since
    /// branch-and-reload keeps a reader for a second branch that names it by its own nodes, and
    /// drops the names of every version no longer held.
    ///
    /// [`OpConversionContext::keep_region`]: crate::interpreter::operator_conversion::OpConversionContext
    pub fn alias_readers(&self, renamed: &HashMap<NodeId, NodeId>, version: &Version) {
        let mut shared = self.shared.write().unwrap_or_else(PoisonError::into_inner);
        let shared = &mut *shared;
        shared.drop_dead_names();
        let lists = shared
            .readers
            .iter_mut()
            .chain(shared.retired.iter_mut().map(|r| &mut r.readers));
        for readers in lists {
            let aliases: Vec<Named> = readers
                .iter()
                .filter_map(|named| renamed.get(&named.reader.node))
                .map(|&node| SlotReader { node })
                .filter(|&alias| !serves(readers, alias))
                .map(|alias| Named::new(alias, version))
                .collect();
            readers.extend(aliases);
        }
    }

    /// End a version handover: the slots it found dead, and the ones that died while it was open,
    /// stop holding the reclamation intersection back and are dropped, now that every replacement
    /// has subscribed and started at its predecessor's release.
    pub fn settle_handover(&self) {
        let mut shared = self.shared.write().unwrap_or_else(PoisonError::into_inner);
        shared.compact();
        shared.retired.clear();
        shared.handing_over = false;
    }

    /// The name of every producer registered with a data source from inside
    /// this fan-out's input chain, nested fan-outs included, when the chain was
    /// subscribed. Empty before the first subscription.
    pub fn source_producers(&self) -> Vec<String> {
        self.shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .source_producers
            .clone()
    }

    /// Reopen this fan-out for a fresh set of slots, keeping the inner
    /// producer and everything it has accumulated.
    ///
    /// For carrying one operator across a program reload. The
    /// [`inspect`](TileOperator::inspect) bookkeeping resets: which slot renders the input subtree
    /// and which renders a back-reference. The dead slots retire, and the handover stays open until
    /// [`settle_handover`](Self::settle_handover): until then every slot that served a reader holds
    /// the reclamation intersection back, dead or alive, so a replacement starts at a guard nothing
    /// has reclaimed past. A subscriber the reload carried forward keeps its guard.
    pub fn reopen(&self) {
        *self.used.write().unwrap_or_else(PoisonError::into_inner) = false;
        let mut shared = self.shared.write().unwrap_or_else(PoisonError::into_inner);
        shared.compact();
        shared.handing_over = true;
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
/// Reading through a `Weak` is sound in that position because the read happens only while the
/// fan-out's store is pulled or steps itself ([`Cycle`]), by a caller holding the fan-out, so the
/// fan-out is alive for the whole of it.
#[derive(Clone)]
enum FanHold {
    /// A downstream reader's handle, which owns the fan-out.
    Reader {
        shared: Arc<RwLock<FanOutShared>>,
        // shared-state-ok: the fan-out's own input operator, the same handle as
        // [`FanOut::input`] — a slot is a view of one fan-out, not a second
        // one. It holds an *operator*, not values passed between operators.
        input: Arc<dyn TileOperator>,
    },
    /// A recurrence's handle on a fan-out whose input chain contains it.
    Recurrence {
        shared: Weak<RwLock<FanOutShared>>,
        input: Weak<dyn TileOperator>,
    },
}

/// Why a recurrence's `Weak` is always upgradable where it is read.
const DEAD_RECURRENCE: &str = "a recurrence reads the fan-out whose input chain it sits in, and \
     that read happens only while the fan-out's store is pulled or steps itself";

impl FanHold {
    fn shared(&self) -> Arc<RwLock<FanOutShared>> {
        match self {
            FanHold::Reader { shared, .. } => shared.clone(),
            FanHold::Recurrence { shared, .. } => shared.upgrade().expect(DEAD_RECURRENCE),
        }
    }

    /// Read the fan-out's input operator. The cell never leaves `FanHold`, so
    /// the one place an operator handle is shared is the `Reader` field.
    fn with_input<R>(&self, f: impl FnOnce(&dyn TileOperator) -> R) -> R {
        match self {
            FanHold::Reader { input, .. } => f(&**input),
            FanHold::Recurrence { input, .. } => f(&*input.upgrade().expect(DEAD_RECURRENCE)),
        }
    }

    /// Subscribe to the fan-out's input operator, the one use that needs it
    /// mutably.
    fn subscribe_input(
        &self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        match self {
            FanHold::Reader { input, .. } => input.clone().subscribe(intent_guard, consumer, cx),
            FanHold::Recurrence { input, .. } => input
                .upgrade()
                .expect(DEAD_RECURRENCE)
                .clone()
                .subscribe(intent_guard, consumer, cx),
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
    /// The reader this slot serves, named by the version that minted it, and the one it
    /// replaces ([`FanOut::slot_read_by`]).
    reader: Option<(Named, Option<SlotReader>)>,
    current_values: bool,
}

impl FanOutSlot {
    fn shared(&self) -> Arc<RwLock<FanOutShared>> {
        self.hold.shared()
    }
}

impl TileOperator for FanOutSlot {
    impl_operator_base!();

    /// A slot's record fields equal what its shared input's do.
    fn field_correlation(&self, field: &str) -> Option<Vec<TilePathStep>> {
        self.hold.with_input(|op| op.field_correlation(field))
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        self.hold.with_input(|op| visit(share(op)));
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = self
            .shared()
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .id;
        if self.primary {
            InspectNode::new(format!("FanOut#{id}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.hold.with_input(|op| op.inspect(opts)))
        } else {
            InspectNode::leaf(format!("→ FanOut#{id}"))
        }
    }

    fn subscribe(
        self: Arc<Self>,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let shared_rc = self.shared();
        // Register the consumer and reserve its release-guard slot. The slot
        // number lives in the cell the producer holds, so `compact` can renumber.
        let slot = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let (seed, inherited) = {
            let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
            slot.store(shared.consumers.len(), std::sync::atomic::Ordering::Relaxed);
            let (reader, predecessor) = self.reader.clone().unzip();
            // A reader that replaces one starts where that one released, and every other
            // starts at what the fan-out has reclaimed.
            let release = predecessor.flatten().and_then(|p| shared.release_of(p));
            // The announcement names only the keys of the predecessor's own record. A slot that
            // died before the handover starts past rows the fan-out reclaimed since, and its
            // reader never received them, so announcing them would hide their loss.
            let unannounced = release
                .as_ref()
                .and_then(|release| Unannounced::new(release.own, self.tiling()));
            let own = release.as_ref().map_or_else(
                || self.tiling().empty_guard(),
                |release| release.own.clone(),
            );
            debug_assert!(
                unannounced.as_ref().is_none_or(|pending| {
                    own.subsumes(&pending.region.guard(self.tiling()))
                        && release.as_ref().is_some_and(|release| {
                            release.guard.subsumes(&pending.region.guard(self.tiling()))
                        })
                }),
                "a slot announces only keys its predecessor's own record names, and answers them \
                 with no rows, so its release covers them: {:?} vs own {own:?}",
                unannounced.as_ref().map(|pending| &pending.region),
            );
            let carried = release.map(|release| (release.guard.clone(), release.position.clone()));
            let inherited = carried.as_ref().map(|(guard, _)| guard.clone());
            let consumer: Box<dyn Consumer> = if unannounced.is_some() {
                Box::new(AnnounceInherited {
                    consumer,
                    shared: Arc::downgrade(&shared_rc),
                    slot: Arc::downgrade(&slot),
                })
            } else {
                consumer
            };
            shared.consumers.push(Arc::from(consumer));
            shared.unannounced.push(unannounced);
            let (seed, position) = match carried {
                Some((guard, at)) => {
                    // The intersection ran over the predecessor's slot, so what it reclaimed
                    // the predecessor had released. Otherwise the replacement would ask for
                    // rows that are gone.
                    debug_assert!(
                        guard.subsumes(&shared.released),
                        "a replaced reader's release covers what the fan-out reclaimed: \
                         {guard:?} vs {:?}",
                        shared.released
                    );
                    (guard, at)
                }
                None => (shared.released.clone(), None),
            };
            debug_assert!(
                reader.as_ref().is_none_or(|named| shared
                    .live_indices()
                    .all(|i| !serves(&shared.readers[i], named.reader))),
                "one live slot of a fan-out serves each reader: {:?}",
                reader.as_ref().map(|named| named.reader)
            );
            shared.release_guards.push(seed.clone());
            shared.own.push(own);
            shared.readers.push(reader.into_iter().collect());
            shared.positions.push(position);
            shared.current_values.push(self.current_values);
            shared
                .recurrence
                .push(matches!(self.hold, FanHold::Recurrence { .. }));
            shared.subscribers.push(Arc::downgrade(&slot));
            (seed, inherited)
        }; // the lock is released here before we might call input.subscribe

        // Decide whether *this* call should drive the inner subscribe.
        // `producer.is_none()` is the standard "first subscription" check;
        // in cyclic mode, `!reentrancy.subscribing_inner` makes the path
        // re-entrancy-safe: a sibling-slot subscribe triggered from
        // inside the inner subscribe call sees the flag set and just
        // returns a producer (the outer call will populate `producer`
        // before anyone pulls).
        let should_subscribe = {
            let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
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
        // We must not hold a read of `shared` during `input.subscribe`
        // because that call may synchronously fire the notification closure,
        // which itself borrows `shared`.
        if should_subscribe {
            // RAII: any path out of this block (success or panic) resets
            // `subscribing_inner` to `false`.  Without the guard, a panic
            // from the inner `subscribe` would leave the flag set
            // forever and silently skip every future subscribe attempt
            // on this fan-out.
            let _guard = SubscribingInnerGuard { shared: &shared_rc };
            let shared_weak = Arc::downgrade(&shared_rc);
            cx.begin_source_producers();
            let inner = self.hold.subscribe_input(
                intent_guard,
                Box::new(FanOutInput {
                    shared: shared_weak,
                }),
                cx,
            );
            let producers = cx.end_source_producers();
            let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
            let (held, cell) = match shared.reentrancy.is_some() {
                true => {
                    let cell = Arc::new(Store::new(inner));
                    (Inner::Store(cell.clone()), Some(cell))
                }
                false => (Inner::Owned(inner), None),
            };
            shared.producer = Some(held);
            shared.source_producers = producers;
            drop(shared);
            if let Some(cell) = cell {
                cell.write().enter_cycle(Cycle {
                    shared: Arc::downgrade(&shared_rc),
                    domain: match self.tiling() {
                        Tiling::Store { domain, .. } => Some(domain.clone()),
                        _ => None,
                    },
                });
            }
            // `_guard` drops here, resetting `subscribing_inner`.
        }

        // The fan-out's own id rather than a fresh one, so every slot's
        // producer reads as the same `FanOut#n`. `ProbeTable` keys on
        // `(node_id, producer_id)`, and that stays unique here because each
        // slot is its own operator with its own `NodeId` — the first
        // component separates them, not the second. Subscribing one slot
        // twice would land both producers in one slot; nothing does, and
        // `FanOut::slot` mints a fresh slot per call.
        let mut base = ProducerBase::new(
            shared_rc.read().unwrap_or_else(PoisonError::into_inner).id,
            self.tiling(),
            self.clone(),
            cx,
        );
        base.obsolete_guard = RwLock::new(seed);
        Box::new(FanOutProducer {
            base,
            // The producer a subscription hands out holds the fan-out the same
            // way this slot does: a recurrence's producer must not own it
            // either.
            hold: self.hold.clone(),
            slot,
            inherited,
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
    slot: Arc<std::sync::atomic::AtomicUsize>,
    /// The release this subscription started at because its slot replaces a reader across a
    /// reload: that reader's release, read off its slot. `None` for a slot that replaces no
    /// reader of this fan-out, which starts at [`FanOutShared::released`] instead.
    inherited: Option<TileGuard>,
}

impl FanOutProducer {
    /// This producer's current slot number.
    fn index(&self) -> usize {
        self.slot.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn shared(&self) -> Arc<RwLock<FanOutShared>> {
        self.hold.shared()
    }
}

impl TileProducer for FanOutProducer {
    impl_producer_base!();

    /// Release as every producer does, then record the argument as the reader gave it in the
    /// slot's [`own`](FanOutShared::own) record and its
    /// [announcement](FanOutShared::unannounced). The slot's obsolete guard starts at the
    /// inherited release, so a release that completes it reaches
    /// [`release_impl`](TileProducer::release_impl) as the universal guard. The records take the
    /// argument instead, because the reader released that region and no more.
    fn release(&self, obsolete_guard: TileGuard) {
        accumulate_release(self, obsolete_guard.clone());
        let shared_rc = self.shared();
        let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
        let index = self.index();
        let tiling = self.tiling();
        shared.own[index] = shared.own[index].union(&obsolete_guard).closed_over(tiling);
        if let Some(pending) = shared.unannounced[index].take() {
            shared.unannounced[index] = pending.after(&obsolete_guard, tiling);
        }
    }

    fn inherited_release(&self) -> Option<&TileGuard> {
        self.inherited.as_ref()
    }

    /// The fan-out's input, which every slot pulls through the shared state. Nothing is
    /// visited while a pull holds that state, or after a recurrence's fan-out has gone.
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        let shared = match &self.hold {
            FanHold::Reader { shared, .. } => Some(shared.clone()),
            FanHold::Recurrence { shared, .. } => shared.upgrade(),
        };
        let Some(shared) = shared else {
            return;
        };
        let Ok(shared) = try_unpoison(shared.try_read()) else {
            return;
        };
        match &shared.producer {
            Some(Inner::Owned(input)) => visit("input", &**input),
            Some(Inner::Store(cell)) => {
                if let Ok(input) = cell.try_read() {
                    visit("input", &**input);
                }
            }
            None => {}
        }
    }

    /// A reader slot visits its fan-out's input. A recurrence slot visits nothing: it sits in a
    /// store's cycle, and the walk reaches the store through a reader slot
    /// (`TileProducer::store_read`).
    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        let FanHold::Reader { shared, .. } = &self.hold else {
            return;
        };
        let cell = match &mut shared
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .producer
        {
            Some(Inner::Owned(input)) => {
                visit("input", &mut **input);
                return;
            }
            Some(Inner::Store(cell)) => cell.clone(),
            None => return,
        };
        if let Ok(mut input) = cell.try_write() {
            visit("input", &mut *input);
        }
    }

    fn store_read(&self) -> Option<StoreRead> {
        let FanHold::Reader { shared, .. } = &self.hold else {
            return None;
        };
        let shared = shared.read().unwrap_or_else(PoisonError::into_inner);
        shared.reentrancy.as_ref()?;
        let Some(Inner::Store(store)) = &shared.producer else {
            return None;
        };
        Some(StoreRead {
            fan: shared.id,
            store: store.clone(),
        })
    }

    fn recurrence_of(&self) -> Option<usize> {
        match &self.hold {
            FanHold::Recurrence { shared, .. } => shared
                .upgrade()
                .map(|shared| shared.read().unwrap_or_else(PoisonError::into_inner).id),
            FanHold::Reader { .. } => None,
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
        let shared = shared.read().unwrap_or_else(PoisonError::into_inner);
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
            let shared = self.shared();
            let shared = shared.read().unwrap_or_else(PoisonError::into_inner);
            let input = match shared
                .producer
                .as_ref()
                .expect("an inspected slot is subscribed")
            {
                Inner::Owned(input) => input.inspect(opts),
                // A store stepping itself has its cell borrowed, and is drawn as a leaf then.
                Inner::Store(cell) => match cell.try_read() {
                    Ok(store) => store.inspect(opts),
                    Err(_) => InspectNode::leaf("store, stepping".to_string()),
                },
            };
            node.child("input", input)
        } else {
            InspectNode::leaf(format!("→ {}", self.name()))
        }
    }

    fn restates(&self) -> Restates {
        Restates::Every
    }

    /// A current-value slot's release guard, which [`Cycle::publish`] widens through the store's
    /// frontier with no call of [`release`](TileProducer::release), and which
    /// [`get_impl`](Self::get_impl) removes from every answer. Any other slot's release guard is
    /// its obsolete guard.
    fn withheld_guard(&self) -> TileGuard {
        let obsolete = self.obsolete_guard();
        let shared = self.shared();
        let shared = shared.read().unwrap_or_else(PoisonError::into_inner);
        let index = self.index();
        match shared.current_values[index] {
            true => obsolete.union(&shared.release_guards[index]),
            false => obsolete,
        }
    }

    /// A cyclic fan-out reads its input whole ([`get_impl`](Self::get_impl)); any other pulls
    /// it at the level it is pulled at.
    fn input_level(&self, _role: &str, level: CurryLevel) -> Option<CurryLevel> {
        let shared = self.shared();
        let shared = shared.read().unwrap_or_else(PoisonError::into_inner);
        match &shared.reentrancy {
            Some(_) => None,
            None => Some(level),
        }
    }

    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        let shared_rc = self.shared();
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let cyclic = shared_rc
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .reentrancy
            .is_some();
        // A sibling that re-enters mid-pull is answered from the cache of the last completed
        // pull, which has to cover whatever region that sibling asks for: a cyclic fan-out reads
        // its input whole.
        let projection_guard = match cyclic {
            true => self.tiling().universal_guard(),
            false => projection.guard(self.tiling()),
        };
        // A cyclic fan-out's store is pulled under its own cell's write, with the shared state
        // free. A pull that finds the cell held is served the latest snapshot and never waits.
        // The holder is one of three: this thread's own pull, re-entered through the store's
        // recurrence; the store stepping itself as a pipeline breaker; or a pull of a sibling
        // slot on another thread. Waiting deadlocks in the first two, and the pull cannot tell
        // the third from them.
        let store = match &shared_rc
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .producer
        {
            Some(Inner::Store(cell)) => Some(cell.clone()),
            _ => None,
        };
        let mut result = match store {
            Some(cell) => match cell.try_write() {
                Ok(producer) => {
                    let tile = producer.get(projection_guard);
                    trace!("{} received {tile:?}", self.name());
                    // Replace, not merge: inner producers like `Memo` already return cumulative
                    // tiles, so each pull supplants the previous snapshot.
                    shared_rc
                        .write()
                        .unwrap_or_else(PoisonError::into_inner)
                        .reentrancy
                        .as_mut()
                        .expect("a fan-out holding a store is cyclic")
                        .cached_tile = tile.clone();
                    tile
                }
                Err(_) => {
                    let cached = shared_rc
                        .read()
                        .unwrap_or_else(PoisonError::into_inner)
                        .reentrancy
                        .as_ref()
                        .expect("a fan-out holding a store is cyclic")
                        .cached_tile
                        .clone();
                    trace!("{} serving cached (re-entrant): {cached:?}", self.name());
                    cached
                }
            },
            None => match shared_rc
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .producer
                .as_ref()
                .expect("a pulled slot is subscribed")
            {
                Inner::Owned(producer) => producer.get(projection_guard),
                Inner::Store(_) => unreachable!("matched above"),
            },
        };

        // Filter by the stored obsolete guard. Because upstream retains data according to the
        // intersection of all obsolete guards, it may have more data than this specific consumer
        // is interested in.
        let guard = shared_rc
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .release_guards[self.index()]
        .clone();
        trace!("{} removing {guard:?} from {result:?}", self.name());
        result.remove_guarded(guard);
        result.restrict_to(&projection, self.tiling());
        result
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let shared_rc = self.shared();
        let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
        let index = self.index();
        // Union with the existing stored guard so that the accumulated set of
        // delivered data grows monotonically.  Replacing (instead of union-ing)
        // would forget previously-released ranges, causing FanOutSlot to
        // re-deliver data that a consumer has already released.
        let accumulated = shared.release_guards[index].union(&obsolete_guard);
        trace!(
            "{} slot {index} accumulate {:?} + {obsolete_guard:?} = {accumulated:?}",
            self.name(),
            shared.release_guards[index]
        );
        // The slot's position rises to the last position of whichever of its accumulated
        // release and this increment is a prefix: a drive that releases position by position
        // releases no prefix each time but accumulates one, and a release of keys absent above
        // the drive's cursor leaves the accumulated release no prefix while the drive's own
        // increments still are.
        let domain = self.tiling().domain_extent();
        let through = |guard: &TileGuard| match guard {
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                match pred.as_prefix_in(domain.as_ref()) {
                    Some(Prefix::Through(position)) => Some(position),
                    _ => None,
                }
            }
            _ => None,
        };
        // The release wrapper hands the universal guard once everything is released, the call
        // that releases the last position included, and the universal guard names no position.
        // Over a finite range of positions everything is through the range's last position,
        // which is where a drive that finished stands.
        let finished = obsolete_guard
            .is_universal()
            .then(|| domain.as_ref().and_then(last_position_of_range))
            .flatten();
        let position = through(&accumulated)
            .max(through(&obsolete_guard))
            .max(finished);
        shared.positions[index] = shared.positions[index].clone().max(position);
        shared.release_guards[index] = accumulated;
        drop(shared);
        release_shared(&shared_rc);
    }
}

/// The last position of `extent` where it is a finite range of positions (`Extent::UIntRange`),
/// `None` for any other extent and for an empty or unbounded range.
fn last_position_of_range(extent: &Extent) -> Option<Position> {
    use intervalsets::Bounding as _;
    let Extent::UIntRange(positions) = extent else {
        return None;
    };
    let run = positions.intervals().last()?;
    let bound = run.right()?;
    let last = if bound.is_closed() {
        *bound.value()
    } else {
        bound.value().checked_sub(1)?
    };
    Some(Position::new(Value::UInt(last)))
}

/// The keys a slot's predecessor released whole that its reader has not released
/// ([`FanOutShared::unannounced`]), which [`AnnounceInherited`] adds to each delivery.
///
/// It names keys alone ([`Projection::keys_named_whole`]). The part of the predecessor's release
/// that names cells beneath keys, such as the fields of a record released before their row, is
/// not announced: a pushed region is a region of keys, and no key spells those cells.
struct Unannounced {
    /// The announced keys the reader's releases do not name whole.
    region: Projection,
    /// Every release the reader made through the slot since it subscribed, accumulated. A key
    /// leaves [`region`](Self::region) once this names it whole, whether one release named it or
    /// several did between them.
    released: TileGuard,
}

impl Unannounced {
    /// The keys `own`, the predecessor's own record, names whole; `None` where it names none.
    fn new(own: &TileGuard, tiling: &Tiling) -> Option<Self> {
        Self::of(Projection::keys_named_whole(own), tiling.empty_guard())
    }

    /// What is left once the reader also releases `release`: the announced keys less the keys
    /// the reader's accumulated release names whole, `None` where none are left.
    fn after(self, release: &TileGuard, tiling: &Tiling) -> Option<Self> {
        let released = self.released.union(release).closed_over(tiling);
        Self::of(
            self.region.minus(&Projection::keys_named_whole(&released)),
            released,
        )
    }

    fn of(region: Projection, released: TileGuard) -> Option<Self> {
        (region != Projection::Nothing).then_some(Self { region, released })
    }
}

/// The consumer a slot that inherited a release registers in place of its reader's: it adds the
/// keys its predecessor released whole that the reader has not released ([`Unannounced`]) to each
/// region delivered to the reader.
///
/// A rebuilt reader's slot starts at its predecessor's release
/// (`src/ccl/design/program-evolution.md`, "Where a rebuilt reader picks up"), and its input pushes
/// only what it still holds, so no push names the inherited keys. The operators above the slot
/// are new, so nothing else states those keys complete to them. The slot answers the keys with no
/// rows, because its release guard covers them, so the reader consumes a statement and replays no
/// row. The announcement repeats on each delivery because a package queued and not claimed at a
/// drained boundary is not carried into the next run's plan. Announcements stop once the reader's
/// releases name the keys whole, in one release or across several, including releases the slot's
/// inherited release already covers ([`FanOutShared::own`]). Until then each delivery costs one
/// [`Projection::union`].
///
/// Only the predecessor's own record is announced ([`FanOutShared::own`]). Rows the fan-out
/// reclaimed after a predecessor died, which that predecessor never received, stay unannounced,
/// so their loss leaves the run unfinished rather than finishing it without them.
struct AnnounceInherited {
    consumer: Box<dyn Consumer>,
    shared: Weak<RwLock<FanOutShared>>,
    /// The slot's number, which [`FanOutShared::compact`] rewrites. It is weak, as
    /// [`FanOutShared::subscribers`] is, because the slot dies with its producer.
    slot: Weak<std::sync::atomic::AtomicUsize>,
}

impl Consumer for AnnounceInherited {
    fn completion_key(&self) -> Option<&Value> {
        self.consumer.completion_key()
    }

    fn notify(
        &self,
        region: &Projection,
        landing: &mut crate::interpreter::dispatcher::Landing<'_>,
    ) {
        // The shared state's lock is released before the reader is notified, since a delivery
        // can reach a pull of this fan-out.
        let announced = match (
            landing.is_delivery(),
            self.shared.upgrade(),
            self.slot.upgrade(),
        ) {
            (true, Some(shared), Some(slot)) => shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .unannounced[slot.load(std::sync::atomic::Ordering::Relaxed)]
            .as_ref()
            .map(|pending| region.union(&pending.region)),
            _ => None,
        };
        self.consumer
            .notify(announced.as_ref().unwrap_or(region), landing);
    }
}

/// Release upstream what every live slot, and every slot an open handover holds, has released
/// ([`FanOutShared::released`]).
fn release_shared(shared_rc: &Arc<RwLock<FanOutShared>>) {
    let mut shared = shared_rc.write().unwrap_or_else(PoisonError::into_inner);
    // Live subscribers and the slots an open handover holds constrain the release: the ones it
    // retired and the ones that died since. Outside a handover a subscriber whose producer has
    // been dropped never releases again, so counting its guard would hold the intersection
    // wherever that subscriber left it and the input would retain everything from there on.
    let mut guards = shared
        .counted_indices()
        .map(|i| &shared.release_guards[i])
        .chain(shared.retired.iter().map(|r| &r.guard));
    let Some(first) = guards.next() else {
        return;
    };
    let intersection = guards.fold(first.clone(), |guard, other| guard.intersect(other));
    if intersection == shared.released {
        return;
    }
    shared.released = intersection.clone();
    let Some(inner) = shared.producer.as_mut() else {
        return;
    };
    let cell = match inner {
        Inner::Owned(producer) => {
            producer.release(intersection);
            return;
        }
        Inner::Store(cell) => cell.clone(),
    };
    drop(shared);
    cell.release(intersection);
}

/// An operator that logically forwards data from its input to its
/// consumer, but caches it so that the data doesn't have to be recomputed.
/// This involves storing the current Tile, merging new Tiles in as they arrive,
/// and immediately releasing upstream according to the received Tiles.
pub struct Memo {
    pub input: Arc<dyn TileOperator>,
    /// The tiling is `input`'s, forwarded unchanged.
    base: OperatorBase,
}

impl Memo {
    pub fn new(input: Arc<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for Memo {
    /// A breaker: its pipeline pushes its output to the pipelines that read it.
    fn keys_arrive_by_push(&self) -> bool {
        true
    }

    impl_operator_base!();

    /// A memo's record fields equal what its input's do.
    fn field_correlation(&self, field: &str) -> Option<Vec<TilePathStep>> {
        self.input.field_correlation(field)
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        self: Arc<Self>,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let consumer = shared_consumer(consumer);
        let (entry, placement) =
            crate::interpreter::dispatcher::Entry::unplaced(self.input.tiling().clone());
        share_breaker(MemoProducer::new(
            ProducerBase::new(MemoProducer::alloc_id(), self.tiling(), self.clone(), cx)
                .breaking(consumer.clone(), placement),
            self.input.clone().subscribe(
                intent_guard,
                Box::new(entry.inline_through(forwarding_consumer_keeping_keys(&consumer))),
                cx,
            ),
        ))
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

pub(crate) struct MemoProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    // shared-state-ok: this producer's own state, which `get`, `consume_impl` and `release` change
    // through `&self` on any worker thread; no other operator holds it.
    cached_tile: RwLock<Tile>,
    // shared-state-ok: held shared by each consume while it reads the input and exclusively by a
    // release of the input, so a release waits for the consumes in flight; no other operator
    // holds it.
    reading_input: RwLock<()>,
}

impl MemoProducer {
    /// A memo over `input` with an empty cache.
    fn new(base: ProducerBase, input: Box<dyn TileProducer>) -> Self {
        let cached_tile = base.tiling.empty_tile();
        Self {
            base,
            input,
            cached_tile: RwLock::new(cached_tile),
            reading_input: RwLock::new(()),
        }
    }

    /// A memo over `input` that nothing subscribed, for a test that builds a chain by hand.
    #[cfg(test)]
    pub(crate) fn over(input: Box<dyn TileProducer>, tiling: &Tiling) -> Self {
        Self::new(ProducerBase::unowned(Self::alloc_id(), tiling), input)
    }

    /// The cache cut to `projection`: it holds whatever was read, which can be more than the
    /// pull asks for.
    fn answer(&self, projection: &Projection) -> Tile {
        let mut tile = self
            .cached_tile
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        tile.restrict_to(projection, self.tiling());
        tile
    }
}

impl MemoProducer {
    /// An exact field pull carries its own publication delta. The input cache can serve
    /// independent fields concurrently. Append the delivered values under the same lock as local reclamation.
    fn consume_fields(
        &self,
        guard: TileGuard,
        projection: &Projection,
        pushes: Option<&mut Pushes<'_>>,
    ) {
        let mut answer = self.input.get(guard);
        answer.retain_finished_state_fields();
        let released = answer.to_guard();
        answer.compact();
        let delta = {
            let mut cache = self
                .cached_tile
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            let obsolete = self.obsolete_guard();
            if !obsolete.is_empty() {
                answer.remove_guarded(obsolete);
                answer.compact();
                answer.restrict_to(projection, self.tiling());
            }
            cache.append(answer, projection, self.tiling())
        };
        self.input.release(released);
        if let Some(pushes) = pushes.filter(|p| p.has_readers()) {
            let remaining = guard_minus(&delta, &self.obsolete_guard());
            pushes.push_region(self, &remaining, |part, _| vec![part.clone()]);
        }
    }

    /// Append the input answer and release it before the dispatcher can land this claim's pushes.
    fn consume_input(&self, guard: TileGuard, pushes: Option<&mut Pushes<'_>>) {
        assert!(guard.check_from(self.input.tiling()));
        let projection = guard.projection_for(self);
        if projection.names_part_of_values() {
            self.consume_fields(guard, &projection, pushes);
            return;
        }
        let _reading = self
            .reading_input
            .read()
            .unwrap_or_else(PoisonError::into_inner);
        if projection == Projection::Nothing || guard_covers(&self.input.obsolete_guard(), &guard) {
            return;
        }
        let mut input = self.input.get(guard.clone());
        input.retain_finished_state_fields();
        let mut released = input.to_guard();
        let pushes = pushes.filter(|p| p.has_readers());
        let flat = pushes.as_ref().and_then(|p| {
            let keys = flat_answer_keys(&input, &guard, &released)?;
            // A package-sized answer needs no key scan or copy when its delta is cut.
            let oversized = (keys.len() > p.morsel_rows()).then(|| keys.clone());
            Some(oversized)
        });
        input.compact();
        #[cfg(debug_assertions)]
        {
            let mut unreleased = input.clone();
            unreleased.remove_guarded(released.clone());
            unreleased.compact();
            debug_assert!(
                !unreleased.holds_a_plain_value(),
                "a memo releases every plain value it takes: {unreleased:?}"
            );
        }

        input.remove_guarded(self.obsolete_guard());
        input.compact();
        let mut cache = self
            .cached_tile
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        let delta = cache.append(input, &projection, self.tiling());

        if let Projection::Keys { level, keys } = &projection {
            let complete = cache.completion_at(*level).intersect(keys);
            released =
                released.union(&Projection::keys_at(*level, complete).guard(self.input.tiling()));
        }
        drop(cache);
        self.input.release(released);
        let Some(pushes) = pushes else { return };
        let remaining = held_after_release(delta, &self.obsolete_guard(), self.tiling());
        pushes.push_region(self, &remaining, |new, rows| match flat {
            Some(None) => vec![new.clone()],
            Some(Some(keys)) => cut_at_keys(
                new,
                (0..keys.len()).map(|i| keys.index_at(i)),
                rows,
                self.tiling(),
            ),
            None if matches!(new, TileGuard::Function(FunctionGuard::Domain(_))) => {
                self.morsels(new, rows)
            }
            None => vec![new.clone()],
        });
    }
}

/// Only a flat answer contributes whole keys directly. Deleted rows may release input
/// without adding output, and a widened answer may include a peer's in-flight region.
fn flat_answer_keys<'a>(
    input: &'a Tile,
    requested: &TileGuard,
    completed: &TileGuard,
) -> Option<&'a ColumnValue> {
    let Tile::DataFunction {
        domain,
        codomain,
        deleted,
        ..
    } = input
    else {
        return None;
    };
    let TileGuard::Function(FunctionGuard::Domain(keys)) = requested else {
        return None;
    };
    let TileGuard::Function(FunctionGuard::Domain(done)) = completed else {
        return None;
    };
    (!codomain.holds_a_level()
        && deleted.is_empty()
        && !keys.qualifies()
        && !done.qualifies()
        && guard_covers(requested, completed))
    .then_some(domain)
}

impl Breaker for MemoProducer {
    /// A consume caches the answer and releases what it states ([`MemoProducer::consume_input`]).
    ///
    /// Reads the input at `guard` whether or not the cache holds the region, since the caller asks
    /// for the pipeline to run. It wakes no consumer: a consuming memo's only reader is the
    /// pipeline the dispatcher pushes to, and what the consume merged reaches it through the
    /// packages pushed after the consume.
    fn consume_impl(&self, _: InputId, guard: TileGuard) {
        self.consume_input(guard, None);
    }

    fn consume_for_dispatch(
        &self,
        _: InputId,
        guard: TileGuard,
        pushes: &mut Pushes<'_>,
    ) -> Option<&dyn BreakingProducer> {
        self.consume_input(guard, Some(pushes));
        None
    }

    fn finish(&mut self, _: InputId, pushes: &mut Pushes<'_>) {
        // Every input pipeline is closed and every claim is integrated, so the input adds no key
        // and no reader asks for more of a value than the cache took: the cache holds every key
        // complete. A reader of one field of a record leaves the others unconsumed, so the
        // input itself need not be released whole. The statement is spelled `True` because a
        // union of per-key statements need not simplify to it, as for nominal keys whose values
        // are records.
        if let Tile::DataFunction {
            domain_predicate, ..
        } = &mut *self
            .cached_tile
            .write()
            .unwrap_or_else(PoisonError::into_inner)
        {
            *domain_predicate = Predicate::True;
        }
        pushes.push_final(self);
    }

    fn finish_parallel_input(&mut self) {
        self.input.release(self.input.tiling().universal_guard());
    }
    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for MemoProducer {
    /// The region the cached tile states, and what its readers released whole, which they release
    /// only once it is decided. A release of a collection's rows leaves its statement as it was,
    /// but a release of a scalar empties it, so the cache alone no longer states it. A release of
    /// some fields' cells beneath a row leaves the row in the cache, which states it, so only the
    /// keys released whole are added (`keys_released_whole`). `final_guard` takes the released
    /// region out again.
    fn complete(&self) -> TileGuard {
        let stated = self
            .cached_tile
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .to_guard();
        let released = self.obsolete_guard();
        if released.is_empty() {
            return stated;
        }
        let released = match names_collection_keys(&released) {
            true => match keys_released_whole(&released) {
                Some(keys) => keys,
                None => return stated,
            },
            false => released.clone(),
        };
        stated.union(&released)
    }

    /// Cut at the cached keys.
    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        let cache = self
            .cached_tile
            .read()
            .unwrap_or_else(PoisonError::into_inner);
        let keys = cache.live_keys().into_iter().flatten();
        cut_at_keys(guard, keys.map(|(_, key)| key), rows, self.tiling())
    }
}

impl TileProducer for MemoProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(
            self.cached_tile
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .cell_count(),
        )
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn restates(&self) -> Restates {
        Restates::Every
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    fn get(&self, guard: TileGuard) -> Tile {
        self.checked_get(guard, &|part| self.get_impl(part))
    }

    fn get_impl(&self, guard: TileGuard) -> Tile {
        self.answer(&guard.projection_for(self))
    }

    fn release_impl(&self, guard: TileGuard) {
        let _no_reads = self
            .reading_input
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        let mut cache = self
            .cached_tile
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        // Releasing complementary fields can complete the release of their row. Apply
        // the accumulated guard so a later whole-row read cannot return its bare key.
        if matches!(guard, TileGuard::Function(FunctionGuard::Domain(_))) {
            cache.remove_guarded(guard.clone());
        } else {
            cache.remove_guarded(self.obsolete_guard());
        }
        cache.compact();
        drop(cache);
        self.input.release(guard);
    }
}

#[cfg(test)]
mod nested_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        ProjectionSpy, ProjectionSpyOp, assert_conforms_beneath, paths_guard, two_levels_of_ints,
    };
    use crate::interpreter::{Predicate, Value};

    fn spy() -> Arc<dyn TileOperator> {
        let (tile, tiling) = two_levels_of_ints();
        Arc::new(ProjectionSpyOp::new(tile, tiling).0)
    }

    #[test]
    fn a_memo_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| Arc::new(Memo::new(spy())));
    }

    fn path(k: u64, j: u64) -> TileGuard {
        paths_guard(Predicate::qualified(
            Predicate::point(Value::UInt(k)),
            Predicate::point(Value::UInt(j)),
        ))
    }

    /// A memo consumed at one path reads its input there, answers a second path from a second
    /// read, and a pull of everything after a consume of everything is the input's whole answer:
    /// what it read at the paths merges into the cache with what it reads after.
    #[test]
    fn a_memo_reads_each_path_it_is_consumed_at_and_caches_them() {
        let (tile, tiling) = two_levels_of_ints();
        let (input, pulled, _) = ProjectionSpy::new(tile.clone(), tiling.clone());
        let mut producer = MemoProducer::over(Box::new(input), &tiling);
        producer.begin_run();
        for (k, j) in [(0, 1), (1, 0)] {
            let mut expected = tile.clone();
            expected.restrict_to(&Projection::of(&path(k, j)).unwrap(), &tiling);
            producer.consume_in_pipeline(InputId::ONLY, path(k, j));
            assert_eq!(producer.get(path(k, j)), expected);
        }
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner)[..2],
            [path(0, 1), path(1, 0)]
        );
        let cells = |tile: &Tile| {
            let mut live = tile.clone();
            live.compact();
            let paths = live.paths_at(CurryLevel::new(1));
            let Tile::Scalar(ColumnValue::Ints(values)) = live.values_at(CurryLevel::new(2)) else {
                panic!("ints beneath two levels: {live:?}")
            };
            let mut cells: Vec<(Vec<Value>, i64)> =
                paths.into_iter().zip(values.iter().copied()).collect();
            cells.sort_by(|a, b| a.0.partial_cmp(&b.0).expect("positions are ordered"));
            cells
        };
        producer.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        let whole = producer.get(tiling.universal_guard());
        assert_eq!(
            cells(&whole),
            cells(&tile),
            "a merge appends the paths it adds"
        );
        assert!(whole.is_terminal());
    }

    /// Settling the last leaf closes its group and the enclosing row. An empty sibling
    /// then closes the outer domain without replaying any of the first row's paths.
    #[test]
    fn nested_memo_publishes_each_enclosing_row_end() {
        use crate::interpreter::dispatcher::{Dispatcher, Next, PipelineId};
        use crate::interpreter::tile_operators::test_helpers::push_to;
        use crate::interpreter::{BaseType, Extent};
        let collection = |n, values| Tiling::data_function(Extent::uint_range(n), values);
        let tiling = collection(
            2,
            collection(
                1,
                collection(2, Tiling::Scalar(Extent::Base(BaseType::Int))),
            ),
        );
        // 0 -> {0 -> {0 -> 7, 1 -> 8}}, 1 -> {}
        let leaves = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
            Predicate::True,
            Default::default(),
        );
        let groups = Tile::grouped(
            vec![0, 1],
            ColumnValue::UInts(vec![0]),
            Box::new(leaves),
            Predicate::True,
            Default::default(),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(groups),
            Predicate::True,
            Default::default(),
        );
        let mut memo = MemoProducer::over(
            Box::new(ProjectionSpy::new(tile, tiling.clone()).0),
            &tiling,
        );
        push_to(&mut memo, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
        let consume = |claim: Projection, expected: Projection| {
            let mut pushes = dispatcher.pushes(PipelineId(0));
            assert!(
                memo.consume_for_dispatch(InputId::ONLY, claim.guard(&tiling), &mut pushes)
                    .is_none()
            );
            dispatcher.land(pushes);
            let mut emitted = Projection::Nothing;
            while let Next::Package(package) = dispatcher.try_claim(Some(PipelineId(1))) {
                let part = Projection::of(&package.guard).unwrap();
                assert_eq!(emitted.intersect(&part), Projection::Nothing);
                emitted = emitted.union(&part);
                dispatcher.acknowledge(package);
            }
            assert_eq!(emitted.minus(&expected), Projection::Nothing);
            assert_eq!(expected.minus(&emitted), Projection::Nothing);
        };
        let path = |p: &[u64]| {
            let keys: Vec<_> = p.iter().copied().map(Value::UInt).collect();
            Projection::keys_at(CurryLevel::new(p.len() - 1), Predicate::exactly(&keys))
        };
        let first = path(&[0, 0, 1]);
        let row = path(&[0]);
        consume(first.clone(), first.clone());
        consume(path(&[0, 0, 0]), row.minus(&first));
        assert!(guard_covers(&memo.complete(), &row.guard(&tiling)));
        assert!(!memo.complete().is_universal());
        consume(path(&[1]), Projection::Everything.minus(&row));
        assert!(memo.complete().is_universal());
    }

    #[test]
    fn a_memo_releases_deleted_rows_but_publishes_only_the_surviving_answer() {
        use crate::interpreter::dispatcher::{Dispatcher, Next, PipelineId};
        use crate::interpreter::tile_operators::test_helpers::{
            TestTileProducer, int_column, keys_between, push_to,
        };
        use crate::interpreter::{BaseType, Extent};

        let tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let mut tile = int_column(vec![1, 2], Predicate::False);
        tile.remove_guarded(keys_between(2, 2));
        let mut memo = MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        );
        push_to(&mut memo, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], 4);
        let mut pushes = dispatcher.pushes(PipelineId(0));
        assert!(
            memo.consume_for_dispatch(InputId::ONLY, tiling.universal_guard(), &mut pushes)
                .is_none()
        );
        dispatcher.land(pushes);
        assert!(guard_covers(
            &memo.input.obsolete_guard(),
            &keys_between(1, 2)
        ));
        let Next::Package(package) = dispatcher.try_claim(Some(PipelineId(1))) else {
            panic!("the surviving row is ready")
        };
        assert_eq!(package.guard, keys_between(1, 1));
        dispatcher.acknowledge(package);
        assert_eq!(dispatcher.outstanding(PipelineId(1)), 0);
    }

    /// A memo consumed at the paths of two rows releases what its input states complete of
    /// them, a path it holds none of included: all of a row the input calls complete, and of a
    /// row complete in part only the paths the input calls complete.
    #[test]
    fn a_memo_consumed_at_paths_releases_what_its_input_states_complete() {
        use crate::interpreter::{BaseType, Extent};
        use bit_set::BitSet;
        let point = |k: u64| Predicate::point(Value::UInt(k));
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Each row holds its positions 0 and 1. Row 0 is complete, its position 2 included,
        // and of row 1 the positions 0 and 1 are.
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 10, 11]))),
                Predicate::qualified(point(1), point(0).union(&point(1))),
                BitSet::new(),
            )),
            point(0),
            BitSet::new(),
        );
        let (input, _, released) = ProjectionSpy::new(tile, tiling.clone());
        let mut memo = MemoProducer::over(Box::new(input), &tiling);

        let every = point(0).union(&point(1)).union(&point(2));
        memo.begin_run();
        memo.consume_in_pipeline(
            InputId::ONLY,
            paths_guard(Predicate::qualified(
                point(0).union(&point(1)),
                every.clone(),
            )),
        );
        let expected = Predicate::qualified(point(0), every)
            .union(&Predicate::qualified(point(1), point(0).union(&point(1))));
        let releases = released.read().unwrap_or_else(PoisonError::into_inner);
        let Some(Ok(Projection::Keys { level, keys })) = releases.last().map(Projection::of) else {
            panic!("a consume releases paths: {releases:?}")
        };
        assert_eq!(level, CurryLevel::new(1));
        assert!(
            keys.subsumes(&expected) && expected.subsumes(&keys),
            "released {keys:?}, not {expected:?}"
        );
        let open = Predicate::qualified(point(1), point(2));
        assert!(
            releases.iter().all(|guard| match Projection::of(guard) {
                Ok(Projection::Keys { keys, .. }) => keys.intersect(&open).is_false(),
                _ => false,
            }),
            "a path the input does not call complete stays held by it: {releases:?}"
        );
    }

    #[test]
    fn a_fan_out_slot_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| FanOut::new(spy()).slot());
    }

    /// A cyclic fan-out reads its input whole, so it declares a whole read at any level; any
    /// other passes the level it is pulled at to its input.
    #[test]
    fn a_cyclic_fan_out_declares_a_whole_read_of_its_input() {
        let level = CurryLevel::new(1);
        let declared = |fan: FanOut| {
            let slot = fan.slot();
            let guard = slot.tiling().universal_guard();
            let producer =
                slot.clone()
                    .clone()
                    .subscribe(guard, Box::new(|| {}), &mut Default::default());
            producer.input_level("input", level)
        };
        assert_eq!(declared(FanOut::new_cyclic(spy())), None);
        assert_eq!(declared(FanOut::new(spy())), Some(level));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::SharedCounter as Cell;
    use std::collections::VecDeque;
    use std::sync::Arc;
    use std::sync::RwLock;

    use bit_set::BitSet;

    use crate::interpreter::tile_operators::test_helpers::QuietSpy;
    use crate::interpreter::tile_operators::{Constant, SubscribeContext};
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};

    #[test]
    fn reopening_a_fan_out_drops_dead_slots_and_renumbers_the_rest() {
        let extent = Extent::Base(BaseType::Int);
        let fan = FanOut::new(std::sync::Arc::new(Constant::new(
            Value::Int(1),
            extent.clone(),
        )));
        let mut cx = SubscribeContext::new();
        let tiling = Tiling::Scalar(extent);

        let first =
            fan.slot()
                .clone()
                .clone()
                .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut cx);
        let second =
            fan.slot()
                .clone()
                .clone()
                .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut cx);
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .subscribers
                .len(),
            2
        );

        // Distinguish the survivor's guard from the empty one the dead slot holds.
        let mine = TileGuard::Scalar(Predicate::True);
        second.release(mine.clone());
        drop(first);

        fan.reopen();

        let shared = fan.shared.read().unwrap_or_else(PoisonError::into_inner);
        assert_eq!(shared.subscribers.len(), 1, "the dead slot is gone");
        assert_eq!(shared.consumers.len(), 1, "consumers stay parallel");
        assert_eq!(shared.release_guards.len(), 1, "guards stay parallel");
        drop(shared);
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .release_guards[0],
            mine,
            "the survivor's guard moved with it, and it reads its new slot"
        );
    }

    /// The positions of a stream: `UInt` keys over `Int` values.
    fn positions() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    fn released_points(points: &[u64]) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::union_all(
            points
                .iter()
                .map(|&p| Predicate::point(Value::UInt(p)))
                .collect(),
        )))
    }

    fn released_through(last: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            last,
        ))))
    }

    /// A fan-out over a stream of positions, whose slots a test keys by reader.
    fn keyed_fan() -> FanOut {
        let (input, _, _) =
            test_helpers::ProjectionSpyOp::new(positions().empty_tile(), positions());
        FanOut::new(Arc::new(input))
    }

    fn a_reader() -> SlotReader {
        SlotReader::new(NodeId::fresh())
    }

    thread_local! {
        /// Names the readers of every test that holds no version of its own; held for the
        /// whole test.
        static HELD: Version = Version::default();
    }

    fn read_by(
        fan: &FanOut,
        reader: SlotReader,
        predecessor: Option<SlotReader>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        HELD.with(|version| read_in(fan, reader, predecessor, version, cx))
    }

    /// [`read_by`] in `version`.
    fn read_in(
        fan: &FanOut,
        reader: SlotReader,
        predecessor: Option<SlotReader>,
        version: &Version,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        fan.slot_read_by(reader, predecessor, version).subscribe(
            positions().empty_guard(),
            Box::new(|| {}),
            cx,
        )
    }

    /// A reader a reload rebuilds starts at the release of the reader it replaces, read off
    /// that reader's slot, and not at the intersection a lagging sibling holds back.
    #[test]
    fn a_rebuilt_reader_starts_at_its_predecessors_release_not_a_lagging_siblings() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let (fast, lagging) = (a_reader(), a_reader());
        let fast_read = read_by(&fan, fast, None, &mut sched);
        let lagging_read = read_by(&fan, lagging, None, &mut sched);
        fast_read.release(released_through(9));
        lagging_read.release(released_through(4));
        drop(fast_read);
        fan.reopen();

        let rebuilt = a_reader();
        let _rebuilt_read = read_by(&fan, rebuilt, Some(fast), &mut sched);
        assert_eq!(fan.released_by(rebuilt), Some(released_through(9)));
        assert_eq!(
            fan.released_position_of(rebuilt),
            Some(Position::new(Value::UInt(9)))
        );
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(4),
            "the intersection only reclaims, and the lagging sibling holds it back"
        );
    }

    /// Two readers a reload rebuilds each start at their own predecessor's release: one that
    /// finished through 9 does not restart at 4 because the other stopped there.
    #[test]
    fn two_rebuilt_readers_each_start_at_their_own_predecessors_release() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let (fast, slow) = (a_reader(), a_reader());
        let fast_read = read_by(&fan, fast, None, &mut sched);
        let slow_read = read_by(&fan, slow, None, &mut sched);
        fast_read.release(released_through(9));
        slow_read.release(released_through(4));
        drop((fast_read, slow_read));
        fan.reopen();

        let (fast_again, slow_again) = (a_reader(), a_reader());
        let _fast = read_by(&fan, fast_again, Some(fast), &mut sched);
        let _slow = read_by(&fan, slow_again, Some(slow), &mut sched);
        assert_eq!(fan.released_by(fast_again), Some(released_through(9)));
        assert_eq!(fan.released_by(slow_again), Some(released_through(4)));
    }

    /// A release with holes is carried exactly: positions 0 and 2 released and 1 not, so the
    /// rebuilt reader still reads 1. No prefix is released, so there is no position to resume
    /// past.
    #[test]
    fn a_release_with_holes_is_carried_exactly() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let first = a_reader();
        let read = read_by(&fan, first, None, &mut sched);
        read.release(released_points(&[0, 2]));
        drop(read);
        fan.reopen();

        let rebuilt = a_reader();
        let _read = read_by(&fan, rebuilt, Some(first), &mut sched);
        assert_eq!(fan.released_by(rebuilt), Some(released_points(&[0, 2])));
        assert_eq!(fan.released_position_of(rebuilt), None);
    }

    /// A reader with no predecessor on this fan-out starts at what the fan-out has reclaimed.
    #[test]
    fn a_reader_with_no_predecessor_starts_at_what_the_fan_out_reclaimed() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let read = read_by(&fan, a_reader(), None, &mut sched);
        read.release(released_through(3));
        drop(read);
        fan.reopen();
        fan.settle_handover();

        let new = a_reader();
        let _read = read_by(&fan, new, Some(a_reader()), &mut sched);
        assert_eq!(fan.released_by(new), Some(released_through(3)));
    }

    /// The slots a handover retires hold the reclamation intersection back until it settles,
    /// so a live sibling's release in between reclaims nothing the replacement still reads.
    #[test]
    fn retired_slots_hold_reclamation_back_until_the_handover_settles() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let retiring = read_by(&fan, a_reader(), None, &mut sched);
        let live = read_by(&fan, a_reader(), None, &mut sched);
        retiring.release(released_through(4));
        drop(retiring);
        fan.reopen();

        live.release(released_through(9));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(4)
        );
        fan.settle_handover();
        live.release(released_through(10));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(10)
        );
    }

    /// A slot that dies after the handover begins holds the reclamation intersection back until
    /// the handover settles. A slot under an operator the new version declined dies so, when the
    /// offer is released. A replacement that subscribes first releases past it, and a later
    /// replacement still starts at its predecessor's release. Once the handover settles, the dead
    /// slots stop counting.
    #[test]
    fn a_slot_that_dies_during_the_handover_holds_reclamation_back_until_it_settles() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let (ahead, behind) = (a_reader(), a_reader());
        let ahead_read = read_by(&fan, ahead, None, &mut sched);
        let behind_read = read_by(&fan, behind, None, &mut sched);
        ahead_read.release(released_through(9));
        behind_read.release(released_through(4));
        fan.reopen();
        drop(ahead_read);
        drop(behind_read);

        let ahead_again = read_by(&fan, a_reader(), Some(ahead), &mut sched);
        ahead_again.release(released_through(10));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(4)
        );
        let behind_again = a_reader();
        let behind_read_again = read_by(&fan, behind_again, Some(behind), &mut sched);
        assert_eq!(fan.released_by(behind_again), Some(released_through(4)));
        fan.settle_handover();
        behind_read_again.release(released_through(10));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(10)
        );
    }

    /// A slot for `reader` replacing `predecessor`, whose deliveries `arrivals` records, and
    /// the consumer the fan-out registered for it.
    fn read_recorded(
        fan: &FanOut,
        tiling: &Tiling,
        reader: SlotReader,
        predecessor: Option<SlotReader>,
        arrivals: &Arrivals,
        cx: &mut SubscribeContext,
    ) -> (Box<dyn TileProducer>, SharedConsumer) {
        let read = HELD.with(|version| {
            fan.slot_read_by(reader, predecessor, version).subscribe(
                tiling.empty_guard(),
                arrivals.consumer(Box::new(|| {})),
                cx,
            )
        });
        let consumer = fan
            .shared
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .consumers
            .last()
            .expect("the slot registered a consumer")
            .clone();
        (read, consumer)
    }

    /// What a delivery of `region` through `consumer` hands the reader behind it.
    fn delivered(
        consumer: &SharedConsumer,
        arrivals: &Arrivals,
        region: &Projection,
    ) -> Projection {
        crate::interpreter::dispatcher::notify_for_test(&**consumer, region);
        arrivals.take()
    }

    fn keys_through(last: u64) -> Projection {
        Projection::admitting(Predicate::at_or_below(Value::UInt(last)))
    }

    fn key(k: u64) -> Projection {
        Projection::admitting(Predicate::point(Value::UInt(k)))
    }

    /// A compaction that drops a dead slot ahead of two announcing slots renumbers them, and
    /// each delivery still announces its own slot's inherited keys.
    #[test]
    fn an_announcement_follows_its_slot_past_a_compacted_dead_slot() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let (first, second) = (a_reader(), a_reader());
        let first_read = read_by(&fan, first, None, &mut sched);
        let second_read = read_by(&fan, second, None, &mut sched);
        first_read.release(released_through(4));
        second_read.release(released_points(&[9]));
        drop((first_read, second_read));
        fan.reopen();

        let ahead = read_by(&fan, a_reader(), None, &mut sched);
        let (first_arrivals, second_arrivals) = (Arrivals::new(), Arrivals::new());
        let (_first_again, first_consumer) = read_recorded(
            &fan,
            &positions(),
            a_reader(),
            Some(first),
            &first_arrivals,
            &mut sched,
        );
        let (_second_again, second_consumer) = read_recorded(
            &fan,
            &positions(),
            a_reader(),
            Some(second),
            &second_arrivals,
            &mut sched,
        );
        fan.settle_handover();
        drop(ahead);
        fan.reopen();
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .subscribers
                .len(),
            2,
            "the dead slot is gone"
        );

        assert_eq!(
            delivered(&first_consumer, &first_arrivals, &key(6)),
            keys_through(4).union(&key(6))
        );
        assert_eq!(
            delivered(&second_consumer, &second_arrivals, &key(6)),
            key(9).union(&key(6))
        );
    }

    /// A slot that died before the handover retires with what the fan-out reclaimed since, and
    /// its replacement starts there. Its reader never received those rows, so the replacement
    /// announces only what the dead slot released itself.
    #[test]
    fn an_announcement_names_only_what_a_slot_dead_before_the_handover_released() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let dead = a_reader();
        let dead_read = read_by(&fan, dead, None, &mut sched);
        let live = read_by(&fan, a_reader(), None, &mut sched);
        dead_read.release(released_through(4));
        drop(dead_read);
        live.release(released_through(9));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(9)
        );
        fan.reopen();

        let arrivals = Arrivals::new();
        let rebuilt = a_reader();
        let (_read, consumer) = read_recorded(
            &fan,
            &positions(),
            rebuilt,
            Some(dead),
            &arrivals,
            &mut sched,
        );
        assert_eq!(fan.released_by(rebuilt), Some(released_through(9)));
        assert_eq!(
            delivered(&consumer, &arrivals, &key(12)),
            keys_through(4).union(&key(12)),
            "positions 5 through 9 are announced by no one"
        );
    }

    /// A predecessor that released one field's cells at a key, besides keys whole, hands its
    /// replacement an announcement of the whole keys alone. A release of cells shrinks no
    /// announced key, and a release of the key ends its announcement.
    #[test]
    fn an_announcement_names_the_keys_a_release_of_cells_leaves_whole() {
        let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([("_0".into(), int()), ("_1".into(), int())])),
        );
        let (input, _, _) = test_helpers::ProjectionSpyOp::new(tiling.empty_tile(), tiling.clone());
        let fan = FanOut::new(Arc::new(input));
        let mut sched = SubscribeContext::new();
        let cells = |field: &str, at: u64| {
            let other = if field == "_0" { "_1" } else { "_0" };
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Record(
                HashMap::from([
                    (
                        field.into(),
                        TileGuard::Scalar(Predicate::qualified(
                            Predicate::point(Value::UInt(at)),
                            Predicate::True,
                        )),
                    ),
                    (other.into(), TileGuard::Scalar(Predicate::False)),
                ]),
            ))))
        };
        let keys = |k| TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(k))));

        let first = a_reader();
        let arrivals = Arrivals::new();
        let (first_read, _) = read_recorded(&fan, &tiling, first, None, &arrivals, &mut sched);
        first_read.release(keys(0).union(&cells("_0", 1)));
        drop(first_read);
        fan.reopen();

        let (read, consumer) = read_recorded(
            &fan,
            &tiling,
            a_reader(),
            Some(first),
            &arrivals,
            &mut sched,
        );
        assert_eq!(
            delivered(&consumer, &arrivals, &key(5)),
            key(0).union(&key(5)),
            "the cells at key 1 are not announced"
        );
        read.release(cells("_1", 0).union(&keys(5)));
        assert_eq!(
            delivered(&consumer, &arrivals, &key(6)),
            key(0).union(&key(6)),
            "a release of cells at key 0 leaves key 0 announced"
        );
        read.release(keys(0));
        assert_eq!(delivered(&consumer, &arrivals, &key(6)), key(6));
    }

    /// A second reload replaces the replacement of a slot that died before the handover. The
    /// slot the second reload replaces started past the rows the fan-out reclaimed after the
    /// dead slot, and its own record does not name them, so the second replacement announces
    /// what the dead slot released and what the first replacement released, and nothing else.
    #[test]
    fn a_second_reload_announces_only_what_a_slot_dead_before_the_first_released() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let dead = a_reader();
        let dead_read = read_by(&fan, dead, None, &mut sched);
        let live = read_by(&fan, a_reader(), None, &mut sched);
        dead_read.release(released_through(4));
        drop(dead_read);
        live.release(released_through(9));
        fan.reopen();

        let arrivals = Arrivals::new();
        let rebuilt = a_reader();
        let (rebuilt_read, consumer) = read_recorded(
            &fan,
            &positions(),
            rebuilt,
            Some(dead),
            &arrivals,
            &mut sched,
        );
        fan.settle_handover();
        assert_eq!(
            delivered(&consumer, &arrivals, &key(12)),
            keys_through(4).union(&key(12))
        );
        rebuilt_read.release(released_points(&[12]));

        fan.reopen();
        drop(rebuilt_read);
        let rebuilt_again = a_reader();
        let (_read, consumer) = read_recorded(
            &fan,
            &positions(),
            rebuilt_again,
            Some(rebuilt),
            &arrivals,
            &mut sched,
        );
        fan.settle_handover();
        assert_eq!(
            fan.released_by(rebuilt_again),
            Some(released_through(9).union(&released_points(&[12])))
        );
        assert_eq!(
            delivered(&consumer, &arrivals, &key(13)),
            keys_through(4).union(&key(12)).union(&key(13)),
            "positions 5 through 9 are announced by no version"
        );
    }

    /// A replacement's reader whose release, together with the release the slot inherited,
    /// covers a union's every tag makes the slot's obsolete guard universal, and its release
    /// reaches `release_impl` as the universal guard. The slot's own record takes the release as
    /// the reader gave it, so the second replacement announces the tags the readers released and
    /// not the tag the fan-out reclaimed after the dead slot.
    #[test]
    fn a_release_that_completes_an_inherited_one_records_only_the_readers_keys() {
        let tag = |name: &'static str| crate::ccl::FieldKey::Name(crate::ccl::Label::fixed(name));
        let tiling = Tiling::data_function(
            Extent::Union(crate::ccl::TagMap::from_arms(
                ["a", "b", "c"]
                    .map(|name| (tag(name), Extent::Base(BaseType::Unit)))
                    .into(),
            )),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let at = |names: &[&'static str]| {
            Predicate::tagged(
                crate::ccl::TagMap::from_arms(
                    names.iter().map(|&n| (tag(n), Predicate::True)).collect(),
                ),
                false,
            )
        };
        let released =
            |names: &[&'static str]| TileGuard::Function(FunctionGuard::Domain(at(names)));
        let (input, _, _) = test_helpers::ProjectionSpyOp::new(tiling.empty_tile(), tiling.clone());
        let fan = FanOut::new(Arc::new(input));
        let mut sched = SubscribeContext::new();
        let arrivals = Arrivals::new();
        let dead = a_reader();
        let (dead_read, _) = read_recorded(&fan, &tiling, dead, None, &arrivals, &mut sched);
        let (live, _) = read_recorded(&fan, &tiling, a_reader(), None, &arrivals, &mut sched);
        dead_read.release(released(&["a"]));
        drop(dead_read);
        live.release(released(&["a", "b"]));
        fan.reopen();

        let rebuilt = a_reader();
        let (rebuilt_read, _) =
            read_recorded(&fan, &tiling, rebuilt, Some(dead), &arrivals, &mut sched);
        fan.settle_handover();
        rebuilt_read.release(released(&["a", "c"]));
        assert!(
            rebuilt_read.obsolete_guard().is_universal(),
            "the inherited release and the reader's close over the union"
        );

        fan.reopen();
        drop(rebuilt_read);
        let (_read, consumer) = read_recorded(
            &fan,
            &tiling,
            a_reader(),
            Some(rebuilt),
            &arrivals,
            &mut sched,
        );
        fan.settle_handover();
        assert_eq!(
            delivered(&consumer, &arrivals, &Projection::Nothing),
            Projection::admitting(at(&["a", "c"])),
            "tag b is announced by no version"
        );
    }

    /// A reader that releases the announced keys in increments, as a morsel drive does, ends
    /// their announcement once its releases name every one of them, although the release the slot
    /// inherited covers each increment.
    #[test]
    fn an_announcement_shrinks_with_each_increment_the_reader_releases() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let first = a_reader();
        let first_read = read_by(&fan, first, None, &mut sched);
        first_read.release(released_through(4));
        drop(first_read);
        fan.reopen();

        let arrivals = Arrivals::new();
        let (read, consumer) = read_recorded(
            &fan,
            &positions(),
            a_reader(),
            Some(first),
            &arrivals,
            &mut sched,
        );
        fan.settle_handover();
        read.release(released_through(1));
        assert_eq!(
            delivered(&consumer, &arrivals, &key(6)),
            keys_through(4).minus(&keys_through(1)).union(&key(6))
        );
        read.release(released_points(&[2, 3]));
        assert_eq!(
            delivered(&consumer, &arrivals, &key(6)),
            key(4).union(&key(6))
        );
        read.release(released_points(&[4]));
        assert_eq!(delivered(&consumer, &arrivals, &key(6)), key(6));
    }

    /// A slot's position rises on a release that is a prefix, accumulated or as given, and on
    /// no other: a point above the start, a release with a hole above the prefix and the
    /// universal release leave it where it is.
    #[test]
    fn a_slots_position_rises_only_on_a_prefix() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let reader = a_reader();
        let read = read_by(&fan, reader, None, &mut sched);
        let at = |fan: &FanOut| fan.released_position_of(reader).map(|p| p.into_value());
        read.release(released_points(&[5]));
        assert_eq!(at(&fan), None, "a point above an empty start is no prefix");
        read.release(released_through(3));
        assert_eq!(at(&fan), Some(Value::UInt(3)));
        read.release(released_points(&[9]));
        assert_eq!(
            at(&fan),
            Some(Value::UInt(3)),
            "the holes at 4 and 6 to 8 are no prefix"
        );
        read.release(positions().universal_guard());
        assert_eq!(
            at(&fan),
            Some(Value::UInt(3)),
            "the universal release over an unbounded domain names no position, so the last one \
             stands"
        );
    }

    /// A slot that releases everything over a finite range of positions, after a partial
    /// release, stands at the range's last position (`FanOutShared::positions`). The release
    /// wrapper hands the slot the universal guard, which names no position, so the slot reads
    /// the position off the range.
    #[rstest::rstest]
    // A transaction drive releases the positions above its extent first; what is left to
    // release is bounded by the extent's last position.
    #[case::above_the_extent_first(Predicate::True.minus(&Predicate::at_or_below(Value::UInt(2))))]
    // A prefix leaves the rest unbounded above, and the release of everything finishes it.
    #[case::a_prefix(Predicate::at_or_below(Value::UInt(1)))]
    fn a_release_of_everything_stands_at_the_ranges_last_position(#[case] first: Predicate) {
        let tiling = Tiling::data_function(
            Extent::uint_range(3),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            Predicate::True,
            BitSet::new(),
        );
        let fan = FanOut::new(Arc::new(Constant::collection(tile, tiling.clone())));
        let mut cx = SubscribeContext::new();
        let reader = a_reader();
        let slot = HELD.with(|version| {
            fan.slot_read_by(reader, None, version).subscribe(
                tiling.empty_guard(),
                Box::new(|| {}),
                &mut cx,
            )
        });
        slot.release(TileGuard::Function(FunctionGuard::Domain(first)));
        slot.release(tiling.universal_guard());
        assert!(fan.released_in_full());
        assert_eq!(
            fan.released_position_of(reader),
            Some(Position::new(Value::UInt(2)))
        );
    }

    /// A slot answers to the readers its reader is renamed to, as a version that keeps a
    /// reader inside a kept region names it by its own nodes.
    #[test]
    fn a_slot_answers_to_the_nodes_its_reader_is_renamed_to() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let reader = a_reader();
        let read = read_by(&fan, reader, None, &mut sched);
        read.release(released_through(2));
        let renamed = NodeId::fresh();
        HELD.with(|version| fan.alias_readers(&HashMap::from([(reader.node, renamed)]), version));
        assert_eq!(
            fan.released_by(SlotReader::new(renamed)),
            Some(released_through(2))
        );
        assert_eq!(fan.released_by(reader), Some(released_through(2)));
    }

    /// A slot kept across reloads answers to the names of the versions still held and drops the
    /// rest. Version 1 mints the reader, versions 2 and 3 keep it under their own nodes, and an
    /// older branch holds version 2 while the main branch moves on. Dropping version 1 drops its
    /// name, and the names of versions 2 and 3 still find the slot. Dropping version 2 drops its
    /// name at version 4's alias.
    #[test]
    fn a_kept_slot_answers_only_to_the_names_of_versions_still_held() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let (v1, v2, v3) = (Version::default(), Version::default(), Version::default());
        let first = a_reader();
        let read = read_in(&fan, first, None, &v1, &mut sched);
        read.release(released_through(2));
        let (second, third) = (NodeId::fresh(), NodeId::fresh());
        fan.alias_readers(&HashMap::from([(first.node, second)]), &v2);
        fan.alias_readers(&HashMap::from([(second, third)]), &v3);
        let names = |fan: &FanOut| -> Vec<NodeId> {
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .readers[0]
                .iter()
                .map(|named| named.reader.node)
                .collect()
        };
        assert_eq!(names(&fan), vec![first.node, second, third]);

        drop(v1);
        fan.reopen();
        fan.settle_handover();
        assert_eq!(names(&fan), vec![second, third]);
        assert_eq!(fan.released_by(first), None, "version 1 is gone");
        for held in [second, third] {
            assert_eq!(
                fan.released_by(SlotReader::new(held)),
                Some(released_through(2))
            );
        }

        drop(v2);
        let (v4, fourth) = (Version::default(), NodeId::fresh());
        fan.alias_readers(&HashMap::from([(third, fourth)]), &v4);
        assert_eq!(names(&fan), vec![third, fourth]);
    }

    /// A slot that died before the handover stopped counting toward the intersection, which a
    /// live sibling moved past it since. It retires covering what the fan-out reclaimed, so the
    /// intersection does not move backwards, and its successor asks for no reclaimed row.
    #[test]
    fn a_slot_that_died_before_the_handover_retires_covering_what_was_reclaimed() {
        let fan = keyed_fan();
        let mut cx = SubscribeContext::new();
        let early = a_reader();
        let early_read = read_by(&fan, early, None, &mut cx);
        let live = read_by(&fan, a_reader(), None, &mut cx);
        early_read.release(released_through(2));
        drop(early_read);
        live.release(released_through(9));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(9)
        );
        fan.reopen();

        live.release(released_through(10));
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            released_through(9)
        );
        let successor = a_reader();
        let _read = read_by(&fan, successor, Some(early), &mut cx);
        assert_eq!(fan.released_by(successor), Some(released_through(9)));
    }

    /// One live slot of a fan-out serves each reader: a second would leave a successor two
    /// releases to start from.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "one live slot of a fan-out serves each reader")]
    fn a_reader_with_two_live_slots_on_one_fan_out_is_refused() {
        let fan = keyed_fan();
        let mut sched = SubscribeContext::new();
        let reader = a_reader();
        let _first = read_by(&fan, reader, None, &mut sched);
        let _second = read_by(&fan, reader, None, &mut sched);
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
        let fan = FanOut::new(std::sync::Arc::new(Constant::new(
            Value::Int(1),
            extent.clone(),
        )));
        let mut cx = SubscribeContext::new();
        let tiling = Tiling::Scalar(extent);

        let first =
            fan.slot()
                .clone()
                .clone()
                .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut cx);
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
        let late =
            fan.slot()
                .clone()
                .clone()
                .subscribe(tiling.empty_guard(), Box::new(|| {}), &mut cx);
        assert_eq!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .release_guards[0],
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
        tiles: Arc<RwLock<VecDeque<Tile>>>,
        pulls: Arc<Cell<usize>>,
        notifier: Notifier,
    }

    struct ScriptedProducer {
        base: ProducerBase,
        tiles: Arc<RwLock<VecDeque<Tile>>>,
        pulls: Arc<Cell<usize>>,
        standing: Arc<Cell<bool>>,
        /// What the last tile called complete, which a pull with nothing new still states.
        complete: RwLock<Option<Predicate>>,
    }

    impl Scripted {
        /// The operator, the pull counter, and a handle that fires the consumer the
        /// memo installs on it.
        fn new(tiles: Vec<Tile>, tiling: &Tiling) -> (Self, Arc<Cell<usize>>, Notifier) {
            let pulls = Arc::new(Cell::new(0usize));
            let notifier = Notifier {
                consumer: Arc::new(RwLock::new(None)),
                standing: Arc::new(Cell::new(true)),
            };
            (
                Self {
                    base: OperatorBase::new(tiling.clone()),
                    tiles: Arc::new(RwLock::new(tiles.into())),
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
        consumer: test_helpers::InputConsumer,
        standing: Arc<Cell<bool>>,
    }

    /// Bring the input's next tile, and notify.
    fn notify(notifier: &Notifier) {
        notifier.standing.set(true);
        test_helpers::subscribed(&notifier.consumer).announce(&Projection::Everything);
    }

    impl TileOperator for Scripted {
        impl_operator_base!();

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            self: std::sync::Arc<Self>,
            _intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            _cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            *self
                .notifier
                .consumer
                .write()
                .unwrap_or_else(PoisonError::into_inner) = Some(consumer.into());
            Box::new(ScriptedProducer {
                base: ProducerBase::unowned(ScriptedProducer::alloc_id(), self.tiling()),
                tiles: self.tiles.clone(),
                pulls: self.pulls.clone(),
                standing: self.notifier.standing.clone(),
                complete: RwLock::new(None),
            })
        }
    }

    impl TileProducer for ScriptedProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&self, _projection_guard: TileGuard) -> Tile {
            self.pulls.set(self.pulls.get() + 1);
            let next = match self.standing.replace(false) {
                true => self
                    .tiles
                    .write()
                    .unwrap_or_else(PoisonError::into_inner)
                    .pop_front(),
                false => None,
            };
            let mut complete = self
                .complete
                .write()
                .unwrap_or_else(PoisonError::into_inner);
            match (next, &*complete) {
                (Some(tile), _) => {
                    if let Tile::DataFunction {
                        domain_predicate, ..
                    } = &tile
                    {
                        *complete = Some(domain_predicate.clone());
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

        fn release_impl(&self, _obsolete_guard: TileGuard) {}
    }

    /// An open tiling whose cached answer remains partial between notifications.
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
        let fan = FanOut::new(std::sync::Arc::new(input));
        let mut cx = SubscribeContext::new();
        let counts: Vec<Arc<Cell<u32>>> = (0..2).map(|_| Arc::new(Cell::new(0))).collect();
        let mut producers: Vec<Box<dyn TileProducer>> = counts
            .iter()
            .map(|count| {
                let count = count.clone();
                fan.slot().clone().subscribe(
                    tiling.universal_guard(),
                    Box::new(move || count.set(count.get() + 1)),
                    &mut cx,
                )
            })
            .collect();
        notify(&notifier);
        notify(&notifier);
        let seen = || counts.iter().map(|c| c.get()).collect::<Vec<_>>();
        assert_eq!(
            seen(),
            [2, 2],
            "each input notification reaches every branch"
        );
        producers[0].read_in_pipeline(tiling.universal_guard());
        notify(&notifier);
        assert_eq!(seen(), [3, 3], "a query does not gate later notifications");
    }

    /// A `Memo` releases its input universally as soon as the input hands over a
    /// complete tile, and from then on the cache is the value: repeated consumes and pulls
    /// answer the same single scalar.
    ///
    /// A consume after the input is released whole reads nothing. Were the memo to read the
    /// input again and the input to answer with the released value, `merge` would append it: a
    /// `Tile::Scalar`'s positions are implicit, so it cannot tell "this position again" from
    /// "one more position", and one value would silently become two, then three.
    #[test]
    fn memo_holds_one_value_across_repeated_pulls() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (upstream, _released) =
            QuietSpy::new(Tile::Scalar(ColumnValue::Ints(vec![-5])), tiling.clone());
        let mut memo = MemoProducer::new(
            ProducerBase::unowned(MemoProducer::alloc_id(), &tiling),
            Box::new(upstream),
        );
        memo.begin_run();

        for pull in 1..=3 {
            memo.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
            let tile = memo.get(tiling.universal_guard());
            assert_eq!(
                tile,
                Tile::Scalar(ColumnValue::Ints(vec![-5])),
                "pull {pull}: the cache holds the one drained value, not one copy per pull"
            );
        }
        assert!(
            memo.input.obsolete_guard().is_universal(),
            "the complete tile should have been released universally on the first pull"
        );
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
    use crate::interpreter::tile_operators::SubscribeContext;
    use crate::interpreter::tile_operators::test_helpers::push_to;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, ProjectionSpyOp, consume_breakers, int_entries, ints_by_position,
        keys_between,
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
        let fan = FanOut::new(Arc::new(input));
        let mut cx = SubscribeContext::new();
        let first =
            fan.slot()
                .clone()
                .clone()
                .subscribe(ints().empty_guard(), Box::new(|| {}), &mut cx);
        let second =
            fan.slot()
                .clone()
                .clone()
                .subscribe(ints().empty_guard(), Box::new(|| {}), &mut cx);
        (first, second, pulled)
    }

    /// `xs ▷ map(c)` fans a stream into two consumers that each read their own morsels. Each
    /// slot's answer is its own morsel, and the shared input is pulled at the region of the slot
    /// that pulls it: a producer states completeness only for the region it returns, so a pull of
    /// one region withdraws nothing it said of another.
    #[test]
    fn slots_read_their_own_morsels_through_one_input() {
        let (mut first, mut second, pulled) = two_slots();

        let one = first.read_in_pipeline(keys_between(0, 3));
        assert_eq!(int_entries(&one), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

        let two = second.read_in_pipeline(keys_between(4, 7));
        assert_eq!(int_entries(&two), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);

        let pulled = pulled.read().unwrap_or_else(PoisonError::into_inner);
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
        let tile = first.read_in_pipeline(ints().empty_guard());
        assert!(int_entries(&tile).is_empty());
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    /// A slot that asks for everything after another took a morsel gets everything, and the
    /// morsel's slot is still answered at its own region afterwards.
    #[test]
    fn a_later_universal_pull_reads_everything_and_the_first_slot_keeps_its_region() {
        let (mut first, mut second, pulled) = two_slots();
        first.read_in_pipeline(keys_between(0, 1));
        let all = second.read_in_pipeline(ints().universal_guard());
        assert_eq!(int_entries(&all).len(), ROWS as usize);
        assert_eq!(
            *pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .last()
                .unwrap(),
            ints().universal_guard()
        );

        let again = first.read_in_pipeline(keys_between(0, 1));
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

    /// A producer over `input` that records each input [`read_again`](TileProducer::read_again)
    /// names, for a test of the walk toward a producer.
    struct Rereading {
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        read_again: Arc<RwLock<Vec<String>>>,
    }

    impl Rereading {
        fn over(input: Box<dyn TileProducer>) -> (Self, Arc<RwLock<Vec<String>>>) {
            let read_again = Arc::new(RwLock::new(Vec::new()));
            let producer = Self {
                base: ProducerBase::unowned(Self::alloc_id(), &ints()),
                input,
                read_again: read_again.clone(),
            };
            (producer, read_again)
        }
    }

    impl TileProducer for Rereading {
        impl_producer_base!();

        fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
            visit("input", &*self.input);
        }

        fn visit_input_producers_mut(
            &mut self,
            visit: &mut dyn FnMut(&str, &mut dyn TileProducer),
        ) {
            visit("input", &mut *self.input);
        }

        fn read_again(&mut self, input: &str) {
            self.read_again
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .push(input.to_owned());
        }

        fn get_impl(&self, _guard: TileGuard) -> Tile {
            self.tiling().empty_tile()
        }

        fn release_impl(&self, _guard: TileGuard) {}
    }

    /// A spy over the stream of `0..ROWS`.
    fn stream() -> Box<dyn TileProducer> {
        let values: Vec<i64> = (0..ROWS as i64).collect();
        Box::new(ProjectionSpy::new(ints_by_position(&values, true), ints()).0)
    }

    /// A walk toward a producer has a producer on a path to it read that input again, and leaves
    /// a producer on no path to it as it is.
    #[test]
    fn a_walk_toward_a_producer_has_the_producer_above_it_read_again() {
        let address =
            |producer: &dyn TileProducer| std::ptr::from_ref(producer).cast::<()>() as usize;
        let (mut above, read_again) = Rereading::over(stream());
        let input = address(&*above.input);
        let is_input = |producer: &dyn TileProducer| (address(producer) == input).then_some(true);
        assert!(read_again_toward(&mut above, &is_input));
        assert_eq!(
            *read_again.read().unwrap_or_else(PoisonError::into_inner),
            ["input"]
        );

        let (mut other, read_again) = Rereading::over(stream());
        assert!(!read_again_toward(&mut other, &is_input));
        assert!(
            read_again
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    /// A walk does not descend beneath a producer its target stops at, as it stops at the
    /// recurrence slot of another loop's store: a producer above it reads nothing again.
    #[test]
    fn a_walk_stops_beneath_a_producer_its_target_stops_at() {
        let address =
            |producer: &dyn TileProducer| std::ptr::from_ref(producer).cast::<()>() as usize;
        let (inner, inner_read_again) = Rereading::over(stream());
        let (mut outer, read_again) = Rereading::over(Box::new(inner));
        let inner = address(&*outer.input);
        let stop = |producer: &dyn TileProducer| (address(producer) == inner).then_some(false);
        assert!(!read_again_toward(&mut outer, &stop));
        assert!(
            read_again
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
        assert!(
            inner_read_again
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    /// A memo consumed at a morsel reads its input over that morsel and releases only that, so the
    /// input keeps the rest for the next morsel. The answer is the morsel, not the cache.
    #[test]
    fn a_memo_reads_and_releases_one_morsel_at_a_time() {
        let (mut memo, pulled, released) = memo_over_stream();
        memo.begin_run();

        memo.consume_in_pipeline(InputId::ONLY, keys_between(0, 3));
        let first = memo.get(keys_between(0, 3));
        assert_eq!(int_entries(&first), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner)[0],
            keys_between(0, 3)
        );
        assert_eq!(
            released.read().unwrap_or_else(PoisonError::into_inner)[0],
            keys_between(0, 3)
        );
        memo.release(keys_between(0, 3));

        memo.consume_in_pipeline(InputId::ONLY, keys_between(4, 7));
        let second = memo.get(keys_between(4, 7));
        assert_eq!(int_entries(&second), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner)[1],
            keys_between(4, 7)
        );
    }

    /// A region the memo has consumed is answered from the cache with no pull. A consume of a
    /// region it has not read pulls the input, and the answer joins the cache.
    #[test]
    fn a_memo_answers_a_read_region_from_its_cache_and_reads_a_new_one() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, keys_between(0, 3));
        memo.release(keys_between(0, 1));

        let kept = memo.get(keys_between(2, 3));
        assert_eq!(int_entries(&kept), vec![(2, 2), (3, 3)]);
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            vec![keys_between(0, 3)],
            "a read region does not reach the input"
        );

        memo.consume_in_pipeline(InputId::ONLY, keys_between(2, 5));
        let wider = memo.get(keys_between(2, 5));
        assert_eq!(
            *pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .last()
                .unwrap(),
            keys_between(2, 5),
            "an unread region reaches the input"
        );
        assert_eq!(wider_keys(&wider), vec![2, 3, 4, 5]);
    }

    /// A memo consumed whole answers every pull from its cache as its input answers it.
    #[test]
    fn a_consuming_memo_answers_as_its_input_does() {
        let values: Vec<i64> = (0..ROWS as i64).collect();
        let (input, _, _) = ProjectionSpy::new(ints_by_position(&values, true), ints());
        let (mut consuming, _, _) = memo_over_stream();
        consuming.begin_run();
        consuming.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(consuming.final_guard(), ints().universal_guard());

        for guard in [
            ints().universal_guard(),
            keys_between(0, 3),
            keys_between(2, 5),
            ints().empty_guard(),
        ] {
            assert_eq!(
                consuming.get(guard.clone()),
                input.get(guard.clone()),
                "a pull at {guard:?}"
            );
        }
    }

    /// A memo answers from the state `consume_impl` built, inside a run or outside one, so the
    /// `get` wrapper holds every pull of it to pulling nothing.
    #[test]
    fn a_memo_answers_from_state_inside_a_run_and_outside_one() {
        let (memo, _, _) = memo_over_stream();
        assert!(memo.answers_from_state(), "outside a run");
        crate::interpreter::dispatcher::in_a_run(|| {
            assert!(memo.answers_from_state(), "unplaced, in a run");
        });
    }

    /// `consume_impl` pulls the input at its guard and releases it at what the answer stated, and
    /// nothing after it reaches the input.
    #[test]
    fn a_consuming_memo_pulls_the_input_once_and_releases_it_whole() {
        let (mut memo, pulled, released) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            vec![ints().universal_guard()]
        );
        assert_eq!(
            *released.read().unwrap_or_else(PoisonError::into_inner),
            vec![ints().universal_guard()]
        );

        for _ in 0..3 {
            memo.get(keys_between(0, 3));
            memo.get(ints().universal_guard());
        }
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner).len(),
            1,
            "a consuming memo's offer pulls nothing, even in a debug build"
        );
    }

    /// A memo consumed at a region answers that region from its cache and pulls nothing for the
    /// rest: the statement of its cache says which region it answers.
    #[test]
    fn a_memo_consumed_in_part_answers_that_part_and_pulls_no_more() {
        let (mut memo, pulled, released) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, keys_between(0, 3));
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            vec![keys_between(0, 3)]
        );
        assert_eq!(
            *released.read().unwrap_or_else(PoisonError::into_inner),
            vec![keys_between(0, 3)]
        );

        let part = memo.get(keys_between(0, 3));
        assert_eq!(int_entries(&part), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
        let rest = memo.get(keys_between(4, 7));
        assert!(int_entries(&rest).is_empty(), "the rest is not consumed");
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner).len(),
            1,
            "and it is not pulled either"
        );
    }

    /// A placed memo answers a pull before its first consume with nothing and pulls its
    /// input nothing.
    #[test]
    fn a_consuming_memo_pulled_before_its_first_consume_pulls_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.begin_run();
        let tile = memo.get(ints().universal_guard());
        assert!(tile.is_empty() && !tile.is_terminal(), "{tile:?}");
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    /// A consume of a memo whose input has already drained pulls nothing.
    #[test]
    fn a_memo_whose_input_has_drained_consumes_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        let pulls = pulled.read().unwrap_or_else(PoisonError::into_inner).len();
        memo.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        assert_eq!(memo.final_guard(), ints().universal_guard());
        assert_eq!(
            pulled.read().unwrap_or_else(PoisonError::into_inner).len(),
            pulls
        );
    }

    /// `finish` queues no wake. A consume that finds nothing new, on a memo whose input has
    /// drained, queues none either, so the queue is empty throughout.
    #[test]
    fn finish_preserves_the_cached_answer() {
        let (mut memo, _, _) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        memo.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        push_to(&mut memo, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| memo.finish(InputId::ONLY, pushes));
        assert!(dispatcher.pop().is_some(), "finish pushed a package");
    }

    /// The final guard of one memo is the guard the memo that reads it consumes: the whole
    /// tiling less what the first released, which the second pulls and releases at.
    #[test]
    fn a_memo_consumes_the_final_guard_of_the_memo_before_it() {
        let (mut first, _, _) = memo_over_stream();
        let (mut second, pulled, released) = memo_over_stream();
        first.begin_run();
        first.consume_in_pipeline(InputId::ONLY, ints().universal_guard());
        first.release(keys_between(0, 3));
        let handed = first.final_guard();
        assert_ne!(
            handed,
            ints().universal_guard(),
            "the released keys are not handed on"
        );
        second.begin_run();
        second.consume_in_pipeline(InputId::ONLY, handed.clone());
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            vec![handed.clone()]
        );
        assert_eq!(
            *released.read().unwrap_or_else(PoisonError::into_inner),
            vec![handed]
        );
        let rest = second.get(ints().universal_guard());
        assert_eq!(int_entries(&rest), vec![(4, 4), (5, 5), (6, 6), (7, 7)]);
    }

    /// A pull at `Nothing` consumes nothing.
    #[test]
    fn consuming_nothing_pulls_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, ints().empty_guard());
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
        assert!(int_entries(&memo.get(ints().universal_guard())).is_empty());
    }

    /// A pull at `Nothing` answers empty and touches neither the cache nor the input.
    #[test]
    fn a_memo_asked_for_nothing_reads_nothing() {
        let (mut memo, pulled, _) = memo_over_stream();
        let tile = memo.read_in_pipeline(ints().empty_guard());
        assert!(int_entries(&tile).is_empty());
        assert!(
            pulled
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .is_empty()
        );
    }

    fn wider_keys(tile: &Tile) -> Vec<u64> {
        int_entries(tile).into_iter().map(|(k, _)| k).collect()
    }

    /// `xs ▷ map(converse(xs))`: each position of a stream is mapped to the positions that hold
    /// its value, which is a group-by read back at the stream. The stream is memoized and fanned
    /// to both the argument leg and, through `Converse`, the function leg.
    ///
    /// The memo is consumed whole, as the pipeline feeding it consumes it, so both legs read the
    /// whole stream from its cache; the morsel's answer is cut at the map.
    #[test]
    fn a_morsel_of_a_map_over_a_converse_of_the_same_memoized_stream() {
        use crate::interpreter::CurryLevel;
        use crate::interpreter::tile_operators::{Converse, MapResult};

        let values = [0i64, 1, 0, 1, 2, 2, 0, 1];
        let (stream, pulled, _) = ProjectionSpyOp::new(ints_by_position(&values, true), ints());
        let fan = FanOut::new(Arc::new(Memo::new(Arc::new(stream))));
        let by_value = Converse::new(fan.slot());
        let map = Arc::new(MapResult::new_at(
            fan.slot(),
            Arc::new(by_value),
            CurryLevel::new(1),
        ));
        let guard = map.tiling().universal_guard();
        let mut cx = SubscribeContext::new();
        let mut producer = map.clone().subscribe(guard, Box::new(|| {}), &mut cx);
        consume_breakers(&mut *producer);

        let morsel = producer.read_in_pipeline(keys_between(2, 3));
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
        // The members follow the cache's order of positions.
        assert_eq!(*members, ColumnValue::UInts(vec![0, 2, 6, 1, 3, 7]));
        // The memo pulls the stream once, whole, and both legs read its cache.
        assert_eq!(
            *pulled.read().unwrap_or_else(PoisonError::into_inner),
            vec![ints().universal_guard()]
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
/// names as its final guard and what reaches the input, each against a model of the rows written
/// and released.
#[cfg(test)]
mod consuming_tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
    use crate::interpreter::tile_operators::SubscribeContext;
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Released, Rng, Shared, Step, entries, growing_source,
        ints, keys_of, keys_predicate, predicate, rows_of, same_region, source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::tile_operators::test_helpers::push_to;
    use crate::interpreter::{Predicate, Value};

    /// A memo over `source`.
    fn memo_over(source: &Shared) -> MemoProducer {
        MemoProducer::over(Box::new(Input::over(source)), &ints())
    }

    /// What the memo's cached tile states complete.
    fn statement(memo: &MemoProducer) -> Predicate {
        let Tile::DataFunction {
            domain_predicate, ..
        } = &*memo.cached_tile.read().unwrap()
        else {
            panic!("a collection, got {:?}", memo.cached_tile)
        };
        domain_predicate.clone()
    }

    // ------------------------------------------------------------------------------------
    // The memo consumes a region
    // ------------------------------------------------------------------------------------

    /// A consume at some keys merges what the input answered for them, states
    /// complete those keys and no others, and releases the input at them once.
    #[test]
    fn a_region_of_keys_is_what_the_memo_consumes() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        let region = Keys(2, 5);

        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, region.guard());

        assert_eq!(entries(&memo.cached_tile.read().unwrap()), rows_of(2..=5));
        let stated = statement(&memo);
        assert!(same_region(&stated, &keys_predicate(2, 5)), "{stated:?}");
        for outside in [0, 1, 6, 9] {
            assert!(!stated.contains(&Value::UInt(outside)), "key {outside}");
        }
        assert_eq!(
            source.read().unwrap_or_else(PoisonError::into_inner).pulled,
            vec![region.guard()]
        );
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            vec![region.guard()]
        );
    }

    /// A second region disjoint from the first joins the cache, which then states both.
    #[test]
    fn a_second_disjoint_region_joins_the_cache() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        for region in [Keys(1, 2), Keys(7, 9)] {
            memo.begin_run();
            memo.consume_in_pipeline(InputId::ONLY, region.guard());
        }
        assert_eq!(
            entries(&memo.cached_tile.read().unwrap()),
            rows_of([1, 2, 7, 8, 9])
        );
        let stated = statement(&memo);
        let both = keys_predicate(1, 2).union(&keys_predicate(7, 9));
        assert!(same_region(&stated, &both), "{stated:?}");
        assert!(
            !stated.contains(&Value::UInt(5)),
            "a key between is not stated"
        );
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            vec![keys_between(1, 2), keys_between(7, 9)]
        );
    }

    /// A region that overlaps the first is answered for the keys the input still holds, and the
    /// cache states the union.
    #[test]
    fn an_overlapping_region_adds_only_the_keys_the_input_still_holds() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        for region in [Keys(2, 5), Keys(4, 8)] {
            memo.begin_run();
            memo.consume_in_pipeline(InputId::ONLY, region.guard());
        }
        assert_eq!(entries(&memo.cached_tile.read().unwrap()), rows_of(2..=8));
        let stated = statement(&memo);
        assert!(same_region(&stated, &keys_predicate(2, 8)), "{stated:?}");
        assert_eq!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released,
            vec![keys_between(2, 5), keys_between(4, 8)],
            "the input is released at each guard consumed"
        );
    }

    /// `Everything` notified and consumed drains the input: the cache states the universe, and
    /// `final_guard` names all of it.
    #[test]
    fn everything_notified_and_consumed_has_the_universe_as_final_guard() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        assert_eq!(entries(&memo.cached_tile.read().unwrap()), rows_of(0..10));
        assert!(same_region(&statement(&memo), &Predicate::True));
        assert_eq!(memo.final_guard(), ints().universal_guard());
    }

    /// Consuming nothing reads nothing.
    #[test]
    fn consuming_nothing_reads_nothing() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, ints().empty_guard());
        assert!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .pulled
                .is_empty()
        );
        assert!(entries(&memo.cached_tile.read().unwrap()).is_empty());
    }

    /// A growing input states complete only the keys it holds, so the release leaves a key it
    /// has not answered, and a row that arrives there later is merged and released.
    #[test]
    fn a_key_the_input_withheld_is_merged_by_a_later_consume() {
        let source = growing_source([0, 1, 2, 4, 5]);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 5).guard());
        let first = predicate(
            &source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released[0],
        );
        assert!(first.contains(&Value::UInt(2)));
        assert!(
            !first.contains(&Value::UInt(3)),
            "the input did not answer key 3"
        );

        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .rows
            .insert(3, value(3));
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 5).guard());
        assert_eq!(entries(&memo.cached_tile.read().unwrap()), rows_of(0..=5));
        let second = predicate(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released
                .last()
                .unwrap(),
        );
        assert!(second.contains(&Value::UInt(3)));
    }

    /// An offer at a region nothing consumed states nothing complete there.
    #[test]
    fn an_offer_at_a_region_never_consumed_states_nothing() {
        let mut memo = memo_over(&source(0..10));
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 3).guard());
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
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 3).guard());
        memo.release(Keys(0, 3).guard());
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 3).guard());
        assert!(entries(&memo.cached_tile.read().unwrap()).is_empty());
        assert!(entries(&memo.get(Keys(0, 3).guard())).is_empty());
    }

    /// A release of the whole output leaves nothing held, and a release of every key of the
    /// universe leaves exactly the keys beyond it.
    #[test]
    fn final_guard_after_releasing_everything_or_every_key_is_exact() {
        let mut memo = memo_over(&source(0..10));
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        memo.release(All.guard());
        assert_eq!(memo.final_guard(), ints().empty_guard());

        let mut memo = memo_over(&source(0..10));
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        memo.release(Keys(0, KEYS - 1).guard());
        assert!(same_region(
            &predicate(&memo.final_guard()),
            &Predicate::True.minus(&keys_predicate(0, KEYS - 1))
        ));
    }

    /// A release of nothing changes neither the cache nor what `final_guard` returns.
    #[test]
    fn a_release_of_nothing_changes_nothing() {
        let mut memo = memo_over(&source(0..10));
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        let before = (
            entries(&memo.cached_tile.read().unwrap()),
            memo.final_guard(),
        );
        memo.release(ints().empty_guard());
        assert_eq!(
            (
                entries(&memo.cached_tile.read().unwrap()),
                memo.final_guard()
            ),
            before
        );
    }

    // ------------------------------------------------------------------------------------
    // What final_guard returns
    // ------------------------------------------------------------------------------------

    /// The final guard of a drained memo is the whole of what it consumed.
    #[test]
    fn final_guard_names_everything_consumed() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        assert_eq!(memo.final_guard(), ints().universal_guard());
    }

    /// A release of a sub-region leaves the rest: the guard excludes exactly the keys released.
    #[test]
    fn final_guard_excludes_what_was_released() {
        let source = source(0..10);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        memo.release(keys_between(2, 3));
        let guard = memo.final_guard();
        assert!(same_region(
            &predicate(&guard),
            &Predicate::True.minus(&keys_predicate(2, 3))
        ));
        assert_eq!(
            entries(&memo.cached_tile.read().unwrap()),
            rows_of([0, 1, 4, 5, 6, 7, 8, 9])
        );
    }

    /// Rows added after a first consume, and consumed, are in the guard; the released keys are
    /// still out of it.
    #[test]
    fn final_guard_includes_rows_added_and_consumed_later_and_still_excludes_released_ones() {
        let source = source(0..6);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, keys_between(0, 5));
        memo.release(keys_between(2, 3));

        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .rows
            .insert(9, value(9));
        memo.consume_in_pipeline(InputId::ONLY, All.guard());

        let guard = keys_of(&memo.final_guard());
        assert_eq!(guard, (0..KEYS).filter(|k| ![2, 3].contains(k)).collect());
        assert!(guard.contains(&9), "the row added later");
        assert_eq!(
            entries(&memo.cached_tile.read().unwrap()),
            rows_of([0, 1, 4, 5, 9])
        );
    }

    /// An input that has stated everything complete and holds no row leaves a cache that states
    /// the universe and holds nothing: its guard is the universe.
    #[test]
    fn final_guard_of_a_memo_over_an_empty_input_is_the_universe() {
        let source = source([]);
        let mut memo = memo_over(&source);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());
        assert!(entries(&memo.cached_tile.read().unwrap()).is_empty());
        assert_eq!(memo.final_guard(), ints().universal_guard());
    }

    /// A cache of outermost keys has no exact difference with a release of a scalar, so
    /// `final_guard` names the gap rather than answering another region.
    #[test]
    #[should_panic(expected = "the guard algebra has no difference")]
    fn guard_minus_of_a_shape_without_a_spelling_panics() {
        let scalar = TileGuard::Scalar(Predicate::qualified(
            Predicate::point(Value::UInt(1)),
            Predicate::True,
        ));
        guard_minus(&ints().universal_guard(), &scalar);
    }

    /// A memo of groups released beneath its keys holds every path of its groups but the ones
    /// released.
    #[test]
    fn a_release_beneath_the_groups_of_a_memo_leaves_the_paths_unreleased() {
        use crate::interpreter::tile_operators::growing::{NestedInput, nested_tiling};
        let mut memo =
            MemoProducer::over(Box::new(NestedInput::over(&source(0..4))), &nested_tiling());
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, nested_tiling().universal_guard());
        let released = TileGuard::Function(FunctionGuard::Codomain(Box::new(Keys(0, 1).guard())));
        memo.release(released.clone());
        let before = Projection::of(&memo.complete()).expect("a region of keys");
        let held = Projection::of(&memo.final_guard()).expect("a region of paths");
        let released = Projection::of(&released).expect("a region of paths");
        assert_eq!(held.level(), Some(CurryLevel::new(1)));
        assert_eq!(held.intersect(&released), Projection::Nothing);
        let rejoined = held.union(&released);
        assert_eq!(
            (rejoined.minus(&before), before.minus(&rejoined)),
            (Projection::Nothing, Projection::Nothing),
            "the paths held and the paths released are what was held"
        );
    }

    /// A memo released beneath its keys, over an open range of positions, holds paths beneath its
    /// outermost keys, and its push of them lands in its reader as a region at their level.
    #[test]
    fn a_push_beneath_the_outermost_keys_lands_at_their_level() {
        use crate::interpreter::tile_operators::growing::{NestedInput, nested_tiling};
        let mut memo =
            MemoProducer::over(Box::new(NestedInput::over(&source(0..4))), &nested_tiling());
        push_to(&mut memo, &[1]);
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, nested_tiling().universal_guard());
        memo.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            Keys(0, 1).guard(),
        ))));
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| pushes.push_final(&memo));
        let crate::interpreter::dispatcher::Next::Package(package) =
            dispatcher.try_claim(Some(PipelineId(1)))
        else {
            panic!("the reader is queued the push")
        };
        let level = Projection::of(&package.guard)
            .expect("a push names a projection")
            .level();
        assert_eq!(level, Some(CurryLevel::new(1)), "{:?}", package.guard);
    }

    /// A memo released position by position through the last position of a row, over a finite
    /// range of positions, holds none of the row's positions, and its final guard names the row's
    /// remainder past them, which states the row's end (`BreakingProducer::final_guard`).
    #[test]
    fn a_row_released_through_its_last_position_keeps_only_its_end() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        use crate::interpreter::{BaseType, ColumnValue, Extent};
        use bit_set::BitSet;
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(2),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // 0 ↦ {0 ↦ 1, 1 ↦ 2}, 1 ↦ {0 ↦ 3, 1 ↦ 4}, every level stated complete.
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let mut memo = MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        );
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        for last in 0..2 {
            memo.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
                TileGuard::Function(FunctionGuard::Domain(Predicate::qualified(
                    Predicate::point(Value::UInt(0)),
                    Predicate::at_or_below(Value::UInt(last)),
                ))),
            ))));
        }
        let row_0 = |here: Predicate| {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                FunctionGuard::Domain(Predicate::qualified(Predicate::point(Value::UInt(0)), here)),
            ))))
        };
        let held = memo.final_guard();
        let positions = row_0(Predicate::at_or_below(Value::UInt(1)));
        assert!(
            held.intersect(&positions).is_empty(),
            "row 0 is released through its last position: {held:?}"
        );
        let end = guard_minus(&row_0(Predicate::True), &positions);
        assert!(
            guard_minus(&end, &held).is_empty(),
            "the final guard names row 0's remainder, its end: {held:?}"
        );
    }

    /// A memo of records released at a key whole and at one field's cells under every key holds
    /// the other keys: the field it still holds there names them (`BreakingProducer::final_guard`).
    #[test]
    fn a_release_of_a_fields_cells_leaves_the_keys_held() {
        use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
        use crate::interpreter::{BaseType, ColumnValue, Extent};
        use bit_set::BitSet;
        let int = || Tiling::Scalar(Extent::Base(BaseType::Int));
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Record(HashMap::from([("_0".into(), int()), ("_1".into(), int())])),
        );
        // 0 ↦ (_0: 1, _1: 3), 1 ↦ (_0: 2, _1: 4).
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Record {
                fields: HashMap::from([
                    ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
                    ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![3, 4]))),
                ]),
                absent: Default::default(),
            }),
            Predicate::True,
            BitSet::new(),
        );
        let mut memo = MemoProducer::over(
            Box::new(TestTileProducer::new(tile, tiling.clone())),
            &tiling,
        );
        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, tiling.universal_guard());
        let first_field = TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(HashMap::from([
                ("_0".into(), TileGuard::Scalar(Predicate::True)),
                ("_1".into(), TileGuard::Scalar(Predicate::False)),
            ])),
        )));
        memo.release(TileGuard::Or(vec![
            TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::UInt(0)))),
            first_field,
        ]));
        let held = Projection::of(&memo.final_guard()).expect("a region of keys");
        let key = |k| Projection::admitting(Predicate::point(Value::UInt(k)));
        assert_eq!(
            held.intersect(&key(0)),
            Projection::Nothing,
            "key 0 is released whole"
        );
        assert_ne!(
            held.intersect(&key(1)),
            Projection::Nothing,
            "key 1 holds field `_1`"
        );
    }

    // ------------------------------------------------------------------------------------
    // Wakes
    // ------------------------------------------------------------------------------------

    /// Notifications reach the consumer once; consuming and finishing publish packages without
    /// sending another notification.
    #[test]
    fn notification_is_delivered_once_and_consumption_publishes_packages() {
        use crate::interpreter::notifications::forwarding_consumer_keeping_keys;

        let woken = Arc::new(Cell::new(0));
        let counted = woken.clone();
        let consumer = shared_consumer(Box::new(move || counted.set(counted.get() + 1)));
        let _cx = SubscribeContext::new();
        let notifier = forwarding_consumer_keeping_keys(&consumer);
        let mut memo = memo_over(&source(0..4));
        memo.base = ProducerBase::unowned(MemoProducer::alloc_id(), &ints());

        notifier.announce(&All.projection());

        assert_eq!(
            woken.get(),
            1,
            "the input's notification reaches the consumer"
        );

        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, All.guard());

        assert_eq!(
            woken.get(),
            1,
            "consumption sends no additional notification"
        );
        memo.get(All.guard());
        push_to(&mut memo, &[1]);
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| memo.finish(InputId::ONLY, pushes));
        assert!(dispatcher.pop().is_some(), "finish pushed a package");
    }

    /// A consumer woken by the input's notification pulls a consuming memo before the driver
    /// consumes the keys notified: it is answered from the rows consumed so far, and the consume
    /// that merges the new rows wakes it no more. The package `finish` pushes announces them.
    #[test]
    fn a_consume_wakes_no_consumer_that_pulled_since_the_notification() {
        use crate::interpreter::notifications::forwarding_consumer_keeping_keys;

        let woken = Arc::new(Cell::new(0));
        let counted = woken.clone();
        let consumer = shared_consumer(Box::new(move || counted.set(counted.get() + 1)));
        let _cx = SubscribeContext::new();
        let notifier = forwarding_consumer_keeping_keys(&consumer);
        let mut memo = memo_over(&source(0..4));
        memo.base = ProducerBase::unowned(MemoProducer::alloc_id(), &ints());

        memo.begin_run();
        memo.consume_in_pipeline(InputId::ONLY, Keys(0, 1).guard());
        notifier.announce(&Keys(2, 3).projection());

        assert_eq!(woken.get(), 1, "the notification wakes the consumer");

        let pulled = memo.get(All.guard());
        assert_eq!(
            entries(&pulled),
            rows_of([0, 1]),
            "the rows consumed so far"
        );

        memo.consume_in_pipeline(InputId::ONLY, Keys(2, 3).guard());

        assert_eq!(woken.get(), 1, "a consuming memo wakes no consumer");
        assert_eq!(
            entries(&memo.get(All.guard())),
            rows_of(0..4),
            "the rows are merged"
        );
    }

    // ------------------------------------------------------------------------------------
    // Interleavings of consumes, releases and new rows
    // ------------------------------------------------------------------------------------

    /// A consuming memo over a growing input, and the model it is held to.
    struct Run {
        consuming: MemoProducer,
        consuming_source: Shared,
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
            let consuming_source = growing_source(initial.iter().copied());
            let mut consuming = memo_over(&consuming_source);
            consuming.begin_run();
            Self {
                consuming,
                consuming_source,
                input: InputModel::new(initial),
                memo_released: Released::default(),
                memo_released_predicate: Predicate::False,
                stated: Predicate::False,
                cache: BTreeSet::new(),
                drained: false,
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        self.consuming_source
                            .write()
                            .unwrap_or_else(PoisonError::into_inner)
                            .rows
                            .insert(key, value(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.consuming_source
                        .write()
                        .unwrap_or_else(PoisonError::into_inner)
                        .closed = true;
                }
                Consume(region) => {
                    self.consuming
                        .consume_in_pipeline(InputId::ONLY, region.guard());
                    if !self.drained && !self.input.released.covers(region) {
                        let (answered, stated) = self.input.pull(region);
                        self.cache.extend(answered);
                        self.stated = self.stated.union(&stated);
                        self.drained = self.input.closed && matches!(region, All);
                        // A consume at keys also releases the consumed keys its cache states
                        // complete, in the one release of what the answer stated.
                        if let Keys(..) = region {
                            let complete = self.stated.intersect(&predicate(&region.guard()));
                            self.input.widen_last_release(&complete);
                        }
                    }
                }
                Release(region) => {
                    self.consuming.release(region.guard());
                    if !self.memo_released.covers(region) {
                        let keys = region.keys();
                        self.cache.retain(|key| !keys.contains(key));
                        self.memo_released.add(region);
                        self.memo_released_predicate = self
                            .memo_released_predicate
                            .union(&predicate(&region.guard()));
                    }
                    // The memo passes every release to its input, a repeat included.
                    self.input.release(region);
                }
            }
        }

        /// The consuming memo and the input against the model.
        fn check(&mut self) {
            let trace = &self.trace;
            assert_eq!(
                entries(&self.consuming.cached_tile.read().unwrap()),
                rows_of(self.cache.iter().copied()),
                "{trace}: the cache"
            );
            self.input.check(&self.consuming_source, trace);
            if self.input.drained() {
                let guard = predicate(&self.consuming.final_guard());
                let expected = self.stated.minus(&self.memo_released_predicate);
                assert!(
                    same_region(&guard, &expected),
                    "{trace}: the final guard is {guard:?}, not what was stated less what was \
                     released {expected:?}"
                );
            }
        }

        /// Close the input, consume everything, and compare what the consuming memo offers at
        /// each region with the modelled cache cut to it.
        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            for region in [All, Keys(0, 3), Keys(4, 7), Keys(2, 9)] {
                let keys = region.keys();
                assert_eq!(
                    entries(&self.consuming.get(region.guard())),
                    rows_of(self.cache.iter().copied().filter(|key| keys.contains(key))),
                    "{}: offer at {region:?}",
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
    use Step::{Add, Close, Consume, Release};

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
            &[Add(2), Consume(Keys(0, 3)), Add(3), Consume(Keys(0, 3))],
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
                let step = rng.step_among(&run.cache);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}

/// A cyclic fan-out's store held in a cell of its own: a pull that re-enters it, and a push
/// through the fan-out.
#[cfg(test)]
mod cycle_tests {
    use super::*;
    use crate::interpreter::dispatcher::{Entry, Landing, PipelineId};
    use crate::interpreter::notifications::SharedConsumer;
    use crate::interpreter::tile_operators::SubscribeContext;
    use crate::interpreter::{BaseType, ColumnValue, Extent};

    fn ints() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    fn int(value: i64) -> Tile {
        Tile::Scalar(ColumnValue::Ints(vec![value]))
    }

    /// What a test shares with a [`StoreDouble`]: the recurrence slot it reads, the consumer
    /// that recurrence slot's subscription notifies, the cycle its fan-out hands it, the
    /// consumer it was subscribed with, and what each of its pulls read of its recurrence.
    #[derive(Default)]
    struct Wiring {
        recurrence: Option<Arc<dyn TileOperator>>,
        inside: Option<Box<dyn Consumer>>,
        cycle: Option<Cycle>,
        own: Option<SharedConsumer>,
        read: Vec<Tile>,
        release_recurrence: bool,
    }

    // shared-state-ok: a test's handle on the double's wiring; no tile passes between
    // operators through it.
    type Wired = Arc<RwLock<Wiring>>;

    /// A store that reads its own fan-out through a recurrence slot on every pull, as a store's
    /// body reads its prior value, and answers `answer`.
    struct StoreDouble {
        base: OperatorBase,
        wiring: Wired,
        answer: Tile,
    }

    impl TileOperator for StoreDouble {
        impl_operator_base!();

        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

        fn subscribe(
            self: Arc<Self>,
            intent_guard: TileGuard,
            consumer: Box<dyn Consumer>,
            cx: &mut SubscribeContext,
        ) -> Box<dyn TileProducer> {
            let own: SharedConsumer = Arc::from(consumer);
            let (recurrence, inside) = {
                let mut wiring = self.wiring.write().unwrap_or_else(PoisonError::into_inner);
                wiring.own = Some(own);
                (
                    wiring
                        .recurrence
                        .take()
                        .expect("a test wires the recurrence slot"),
                    wiring
                        .inside
                        .take()
                        .expect("a test wires the cycle's consumer"),
                )
            };
            let recurrence = recurrence.clone().subscribe(intent_guard, inside, cx);
            Box::new(StoreDoubleProducer {
                base: ProducerBase::new(
                    StoreDoubleProducer::alloc_id(),
                    self.tiling(),
                    self.clone(),
                    cx,
                ),
                wiring: self.wiring.clone(),
                recurrence,
                answer: self.answer.clone(),
            })
        }
    }

    struct StoreDoubleProducer {
        base: ProducerBase,
        wiring: Wired,
        recurrence: Box<dyn TileProducer>,
        answer: Tile,
    }

    impl TileProducer for StoreDoubleProducer {
        impl_producer_base!();

        fn get_impl(&self, _guard: TileGuard) -> Tile {
            let read = self
                .recurrence
                .get(self.recurrence.tiling().universal_guard());
            self.wiring
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .read
                .push(read);
            self.answer.clone()
        }

        fn release_impl(&self, _guard: TileGuard) {
            if self
                .wiring
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .release_recurrence
            {
                self.recurrence
                    .release(self.recurrence.tiling().universal_guard());
            }
        }

        fn enter_cycle(&mut self, cycle: Cycle) {
            self.wiring
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .cycle = Some(cycle);
        }
    }

    /// A cyclic fan-out over a [`StoreDouble`] answering `answer`, whose recurrence slot's
    /// subscription notifies the consumer `inside` builds from the wiring.
    fn cyclic(answer: Tile, inside: impl FnOnce(&Wired) -> Box<dyn Consumer>) -> (FanOut, Wired) {
        let wiring = Wired::default();
        let fan = FanOut::new_cyclic(Arc::new(StoreDouble {
            base: OperatorBase::new(ints()),
            wiring: wiring.clone(),
            answer,
        }));
        let consumer = inside(&wiring);
        {
            let mut wired = wiring.write().unwrap_or_else(PoisonError::into_inner);
            wired.recurrence = Some(fan.recurrence_slot());
            wired.inside = Some(consumer);
        }
        (fan, wiring)
    }

    fn cycle_of(wiring: &Wired) -> Cycle {
        let cycle = wiring
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .cycle
            .take();
        cycle.expect("the fan-out hands its store a cycle when the store is subscribed")
    }

    #[rstest::rstest]
    fn a_final_release_reaches_the_store_even_when_the_last_slot_is_reentrant(
        #[values(false, true)] reentrant_last: bool,
    ) {
        let (fan, wiring) = cyclic(int(2), |_| Box::new(|| {}));
        let mut cx = SubscribeContext::new();
        let whole = ints().universal_guard();
        let reader = fan
            .slot()
            .clone()
            .clone()
            .subscribe(whole.clone(), Box::new(|| {}), &mut cx);
        cycle_of(&wiring).publish(&int(1));
        if reentrant_last {
            reader.release(whole.clone());
        }
        wiring
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release_recurrence = true;
        let store = fan.store().unwrap();
        // A release of the store, even of nothing, releases its recurrence slot under the
        // store's borrow.
        store.write().release(ints().empty_guard());
        // Repeating a release after the borrow ends cannot repair a lost forward.
        reader.release(whole);
        assert!(
            fan.shared
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released
                .is_universal()
        );
        assert!(
            store.read().obsolete_guard().is_universal(),
            "all slots released everything, but the store never received the release"
        );
    }

    #[test]
    fn a_store_borrow_retains_the_reentrant_release() {
        let (fan, wiring) = cyclic(int(2), |_| Box::new(|| {}));
        let mut cx = SubscribeContext::new();
        let whole = ints().universal_guard();
        let reader = fan
            .slot()
            .clone()
            .clone()
            .subscribe(whole.clone(), Box::new(|| {}), &mut cx);
        reader.release(whole.clone());
        wiring
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release_recurrence = true;
        let store = fan.store().unwrap();
        let borrow = store.write();
        // A release of the store, even of nothing, releases its recurrence slot under the
        // store's borrow.
        borrow.release(ints().empty_guard());
        assert!(!borrow.obsolete_guard().is_universal());
        drop(borrow);
        assert!(store.read().obsolete_guard().is_universal());
    }

    #[test]
    fn the_last_read_borrow_settles_the_exact_union_of_pending_releases() {
        use super::growing::{Input, keys_of, source};
        use super::test_helpers::keys_between;

        let source = source(0..10);
        let store = Store::new(Box::new(Input::over(&source)));
        let first = store.read();
        let last = store.read();
        store.release(keys_between(1, 2));
        store.release(keys_between(5, 6));
        assert!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released
                .is_empty()
        );
        drop(first);
        assert!(
            source
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .released
                .is_empty()
        );
        drop(last);
        let released = source.read().unwrap_or_else(PoisonError::into_inner);
        assert_eq!(released.released.len(), 1);
        assert_eq!(
            keys_of(&released.released[0]),
            [1, 2, 5, 6].into_iter().collect()
        );
    }

    /// A pull of the store reads its recurrence slot, which finds the store's cell borrowed and
    /// is answered the snapshot the store published; the completed pull then replaces it.
    #[test]
    fn a_pull_that_re_enters_the_store_reads_the_published_snapshot() {
        let (fan, wiring) = cyclic(int(2), |_| Box::new(|| {}));
        let mut cx = SubscribeContext::new();
        let mut reader =
            fan.slot()
                .clone()
                .subscribe(ints().universal_guard(), Box::new(|| {}), &mut cx);
        cycle_of(&wiring).publish(&int(1));
        assert_eq!(reader.read_in_pipeline(ints().universal_guard()), int(2));
        assert_eq!(
            wiring.read().unwrap_or_else(PoisonError::into_inner).read,
            vec![int(1)]
        );
        assert_eq!(fan.cached_tile(), Some(int(2)));
    }

    /// A push through a cyclic fan-out reaches its reader slots and skips its recurrence slots,
    /// whose operators read the store within its own pipeline.
    #[test]
    fn a_push_through_a_cyclic_fan_out_skips_its_recurrence_slots() {
        let (fan, wiring) = cyclic(int(2), |_| Box::new(Entry::new(PipelineId(2), ints())));
        let mut cx = SubscribeContext::new();
        let _reader = fan.slot().clone().subscribe(
            ints().universal_guard(),
            Box::new(Entry::new(PipelineId(1), ints())),
            &mut cx,
        );
        let own = wiring
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .own
            .clone()
            .expect("the store was subscribed");
        let mut landing = Landing::probe(PipelineId(0));
        crate::interpreter::notifications::notify_shared(
            &own,
            &Projection::Everything,
            &mut landing,
        );
        let reached: Vec<_> = landing
            .arrivals()
            .into_iter()
            .map(|arrival| arrival.pipeline)
            .collect();
        assert_eq!(reached, [PipelineId(1)]);
    }
}

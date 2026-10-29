use crate::interpreter::LockNow;
use bit_set::BitSet;
use intervalsets::{
    Bounding, Interval, IntervalSet,
    ops::{Difference, Intersection},
};
use smol_str::SmolStr;
use std::{
    collections::HashMap,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
};

use super::*;
use crate::ccl::TagMap;
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, NotifyOrSubscribeResult,
    Projection, Scheduler, SharedConsumer, UnionArm, Value, scheduler::shared_consumer,
};

/// Produces a function tile whose domain and codomain both equal `extent`.
///
/// Used to enumerate all values in an extent: the resulting tile maps each
/// element to itself (`identity`)
pub struct IterateExtent {
    /// The extent to iterate over.
    pub extent: Extent,
    /// The tiling — always the one-level `extent → extent`.
    base: OperatorBase,
}

impl IterateExtent {
    pub fn new(extent: Extent) -> Self {
        let tiling = Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone()));
        Self {
            base: OperatorBase::new(tiling),
            extent,
        }
    }

    fn add_all_source_handles(
        extent: &Extent,
        consumer: SharedConsumer,
        scheduler: &mut Scheduler,
    ) {
        // The outermost keys of the extent are a source's keys when the extent is that source's
        // domain, or a restriction of it; inside a record or a union they are not.
        fn outermost_source(
            extent: &Extent,
        ) -> Option<&Arc<Mutex<dyn DataSourceDomainExtentImpl>>> {
            match extent {
                Extent::DataSourceDomain(source) => Some(source),
                Extent::Restricted { base, .. } => outermost_source(base),
                _ => None,
            }
        }
        let outermost = outermost_source(extent);
        extent.for_each_source(&mut |source| {
            let outermost_keys = outermost.is_some_and(|keys| Arc::ptr_eq(keys, source));
            scheduler.add_source_handle(source.clone(), Arc::downgrade(&consumer), outermost_keys);
        });
    }
}

impl TileOperator for IterateExtent {
    impl_operator_base!();

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
    fn visit_inputs_mut(&mut self, _visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {}

    /// A finite range `[0, n)` reads no source, so its rows are cut into morsels by position. A
    /// data-source domain of a source that cuts morsels is a [`LiveSource`] over the source's
    /// yield predicate and keys. Every other extent is read whole.
    fn morsel_source(&self) -> Option<Arc<dyn MorselSource>> {
        if let Extent::DataSourceDomain(source) = &self.extent {
            if !source.lock_wait().cuts_morsels() {
                return None;
            }
            let (ready, keys) = (source.clone(), source.clone());
            return Some(Arc::new(LiveSource::new(
                move || ready.lock_wait().get_yield_predicate(),
                move |region, rows| keys.lock_wait().first_keys_in(region, rows),
            )));
        }
        let Extent::UIntRange(set) = &self.extent else {
            return None;
        };
        let rows = match set.intervals().as_slice() {
            // An empty literal is the range `[0, 0)`.
            [] => 0,
            [one] if one.lval() == Some(&0) => one.rval()?.checked_add(1)?,
            _ => return None,
        };
        Some(Arc::new(RangeSource::new(rows)))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let NotifyOrSubscribeResult { notify, subscribe } =
            self.extent.subscribe_to_iteration_action();
        if notify {
            consumer.notify(&Projection::Everything);
        }
        // The producer owns the registration: the scheduler holds only a `Weak`, so this
        // handle is what keeps the source waking this producer, and dropping the producer
        // deregisters it.
        let (source_wakeup, gate) = subscribe.then(|| shared_consumer(consumer)).unzip();
        let mut producer = Box::new(IterateExtentProducer {
            base: ProducerBase::new(
                IterateExtentProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            extent: self.extent.clone(),
            released: Predicate::False,
            _source_wakeup: source_wakeup.as_ref().map(|w| w.shared().clone()),
            shared_release_record: scheduler.pooled_release_record_for(self.operator_id()),
        });
        if let Some(source_wakeup) = source_wakeup {
            Self::add_all_source_handles(&self.extent, source_wakeup.shared().clone(), scheduler);
            let name = producer.releaser();
            // Register this producer with any data sources in the extent by calling release with
            // a false predicate.  This way the sources knows about all producers that read it
            //before execution starts.
            release_extent(&mut producer.extent, &Predicate::False, &name);
            scheduler.note_source_producer(name);
        }

        producer
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Tell every source in `extent` that `producer` is gone, so its release record
/// goes with it ([`DataSourceDomainExtentImpl::retire_producer`]).
fn retire_producer_from_extent(extent: &Extent, producer: &str) {
    extent.for_each_source(&mut |source| {
        // A drop runs wherever the last owner goes, so the source may already
        // be locked by a call further up that stack. Keeping the record is
        // the conservative outcome, the source retaining more than it must,
        // and the lock succeeding is the case worth knowing about.
        match source.try_lock_now() {
            Some(mut source) => source.retire_producer(producer),
            None => debug_assert!(
                false,
                "{producer} dropped while its source was locked, so its \
release record outlives it",
            ),
        }
    });
}

/// The positions `[0, rows)` of an [`IterateExtent`], claimed as morsels by advancing one
/// cursor.
pub(crate) struct RangeSource {
    rows: u64,
    /// The first position not yet claimed. It only grows, to at most `rows`.
    next: AtomicU64,
}

impl RangeSource {
    pub(crate) fn new(rows: u64) -> Self {
        Self {
            rows,
            next: AtomicU64::new(0),
        }
    }
}

impl MorselSource for RangeSource {
    fn claim(&self, rows: u64) -> Claim {
        let rows = rows.max(1);
        // Acquire-release, as `MorselSource::claim` requires: the update that answers
        // `Exhausted` reads the update that answered the last morsel. The data a worker reads
        // under a guard comes from its own chain.
        let Ok(first) = self
            .next
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |first| {
                (first < self.rows).then(|| first.saturating_add(rows).min(self.rows))
            })
        else {
            return Claim::Exhausted;
        };
        let last = first.saturating_add(rows).min(self.rows) - 1;
        Claim::Morsel(positions(first, last))
    }
}

/// The guard naming the positions `[first, last]` of the outermost collection.
fn positions(first: u64, last: u64) -> TileGuard {
    TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
        IntervalSet::from(Interval::closed(Value::UInt(first), Value::UInt(last))),
    )))
}

/// The keys of a source that receives rows, claimed as morsels from the region published so far.
/// Keys arrive in any order and are any totally ordered values.
///
/// The source's yield predicate, `ready`, is the region of keys whose rows are ready to read. For
/// a data-source domain it is also the completeness an `IterateExtent` states: a key outside
/// `ready` may arrive later, and no further key arrives inside it. A publish names a region of
/// `ready`, which `Everything` is resolved to, and the source adds it to `pending`, less what was
/// claimed before, so a region published twice is claimed once and a key that is not ready is
/// never claimed. A claim asks the source for the first `rows` keys of `pending` in key order
/// (`first_keys`) and claims the keys from the first to the last that `pending` names, so a morsel
/// holds exactly those keys when the keys are sparse. `pending` and `claimed` live under the live
/// source's state lock, which makes the claims a total order: the claim that answers `Exhausted`
/// follows every claim that answered a morsel. The state lock is taken before the data source's
/// `Mutex`, which `ready` and `first_keys` read. `claimed` grows with the keys claimed, and a
/// claim does work in proportion to the keys the source holds: known costs, not addressed.
pub struct LiveSource {
    // shared-state-ok: the keys published and claimed, which name morsels and hold no
    // tile. One lock orders every claim, which the finish rule of the dispatcher relies on.
    state: Mutex<LiveState>,
    /// The yield predicate, read when a region is published.
    ready: Box<dyn Fn() -> Predicate + Send + Sync>,
    /// The first keys of a region, in key order: the source's own, since it knows its keys.
    first_keys: FirstKeys,
}

/// A source's answer for the first `rows` keys of a region, in key order.
type FirstKeys = Box<dyn Fn(&Predicate, u64) -> Vec<Value> + Send + Sync>;

struct LiveState {
    /// Published and not claimed.
    pending: Predicate,
    /// Claimed.
    claimed: Predicate,
    closed: bool,
}

impl LiveSource {
    /// A source whose keys are the ones `ready()` names, a region that only grows as rows are
    /// appended, in any order. `first_keys(region, rows)` answers the first `rows` keys of
    /// `region` that the source holds, in key order. `Everything` published to the source means
    /// every key in `ready`, not every key of the source's extent. The thread that appends a row
    /// writes it and adds its key to `ready`, then publishes the region that names it, and
    /// `close` follows the last publish. That thread holds no lock that `ready` or `first_keys`
    /// takes while it publishes, since `publish` calls `ready` and the cascade that reached
    /// `publish` may hold others. `claim` calls `first_keys` holding the source's own lock.
    pub fn new(
        ready: impl Fn() -> Predicate + Send + Sync + 'static,
        first_keys: impl Fn(&Predicate, u64) -> Vec<Value> + Send + Sync + 'static,
    ) -> Self {
        Self {
            state: Mutex::new(LiveState {
                pending: Predicate::False,
                claimed: Predicate::False,
                closed: false,
            }),
            ready: Box::new(ready),
            first_keys: Box::new(first_keys),
        }
    }

    /// The keys claimed so far.
    #[cfg(test)]
    pub fn claimed(&self) -> Predicate {
        self.state.lock_wait().claimed.clone()
    }
}

impl MorselSource for LiveSource {
    fn claim(&self, rows: u64) -> Claim {
        let rows = rows.max(1);
        let mut state = self.state.lock_wait();
        let idle = |state: &LiveState| match state.closed {
            true => Claim::Exhausted,
            false => Claim::Idle,
        };
        if state.pending.is_false() {
            return idle(&state);
        }
        let keys = (self.first_keys)(&state.pending, rows);
        let (Some(first), Some(last)) = (keys.first(), keys.last()) else {
            // The region names no key the source holds, so there is nothing to claim in it: a
            // yield predicate that covers keys which will not arrive says so.
            state.claimed = state.claimed.union(&state.pending);
            state.pending = Predicate::False;
            return idle(&state);
        };
        let morsel = Predicate::intervals(IntervalSet::from(Interval::closed(
            first.clone(),
            last.clone(),
        )))
        .intersect(&state.pending);
        debug_assert!(
            state.claimed.intersect(&morsel).is_false(),
            "a morsel is disjoint from the keys claimed before it"
        );
        state.pending = state.pending.minus(&morsel);
        state.claimed = state.claimed.union(&morsel);
        Claim::Morsel(TileGuard::Function(FunctionGuard::Domain(morsel)))
    }

    fn publish(&self, arrived: &Projection) {
        let ready = (self.ready)();
        let region = match arrived {
            Projection::Nothing => return,
            // A region of fields names where a change is in a record, and a source's pending
            // region is keys: the keys that are ready are the region that is safe to name.
            Projection::Everything | Projection::Fields(_) => ready,
            Projection::Keys(keys) => {
                assert!(
                    keys.minus(&ready).is_false(),
                    "the rows of {keys:?} are ready before their region is published, and \
                     {ready:?} is ready"
                );
                keys.clone()
            }
        };
        let mut state = self.state.lock_wait();
        let unclaimed = region.minus(&state.claimed);
        debug_assert!(
            !state.closed || unclaimed.is_false(),
            "a closed source is published to only what was claimed already"
        );
        state.pending = state.pending.union(&unclaimed);
    }

    fn close(&self) {
        self.state.lock_wait().closed = true;
    }
}

/// Producer for [`IterateExtent`]: emits an identity function tile.
struct IterateExtentProducer {
    base: ProducerBase,
    /// The extent being iterated.
    ///
    /// For `UIntRange` extents this is an `IntervalSet<u64>` that shrinks
    /// directly as sub-intervals are released.
    extent: Extent,
    /// Accumulates every predicate that has been released so far.
    ///
    /// Used for pair-level filtering in `get_impl`: after `iterate_extent`
    /// produces the cross-product, any row whose domain value satisfies this
    /// predicate is removed before returning the tile.  This is necessary for
    /// `Extent::Record` cross-products where individual source extents cannot
    /// be safely shrunk (shrinking source2's key 0 would prevent future
    /// cross-product pairs like (1, 0) from ever being produced).
    released: Predicate,
    /// The wake-up this producer registered with the scheduler, which holds only
    /// a `Weak` to it.
    ///
    /// Owning it here ties the registration's lifetime to the producer's: a
    /// producer carried across a program reload keeps waking, and one the reload
    /// dropped is pruned on the next
    /// [`check_for_notifications`](Scheduler::check_for_notifications).
    /// `None` when the extent needs no source subscription.
    _source_wakeup: Option<Arc<Mutex<dyn Consumer>>>,
    /// The name the producer holds its release record under, when it is not its own: the
    /// identity the pool gives every worker's chain, so a source sees one reader of the
    /// pipeline and not one per worker
    /// (`src/interpreter/design-parallel.md`, "A pool owns its pipeline's release record").
    shared_release_record: Option<String>,
}

impl IterateExtentProducer {
    /// The name the source knows this producer by: where its releases and its elements are
    /// recorded.
    fn releaser(&self) -> String {
        self.shared_release_record
            .clone()
            .unwrap_or_else(|| self.name())
    }
}

fn get_iterate_extent_predicate(extent: &Extent) -> Predicate {
    match extent {
        Extent::DataSourceDomain(source) => source.lock_wait().get_yield_predicate(),
        // For a cross-product, the domain_predicate must be the conjunction (AND / Record) of
        // each field's predicate.  Only pairs where EVERY field's value has already been
        // committed by its source can be guaranteed to have already been delivered; a pair
        // where even one field comes from a source that can still grow might be new next time.
        //
        // An OR would over-claim: e.g. arm {_1:≤u0, _0:True} says "(x,0) for any x has
        // already been seen", but if source0 later adds key 1 then (1,0) is genuinely new.
        Extent::Record(fields) => Predicate::Record(
            fields
                .iter()
                .map(|(f, e)| (f.clone(), get_iterate_extent_predicate(e)))
                .collect(),
        ),
        // For a disjoint union, each variant contributes its own predicate over
        // its own tag; the arms stay keyed by tag so a downstream consumer can
        // split per-variant releases back to their source sub-extents by name
        // rather than relying on two arm vectors staying in the same order.
        Extent::Union(arms) => {
            Predicate::over_every_tag(arms.map(|_, e| get_iterate_extent_predicate(e)))
        }
        _ => Predicate::True,
    }
}

/// Convert a `IntervalSet<Value::UInt>` values into an
/// `IntervalSet<u64>`, preserving bound types.
///
/// Discrete `Value` intervals are normalised to closed form by `intervalsets`,
/// so the resulting `u64` intervals are also closed.
fn predicate_intervals_to_u64(intervals: &IntervalSet<Value>) -> IntervalSet<u64> {
    IntervalSet::from_iter(intervals.intervals().iter().map(|iv| {
        // Left-unbounded intervals (e.g. (-∞, 3]) are clamped to [0, r] since
        // UIntRange indices are always non-negative.
        let left: u64 = iv.lval().map_or(0, |v| v.as_uint());
        match iv.rval() {
            Some(r) => Interval::closed(left, r.as_uint()),
            None => Interval::closed_unbound(left),
        }
    }))
}

/// Release values from `extent` that are covered by `pred`.
///
/// For [`Extent::UIntRange`] extents, released sub-intervals are subtracted
/// directly from the stored [`IntervalSet<u64>`], so arbitrary non-contiguous
/// releases are handled without any external accumulator.
fn release_extent(extent: &mut Extent, pred: &Predicate, releaser: &str) {
    match extent {
        Extent::Record(fields) => match pred {
            p if p.as_bool().is_some_and(|p| p) => {
                for e in fields.values_mut() {
                    release_extent(e, &Predicate::True, releaser);
                }
            }
            p if p.as_bool().is_some_and(|p| !p) => {
                for e in fields.values_mut() {
                    release_extent(e, &Predicate::False, releaser);
                }
            }
            // Or: apply each arm independently.  Each arm describes a distinct
            // sub-region; releasing all arms releases their union.
            Predicate::Or(arms) => {
                for arm in arms {
                    release_extent(extent, arm, releaser);
                }
            }
            p => {
                // A Record predicate is a conjunction: {f0: p0, f1: p1} means
                // "release pairs where p0(f0) AND p1(f1)".  We can only safely
                // advance a dimension's extent when all other dimensions are
                // unconstrained (Predicate::True), because the AND means the
                // full cross-product sub-space is released along that axis.
                let field_preds = p.split_record(fields);
                for (f, e) in fields.iter_mut() {
                    let others_all_true = field_preds
                        .iter()
                        .all(|(k, p)| k == f || *p == Predicate::True);
                    if others_all_true {
                        release_extent(e, &field_preds[f], releaser);
                    } else {
                        // TODO: handle the case where multiple fields have
                        // non-trivial predicates; requires releasing the
                        // intersection of projected ranges per dimension.
                    }
                }
            }
        },
        Extent::DataSourceDomain(source) => {
            source.lock_wait().release(releaser, pred.clone());
        }
        Extent::UIntRange(remaining) => match pred {
            Predicate::True => {
                *remaining = IntervalSet::from(Interval::<u64>::empty());
            }
            Predicate::False => {}
            Predicate::Intervals(intervals) => {
                // Subtract the released sub-intervals directly from the remaining set.
                let to_remove = predicate_intervals_to_u64(intervals);
                *remaining = remaining.difference(&to_remove);
            }
            _ => todo!("Got {pred:?} for UIntRange"),
        },
        Extent::Base(BaseType::Unit) => {}
        Extent::Union(ext_arms) => match pred {
            p if p.as_bool().is_some_and(|p| p) => {
                for (_, e) in ext_arms.iter_mut() {
                    release_extent(e, &Predicate::True, releaser);
                }
            }
            p if p.as_bool().is_some_and(|p| !p) => {
                for (_, e) in ext_arms.iter_mut() {
                    release_extent(e, &Predicate::False, releaser);
                }
            }
            // A Union predicate pairs with the extent's arms **by tag**, so each
            // arm releases its own sub-extent. Pairing positionally would release
            // the wrong sub-extent whenever the predicate covers a different tag
            // set than the extent — which width subtyping makes legal.
            Predicate::Union { .. } => {
                for (tag, e) in ext_arms.iter_mut() {
                    // A tag the predicate does not name releases what its `rest` says.
                    let arm = pred
                        .under_tag(tag)
                        .unwrap_or_else(|| unreachable!("matched as a union predicate"));
                    release_extent(e, &arm, releaser);
                }
            }
            _ => todo!("Got {pred:?} for Union extent"),
        },
        _ => panic!("Unexpected extent: {extent:?}"),
    }
}

/// Produce all values for the given extent.
fn iterate_extent(extent: &Extent, producer: &str) -> ColumnValue {
    match extent {
        Extent::Base(BaseType::Unit) => ColumnValue::Units(1),
        Extent::UIntRange(remaining) => {
            // Discrete intervals are normalised to closed bounds, so iterate
            // each [a, b] as a..=b to produce all remaining indices.
            let values: Vec<u64> = remaining
                .intervals()
                .iter()
                .flat_map(|iv| {
                    let left = *iv
                        .lval()
                        .expect("UIntRange: unexpected left-unbounded interval");
                    let right = *iv
                        .rval()
                        .expect("UIntRange: unexpected right-unbounded interval");
                    left..=right
                })
                .collect();
            ColumnValue::from_uints(values)
        }
        Extent::DataSourceDomain(source_impl) => source_impl.lock_wait().get_elements(producer),
        Extent::Record(fields) => iterate_record(fields, producer),
        Extent::Union(arms) => iterate_union(arms, producer),
        Extent::Restricted { .. } => {
            panic!("Iterating over restricted extents not supported; use Filter operators instead")
        }
        other => panic!("Attempted to iterate on infinite Extent: {other:?}"),
    }
}

/// Iterate an [`Extent::Union`] by enumerating each arm in turn, laying the arms
/// out in tag order so each occupies a contiguous run of rows.
fn iterate_union(ext_arms: &TagMap<Extent>, producer: &str) -> ColumnValue {
    let mut next_row = 0usize;
    let arms = ext_arms.map(|_, ext| {
        let values = iterate_extent(ext, producer);
        let rows: Vec<usize> = (next_row..next_row + values.len()).collect();
        next_row += values.len();
        UnionArm::new(rows, values)
    });
    let cv = ColumnValue::Union(arms);
    cv.debug_assert_union_invariants();
    cv
}

fn iterate_record(fields: &HashMap<SmolStr, Extent>, producer: &str) -> ColumnValue {
    let data: HashMap<SmolStr, ColumnValue> = fields
        .iter()
        .map(|(field, field_extent)| (field.clone(), iterate_extent(field_extent, producer)))
        .collect();
    ColumnValue::cartesian_product(data)
}

impl Drop for IterateExtentProducer {
    /// Hand back the release record this producer registered.
    ///
    /// The record has to last exactly as long as the producer: a source outlives
    /// every version reading it, and its release agreement is an intersection
    /// over the records it holds, so one left behind pins that agreement where a
    /// dropped producer stopped. Dropping it here rather than at the version
    /// handover is what distinguishes the two cases — an operator the reload
    /// rebuilt goes and takes its record with it, and one the reload carried
    /// forward keeps both, which is what stops the source dropping data that
    /// operator has not finished with.
    fn drop(&mut self) {
        // A record under a pool's name belongs to the pool, which retires it once its chains are
        // gone: the first chain to drop must not take the others' record with it.
        if self.shared_release_record.is_none() {
            retire_producer_from_extent(&self.extent, &self.name());
        }
    }
}

impl TileProducer for IterateExtentProducer {
    impl_producer_base!();

    /// The extent's positions inside the projection. A finite range and a data-source domain
    /// are cut before they are rendered, so a morsel costs the morsel's size; every other extent
    /// renders whole and is cut after, since a cross product's keys are not an interval of
    /// positions.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let extent = match (&self.extent, &projection) {
            (Extent::UIntRange(remaining), Projection::Keys(Predicate::Intervals(admitted))) => {
                Extent::UIntRange(remaining.intersection(&predicate_intervals_to_u64(admitted)))
            }
            (extent, _) => extent.clone(),
        };
        // The completeness is read before the rows: a key that arrives between the two reads is
        // in the tile and outside the statement, and the other order states complete a region
        // whose key the tile lacks.
        let domain_predicate = get_iterate_extent_predicate(&extent);
        // A data-source domain is cut to the morsel before it is rendered, by the source.
        let values = match (&extent, &projection) {
            (Extent::DataSourceDomain(source), Projection::Keys(admitted)) => {
                source.lock_wait().elements_in(&self.releaser(), admitted)
            }
            _ => iterate_extent(&extent, &self.releaser()),
        };
        let mut tile = Tile::data_function(
            values.clone(),
            Box::new(Tile::Scalar(values)),
            domain_predicate,
            BitSet::new(),
        );
        tile.restrict_to(&projection, self.tiling());
        // Filter out any domain rows that have already been released.
        // Values may also be removed from underlying sources for efficiency, but
        // this filter here is ultimately responsible for not returning released data.
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(
            self.released.clone(),
        )));
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let name = self.releaser();
        let TileGuard::Function(FunctionGuard::Domain(pred)) = obsolete_guard else {
            panic!("IterateExtent::release expected Domain guard, got {obsolete_guard:?}")
        };
        // Accumulate so get_impl can filter already-released rows.
        self.released = self.released.union(&pred);
        // Also propagate to sub-extents where safe (e.g. full-slice UIntRange
        // shrinks, or single-dimension DataSourceDomain releases when all other
        // dimensions are unconstrained).
        release_extent(&mut self.extent, &pred, &name);
    }
}

/// The positions `[first, last]` as a region of keys.
#[cfg(test)]
pub(crate) fn uint_range(first: u64, last: u64) -> Predicate {
    Predicate::intervals(IntervalSet::from(Interval::closed(
        Value::UInt(first),
        Value::UInt(last),
    )))
}

/// The region naming exactly `keys`, as one set of intervals, so that adjacent keys are one
/// interval and a union of two such regions stays canonical.
#[cfg(test)]
pub(crate) fn points(keys: &[Value]) -> Predicate {
    Predicate::intervals(IntervalSet::from_iter(
        keys.iter()
            .map(|key| Interval::closed(key.clone(), key.clone())),
    ))
}

/// The first `rows` positions of `region`, which names closed ranges of positions: what a test
/// source of dense positions answers for [`LiveSource`].
#[cfg(test)]
pub(crate) fn uint_keys_in(region: &Predicate, rows: u64) -> Vec<Value> {
    let Predicate::Intervals(set) = region else {
        return Vec::new();
    };
    set.intervals()
        .iter()
        .flat_map(|interval| match (interval.lval(), interval.rval()) {
            (Some(Value::UInt(first)), Some(Value::UInt(last))) => *first..=*last,
            other => panic!("a closed range of positions, got {other:?}"),
        })
        .take(usize::try_from(rows).unwrap_or(usize::MAX))
        .map(Value::UInt)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value, tuple_field};
    use intervalsets::MaybeEmpty;
    use intervalsets::ops::Contains;

    /// A producer's release record is retired from a source reached through a
    /// `Union` arm, not only from one reached directly or through a `Record`.
    ///
    /// Subscribing registers the record through every compound arm
    /// ([`release_extent`]), so retiring has to reach the same set. A record
    /// left behind pins the source's agreement at wherever the dead producer
    /// stopped, and the source never drops that data again.
    #[test]
    fn retire_reaches_a_source_under_a_union_arm() {
        use crate::ccl::FieldKey;
        use crate::interpreter::{DataSourceDomainExtentImpl, test_source::TestDataSource};

        let src = Arc::new(Mutex::new(TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let as_domain: Arc<Mutex<dyn DataSourceDomainExtentImpl>> = src.clone();
        let extent = Extent::Union(TagMap::from_arms(vec![(
            FieldKey::Name("only".into()),
            Extent::DataSourceDomain(as_domain),
        )]));

        src.lock_now().release("p", Predicate::True);
        assert_eq!(
            src.lock_now().get_released_predicate(),
            Predicate::True,
            "`p` holds a record for the retire to find"
        );

        retire_producer_from_extent(&extent, "p");

        assert_eq!(
            src.lock_now().get_released_predicate(),
            Predicate::False,
            "`p` is gone, so its record is gone: an empty agreement, not `p`'s last one"
        );
    }

    /// Helper: extract the `IntervalSet<u64>` from a `UIntRange` extent.
    fn uint_range_set(extent: &Extent) -> &IntervalSet<u64> {
        let Extent::UIntRange(s) = extent else {
            panic!("expected UIntRange, got {extent:?}");
        };
        s
    }

    /// `Predicate::True` releases everything — extent becomes empty.
    #[test]
    fn release_extent_predicate_true_clears_uint_range() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &Predicate::True, "");
        assert!(
            uint_range_set(&extent).is_empty(),
            "True release should empty the extent"
        );
    }

    /// `Predicate::False` releases nothing — extent is unchanged.
    #[test]
    fn release_extent_predicate_false_is_noop() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &Predicate::False, "");
        let s = uint_range_set(&extent);
        for i in 0..5u64 {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::at_or_below(v)` releases [0, v] inclusive.
    #[test]
    fn release_extent_at_or_below_releases_prefix() {
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &Predicate::at_or_below(Value::UInt(4)), "");
        let s = uint_range_set(&extent);
        for i in 0..=4u64 {
            assert!(!s.contains(&i), "{i} should be released");
        }
        for i in 5..10u64 {
            assert!(s.contains(&i), "{i} should remain");
        }
    }

    /// `Predicate::Intervals` with only bounded intervals subtracts each one.
    #[test]
    fn release_extent_bounded_intervals_predicate() {
        // Release {2, 3} ∪ {7} from [0, 9].
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3, 7]));
        let mut extent = Extent::uint_range(10);
        release_extent(&mut extent, &p, "");
        let s = uint_range_set(&extent);
        assert!(!s.contains(&2u64), "2 should be released");
        assert!(!s.contains(&3u64), "3 should be released");
        assert!(!s.contains(&7u64), "7 should be released");
        for i in [0, 1, 4, 5, 6, 8, 9u64] {
            assert!(s.contains(&i), "{i} should remain");
        }
    }

    /// `Predicate::Intervals` with a right-unbounded interval (e.g. [5, +∞))
    /// releases everything from 5 to the end of the extent.
    #[test]
    fn release_extent_right_unbounded_intervals_predicate() {
        // Everything not at or below 4: [5, +∞).
        let p = Predicate::True.minus(&Predicate::at_or_below(Value::UInt(4)));
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");
        let s = uint_range_set(&extent);
        for i in 0..5u64 {
            assert!(s.contains(&i), "{i} should remain");
        }
        for i in 5..10u64 {
            assert!(!s.contains(&i), "{i} should be released");
        }
    }

    /// A prefix release unioned with a later point subtracts both from the `UIntRange`
    /// extent: `[0, 3] ∪ {7}`.
    #[test]
    fn release_extent_prefix_and_point_predicate() {
        let p = Predicate::at_or_below(Value::UInt(3))
            .union(&Predicate::from_column_value(&ColumnValue::UInts(vec![7])));

        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");

        // After releasing [0, 3] ∪ {7}, remaining should be {4, 5, 6, 8, 9}.
        let Extent::UIntRange(ref remaining) = extent else {
            panic!("expected UIntRange");
        };
        assert!(!remaining.contains(&0u64), "0 should be released");
        assert!(!remaining.contains(&3u64), "3 should be released");
        assert!(remaining.contains(&4u64), "4 should remain");
        assert!(!remaining.contains(&7u64), "7 should be released");
        assert!(remaining.contains(&9u64), "9 should remain");
    }

    /// A finite range pulled at an interval renders that interval and calls it complete; a
    /// key released earlier is absent from a later interval that overlaps it.
    #[test]
    fn a_finite_range_renders_the_admitted_interval() {
        let extent = Extent::uint_range(10);
        let tiling = Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone()));
        let mut producer = IterateExtentProducer {
            base: ProducerBase::unowned(0, &tiling),
            extent,
            released: Predicate::False,
            _source_wakeup: None,
            shared_release_record: None,
        };
        let interval = |first: u64, last: u64| {
            let at_or_below = |v: u64| Predicate::at_or_below(Value::UInt(v));
            TileGuard::Function(FunctionGuard::Domain(match first {
                0 => at_or_below(last),
                _ => at_or_below(last).minus(&at_or_below(first - 1)),
            }))
        };
        let keys_of = |tile: &Tile| match tile {
            Tile::DataFunction { domain, .. } => domain.clone(),
            other => panic!("a collection, got {other:?}"),
        };
        let first = producer.get(interval(0, 4));
        assert_eq!(
            keys_of(&first),
            ColumnValue::from_uints(vec![0, 1, 2, 3, 4])
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &first
        else {
            unreachable!()
        };
        assert!(domain_predicate.contains(&Value::UInt(4)));
        assert!(!domain_predicate.contains(&Value::UInt(5)));
        producer.release(interval(0, 4));
        let overlapping = producer.get(interval(3, 7));
        assert_eq!(
            keys_of(&overlapping),
            ColumnValue::from_uints(vec![5, 6, 7])
        );
    }

    #[test]
    fn iterate_extent_fragmented_uint_range() {
        // Simulate [0,5) with indices 1,2,3 already released → {[0,0],[4,4]}
        let mut extent = Extent::uint_range(5);
        // release [1,3]
        if let Extent::UIntRange(ref mut set) = extent {
            let to_remove = IntervalSet::from(Interval::closed(1u64, 3u64));
            *set = set.difference(&to_remove);
        }
        let tiling = Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone()));
        let mut producer = IterateExtentProducer {
            base: ProducerBase::unowned(0, &tiling),
            extent,
            released: Predicate::False,
            _source_wakeup: None,
            shared_release_record: None,
        };
        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::DataFunction { domain, .. } = tile else {
            panic!()
        };
        let ColumnValue::UInts(vals) = domain else {
            panic!()
        };
        assert_eq!(vals, vec![0, 4]);
    }

    #[test]
    fn iterate_extent_predicate_with_record() {
        // Test that get_iterate_extent_predicate generates correct OR predicates for records
        //
        // When iterating over a record extent with multiple fields, the predicate
        // should be the union of field-specific predicates (one predicate per field
        // with that field's predicate true and others true, then OR'd together).

        // Create a test extent with a record of base types
        let extent = Extent::Record(
            [
                (tuple_field(0), Extent::Base(BaseType::UInt)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        );

        let predicate = get_iterate_extent_predicate(&extent);

        // For a record extent with base-type fields, the predicate should be
        // a union of field predicates. Since each field's predicate is True
        // for base types, the resulting Record predicates are all identical
        // {_0: True, _1: True} and may collapse.
        match predicate {
            Predicate::Record(fields) => {
                // When two identical record predicates with all True union,
                // they may collapse to a single Record
                assert_eq!(fields.len(), 2, "Record should have 2 fields");
                assert_eq!(
                    fields.get(&tuple_field(0)),
                    Some(&Predicate::True),
                    "_0 field should be True"
                );
                assert_eq!(
                    fields.get(&tuple_field(1)),
                    Some(&Predicate::True),
                    "_1 field should be True"
                );
            }
            Predicate::True => {
                // Also accept True if all record fields are True
            }
            Predicate::Or(preds) => {
                // Or accept OR if it wasn't simplified
                assert!(!preds.is_empty(), "OR predicate should have terms");
                for pred in &preds {
                    match pred {
                        Predicate::Record(fields) => {
                            assert_eq!(fields.len(), 2, "Record predicate should have all fields");
                        }
                        _ => panic!("Expected Record predicates in OR, got {pred:?}"),
                    }
                }
            }
            other => panic!("Unexpected predicate for record extent with base types: {other:?}"),
        }
    }

    /// The `[first, last]` a morsel's guard names.
    fn bounds(guard: &TileGuard) -> (u64, u64) {
        let TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(set))) = guard else {
            panic!("a morsel is a domain interval, got {guard:?}");
        };
        let [interval] = set.intervals().as_slice() else {
            panic!("a morsel is one interval, got {set:?}");
        };
        match (interval.lval(), interval.rval()) {
            (Some(Value::UInt(first)), Some(Value::UInt(last))) => (*first, *last),
            other => panic!("a closed range of positions, got {other:?}"),
        }
    }

    #[test]
    fn a_range_source_claims_disjoint_morsels_and_then_none() {
        let source = RangeSource::new(10);
        let claimed: Vec<_> = std::iter::from_fn(|| source.claim(4).morsel())
            .map(|guard| bounds(&guard))
            .collect();
        assert_eq!(claimed, [(0, 3), (4, 7), (8, 9)]);
        assert!(
            matches!(source.claim(4), Claim::Exhausted),
            "exhausted is final"
        );
        assert!(
            matches!(source.claim(1), Claim::Exhausted),
            "whatever size is asked"
        );
    }

    /// The keys a live source holds and the region of them that is ready to read, which a test
    /// advances as rows arrive.
    #[derive(Clone)]
    struct Held {
        keys: Arc<Mutex<Vec<Value>>>,
        ready: Arc<Mutex<Predicate>>,
    }

    impl Default for Held {
        fn default() -> Self {
            Self {
                keys: Arc::default(),
                ready: Arc::new(Mutex::new(Predicate::False)),
            }
        }
    }

    impl Held {
        fn source(&self) -> LiveSource {
            let (ready, keys) = (self.ready.clone(), self.keys.clone());
            LiveSource::new(
                move || ready.lock_wait().clone(),
                move |region, rows| {
                    keys.lock_wait()
                        .iter()
                        .filter(|key| region.contains(key))
                        .take(usize::try_from(rows).unwrap_or(usize::MAX))
                        .cloned()
                        .collect()
                },
            )
        }

        /// Write `keys` in key order.
        fn write(&self, keys: &[Value]) {
            let mut held = self.keys.lock_wait();
            held.extend(keys.iter().cloned());
            held.sort_by(|a, b| a.partial_cmp(b).expect("keys of one type compare"));
            held.dedup();
        }

        /// `keys` are written and ready, and their region is published.
        fn arrive(&self, source: &LiveSource, keys: &[Value]) {
            self.write(keys);
            {
                let mut ready = self.ready.lock_wait();
                *ready = ready.union(&points(keys));
            }
            source.publish(&Projection::admitting(points(keys)));
        }

        /// The positions `[first, last]` arrive.
        fn arrive_positions(&self, source: &LiveSource, first: u64, last: u64) {
            self.arrive(source, &(first..=last).map(Value::UInt).collect::<Vec<_>>());
        }

        /// `rows` further positions arrive after the ones that did, in order.
        fn arrive_next(&self, source: &LiveSource, rows: u64) -> (u64, u64) {
            let first = match self.keys.lock_wait().last() {
                Some(Value::UInt(last)) => last + 1,
                _ => 0,
            };
            self.arrive_positions(source, first, first + rows - 1);
            (first, first + rows - 1)
        }
    }

    /// The keys a guard names among `keys`.
    fn named(guard: &TileGuard, keys: &[Value]) -> Vec<Value> {
        let TileGuard::Function(FunctionGuard::Domain(region)) = guard else {
            panic!("a morsel is a domain region, got {guard:?}");
        };
        keys.iter()
            .filter(|k| region.contains(k))
            .cloned()
            .collect()
    }

    fn int(n: i64) -> Value {
        Value::Int(n)
    }

    fn string(s: &str) -> Value {
        Value::String(s.into())
    }

    /// A live source hands out only what was published, in morsels of at most the asked size,
    /// and is `Idle` while open with nothing pending.
    #[test]
    fn a_live_source_claims_only_what_was_published() {
        let held = Held::default();
        let source = held.source();
        assert!(matches!(source.claim(4), Claim::Idle));
        held.arrive_next(&source, 6);
        assert_eq!(bounds(&source.claim(4).morsel().expect("a morsel")), (0, 3));
        assert_eq!(bounds(&source.claim(4).morsel().expect("a morsel")), (4, 5));
        assert!(
            matches!(source.claim(4), Claim::Idle),
            "open, nothing pending"
        );
        held.arrive_next(&source, 2);
        assert_eq!(bounds(&source.claim(4).morsel().expect("a morsel")), (6, 7));
    }

    /// A region published twice is claimed once, as an `Everything` that covers rows already
    /// published publishes them again.
    #[test]
    fn a_region_published_twice_is_claimed_once() {
        let held = Held::default();
        let source = held.source();
        let (first, last) = held.arrive_next(&source, 4);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (0, 3));
        source.publish(&Projection::Keys(uint_range(first, last)));
        source.publish(&Projection::Everything);
        assert!(matches!(source.claim(8), Claim::Idle));
        assert_eq!(source.claimed(), uint_range(0, 3));
    }

    /// `Everything` names the keys that are ready, and no others.
    #[test]
    fn everything_is_cut_to_the_keys_that_are_ready() {
        let held = Held::default();
        let source = held.source();
        held.arrive_next(&source, 3);
        source.publish(&Projection::Everything);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (0, 2));
        assert!(matches!(source.claim(8), Claim::Idle));
        held.arrive_next(&source, 2);
        source.publish(&Projection::Everything);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (3, 4));
    }

    /// Keys arrive in any order: a region that arrives ahead of an earlier one is claimed
    /// first, the earlier one is not claimable until it arrives, and an `Everything` sent while
    /// it is missing claims nothing from it. A row count cannot say this.
    #[test]
    fn a_region_that_arrives_ahead_of_an_earlier_one_is_claimed_first() {
        let held = Held::default();
        let source = held.source();
        held.arrive_positions(&source, 4, 7);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (4, 7));
        source.publish(&Projection::Everything);
        assert!(
            matches!(source.claim(8), Claim::Idle),
            "[0, 3] has not arrived"
        );
        assert_eq!(source.claimed(), uint_range(4, 7));

        held.arrive_positions(&source, 0, 3);
        source.publish(&Projection::Everything);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (0, 3));
        assert!(matches!(source.claim(8), Claim::Idle), "each row once");
        assert_eq!(source.claimed(), uint_range(0, 7));
    }

    /// A region whose keys are not ready is a bug in the publisher, and release builds refuse
    /// it too.
    #[test]
    #[should_panic(expected = "are ready before their region is published")]
    fn a_region_outside_the_ready_keys_is_refused() {
        let held = Held::default();
        let source = held.source();
        held.arrive_positions(&source, 0, 3);
        source.publish(&Projection::Keys(uint_range(2, 6)));
    }

    /// `UInt` is discrete, so a region built from open bounds, or by `Projection::minus`, names
    /// exactly the closed positions it contains.
    #[test]
    fn a_region_with_open_bounds_names_the_positions_it_contains() {
        let held = Held::default();
        let source = held.source();
        held.write(&(0..=9).map(Value::UInt).collect::<Vec<_>>());
        *held.ready.lock_wait() = uint_range(0, 9);
        let open = Projection::Keys(Predicate::intervals(IntervalSet::from(Interval::open(
            Value::UInt(3),
            Value::UInt(7),
        ))));
        let minus = Projection::Keys(uint_range(0, 9)).minus(&Projection::Keys(uint_range(3, 5)));
        source.publish(&open);
        assert_eq!(bounds(&source.claim(8).morsel().expect("a morsel")), (4, 6));
        assert!(matches!(source.claim(8), Claim::Idle));
        // `[0, 9]` less `[3, 5]` is `[0, 2] ∪ [6, 9]`, and 6 was claimed above.
        source.publish(&minus);
        let rest = source.claim(8).morsel().expect("a morsel");
        let all: Vec<Value> = (0..=9).map(Value::UInt).collect();
        let named_rest: Vec<u64> = named(&rest, &all).iter().map(Value::as_uint).collect();
        assert_eq!(named_rest, [0, 1, 2, 7, 8, 9]);
        assert!(matches!(source.claim(8), Claim::Idle));
    }

    /// Keys need not be positions. A morsel of sparse keys names exactly the keys it holds, and
    /// none of the values between them.
    #[test]
    fn a_morsel_of_sparse_keys_names_exactly_those_keys() {
        let held = Held::default();
        let source = held.source();
        let all = [10, 20, 35, 41, 90].map(int);
        held.arrive(&source, &all);

        let first = source.claim(3).morsel().expect("a morsel");
        assert_eq!(named(&first, &all), [int(10), int(20), int(35)]);
        let TileGuard::Function(FunctionGuard::Domain(region)) = &first else {
            unreachable!()
        };
        assert!(
            !region.contains(&int(15)),
            "a value between two keys is not named"
        );
        assert!(!region.contains(&int(41)));
        let second = source.claim(3).morsel().expect("a morsel");
        assert_eq!(named(&second, &all), [int(41), int(90)]);
        assert!(matches!(source.claim(3), Claim::Idle));
    }

    /// Keys that arrive out of order, ahead of smaller ones, are claimed when they are ready and
    /// the missing ones are not claimable.
    #[test]
    fn sparse_keys_that_arrive_out_of_order_are_claimed_when_ready() {
        let held = Held::default();
        let source = held.source();
        let all = [10, 20, 35, 41, 90].map(int);
        held.arrive(&source, &[int(41), int(90)]);
        let late = source.claim(8).morsel().expect("a morsel");
        assert_eq!(named(&late, &all), [int(41), int(90)]);
        source.publish(&Projection::Everything);
        assert!(matches!(source.claim(8), Claim::Idle));

        held.arrive(&source, &[int(10), int(20), int(35)]);
        source.publish(&Projection::Everything);
        let early = source.claim(8).morsel().expect("a morsel");
        assert_eq!(named(&early, &all), [int(10), int(20), int(35)]);
        assert!(matches!(source.claim(8), Claim::Idle), "each key once");
    }

    /// String keys are ordered too.
    #[test]
    fn string_keys_are_claimed_in_key_order() {
        let held = Held::default();
        let source = held.source();
        let all = ["pear", "apple", "kiwi"].map(string);
        held.arrive(&source, &all);
        let morsel = source.claim(2).morsel().expect("a morsel");
        assert_eq!(named(&morsel, &all), [string("apple"), string("kiwi")]);
        let rest = source.claim(2).morsel().expect("a morsel");
        assert_eq!(named(&rest, &all), [string("pear")]);
    }

    /// A yield predicate that covers keys which never arrive holds nothing to claim, and does not
    /// keep the source from being exhausted once it is closed.
    #[test]
    fn a_ready_region_with_no_keys_is_not_left_pending() {
        let held = Held::default();
        let source = held.source();
        *held.ready.lock_wait() = uint_range(0, 9);
        source.publish(&Projection::Everything);
        assert!(matches!(source.claim(4), Claim::Idle));
        source.close();
        assert!(matches!(source.claim(4), Claim::Exhausted));
    }

    /// A closed source is exhausted only once its published rows are claimed.
    #[test]
    fn a_closed_live_source_is_exhausted_after_its_published_rows() {
        let held = Held::default();
        let source = held.source();
        held.arrive_next(&source, 3);
        source.close();
        assert_eq!(bounds(&source.claim(2).morsel().expect("a morsel")), (0, 1));
        assert_eq!(bounds(&source.claim(2).morsel().expect("a morsel")), (2, 2));
        assert!(matches!(source.claim(2), Claim::Exhausted));
        assert!(matches!(source.claim(2), Claim::Exhausted), "and stays so");
    }

    #[test]
    fn a_range_source_answers_a_morsel_of_at_least_one_row() {
        let source = RangeSource::new(2);
        assert_eq!(bounds(&source.claim(0).morsel().expect("a morsel")), (0, 0));
        assert_eq!(
            bounds(&source.claim(u64::MAX).morsel().expect("a morsel")),
            (1, 1)
        );
        assert!(matches!(source.claim(u64::MAX), Claim::Exhausted));
    }

    #[test]
    fn a_finite_range_from_zero_is_a_morsel_source_and_no_other_extent_is() {
        let claimed = |extent: Extent| {
            IterateExtent::new(extent)
                .morsel_source()
                .map(|source| std::iter::from_fn(|| source.claim(100).morsel()).count())
        };
        assert_eq!(claimed(Extent::uint_range(5)), Some(1));
        assert_eq!(claimed(Extent::uint_range(0)), Some(0));
        assert_eq!(
            claimed(Extent::uint_range_interval(2, 5)),
            None,
            "starts above 0"
        );
        assert_eq!(claimed(Extent::Base(BaseType::Int)), None);
        assert_eq!(
            claimed(Extent::UIntRange(IntervalSet::from(Interval::closed(
                0,
                u64::MAX
            )))),
            None,
            "a range to the largest position has no row count"
        );
        assert_eq!(
            claimed(Extent::UIntRange(IntervalSet::from(Interval::open_closed(
                0, 5
            )))),
            None,
            "an open left bound starts above 0"
        );
    }
}

/// The projection a chain head is pulled with: a pipeline cuts its source into morsels, and a
/// worker pulls its chain at one morsel at a time.
#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{DataSourceDomainExtentImpl, test_source::TestDataSource};

    /// A source holding the keys `0..4`.
    fn source_of_four_keys() -> Arc<Mutex<TestDataSource>> {
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        source.lock_wait().add_data(
            &(0..4)
                .map(|k| (Value::UInt(k), Value::Int(k as i64)))
                .collect::<Vec<_>>(),
        );
        source
    }

    fn released_by(source: &Arc<Mutex<TestDataSource>>) -> Predicate {
        source.lock_wait().get_released_predicate()
    }

    /// The chains of a pool hold one release record with the source: each releases the morsels it
    /// ran, and the source reclaims their union. One record per chain would reclaim only what
    /// every chain released, which is nothing.
    #[test]
    fn the_chains_of_a_pool_release_into_one_record() {
        let source = source_of_four_keys();
        let mut operator = IterateExtent::new(Extent::DataSourceDomain(source.clone()));
        let mut scheduler = Scheduler::new();
        let guard = operator.tiling().universal_guard();
        let ([mut first, mut second], _records) =
            scheduler.with_pooled_release_records("pool#test".to_string(), |scheduler| {
                [(); 2].map(|()| operator.subscribe(guard.clone(), Box::new(|| {}), scheduler))
            });

        first.release(keys_between(0, 1));
        second.release(keys_between(2, 3));
        let released = released_by(&source);
        assert!(
            (0..4).all(|key| released.contains(&Value::UInt(key))),
            "the source reclaims what the two chains released between them: {released:?}"
        );
    }

    /// A chain of a pool that drops does not take the pool's record with it: the other chains
    /// are still reading, and the pool retires the record when its chains are gone.
    #[test]
    fn a_dropped_chain_leaves_the_pools_record_to_the_pool() {
        let source = source_of_four_keys();
        let mut operator = IterateExtent::new(Extent::DataSourceDomain(source.clone()));
        let mut scheduler = Scheduler::new();
        let guard = operator.tiling().universal_guard();
        let ([first, mut second], records) =
            scheduler.with_pooled_release_records("pool#test".to_string(), |scheduler| {
                [(); 2].map(|()| operator.subscribe(guard.clone(), Box::new(|| {}), scheduler))
            });
        drop(first);
        second.release(keys_between(0, 3));
        assert!(
            (0..4).all(|key| released_by(&source).contains(&Value::UInt(key))),
            "the record outlives the chain that dropped"
        );
        drop(second);
        assert!(
            (0..4).all(|key| released_by(&source).contains(&Value::UInt(key))),
            "and the last chain's drop leaves it too"
        );
        drop(records);
        assert_eq!(
            released_by(&source),
            Predicate::False,
            "the pool retires its records, and no record agrees to nothing"
        );
    }

    /// A source's keys are the outermost keys of an `IterateExtent` over its domain, and not of one
    /// over a record that holds it: the second is told `Everything` of any region of the source's
    /// keys.
    #[test]
    fn a_region_of_a_sources_keys_reaches_an_extent_over_its_domain_and_widens_inside_a_record() {
        use crate::interpreter::tile_operators::test_helpers::RegionLog;
        let region = Projection::Keys(uint_range(1, 2));
        let notified = |extent: Extent| {
            let source = source_of_four_keys();
            let extent = match extent {
                Extent::Record(_) => Extent::Record(
                    [(
                        crate::interpreter::tuple_field(0),
                        Extent::DataSourceDomain(source.clone()),
                    )]
                    .into_iter()
                    .collect(),
                ),
                _ => Extent::DataSourceDomain(source),
            };
            let mut operator = IterateExtent::new(extent);
            let (log, regions) = RegionLog::new(true);
            let mut scheduler = Scheduler::new();
            let guard = operator.tiling().universal_guard();
            let _producer = operator.subscribe(guard, Box::new(log), &mut scheduler);
            regions.lock_wait().clear();
            assert!(scheduler.notify_source_consumers("source1", &region));
            let seen = regions.lock_wait();
            seen.clone()
        };
        assert_eq!(
            notified(Extent::Base(BaseType::UInt)),
            std::slice::from_ref(&region)
        );
        assert_eq!(
            notified(Extent::Record(Default::default())),
            [Projection::Everything]
        );
    }

    /// Chains subscribed outside a pool each hold a record, and the source reclaims only what
    /// every one released. This is the pinning a pool's shared record removes.
    #[test]
    fn chains_outside_a_pool_each_hold_a_record() {
        let source = source_of_four_keys();
        let mut operator = IterateExtent::new(Extent::DataSourceDomain(source.clone()));
        let mut scheduler = Scheduler::new();
        let guard = operator.tiling().universal_guard();
        let mut first = operator.subscribe(guard.clone(), Box::new(|| {}), &mut scheduler);
        let mut second = operator.subscribe(guard, Box::new(|| {}), &mut scheduler);
        first.release(keys_between(0, 1));
        second.release(keys_between(2, 3));
        assert_eq!(released_by(&source), Predicate::False);
    }

    /// A producer that releases nothing holds the source's reclaim at nothing until it is
    /// dropped, and the pool's record is the whole agreement after.
    #[test]
    fn a_dropped_idle_producer_stops_pinning_the_source() {
        let source = source_of_four_keys();
        let mut operator = IterateExtent::new(Extent::DataSourceDomain(source.clone()));
        let mut scheduler = Scheduler::new();
        let guard = operator.tiling().universal_guard();
        let idle = operator.subscribe(guard.clone(), Box::new(|| {}), &mut scheduler);
        let (mut worker, _records) = scheduler
            .with_pooled_release_records("pool#test".to_string(), |scheduler| {
                operator.subscribe(guard, Box::new(|| {}), scheduler)
            });

        worker.release(keys_between(0, 3));
        assert_eq!(
            released_by(&source),
            Predicate::False,
            "the idle one pins it"
        );
        drop(idle);
        assert!(
            (0..4).all(|key| released_by(&source).contains(&Value::UInt(key))),
            "the pool's record is the agreement once the idle producer is gone"
        );
    }

    /// A source holding `keys`, whose keys are of `key_extent`.
    fn source_of_keys(keys: &[Value], key_extent: Extent) -> Arc<Mutex<TestDataSource>> {
        let source = Arc::new(Mutex::new(
            TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )
            .with_key_extent(key_extent),
        ));
        source.lock_wait().add_data(
            &keys
                .iter()
                .map(|key| (key.clone(), Value::Int(0)))
                .collect::<Vec<_>>(),
        );
        source
    }

    /// A data-source domain is a morsel source when its source cuts morsels, and every other
    /// source, and a source whose keys are not totally ordered, is read whole.
    #[test]
    fn a_data_source_domain_is_a_morsel_source_when_its_source_cuts_morsels() {
        let ordered = source_of_keys(&[Value::Int(10)], Extent::Base(BaseType::Int));
        assert!(
            IterateExtent::new(Extent::DataSourceDomain(ordered))
                .morsel_source()
                .is_some()
        );
        let record_keys = Extent::Record(
            [(
                crate::interpreter::tuple_field(0),
                Extent::Base(BaseType::Int),
            )]
            .into_iter()
            .collect(),
        );
        let unordered = source_of_keys(&[], record_keys);
        assert!(
            IterateExtent::new(Extent::DataSourceDomain(unordered))
                .morsel_source()
                .is_none(),
            "keys that are not totally ordered have no morsels"
        );
    }

    /// A producer pulled at a morsel renders the morsel's keys and no others, and the source does
    /// not render its whole domain to find them: the source refuses a whole read, so the cut has
    /// to be the source's own.
    #[test]
    fn a_data_source_domain_is_cut_to_the_morsel_before_it_is_rendered() {
        let keys = [10, 20, 35, 41, 90].map(Value::Int);
        let source = source_of_keys(&keys, Extent::Base(BaseType::Int));
        source.lock_wait().refuse_whole_reads();
        source
            .lock_wait()
            .set_yield_predicate(Predicate::intervals(IntervalSet::from_iter(
                keys.iter()
                    .map(|key| Interval::closed(key.clone(), key.clone())),
            )));
        let mut operator = IterateExtent::new(Extent::DataSourceDomain(source));
        let mut scheduler = Scheduler::new();
        let guard = operator.tiling().universal_guard();
        let mut producer = operator.subscribe(guard, Box::new(|| {}), &mut scheduler);

        let morsel = TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
            IntervalSet::from_iter([
                Interval::closed(Value::Int(20), Value::Int(35)),
                Interval::closed(Value::Int(90), Value::Int(90)),
            ]),
        )));
        let tile = producer.get(morsel);
        let Tile::DataFunction { mut domain, .. } = tile else {
            panic!("a collection");
        };
        let mut rendered: Vec<Value> = domain.drain_to_value_iter().collect();
        rendered.sort_by(|a, b| a.partial_cmp(b).expect("keys compare"));
        assert_eq!(rendered, [Value::Int(20), Value::Int(35), Value::Int(90)]);
    }

    fn head(extent: Extent) -> IterateExtentProducer {
        let tiling = Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone()));
        IterateExtentProducer {
            base: ProducerBase::unowned(0, &tiling),
            extent,
            released: Predicate::False,
            _source_wakeup: None,
            shared_release_record: None,
        }
    }

    /// The positions a head tile holds, which it keys and values alike.
    fn positions(tile: &Tile) -> Vec<u64> {
        let Tile::DataFunction {
            domain: ColumnValue::UInts(keys),
            ..
        } = tile
        else {
            panic!("a collection of positions, got {tile:?}")
        };
        let mut keys = keys.clone();
        keys.sort_unstable();
        keys
    }

    fn completeness(tile: &Tile) -> Predicate {
        let Tile::DataFunction {
            domain_predicate, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        domain_predicate.clone()
    }

    fn between(first: u64, last: u64) -> Predicate {
        let TileGuard::Function(FunctionGuard::Domain(keys)) = keys_between(first, last) else {
            unreachable!("a morsel is a domain guard")
        };
        keys
    }

    /// A chain over `iterate([0, 10))` is pulled one morsel at a time. Each morsel holds its own
    /// positions and calls only them complete, and the morsels together are the whole range.
    #[test]
    fn a_range_head_answers_one_morsel_at_a_time() {
        let mut head = head(Extent::uint_range(10));
        let mut seen = Vec::new();
        for (first, last) in [(0, 3), (4, 7), (8, 9)] {
            let morsel = head.get(keys_between(first, last));
            assert_eq!(positions(&morsel), (first..=last).collect::<Vec<_>>());
            assert_eq!(
                completeness(&morsel),
                between(first, last),
                "a morsel is complete over its own interval"
            );
            seen.extend(positions(&morsel));
            // The next morsel is pulled after this one is released.
            head.release(keys_between(first, last));
        }
        assert_eq!(seen, (0..10).collect::<Vec<_>>());
    }

    /// The last morsel of a range is usually cut past its end: the head answers the positions it
    /// has, and the range is complete over the rest of the morsel because nothing lies there.
    #[test]
    fn a_morsel_past_the_end_holds_what_the_range_holds() {
        let mut head = head(Extent::uint_range(10));
        let morsel = head.get(keys_between(8, 20));
        assert_eq!(positions(&morsel), [8, 9]);
        assert_eq!(completeness(&morsel), between(8, 20));
    }

    #[test]
    fn a_released_morsel_is_not_answered_again() {
        let mut head = head(Extent::uint_range(10));
        head.get(keys_between(0, 3));
        head.release(keys_between(0, 3));
        let rest = head.get(head.tiling().universal_guard());
        assert_eq!(positions(&rest), (4..10).collect::<Vec<_>>());
    }

    #[test]
    fn nothing_names_no_positions() {
        let mut head = head(Extent::uint_range(10));
        assert_eq!(
            head.get(head.tiling().empty_guard()),
            head.tiling().empty_tile()
        );
    }

    /// The head of a program over a live source. A morsel is cut from what has ready, and the
    /// head says nothing about positions that may still arrive in the morsel.
    #[test]
    fn a_live_source_head_is_complete_only_over_what_has_arrived() {
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let as_domain: Arc<Mutex<dyn DataSourceDomainExtentImpl>> = source.clone();
        let mut head = head(Extent::DataSourceDomain(as_domain));
        source.lock_now().release(&head.name(), Predicate::False);
        source.lock_now().add_data(&[
            (Value::UInt(0), Value::Int(10)),
            (Value::UInt(1), Value::Int(20)),
            (Value::UInt(2), Value::Int(30)),
            (Value::UInt(3), Value::Int(40)),
            (Value::UInt(4), Value::Int(50)),
        ]);
        source
            .lock_now()
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(4)));

        let inside = head.get(keys_between(1, 2));
        assert_eq!(positions(&inside), [1, 2]);
        assert_eq!(completeness(&inside), between(1, 2));
        head.release(keys_between(1, 2));

        // Positions 5 to 9 have not ready, so the morsel is complete over 3 and 4 only.
        let straddling = head.get(keys_between(3, 9));
        assert_eq!(positions(&straddling), [3, 4]);
        assert_eq!(completeness(&straddling), between(3, 4));
    }

    /// A cross product's keys are records, which the projection cuts by field.
    #[test]
    fn a_cross_product_is_cut_by_the_fields_of_its_keys() {
        let extent = Extent::Record(
            [
                (SmolStr::new("a"), Extent::uint_range(3)),
                (SmolStr::new("b"), Extent::uint_range(2)),
            ]
            .into_iter()
            .collect(),
        );
        let mut head = head(extent);
        let first_a = Predicate::Record(
            [
                (SmolStr::new("a"), Predicate::point(Value::UInt(0))),
                (SmolStr::new("b"), Predicate::True),
            ]
            .into_iter()
            .collect(),
        );
        let tile = head.get(TileGuard::Function(FunctionGuard::Domain(first_a)));
        let Tile::DataFunction { domain, .. } = &tile else {
            panic!("a collection")
        };
        assert_eq!(domain.len(), 2, "(0, 0) and (0, 1)");
    }
}

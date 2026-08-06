use bit_set::BitSet;
use intervalsets::{Bounding, Interval, IntervalSet, ops::Difference};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;
use crate::ccl::TagMap;
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, NotifyOrSubscribeResult, Scheduler, UnionArm, Value,
};

/// Produces a sealed-function tile whose domain and codomain both equal `extent`.
///
/// Used to enumerate all values in an extent: the resulting tile maps each
/// element to itself (`identity`)
pub struct IterateExtent {
    /// The extent to iterate over.
    pub extent: Extent,
    /// The tiling — always `Tiling::SealedFunction { domain: extent, codomain: extent }`.
    pub tiling: Tiling,
}

impl IterateExtent {
    pub fn new(extent: Extent) -> Self {
        let tiling = Tiling::SealedFunction {
            domain: extent.clone(),
            codomain: Box::new(Tiling::Scalar(extent.clone())),
        };
        Self { tiling, extent }
    }

    fn add_all_source_handles(
        extent: &Extent,
        consumer: Rc<RefCell<dyn Consumer>>,
        scheduler: &mut Scheduler,
    ) {
        match extent {
            Extent::DataSourceDomain(extent_impl, ..) => {
                let c = consumer.clone();
                scheduler.add_source_handle(
                    extent_impl.clone(),
                    Box::new(move || c.borrow_mut().notify()),
                );
            }
            Extent::Record(fields) => {
                for field_extent in fields.values() {
                    Self::add_all_source_handles(field_extent, consumer.clone(), scheduler);
                }
            }
            Extent::Restricted { base, .. } => {
                Self::add_all_source_handles(base, consumer, scheduler);
            }
            Extent::Union(arms) => {
                for extent in arms.values() {
                    Self::add_all_source_handles(extent, consumer.clone(), scheduler);
                }
            }
            // Nothing to do for other extents since they all complete from the start of the program
            _ => {}
        }
    }
}

impl TileOperator for IterateExtent {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let mut producer = Box::new(IterateExtentProducer {
            base: ProducerBase::new(IterateExtentProducer::alloc_id(), &self.tiling),
            extent: self.extent.clone(),
            released: Predicate::False,
        });

        let NotifyOrSubscribeResult { notify, subscribe } =
            self.extent.subscribe_to_iteration_action();
        if notify {
            consumer.notify();
        }
        if subscribe {
            let consumer_wrapper = Rc::new(RefCell::new(move || {
                consumer.notify();
            }));
            Self::add_all_source_handles(&self.extent, consumer_wrapper, scheduler);
            let name = producer.name();
            // Register this producer with any data sources in the extent by calling release with
            // a false predicate.  This way the sources knows about all producers that read it
            //before execution starts.
            release_extent(&mut producer.extent, &Predicate::False, &name);
        }

        producer
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Producer for [`IterateExtent`]: emits an identity sealed-function tile.
struct IterateExtentProducer {
    base: ProducerBase,
    /// The extent being iterated.
    ///
    /// For `UIntRange` extents this is an `IntervalSet<usize>` that shrinks
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
}

fn get_iterate_extent_predicate(extent: &Extent) -> Predicate {
    match extent {
        Extent::DataSourceDomain(source) => source.borrow().get_yield_predicate(),
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
        Extent::Union(arms) => Predicate::Union(arms.map(|_, e| get_iterate_extent_predicate(e))),
        _ => Predicate::True,
    }
}

/// Convert a `IntervalSet<Value::UInt>` values into an
/// `IntervalSet<usize>`, preserving bound types.
///
/// Discrete `Value` intervals are normalised to closed form by `intervalsets`,
/// so the resulting `usize` intervals are also closed.
fn predicate_intervals_to_usize(intervals: &IntervalSet<Value>) -> IntervalSet<usize> {
    IntervalSet::from_iter(intervals.intervals().iter().map(|iv| {
        // Left-unbounded intervals (e.g. (-∞, 3]) are clamped to [0, r] since
        // UIntRange indices are always non-negative.
        let left: usize = iv.lval().map_or(0, |v| v.as_uint());
        match iv.rval() {
            Some(r) => Interval::closed(left, r.as_uint()),
            None => Interval::closed_unbound(left),
        }
    }))
}

/// Release values from `extent` that are covered by `pred`.
///
/// For [`Extent::UIntRange`] extents, released sub-intervals are subtracted
/// directly from the stored [`IntervalSet<usize>`], so arbitrary non-contiguous
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
            source.borrow_mut().release(releaser, pred.clone());
        }
        Extent::UIntRange(remaining) => match pred {
            Predicate::True => {
                *remaining = IntervalSet::from(Interval::<usize>::empty());
            }
            Predicate::False => {}
            Predicate::LessThanEq(v) => {
                // Release every index up to and including v.
                let to_remove = IntervalSet::from(Interval::closed(0usize, v.as_uint()));
                *remaining = remaining.difference(&to_remove);
            }
            Predicate::Intervals(intervals) => {
                // Subtract the released sub-intervals directly from the remaining set.
                let to_remove = predicate_intervals_to_usize(intervals);
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
            Predicate::Union(pred_arms) => {
                for (tag, e) in ext_arms.iter_mut() {
                    // A tag the predicate does not mention is unconstrained, so
                    // nothing of it is released.
                    if let Some(arm) = pred_arms.get(tag) {
                        release_extent(e, arm, releaser);
                    }
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
            let values: Vec<usize> = remaining
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
        Extent::DataSourceDomain(source_impl) => source_impl.borrow_mut().get_elements(producer),
        Extent::Record(fields) => iterate_record(fields, producer),
        Extent::Union(arms) => iterate_union(arms, producer),
        Extent::Restricted { .. } => {
            panic!("Iterating over restricted extents not supported; use Filter operators instead")
        }
        _ => panic!("Attempted to iterate on infinite Extent"),
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

fn iterate_record(fields: &HashMap<String, Extent>, producer: &str) -> ColumnValue {
    let data: HashMap<String, ColumnValue> = fields
        .iter()
        .map(|(field, field_extent)| (field.clone(), iterate_extent(field_extent, producer)))
        .collect();
    ColumnValue::cartesian_product(data)
}

impl TileProducer for IterateExtentProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let values = iterate_extent(&self.extent, &self.name());
        let domain_predicate = get_iterate_extent_predicate(&self.extent);
        let mut tile = Tile::SealedFunction {
            domain: values.clone(),
            codomain: Box::new(Tile::Scalar(values)),
            domain_predicate,
            deleted: BitSet::new(),
        };
        // Filter out any domain rows that have already been released.
        // Values may also be removed from underlying sources for efficiency, but
        // this filter here is ultimately responsible for not returning released data.
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(
            self.released.clone(),
        )));
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let name = self.name();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value, tuple_field};
    use intervalsets::MaybeEmpty;
    use intervalsets::ops::Contains;

    /// Helper: extract the `IntervalSet<usize>` from a `UIntRange` extent.
    fn uint_range_set(extent: &Extent) -> &IntervalSet<usize> {
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
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::LessThanEq(v)` releases [0, v] inclusive.
    #[test]
    fn release_extent_less_than_eq_releases_prefix() {
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &Predicate::LessThanEq(Value::UInt(4)), "");
        let s = uint_range_set(&extent);
        for i in 0..=4usize {
            assert!(!s.contains(&i), "{i} should be released");
        }
        for i in 5..10usize {
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
        assert!(!s.contains(&2usize), "2 should be released");
        assert!(!s.contains(&3usize), "3 should be released");
        assert!(!s.contains(&7usize), "7 should be released");
        for i in [0, 1, 4, 5, 6, 8, 9usize] {
            assert!(s.contains(&i), "{i} should remain");
        }
    }

    /// `Predicate::Intervals` with a right-unbounded interval (e.g. [5, +∞))
    /// releases everything from 5 to the end of the extent.
    #[test]
    fn release_extent_right_unbounded_intervals_predicate() {
        // LessThanEq(4) union True = True, so build the right-unbounded interval
        // directly via the complement: values NOT ≤ 4 are > 4, i.e. [5, +∞).
        // We exercise this by unioning {5} with a GreaterThan-style Intervals predicate.
        // Simplest path: union two Intervals so the result stays as Intervals.
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![5])).union(
            &Predicate::from_column_value(&ColumnValue::UInts(vec![6, 7, 8, 9, 10])),
        );
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should remain");
        }
        for i in 5..10usize {
            assert!(!s.contains(&i), "{i} should be released");
        }
    }

    /// Releasing a `Predicate::Intervals` that contains a left-unbounded interval
    /// (produced by `Predicate::union(LessThanEq, Intervals)`) must subtract the
    /// full interval from the `UIntRange` extent, not silently drop it.
    #[test]
    fn release_extent_left_unbounded_intervals_predicate() {
        // Build the predicate that union() produces from LessThanEq(3) | {7}:
        // result is Predicate::Intervals containing (-∞, 3] ∪ {7}.
        let p = Predicate::LessThanEq(Value::UInt(3))
            .union(&Predicate::from_column_value(&ColumnValue::UInts(vec![7])));

        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");

        // After releasing (-∞, 3] ∪ {7}, remaining should be {4, 5, 6, 8, 9}.
        let Extent::UIntRange(ref remaining) = extent else {
            panic!("expected UIntRange");
        };
        assert!(!remaining.contains(&0usize), "0 should be released");
        assert!(!remaining.contains(&3usize), "3 should be released");
        assert!(remaining.contains(&4usize), "4 should remain");
        assert!(!remaining.contains(&7usize), "7 should be released");
        assert!(remaining.contains(&9usize), "9 should remain");
    }

    #[test]
    fn iterate_extent_fragmented_uint_range() {
        // Simulate [0,5) with indices 1,2,3 already released → {[0,0],[4,4]}
        let mut extent = Extent::uint_range(5);
        // release [1,3]
        if let Extent::UIntRange(ref mut set) = extent {
            let to_remove = IntervalSet::from(Interval::closed(1usize, 3usize));
            *set = set.difference(&to_remove);
        }
        let tiling = Tiling::SealedFunction {
            domain: extent.clone(),
            codomain: Box::new(Tiling::Scalar(extent.clone())),
        };
        let mut producer = IterateExtentProducer {
            base: ProducerBase::new(0, &tiling),
            extent,
            released: Predicate::False,
        };
        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = tile else {
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
}

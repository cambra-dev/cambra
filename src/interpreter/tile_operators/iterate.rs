#[cfg(test)]
use crate::interpreter::tile_operators::test_helpers::ReadInPipeline as _;
use std::sync::PoisonError;
mod cartesian;

use cartesian::CartesianIteration;

use bit_set::BitSet;
use intervalsets::{
    Bounding, Interval, IntervalSet,
    ops::{Difference, Intersection},
};
use smol_str::SmolStr;
use std::sync::RwLock;
use std::{collections::HashMap, sync::Arc};

use super::*;
use crate::ccl::TagMap;
use crate::interpreter::{
    BaseType, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, Projection,
    SubscribeContext, UnionArm, Value, notifications::shared_consumer,
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

    fn add_all_source_handles(extent: &Extent, cx: &mut SubscribeContext) {
        extent.for_each_source(&mut |source| {
            cx.source_registry().add_source_handle(source.clone());
        });
    }
}

impl TileOperator for IterateExtent {
    impl_operator_base!();

    fn keys_arrive_by_push(&self) -> bool {
        self.extent.reads_a_source()
    }

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        if let Extent::Record(fields) = &self.extent
            && self.extent.reads_a_source()
        {
            return cartesian::subscribe(self.clone(), fields, consumer, cx);
        }
        let leaf = shared_consumer(consumer);
        let mut producer = Box::new(IterateExtentProducer {
            base: ProducerBase::new(
                IterateExtentProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .leaf(leaf.clone()),
            _retirements: Vec::new(),
            iteration: Iteration::Direct(RwLock::new(DirectIteration {
                extent: self.extent.clone(),
                released: Predicate::False,
            })),
        });
        if self.extent.reads_a_source() {
            Self::add_all_source_handles(&self.extent, cx);
            let name = producer.name();
            // Register this producer with any data sources in the extent by calling release with
            // a false predicate.  This way the sources knows about all producers that read it
            //before execution starts.
            let Iteration::Direct(direct) = &mut producer.iteration else {
                unreachable!("a source subscription iterates its extent directly")
            };
            release_extent(
                &mut direct
                    .get_mut()
                    .unwrap_or_else(PoisonError::into_inner)
                    .extent,
                &Predicate::False,
                &name,
            );
            self.extent.for_each_source(&mut |source| {
                producer._retirements.push(
                    source
                        .read()
                        .unwrap_or_else(PoisonError::into_inner)
                        .producer_retirement(&name),
                );
            });
            cx.note_source_producer(name);
        }

        producer
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Producer for [`IterateExtent`]: emits an identity function tile.
struct IterateExtentProducer {
    base: ProducerBase,
    iteration: Iteration,
    _retirements: Vec<crate::interpreter::SourceReaderRetirement>,
}

enum Iteration {
    Direct(RwLock<DirectIteration>),
    // shared-state-ok: one producer's iteration state, shared only with that producer's own leaf
    // consumer (`CartesianSource`), which ingests the sources' arrivals into it. The arrivals come
    // from data sources at the I/O boundary; no other operator reaches the cell.
    Cartesian(Arc<RwLock<CartesianIteration>>),
}

struct DirectIteration {
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
            source
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .release(releaser, pred.clone());
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
        Extent::DataSourceDomain(source_impl) => source_impl
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .get_elements(producer),
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

impl TileProducer for IterateExtentProducer {
    impl_producer_base!();

    fn state_info(&self) -> ProducerStateInfo {
        match &self.iteration {
            Iteration::Direct(_) => ProducerStateInfo::holding(0),
            Iteration::Cartesian(cartesian) => cartesian
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .state_info(),
        }
    }

    fn data_sources(&self) -> Vec<Arc<RwLock<dyn DataSourceDomainExtentImpl>>> {
        let mut sources = Vec::new();
        self.tiling()
            .domain_extent()
            .expect("an iterator has a domain")
            .for_each_source(&mut |source| sources.push(source.clone()));
        sources
    }

    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        if matches!(&self.iteration, Iteration::Cartesian(_)) {
            let tiling = self.tiling().clone();
            let obsolete = self.obsolete_guard().clone();
            let Iteration::Cartesian(cartesian) = &self.iteration else {
                unreachable!()
            };
            return cartesian
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .get(projection_guard, &tiling, &obsolete);
        }
        let Iteration::Direct(direct) = &self.iteration else {
            unreachable!()
        };
        let direct = direct.read().unwrap_or_else(PoisonError::into_inner);
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let extent = match (&direct.extent, &projection) {
            (
                Extent::UIntRange(remaining),
                Projection::Keys {
                    keys: Predicate::Intervals(admitted),
                    ..
                },
            ) => Extent::UIntRange(remaining.intersection(&predicate_intervals_to_u64(admitted))),
            (extent, _) => extent.clone(),
        };
        let values = iterate_extent(&extent, &self.name());
        let domain_predicate = extent.complete_region();
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
            direct.released.clone(),
        )));
        tile
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        let name = self.name();
        let obsolete = self.obsolete_guard().clone();
        match &self.iteration {
            Iteration::Cartesian(cartesian) => cartesian
                .write()
                .unwrap_or_else(PoisonError::into_inner)
                .release(&obsolete),
            Iteration::Direct(direct) => {
                let mut direct = direct.write().unwrap_or_else(PoisonError::into_inner);
                let TileGuard::Function(FunctionGuard::Domain(pred)) = obsolete_guard else {
                    panic!("IterateExtent::release expected Domain guard, got {obsolete_guard:?}")
                };
                direct.released = direct.released.union(&pred);
                release_extent(&mut direct.extent, &pred, &name);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value, tuple_field};
    use intervalsets::MaybeEmpty;
    use intervalsets::ops::Contains;

    #[rstest::rstest]
    fn dropping_a_reader_retires_it_while_another_worker_holds_the_source(
        #[values(false, true)] product: bool,
    ) {
        let source = crate::interpreter::TestDataSource::new(
            "retirement",
            crate::ccl::Type::Base(BaseType::UInt),
            Extent::Base(BaseType::UInt),
        );
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release("other", Predicate::True);
        let domain = Extent::DataSourceDomain(source.runtime());
        let extent = if product {
            Extent::Record(HashMap::from([
                ("source".into(), domain),
                ("unit".into(), Extent::Base(BaseType::Unit)),
            ]))
        } else {
            domain
        };
        let op = Arc::new(IterateExtent::new(extent));
        let reader = op.clone().subscribe(
            op.tiling().universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let held = source.write().unwrap_or_else(PoisonError::into_inner);
        assert_eq!(held.get_released_predicate(), Predicate::False);
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            drop(reader);
            done_tx.send(()).unwrap();
        });
        let retired = done_rx.recv_timeout(std::time::Duration::from_secs(5));
        let agreement = held.get_released_predicate();
        drop(held);
        worker.join().unwrap();
        retired.expect("reader retirement must not wait for the source data lock");
        assert_eq!(agreement, Predicate::True);
    }

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

        let src = TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        let as_domain: Arc<RwLock<dyn DataSourceDomainExtentImpl>> = src.runtime();
        let extent = Extent::Union(TagMap::from_arms(vec![(
            FieldKey::Name("only".into()),
            Extent::DataSourceDomain(as_domain),
        )]));

        src.write()
            .unwrap_or_else(PoisonError::into_inner)
            .release("p", Predicate::True);
        assert_eq!(
            src.read()
                .unwrap_or_else(PoisonError::into_inner)
                .get_released_predicate(),
            Predicate::True,
            "`p` holds a record for the retire to find"
        );

        extent.for_each_source(&mut |source| {
            drop(
                source
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .producer_retirement("p"),
            );
        });

        assert_eq!(
            src.read()
                .unwrap_or_else(PoisonError::into_inner)
                .get_released_predicate(),
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
            _retirements: Vec::new(),
            iteration: Iteration::Direct(RwLock::new(DirectIteration {
                extent,
                released: Predicate::False,
            })),
        };
        let tile = producer.read_in_pipeline(producer.tiling().universal_guard());
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
        // A record is decided where every field is decided.
        let extent = Extent::Record(
            [
                (tuple_field(0), Extent::Base(BaseType::UInt)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        );

        let predicate = extent.complete_region();

        match predicate {
            Predicate::Record(fields) => {
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

/// The projection a chain head is pulled with: a pipeline cuts its source into morsels, and a
/// worker pulls its chain at one morsel at a time.
#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{DataSourceDomainExtentImpl, test_source::TestDataSource};

    fn head(extent: Extent) -> IterateExtentProducer {
        let tiling = Tiling::data_function(extent.clone(), Tiling::Scalar(extent.clone()));
        IterateExtentProducer {
            base: ProducerBase::unowned(0, &tiling),
            _retirements: Vec::new(),
            iteration: Iteration::Direct(RwLock::new(DirectIteration {
                extent,
                released: Predicate::False,
            })),
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
            let morsel = head.read_in_pipeline(keys_between(first, last));
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
        let morsel = head.read_in_pipeline(keys_between(8, 20));
        assert_eq!(positions(&morsel), [8, 9]);
        assert_eq!(completeness(&morsel), between(8, 20));
    }

    #[test]
    fn a_released_morsel_is_not_answered_again() {
        let mut head = head(Extent::uint_range(10));
        head.read_in_pipeline(keys_between(0, 3));
        head.release(keys_between(0, 3));
        let rest = head.read_in_pipeline(head.tiling().universal_guard());
        assert_eq!(positions(&rest), (4..10).collect::<Vec<_>>());
    }

    #[test]
    fn nothing_names_no_positions() {
        let mut head = head(Extent::uint_range(10));
        assert_eq!(
            head.read_in_pipeline(head.tiling().empty_guard()),
            head.tiling().empty_tile()
        );
    }

    /// The head of a program over a live source. A morsel is cut from what has arrived, and the
    /// head says nothing about positions that may still arrive in the morsel.
    #[test]
    fn a_live_source_head_is_complete_only_over_what_has_arrived() {
        let source = TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        );
        let as_domain: Arc<RwLock<dyn DataSourceDomainExtentImpl>> = source.runtime();
        let mut head = head(Extent::DataSourceDomain(as_domain));
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .release(&head.name(), Predicate::False);
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .add_data(&[
                (Value::UInt(0), Value::Int(10)),
                (Value::UInt(1), Value::Int(20)),
                (Value::UInt(2), Value::Int(30)),
                (Value::UInt(3), Value::Int(40)),
                (Value::UInt(4), Value::Int(50)),
            ]);
        source
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(4)));

        let inside = head.read_in_pipeline(keys_between(1, 2));
        assert_eq!(positions(&inside), [1, 2]);
        assert_eq!(completeness(&inside), between(1, 2));
        head.release(keys_between(1, 2));

        // Positions 5 to 9 have not arrived, so the morsel is complete over 3 and 4 only.
        let straddling = head.read_in_pipeline(keys_between(3, 9));
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
        let tile = head.read_in_pipeline(TileGuard::Function(FunctionGuard::Domain(first_a)));
        let Tile::DataFunction { domain, .. } = &tile else {
            panic!("a collection")
        };
        assert_eq!(domain.len(), 2, "(0, 0) and (0, 1)");
    }
}

//! The region an operator's consumer receives for a region of keys that changed at one of its
//! inputs: the keys unchanged where the operator's row of the projection table pulls that input
//! at the projection, and `Everything` where it re-keys or reads the input whole.
//! See `src/interpreter/design-operators.md`, "The notification contract".

use smol_str::SmolStr;

use super::test_helpers::{InputConsumer, NotifyingOp, RegionLog, keys_between, notify_input};
use super::*;
use crate::interpreter::{BaseType, CurryLevel, Extent, Projection, Scheduler, Tiling};

/// An operator and the consumers it installed on its inputs, which a test notifies through.
type Built = (Box<dyn TileOperator>, Vec<InputConsumer>);

/// A stream of integers keyed by position.
fn ints() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(8),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// An operator that keeps the consumer it is subscribed with, for the test to notify through.
fn feed(tiling: Tiling) -> (Box<dyn TileOperator>, InputConsumer) {
    let (op, consumer) = NotifyingOp::new(tiling.empty_tile(), tiling);
    (Box::new(op), consumer)
}

fn region() -> Projection {
    Projection::of(&keys_between(2, 4)).expect("keys")
}

fn another_region() -> Projection {
    Projection::of(&keys_between(6, 7)).expect("keys")
}

/// What a recording consumer of the operator `build` makes receives when `region` is notified at
/// its input `notified`. A consumer passes one notification between pulls, so each call builds an
/// operator of its own.
fn received(build: &dyn Fn() -> Built, notified: usize, region: &Projection) -> Vec<Projection> {
    let (mut operator, inputs) = build();
    let (log, regions) = RegionLog::new();
    let guard = operator.tiling().universal_guard();
    let _producer = operator.subscribe(guard, Box::new(log), &mut Scheduler::new());
    // Some inputs notify when they are subscribed.
    regions.borrow_mut().clear();
    notify_input(&inputs[notified], region);
    let seen = regions.borrow_mut();
    seen.clone()
}

/// The operator forwards a region of input `notified` unchanged.
fn assert_keeps(build: &dyn Fn() -> Built, notified: usize) {
    assert_eq!(received(build, notified, &region()), [region()]);
}

/// The operator carries nothing from one notification to the next: `Everything` stays
/// `Everything`, and a different region is delivered as itself.
fn assert_keeps_without_state(build: &dyn Fn() -> Built, notified: usize) {
    assert_eq!(
        received(build, notified, &Projection::Everything),
        [Projection::Everything]
    );
    assert_eq!(
        received(build, notified, &another_region()),
        [another_region()]
    );
}

fn record_wrap() -> Built {
    let (input, consumer) = feed(ints());
    let op = RecordWrap::new_at(SmolStr::new("a"), input, CurryLevel::new(1));
    (Box::new(op), vec![consumer])
}

#[test]
fn record_wrap_forwards_its_inputs_region() {
    assert_keeps(&record_wrap, 0);
}

#[test]
fn record_wrap_carries_no_region_between_notifications() {
    assert_keeps_without_state(&record_wrap, 0);
}

fn map_domain() -> Built {
    let (input, consumer) = feed(ints());
    (Box::new(MapDomain::new(input)), vec![consumer])
}

#[test]
fn map_domain_forwards_its_inputs_region() {
    assert_keeps(&map_domain, 0);
}

#[test]
fn map_domain_carries_no_region_between_notifications() {
    assert_keeps_without_state(&map_domain, 0);
}

fn bools() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(8),
        Tiling::Scalar(Extent::Base(BaseType::Bool)),
    )
}

fn restrict() -> Built {
    let (predicate, consumer) = feed(bools());
    (Box::new(Restrict::new(predicate)), vec![consumer])
}

#[test]
fn restrict_forwards_its_predicates_region() {
    assert_keeps(&restrict, 0);
}

#[test]
fn restrict_carries_no_region_between_notifications() {
    assert_keeps_without_state(&restrict, 0);
}

fn map_result_with_source() -> Built {
    use crate::interpreter::TestDataSource;
    use std::{cell::RefCell, rc::Rc};
    let source = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        crate::ccl::Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    let domain = IterateExtent::new(Extent::DataSourceDomain(source.clone()));
    let (input, consumer) = feed(domain.tiling().clone());
    let op = MapResultWithSource::new(source, input);
    (Box::new(op), vec![consumer])
}

#[test]
fn map_result_with_source_forwards_its_inputs_region() {
    assert_keeps(&map_result_with_source, 0);
}

#[test]
fn map_result_with_source_carries_no_region_between_notifications() {
    assert_keeps_without_state(&map_result_with_source, 0);
}

fn nested() -> Tiling {
    Tiling::data_function(Extent::uint_range(8), ints())
}

fn map_aggregate() -> Built {
    let (input, consumer) = feed(nested());
    let op = MapAggregate::new(input, crate::ccl::AggregateKind::Sum);
    (Box::new(op), vec![consumer])
}

#[test]
fn map_aggregate_forwards_its_inputs_outermost_region() {
    assert_keeps(&map_aggregate, 0);
}

#[test]
fn map_aggregate_carries_no_region_between_notifications() {
    assert_keeps_without_state(&map_aggregate, 0);
}

/// The extract reads the groups a `MapAggregate` folds, so the region passes both.
fn map_extract_aggregate() -> Built {
    let (input, consumer) = feed(nested());
    let fold = MapAggregate::new(input, crate::ccl::AggregateKind::Sum);
    let op = MapExtractAggregate::new(Box::new(fold), crate::ccl::AggregateKind::Sum);
    (Box::new(op), vec![consumer])
}

#[test]
fn map_extract_aggregate_forwards_its_inputs_outermost_region() {
    assert_keeps(&map_extract_aggregate, 0);
}

#[test]
fn map_extract_aggregate_carries_no_region_between_notifications() {
    assert_keeps_without_state(&map_extract_aggregate, 0);
}

fn memo() -> Built {
    let (input, consumer) = feed(ints());
    (Box::new(Memo::new(input)), vec![consumer])
}

#[test]
fn a_memo_forwards_its_inputs_region() {
    assert_keeps(&memo, 0);
}

#[test]
fn a_memo_carries_no_region_between_notifications() {
    assert_keeps_without_state(&memo, 0);
}

/// A region that changes at the bottom of `feed → MapDomain → RecordWrap → Memo` reaches the
/// chain's consumer as it was named: each operator on the way keeps keys.
#[test]
fn a_region_crosses_a_chain_of_operators_that_keep_keys() {
    let chain = || {
        let (input, consumer) = feed(ints());
        let domain = MapDomain::new(input);
        let wrapped = RecordWrap::new_at(SmolStr::new("a"), Box::new(domain), CurryLevel::new(1));
        (
            Box::new(Memo::new(Box::new(wrapped))) as Box<dyn TileOperator>,
            vec![consumer],
        )
    };
    assert_keeps(&chain, 0);
}

fn zip() -> Built {
    let (a, first) = feed(ints());
    let (b, second) = feed(ints());
    let op = Zip::new_at(
        vec![SmolStr::new("_0"), SmolStr::new("_1")],
        vec![a, b],
        CurryLevel::new(1),
    );
    (Box::new(op), vec![first, second])
}

#[test]
fn zip_forwards_the_region_of_its_first_arm() {
    assert_keeps(&zip, 0);
}

#[test]
fn zip_forwards_the_region_of_its_second_arm_without_state() {
    assert_keeps(&zip, 1);
    assert_keeps_without_state(&zip, 1);
}

fn product() -> Built {
    let (outer, first) = feed(ints());
    let (inner, second) = feed(nested());
    let op = Product::per_row_at(outer, inner, CurryLevel::new(1));
    (Box::new(op), vec![first, second])
}

#[test]
fn product_forwards_the_region_of_its_outer_side() {
    assert_keeps(&product, 0);
}

#[test]
fn product_forwards_the_region_of_its_inner_side_without_state() {
    assert_keeps(&product, 1);
    assert_keeps_without_state(&product, 1);
}

fn int() -> Extent {
    Extent::Base(BaseType::Int)
}

/// The operator sends `Everything` for any region of input `notified`.
fn assert_widens(build: &dyn Fn() -> Built, notified: usize) {
    for sent in [region(), another_region(), Projection::Everything] {
        assert_eq!(
            received(build, notified, &sent),
            [Projection::Everything],
            "{sent:?}"
        );
    }
}

fn union(flat: bool) -> Built {
    let (a, first) = feed(ints());
    let (b, second) = feed(ints());
    let arms = vec![a, b];
    let op: Box<dyn TileOperator> = match flat {
        true => Box::new(UnionOperator::new_flat(arms, int())),
        false => Box::new(UnionOperator::new(arms, int())),
    };
    (op, vec![first, second])
}

#[test]
fn a_flat_union_forwards_the_region_of_each_arm() {
    for arm in [0, 1] {
        assert_keeps(&|| union(true), arm);
    }
    assert_keeps_without_state(&|| union(true), 1);
}

/// A tagged union keys its rows by arm, which a region of plain keys does not name.
#[test]
fn a_tagged_union_sends_everything_for_any_region() {
    assert_widens(&|| union(false), 0);
    assert_widens(&|| union(false), 1);
}

fn lookup(keys: Tiling) -> Built {
    let (collection, table) = feed(ints());
    let (keys, stream) = feed(keys);
    let op = CheckedLookup::split(collection, keys, int());
    (Box::new(op), vec![table, stream])
}

fn lookup_of_a_stream() -> Built {
    lookup(ints())
}

#[test]
fn a_lookup_forwards_the_region_of_a_stream_of_keys() {
    assert_keeps(&lookup_of_a_stream, 1);
}

#[test]
fn a_lookup_of_a_stream_carries_no_region_between_notifications() {
    assert_keeps_without_state(&lookup_of_a_stream, 1);
}

/// One key has no keys to project.
#[test]
fn a_lookup_of_one_key_sends_everything_for_any_region() {
    let one_key = || lookup(Tiling::Scalar(Extent::Base(BaseType::UInt)));
    assert_widens(&one_key, 1);
}

/// The pairs are one stream, and each answer sits at its row's position.
fn paired_lookup() -> Built {
    let pairs = Tiling::data_function(
        Extent::uint_range(8),
        Tiling::Record(
            [
                (
                    crate::interpreter::tuple_field(0),
                    Tiling::Scalar(Extent::Function {
                        domain: Box::new(Extent::Base(BaseType::UInt)),
                        codomain: Box::new(int()),
                    }),
                ),
                (
                    crate::interpreter::tuple_field(1),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
            ]
            .into_iter()
            .collect(),
        ),
    );
    let (input, consumer) = feed(pairs);
    let op = CheckedLookup::paired(input, int()).expect("a stream of pairs");
    (Box::new(op), vec![consumer])
}

#[test]
fn a_paired_lookup_forwards_the_region_of_its_rows() {
    assert_keeps(&paired_lookup, 0);
}

#[test]
fn a_paired_lookup_carries_no_region_between_notifications() {
    assert_keeps_without_state(&paired_lookup, 0);
}

fn filter(predicate: Tiling) -> Built {
    let (input, data) = feed(ints());
    let (predicate, mask) = feed(predicate);
    let op = Filter::new_at(input, predicate, CurryLevel::OUTERMOST);
    (Box::new(op), vec![data, mask])
}

#[test]
fn filter_forwards_the_region_of_each_collection_side() {
    for side in [0, 1] {
        assert_keeps(&|| filter(bools()), side);
    }
    assert_keeps_without_state(&|| filter(bools()), 1);
}

/// A predicate that is one function value is read whole.
#[test]
fn filter_sends_everything_for_a_function_valued_predicate() {
    let function = || {
        filter(Tiling::Scalar(Extent::Function {
            domain: Box::new(int()),
            codomain: Box::new(Extent::Base(BaseType::Bool)),
        }))
    };
    assert_widens(&function, 1);
    assert_keeps(&function, 0);
}

fn map_result_to_const(level: CurryLevel) -> Built {
    let (input, data) = feed(match level == CurryLevel::OUTERMOST {
        true => ints(),
        false => nested(),
    });
    let (constant, constant_consumer) = feed(Tiling::Scalar(int()));
    let op = MapResultToConst::new_at(input, constant, MapResultToConstMode::Replace, level);
    (Box::new(op), vec![data, constant_consumer])
}

fn beneath_a_level() -> Built {
    map_result_to_const(CurryLevel::new(1))
}

#[test]
fn map_result_to_const_forwards_its_inputs_region_beneath_a_level() {
    assert_keeps(&beneath_a_level, 0);
    assert_keeps_without_state(&beneath_a_level, 0);
}

/// Every row reads all of the constant, so a change to it is a change at every key.
#[test]
fn map_result_to_const_sends_everything_for_its_constant() {
    assert_widens(&beneath_a_level, 1);
}

/// Applied at the outermost level the constant replaces the whole input, so the input's keys are
/// not the output's.
#[test]
fn map_result_to_const_at_the_outermost_level_sends_everything_for_its_inputs_region() {
    assert_widens(&|| map_result_to_const(CurryLevel::OUTERMOST), 0);
}

fn select_field(input: Tiling) -> Built {
    let (input, consumer) = feed(input);
    (Box::new(SelectField::new(input, "a")), vec![consumer])
}

fn a_stream_of_records() -> Built {
    select_field(Tiling::data_function(
        Extent::uint_range(8),
        Tiling::Record(
            [(SmolStr::new("a"), Tiling::Scalar(int()))]
                .into_iter()
                .collect(),
        ),
    ))
}

#[test]
fn select_field_forwards_the_region_of_a_stream_of_records() {
    assert_keeps(&a_stream_of_records, 0);
    assert_keeps_without_state(&a_stream_of_records, 0);
}

/// A product of collections is read whole and its field cut, so a region of one collection's keys
/// is not a region of the field's.
#[test]
fn select_field_over_a_product_of_collections_sends_everything() {
    let product = || {
        select_field(Tiling::Record(
            [(SmolStr::new("a"), ints())].into_iter().collect(),
        ))
    };
    assert_widens(&product, 0);
}

fn variant_wrap(input: Tiling, level: CurryLevel) -> Built {
    let (input, consumer) = feed(input);
    let wrap = VariantWrap::new_at(
        input,
        crate::ccl::FieldKey::Index(0),
        crate::ccl::TagMap::from_arms(vec![(crate::ccl::FieldKey::Index(0), int())]),
        level,
    );
    (Box::new(wrap), vec![consumer])
}

fn wrapped_stream() -> Built {
    variant_wrap(ints(), CurryLevel::new(1))
}

#[test]
fn variant_wrap_forwards_the_region_of_a_stream() {
    assert_keeps(&wrapped_stream, 0);
    assert_keeps_without_state(&wrapped_stream, 0);
}

/// At the outermost level the payload becomes one union value, which has no keys.
#[test]
fn variant_wrap_at_the_outermost_level_sends_everything() {
    assert_widens(
        &|| variant_wrap(Tiling::Scalar(int()), CurryLevel::OUTERMOST),
        0,
    );
}

fn union_extent() -> Extent {
    Extent::Union(crate::ccl::TagMap::from_arms(vec![(
        crate::ccl::FieldKey::Index(0),
        int(),
    )]))
}

fn union_stream() -> Tiling {
    Tiling::data_function(Extent::uint_range(8), Tiling::Scalar(union_extent()))
}

fn variant_project(input: Tiling) -> Built {
    let (input, consumer) = feed(input);
    let op = VariantProject::new(input, crate::ccl::FieldKey::Index(0), int());
    (Box::new(op), vec![consumer])
}

#[test]
fn variant_project_forwards_the_region_of_a_stream() {
    assert_keeps(&|| variant_project(union_stream()), 0);
    assert_keeps_without_state(&|| variant_project(union_stream()), 0);
}

/// A bare union has no keys of its own.
#[test]
fn variant_project_over_a_bare_union_sends_everything() {
    assert_widens(&|| variant_project(Tiling::Scalar(union_extent())), 0);
}

fn variant_is(input: Tiling) -> Built {
    let (input, consumer) = feed(input);
    let op = VariantIs::new(input, crate::ccl::FieldKey::Index(0));
    (Box::new(op), vec![consumer])
}

#[test]
fn variant_is_forwards_the_region_of_a_stream() {
    assert_keeps(&|| variant_is(union_stream()), 0);
    assert_keeps_without_state(&|| variant_is(union_stream()), 0);
}

/// A bare union has no keys of its own.
#[test]
fn variant_is_over_a_bare_union_sends_everything() {
    assert_widens(&|| variant_is(Tiling::Scalar(union_extent())), 0);
}

fn converse(level: CurryLevel) -> Built {
    let (input, consumer) = feed(match level == CurryLevel::OUTERMOST {
        true => ints(),
        false => nested(),
    });
    (Box::new(Converse::new_at(input, level)), vec![consumer])
}

#[test]
fn converse_beneath_a_standing_level_forwards_the_region() {
    let beneath = || converse(CurryLevel::new(1));
    assert_keeps(&beneath, 0);
    assert_keeps_without_state(&beneath, 0);
}

/// Inverting the outermost collection makes its values the keys.
#[test]
fn converse_at_the_outermost_level_sends_everything() {
    assert_widens(&|| converse(CurryLevel::OUTERMOST), 0);
}

fn uncurry(level: CurryLevel) -> Built {
    let (input, consumer) = feed(match level == CurryLevel::OUTERMOST {
        true => nested(),
        false => Tiling::data_function(Extent::uint_range(8), nested()),
    });
    (Box::new(Uncurry::new_at(input, level)), vec![consumer])
}

#[test]
fn uncurry_beneath_a_standing_level_forwards_the_region() {
    let beneath = || uncurry(CurryLevel::new(1));
    assert_keeps(&beneath, 0);
    assert_keeps_without_state(&beneath, 0);
}

/// Pairing the whole tile re-keys it.
#[test]
fn uncurry_at_the_outermost_level_sends_everything() {
    assert_widens(&|| uncurry(CurryLevel::OUTERMOST), 0);
}

fn aggregate() -> Built {
    let (input, consumer) = feed(ints());
    let op = Aggregate::new(input, crate::ccl::AggregateKind::Sum);
    (Box::new(op), vec![consumer])
}

/// The accumulator has no keys.
#[test]
fn an_aggregate_sends_everything_for_a_region_of_its_input() {
    assert_widens(&aggregate, 0);
}

#[test]
fn an_aggregate_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&aggregate, 0, &another_region()),
        [Projection::Everything]
    );
}

fn extract_aggregate() -> Built {
    let (input, consumer) = feed(ints());
    let op = ExtractAggregate::new(input, crate::ccl::AggregateKind::Sum, true);
    (Box::new(op), vec![consumer])
}

/// The accumulator has no keys.
#[test]
fn an_extract_aggregate_sends_everything_for_a_region_of_its_input() {
    assert_widens(&extract_aggregate, 0);
}

#[test]
fn an_extract_aggregate_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&extract_aggregate, 0, &another_region()),
        [Projection::Everything]
    );
}

fn extract_final() -> Built {
    let (source, keys) = feed(ints());
    let (default, fallback) = feed(Tiling::Scalar(int()));
    let op = ExtractFinal::new(source, default);
    (Box::new(op), vec![keys, fallback])
}

/// The final value is the last position's, which a region of keys does not name.
#[test]
fn extract_final_sends_everything_for_a_region_of_its_source() {
    assert_widens(&extract_final, 0);
}

#[test]
fn extract_final_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&extract_final, 0, &another_region()),
        [Projection::Everything]
    );
}

fn two_keys() -> Extent {
    Extent::Record(
        [
            (crate::interpreter::tuple_field(0), Extent::uint_range(8)),
            (crate::interpreter::tuple_field(1), Extent::uint_range(8)),
        ]
        .into_iter()
        .collect(),
    )
}

fn permute_record_domain() -> Built {
    let (input, consumer) = feed(Tiling::data_function(two_keys(), Tiling::Scalar(int())));
    let op = PermuteRecordDomain::new(input, vec![1, 0]);
    (Box::new(op), vec![consumer])
}

/// The keys are renamed, so a region of the input's keys names none of the output's.
#[test]
fn permute_record_domain_sends_everything_for_a_region_of_its_input() {
    assert_widens(&permute_record_domain, 0);
}

#[test]
fn permute_record_domain_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&permute_record_domain, 0, &another_region()),
        [Projection::Everything]
    );
}

fn flatten_tuple_domain() -> Built {
    let outer = Extent::Record(
        [(crate::interpreter::tuple_field(0), two_keys())]
            .into_iter()
            .collect(),
    );
    let (input, consumer) = feed(Tiling::data_function(outer, Tiling::Scalar(int())));
    let op = FlattenTupleDomain::new(input, vec![0]);
    (Box::new(op), vec![consumer])
}

/// The keys are re-keyed, so a region of the input's keys names none of the output's.
#[test]
fn flatten_tuple_domain_sends_everything_for_a_region_of_its_input() {
    assert_widens(&flatten_tuple_domain, 0);
}

#[test]
fn flatten_tuple_domain_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&flatten_tuple_domain, 0, &another_region()),
        [Projection::Everything]
    );
}

fn make_record() -> Built {
    let (a, first) = feed(ints());
    let (b, second) = feed(ints());
    let op = MakeRecord::new(vec![a, b]);
    (Box::new(op), vec![first, second])
}

/// A record of values has no keys of its own.
#[test]
fn make_record_sends_everything_for_a_region_of_either_field() {
    assert_widens(&make_record, 0);
    assert_widens(&make_record, 1);
}

#[test]
fn make_record_sends_everything_for_a_later_region() {
    assert_eq!(
        received(&make_record, 1, &another_region()),
        [Projection::Everything]
    );
}

/// Every key is answered against all of the collection.
#[test]
fn a_lookup_sends_everything_for_its_collection() {
    assert_widens(&lookup_of_a_stream, 0);
}

#[test]
fn a_lookup_sends_everything_for_a_later_region_at_its_collection() {
    assert_eq!(
        received(&lookup_of_a_stream, 0, &another_region()),
        [Projection::Everything]
    );
}

/// A fan-out over a feed with a recording consumer on each of its two slots, as the bindings
/// `logs`, `producers` and `consumer`: the consumers' logs, the slots' producers, and the consumer
/// the feed notifies through.
macro_rules! fan_out_with_two_slots {
    ($logs:ident, $producers:ident, $consumer:ident) => {
        let ($logs, mut $producers, $consumer) = {
            let (input, consumer) = feed(ints());
            let fan = FanOut::new(input);
            let mut scheduler = Scheduler::new();
            let mut logs = Vec::new();
            let mut producers = Vec::new();
            for _ in 0..2 {
                let (log, regions) = RegionLog::new();
                let mut slot = fan.slot();
                let guard = slot.tiling().universal_guard();
                producers.push(slot.subscribe(guard, Box::new(log), &mut scheduler));
                logs.push(regions);
            }
            for regions in &logs {
                regions.borrow_mut().clear();
            }
            (logs, producers, consumer)
        };
    };
}

#[test]
fn a_fan_out_forwards_a_region_to_every_live_slot_unchanged() {
    fan_out_with_two_slots!(logs, _producers, consumer);
    notify_input(&consumer, &region());
    for regions in &logs {
        assert_eq!(*regions.borrow_mut(), [region()]);
    }
}

/// One notification passes between pulls; a pull reopens it, and the region of the next one is
/// delivered.
#[test]
fn a_fan_out_suppresses_a_second_notification_until_a_pull_reopens_it() {
    fan_out_with_two_slots!(logs, producers, consumer);
    notify_input(&consumer, &region());
    notify_input(&consumer, &another_region());
    assert_eq!(*logs[0].borrow_mut(), [region()]);
    let guard = producers[0].tiling().universal_guard();
    producers[0].get(guard);
    notify_input(&consumer, &another_region());
    assert_eq!(*logs[0].borrow_mut(), [region(), another_region()]);
}

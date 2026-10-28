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

//! The region an operator's consumer receives for a region of keys that changed at one of its
//! inputs: the keys unchanged where the operator's row of the projection table pulls that input
//! at the projection, and `Everything` where it re-keys or reads the input whole.
//! See `src/interpreter/design-operators.md`, "The notification contract".

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

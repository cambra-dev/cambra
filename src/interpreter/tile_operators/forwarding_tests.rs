//! The region an operator's consumer receives for a region of keys that changed at one of its
//! inputs: the keys unchanged where the operator's row of the projection table pulls that input
//! at the projection, and `Everything` where it re-keys or reads the input whole.
//! See `src/interpreter/design-operators.md`, "The notification contract".

use super::test_helpers::{InputConsumer, NotifyingOp, RegionLog, keys_between, notify_input};
use super::*;
use crate::interpreter::{BaseType, Extent, Projection, Scheduler, Tiling};

/// An operator and the consumers it installed on its inputs, which a test notifies through.
type Built = (Box<dyn TileOperator>, Vec<InputConsumer>);

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

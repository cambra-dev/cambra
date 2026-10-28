//! The notifications of each operator that keeps its input's keys, checked against its answers
//! over scripted growth of its input ([`assert_notification_sound`]): the region it notifies is
//! sound, and it is exactly the region its input notified.
//! See `src/interpreter/design-operators.md`, "Guard translation".

use smol_str::SmolStr;

use super::notification_sound::{
    Expect, Growth, Step, Values, assert_notification_sound, grow, int_stream, int_stream_tiling,
    keys_region,
};
use super::*;
use crate::interpreter::{BaseType, CurryLevel, Extent, Predicate, Projection, Tiling};

type Build = dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>;

fn stream_tiling(values: Values) -> Tiling {
    Tiling::data_function(
        Extent::uint_range(16),
        Tiling::Scalar(Extent::Base(match values {
            Values::Ints => BaseType::Int,
            Values::Bools => BaseType::Bool,
        })),
    )
}

/// Keys that arrive out of order, an `Everything` notification, a step that changes nothing, and
/// completeness that arrives last.
fn out_of_order() -> (Vec<Tile>, Vec<Step>) {
    let none = Predicate::False;
    let tiles = vec![
        int_stream(&[], none.clone()),
        int_stream(&[(7, 70)], none.clone()),
        int_stream(&[(7, 70), (2, 20)], none.clone()),
        int_stream(&[(7, 70), (2, 20)], none),
        int_stream(&[(2, 20), (7, 70)], Predicate::True),
    ];
    let steps = [
        keys_region(&[7]),
        keys_region(&[2]),
        Projection::Nothing,
        Projection::Everything,
    ]
    .into_iter()
    .map(|changed| Step { input: 0, changed })
    .collect();
    (tiles, steps)
}

/// The scripts every operator over one stream runs: four generated and one by hand.
fn scripts(values: Values) -> Vec<(Vec<Tile>, Vec<Step>)> {
    let mut scripts = vec![
        grow(1, 8, Growth::OneAtATime, values),
        grow(2, 6, Growth::Bursts, values),
        grow(3, 10, Growth::CompletenessAndEmpty, values),
        grow(4, 10, Growth::OneAtATime, values),
    ];
    if matches!(values, Values::Ints) {
        scripts.push(out_of_order());
    }
    scripts
}

fn check(build: &Build, values: Values, expect: Expect) {
    for (tiles, steps) in scripts(values) {
        let feeds = [(stream_tiling(values), tiles)];
        assert_notification_sound(build, &feeds, &steps, expect);
    }
}

fn record_wrap(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(RecordWrap::new_at(
        SmolStr::new("a"),
        inputs.remove(0),
        CurryLevel::new(1),
    ))
}

#[test]
fn record_wrap_notifies_exactly_what_changed_over_growth() {
    check(&record_wrap, Values::Ints, Expect::Exact);
}

fn map_domain(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(MapDomain::new(inputs.remove(0)))
}

#[test]
fn map_domain_notifies_exactly_what_changed_over_growth() {
    check(&map_domain, Values::Ints, Expect::Exact);
}

fn memo(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(Memo::new(inputs.remove(0)))
}

#[test]
fn a_memo_notifies_exactly_what_changed_over_growth() {
    check(&memo, Values::Ints, Expect::Exact);
}

fn restrict(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(Restrict::new(inputs.remove(0)))
}

#[test]
fn restrict_notifies_exactly_what_changed_over_growth() {
    check(&restrict, Values::Bools, Expect::Exact);
}

/// A tiling check of the scripts: the generated streams are the tiling the operators are built
/// over.
#[test]
fn the_generated_streams_match_the_integer_stream_tiling() {
    assert_eq!(stream_tiling(Values::Ints), int_stream_tiling());
}

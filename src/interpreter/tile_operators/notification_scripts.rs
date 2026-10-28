//! The notifications of each operator that keeps its input's keys, checked against its answers
//! over scripted growth of its input ([`assert_notification_sound`]): the region it notifies is
//! sound, and it is exactly the region its input notified.
//! See `src/interpreter/design-operators.md`, "Guard translation".

use smol_str::SmolStr;

use super::notification_sound::{
    Expect, Growth, Step, Values, assert_notification_sound, assert_release_sound, grow, grow_many,
    int_stream, int_stream_tiling, keys_region, positions_stream,
};
use super::*;
use crate::interpreter::{BaseType, CurryLevel, Extent, Predicate, Projection, Tiling};

type Build = dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>;

fn stream_tiling(values: Values) -> Tiling {
    Tiling::data_function(
        Extent::uint_range(16),
        Tiling::Scalar(match values {
            Values::Ints => Extent::Base(BaseType::Int),
            Values::Bools => Extent::Base(BaseType::Bool),
            Values::Positions => Extent::uint_range(16),
        }),
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
    let expect = [expect];
    for (tiles, steps) in scripts(values) {
        let feeds = [(stream_tiling(values), tiles)];
        assert_notification_sound(build, &feeds, &steps, &expect);
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

type Shapes<'a> = &'a [(Values, Option<(u64, u64)>)];

/// The scripts every operator over several streams runs: generated, with the inputs moving in
/// turn.
fn check_many(build: &Build, shapes: Shapes, expect: &[Expect]) {
    let growths = [
        (1, 12, Growth::OneAtATime),
        (2, 10, Growth::Bursts),
        (3, 14, Growth::CompletenessAndEmpty),
        (4, 14, Growth::OneAtATime),
        (5, 10, Growth::Bursts),
    ];
    for (seed, steps, growth) in growths {
        let (tiles, script) = grow_many(seed, shapes, steps, growth);
        let feeds: Vec<(Tiling, Vec<Tile>)> = shapes
            .iter()
            .zip(tiles)
            .map(|((values, _), tiles)| (stream_tiling(*values), tiles))
            .collect();
        assert_notification_sound(build, &feeds, &script, expect);
    }
}

fn zip(inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(Zip::new_at(
        vec![SmolStr::new("_0"), SmolStr::new("_1")],
        inputs,
        CurryLevel::new(1),
    ))
}

#[test]
fn zip_notifies_exactly_what_either_arm_changed_over_growth() {
    let shapes = [(Values::Ints, None), (Values::Ints, None)];
    check_many(&zip, &shapes, &[Expect::Exact, Expect::Exact]);
}

fn filter(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let predicate = inputs.remove(1);
    Box::new(Filter::new_at(
        inputs.remove(0),
        predicate,
        CurryLevel::OUTERMOST,
    ))
}

#[test]
fn filter_notifies_exactly_what_its_input_or_its_mask_changed_over_growth() {
    let shapes = [(Values::Ints, None), (Values::Bools, None)];
    check_many(&filter, &shapes, &[Expect::Exact, Expect::Exact]);
}

fn flat_union(inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(UnionOperator::new_flat(inputs, Extent::Base(BaseType::Int)))
}

fn tagged_union(inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(UnionOperator::new(inputs, Extent::Base(BaseType::Int)))
}

/// The arms of a flat union are disjoint slices of one collection.
#[test]
fn a_flat_union_notifies_exactly_what_either_arm_changed_over_growth() {
    let shapes = [(Values::Ints, Some((2, 0))), (Values::Ints, Some((2, 1)))];
    check_many(&flat_union, &shapes, &[Expect::Exact, Expect::Exact]);
}

/// A tagged union keys its rows by arm, so a region of an arm's keys names none of them.
#[test]
fn a_tagged_union_widens_over_growth_even_where_its_arms_share_keys() {
    let shapes = [(Values::Ints, None), (Values::Ints, None)];
    check_many(&tagged_union, &shapes, &[Expect::Widens, Expect::Widens]);
}

fn map_result(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let function = inputs.remove(1);
    Box::new(MapResult::new_at(
        inputs.remove(0),
        function,
        CurryLevel::new(1),
    ))
}

/// The keys of the result are the input's, and a change to the function is a change at every key.
#[test]
fn map_result_notifies_its_inputs_region_and_everything_for_its_function_over_growth() {
    let shapes = [(Values::Positions, None), (Values::Ints, None)];
    check_many(&map_result, &shapes, &[Expect::Exact, Expect::Widens]);
}

/// Rows whose looked-up key arrives after them: the function gains the keys the input's values
/// name, so a change to the function is a change at keys of the input that its own keys do not
/// name.
#[test]
fn map_result_notifies_everything_for_a_function_key_that_answers_rows_already_read() {
    let none = Predicate::False;
    let input = vec![
        positions_stream(&[], none.clone()),
        positions_stream(&[(0, 3)], none.clone()),
        positions_stream(&[(0, 3), (1, 5)], none.clone()),
    ];
    let function = vec![
        int_stream(&[], none.clone()),
        int_stream(&[(3, 30)], none.clone()),
        int_stream(&[(3, 30), (5, 50)], Predicate::True),
    ];
    let feeds = [
        (stream_tiling(Values::Positions), input),
        (stream_tiling(Values::Ints), function),
    ];
    let steps: Vec<Step> = [
        (0, keys_region(&[0])),
        (0, keys_region(&[1])),
        (1, keys_region(&[3])),
        (1, keys_region(&[5])),
    ]
    .into_iter()
    .map(|(input, changed)| Step { input, changed })
    .collect();
    assert_notification_sound(
        &map_result,
        &feeds,
        &steps,
        &[Expect::Exact, Expect::Widens],
    );
    // Soundness alone catches a function operand that keeps its keys.
    assert_notification_sound(&map_result, &feeds, &steps, &[Expect::Sound, Expect::Sound]);
}

/// A stream of records `{a: Int}`: the integer stream with each value wrapped in a record.
fn as_records(tile: Tile) -> Tile {
    let Tile::DataFunction {
        row_starts,
        domain,
        codomain,
        domain_predicate,
        deleted,
    } = tile
    else {
        panic!("a collection, got {tile:?}");
    };
    Tile::DataFunction {
        row_starts,
        domain,
        codomain: Box::new(Tile::record(
            [(SmolStr::new("a"), *codomain)].into_iter().collect(),
        )),
        domain_predicate,
        deleted,
    }
}

fn records_tiling() -> Tiling {
    Tiling::data_function(
        Extent::uint_range(16),
        Tiling::Record(
            [(
                SmolStr::new("a"),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            )]
            .into_iter()
            .collect(),
        ),
    )
}

fn select_field(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(SelectField::new(inputs.remove(0), "a"))
}

#[test]
fn select_field_over_a_stream_of_records_notifies_exactly_what_changed_over_growth() {
    for (seed, steps, growth) in [
        (1, 10, Growth::OneAtATime),
        (2, 8, Growth::Bursts),
        (3, 12, Growth::CompletenessAndEmpty),
    ] {
        let (tiles, script) = grow(seed, steps, growth, Values::Ints);
        let feeds = [(
            records_tiling(),
            tiles.into_iter().map(as_records).collect::<Vec<_>>(),
        )];
        assert_notification_sound(&select_field, &feeds, &script, &[Expect::Exact]);
    }
}

/// The states of a product `{a: Int stream, b: Int stream}` that gains rows in either field in
/// turn, and the steps that reach them, each notifying the keys the field gained.
fn product_script(seed: u64, steps: usize) -> (Tiling, Vec<Tile>, Vec<Step>) {
    use super::notification_sound::{Rng, Stream};
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut fields = [
        Stream::new(Values::Ints, None),
        Stream::new(Values::Ints, None),
    ];
    let state = |fields: &[Stream; 2]| {
        Tile::record(
            [
                (SmolStr::new("a"), fields[0].tile()),
                (SmolStr::new("b"), fields[1].tile()),
            ]
            .into_iter()
            .collect(),
        )
    };
    let mut tiles = vec![state(&fields)];
    let mut script = Vec::new();
    for _ in 0..steps {
        let field = (rng.next() % 2) as usize;
        let changed = fields[field].advance(&mut rng, Growth::OneAtATime);
        tiles.push(state(&fields));
        script.push(Step { input: 0, changed });
    }
    let tiling = Tiling::Record(
        [
            (SmolStr::new("a"), stream_tiling(Values::Ints)),
            (SmolStr::new("b"), stream_tiling(Values::Ints)),
        ]
        .into_iter()
        .collect(),
    );
    (tiling, tiles, script)
}

/// A product of collections is read whole and its field cut, so a region of keys named by the
/// product's feed is a region of the product, not of the field: the selection widens it.
#[test]
fn select_field_over_a_product_of_collections_widens_over_growth() {
    for seed in [1, 2, 3, 4] {
        let (tiling, tiles, script) = product_script(seed, 12);
        let feeds = [(tiling, tiles)];
        assert_notification_sound(&select_field, &feeds, &script, &[Expect::Widens]);
    }
}

/// A release of some of the selected field's keys releases every other field whole, and what is
/// left of the field reads as it did.
#[test]
fn select_field_releases_only_what_nothing_beneath_it_reads_again() {
    let (tiling, tiles, _) = product_script(7, 12);
    let last = tiles.len() - 1;
    let feeds = [(tiling, tiles)];
    assert_release_sound(&select_field, &feeds, &[last], &keys_region(&[1, 2, 3]));
    let (tiles, _) = grow(5, 12, Growth::OneAtATime, Values::Ints);
    let last = tiles.len() - 1;
    let feeds = [(
        records_tiling(),
        tiles.into_iter().map(as_records).collect::<Vec<_>>(),
    )];
    assert_release_sound(&select_field, &feeds, &[last], &keys_region(&[1, 2, 3]));
}

//! The notifications of each operator that keeps its input's keys, checked against its answers
//! over scripted growth of its input ([`assert_notification_sound`]): the region it notifies is
//! sound, and it is exactly the region its input notified.
//! See `src/interpreter/design-operators.md`, "Guard translation".

use smol_str::SmolStr;

use super::notification_sound::{
    Expect, FeedOp, Growth, Step, Values, assert_notification_sound,
    assert_notifications_survive_the_gates, assert_release_sound, grow, grow_many, int_stream,
    int_stream_tiling, keys_region, positions_stream,
};
use super::test_helpers::RegionLog;
use super::*;
use crate::interpreter::{
    BaseType, ColumnValue, CurryLevel, Extent, Predicate, Projection, Tiling,
};

type Build = dyn Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator>;

fn pair_keys() -> Extent {
    Extent::Record(
        [
            (crate::interpreter::tuple_field(0), Extent::uint_range(4)),
            (crate::interpreter::tuple_field(1), Extent::uint_range(4)),
        ]
        .into_iter()
        .collect(),
    )
}

fn stream_tiling(values: Values) -> Tiling {
    let keys = Extent::uint_range(16);
    let scalar = |extent| Tiling::data_function(keys.clone(), Tiling::Scalar(extent));
    match values {
        Values::Ints => scalar(Extent::Base(BaseType::Int)),
        Values::Bools => scalar(Extent::Base(BaseType::Bool)),
        Values::Positions => scalar(Extent::uint_range(16)),
        Values::Pairs => {
            Tiling::data_function(pair_keys(), Tiling::Scalar(Extent::Base(BaseType::Int)))
        }
        Values::PairsInARecord => Tiling::data_function(
            Extent::Record(
                [(crate::interpreter::tuple_field(0), pair_keys())]
                    .into_iter()
                    .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        ),
        Values::Variants => Tiling::data_function(
            keys,
            Tiling::Scalar(Extent::Union(crate::ccl::TagMap::from_arms(vec![(
                crate::ccl::FieldKey::Index(0),
                Extent::Base(BaseType::Int),
            )]))),
        ),
        Values::Nested3 => Tiling::data_function(
            keys.clone(),
            Tiling::data_function(
                keys.clone(),
                Tiling::data_function(keys, Tiling::Scalar(Extent::Base(BaseType::Int))),
            ),
        ),
        Values::Nested => Tiling::data_function(
            keys.clone(),
            Tiling::data_function(keys, Tiling::Scalar(Extent::Base(BaseType::Int))),
        ),
    }
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
/// product's feed is a region of the product, not of the field: the selection widens it. A keep
/// would also be sound here, since a product names no keys of its own, so the `Widens` variant
/// carries the decision, and `select_field_over_a_product_of_collections_sends_everything` pins
/// it.
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

/// The growth scripts of one nested input: every element added to a group notifies the group's
/// outer key.
fn check_nested(build: &Build, expect: Expect) {
    let expect = [expect];
    for (seed, steps, growth) in [
        (1, 12, Growth::OneAtATime),
        (2, 10, Growth::Bursts),
        (3, 14, Growth::CompletenessAndEmpty),
        (4, 14, Growth::OneAtATime),
    ] {
        let (tiles, script) = grow(seed, steps, growth, Values::Nested);
        let feeds = [(stream_tiling(Values::Nested), tiles)];
        assert_notification_sound(build, &feeds, &script, &expect);
    }
}

fn map_aggregate(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(MapAggregate::new(
        inputs.remove(0),
        crate::ccl::AggregateKind::Sum,
    ))
}

#[test]
fn map_aggregate_notifies_the_outer_key_of_a_group_that_gained_an_element() {
    check_nested(&map_aggregate, Expect::Exact);
}

fn map_extract_aggregate(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let fold = MapAggregate::new(inputs.remove(0), crate::ccl::AggregateKind::Sum);
    Box::new(MapExtractAggregate::new(
        Box::new(fold),
        crate::ccl::AggregateKind::Sum,
    ))
}

#[test]
fn map_extract_aggregate_notifies_the_outer_key_of_a_group_that_gained_an_element() {
    check_nested(&map_extract_aggregate, Expect::Exact);
}

fn converse(level: CurryLevel) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    move |mut inputs| Box::new(Converse::new_at(inputs.remove(0), level))
}

/// Beneath a standing level the outer keys stand, and only the group under one is inverted.
#[test]
fn converse_beneath_a_level_notifies_the_outer_key_of_a_group_that_gained_an_element() {
    check_nested(&converse(CurryLevel::new(1)), Expect::Exact);
}

/// At the outermost level the values become the keys, so a changed key names none of the output's.
#[test]
fn converse_at_the_outermost_level_widens_over_growth() {
    check(
        &converse(CurryLevel::OUTERMOST),
        Values::Ints,
        Expect::Widens,
    );
}

fn uncurry(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(Uncurry::new(inputs.remove(0)))
}

/// Pairing the whole tile re-keys it: an outer key's group becomes pairs keyed by both keys.
#[test]
fn uncurry_at_the_outermost_level_widens_over_growth() {
    check_nested(&uncurry, Expect::Widens);
}

/// The scripts of an operator over a nested input and a constant that never changes.
fn check_with_constant(
    build: &Build,
    input: Values,
    constant: Tile,
    constant_tiling: Tiling,
    expect: Expect,
) {
    for (seed, steps, growth) in [
        (1, 12, Growth::OneAtATime),
        (2, 10, Growth::Bursts),
        (3, 14, Growth::CompletenessAndEmpty),
    ] {
        let (tiles, script) = grow(seed, steps, growth, input);
        let feeds = [
            (stream_tiling(input), tiles),
            (constant_tiling.clone(), vec![constant.clone()]),
        ];
        assert_notification_sound(build, &feeds, &script, &[expect, Expect::Widens]);
    }
}

fn map_result_to_const(
    level: CurryLevel,
) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    move |mut inputs| {
        let constant = inputs.remove(1);
        Box::new(MapResultToConst::new_at(
            inputs.remove(0),
            constant,
            MapResultToConstMode::Replace,
            level,
        ))
    }
}

fn int_constant() -> (Tile, Tiling) {
    (
        Tile::Scalar(ColumnValue::Ints(vec![7])),
        Tiling::Scalar(Extent::Base(BaseType::Int)),
    )
}

/// The constant never changes in these scripts, and a scalar announces only everything, so its
/// widening is pinned by `map_result_to_const_sends_everything_for_its_constant`.
#[test]
fn map_result_to_const_beneath_a_level_notifies_its_inputs_region() {
    let (constant, tiling) = int_constant();
    check_with_constant(
        &map_result_to_const(CurryLevel::new(1)),
        Values::Nested,
        constant,
        tiling,
        Expect::Exact,
    );
}

/// At the outermost level the constant replaces the whole input.
#[test]
fn map_result_to_const_at_the_outermost_level_widens_its_inputs_region() {
    let (constant, tiling) = int_constant();
    check_with_constant(
        &map_result_to_const(CurryLevel::OUTERMOST),
        Values::Ints,
        constant,
        tiling,
        Expect::Widens,
    );
}

fn product(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let inner = inputs.remove(1);
    Box::new(Product::per_row_at(
        inputs.remove(0),
        inner,
        CurryLevel::new(1),
    ))
}

#[test]
fn product_notifies_exactly_what_either_side_changed_over_growth() {
    let shapes = [(Values::Ints, None), (Values::Nested, None)];
    check_many(&product, &shapes, &[Expect::Exact, Expect::Exact]);
}

fn aggregate(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(Aggregate::new(
        inputs.remove(0),
        crate::ccl::AggregateKind::Sum,
    ))
}

/// The accumulator has no keys, so a change to any key is a change to it.
#[test]
fn an_aggregate_widens_over_growth() {
    check(&aggregate, Values::Ints, Expect::Widens);
}

fn extract_aggregate(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let fold = Aggregate::new(inputs.remove(0), crate::ccl::AggregateKind::Sum);
    Box::new(ExtractAggregate::new(
        Box::new(fold),
        crate::ccl::AggregateKind::Sum,
        true,
    ))
}

/// The aggregate beneath it already widens, which masks a keep in the extract, and a scalar input
/// announces only everything. The extract's decision is pinned by
/// `an_extract_aggregate_sends_everything_for_a_region_of_its_input`.
#[test]
fn an_extract_aggregate_widens_over_growth() {
    check(&extract_aggregate, Values::Ints, Expect::Widens);
}

fn extract_final(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let default = inputs.remove(1);
    Box::new(ExtractFinal::new(inputs.remove(0), default))
}

/// The final value is the last position's, which a region of keys does not name.
#[test]
fn extract_final_widens_over_growth() {
    let (default, tiling) = int_constant();
    check_with_constant(
        &extract_final,
        Values::Ints,
        default,
        tiling,
        Expect::Widens,
    );
}

fn make_record(inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(MakeRecord::new(inputs))
}

/// A record of values has no keys of its own: an input's region is the region of its field.
#[test]
fn make_record_routes_each_inputs_region_to_its_field_over_growth() {
    let shapes = [(Values::Ints, None), (Values::Ints, None)];
    check_many(
        &make_record,
        &shapes,
        &[Expect::Routed("_0"), Expect::Routed("_1")],
    );
}

fn permute_record_domain(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(PermuteRecordDomain::new(inputs.remove(0), vec![1, 0]))
}

/// The keys are renamed. A region of record keys has no spelling, so the input notifies
/// everything and the check is of soundness only; the decision is pinned by
/// `permute_record_domain_sends_everything_for_a_region_of_its_input`.
#[test]
fn permute_record_domain_notifies_soundly_over_growth() {
    check(&permute_record_domain, Values::Pairs, Expect::Sound);
}

fn flatten_tuple_domain(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(FlattenTupleDomain::new(inputs.remove(0), vec![0]))
}

/// The keys are re-keyed. A region of record keys has no spelling, so the input notifies
/// everything and the check is of soundness only; the decision is pinned by
/// `flatten_tuple_domain_sends_everything_for_a_region_of_its_input`.
#[test]
fn flatten_tuple_domain_notifies_soundly_over_growth() {
    check(&flatten_tuple_domain, Values::PairsInARecord, Expect::Sound);
}

/// A release of rows the mask rejected, and of rows it kept, leaves the rest answering as a fresh
/// pull does.
#[test]
fn filter_releases_what_nothing_beneath_it_reads_again() {
    let shapes = [(Values::Ints, None), (Values::Bools, None)];
    for seed in [1, 2, 3] {
        let (tiles, _) = grow_many(seed, &shapes, 16, Growth::Bursts);
        let at: Vec<usize> = tiles.iter().map(|states| states.len() - 1).collect();
        let feeds: Vec<(Tiling, Vec<Tile>)> = shapes
            .iter()
            .zip(tiles)
            .map(|((values, _), tiles)| (stream_tiling(*values), tiles))
            .collect();
        assert_release_sound(&filter, &feeds, &at, &keys_region(&[0, 1, 2, 3]));
        assert_release_sound(&filter, &feeds, &at, &keys_region(&[4, 7]));
    }
}

/// The constant is read by every row, so releasing rows of the output never releases it.
#[test]
fn map_result_to_const_releases_rows_and_keeps_its_constant() {
    let (constant, constant_tiling) = int_constant();
    for seed in [1, 2, 3] {
        let (tiles, _) = grow(seed, 14, Growth::Bursts, Values::Nested);
        let last = tiles.len() - 1;
        let feeds = [
            (stream_tiling(Values::Nested), tiles),
            (constant_tiling.clone(), vec![constant.clone()]),
        ];
        assert_release_sound(
            &map_result_to_const(CurryLevel::new(1)),
            &feeds,
            &[last, 0],
            &keys_region(&[0, 1, 2]),
        );
    }
}

/// Two slots of one fan-out: the input is released only what both slots released, so a release by
/// one slot leaves the other its rows.
#[test]
fn a_fan_out_releases_the_meet_of_its_slots_releases() {
    let (tiles, _) = grow(2, 12, Growth::Bursts, Values::Ints);
    let last = tiles.len() - 1;
    let (feed, handle) = FeedOp::new(stream_tiling(Values::Ints), tiles);
    handle.advance_to(last);
    let fan = FanOut::new(Box::new(feed));
    let mut scheduler = Scheduler::new();
    let mut slots = [fan.slot(), fan.slot()];
    let tiling = stream_tiling(Values::Ints);
    let guard = slots[0].tiling().universal_guard();
    let (log_a, _regions_a) = RegionLog::new(true);
    let (log_b, _regions_b) = RegionLog::new(true);
    let mut first = slots[0].subscribe(guard.clone(), Box::new(log_a), &mut scheduler);
    let mut second = slots[1].subscribe(guard, Box::new(log_b), &mut scheduler);
    let region = keys_region(&[0, 1, 2, 3]);
    first.get(region.guard(&tiling));
    first.release(region.guard(&tiling));
    let mut got = second.get(region.guard(&tiling));
    got.compact();
    let mut expected = {
        let (tiles, _) = grow(2, 12, Growth::Bursts, Values::Ints);
        tiles[tiles.len() - 1].clone()
    };
    expected.restrict_to(&region, &tiling);
    expected.compact();
    assert_eq!(
        crate::interpreter::sort_function_by_domain(got),
        crate::interpreter::sort_function_by_domain(expected),
        "the second slot lost rows the first released"
    );
}

fn fan_out_slot(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    FanOut::new(inputs.remove(0)).slot()
}

/// The fan-out passes its input's region to a slot, and suppresses one inside what passed since
/// the last pull.
#[test]
fn a_fan_out_slot_notifies_exactly_what_its_input_changed_over_growth() {
    check(&fan_out_slot, Values::Ints, Expect::Exact);
}

fn int_extent() -> Extent {
    Extent::Base(BaseType::Int)
}

fn union_of_ints() -> crate::ccl::TagMap<Extent> {
    crate::ccl::TagMap::from_arms(vec![(crate::ccl::FieldKey::Index(0), int_extent())])
}

fn variant_project(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(VariantProject::new(
        inputs.remove(0),
        crate::ccl::FieldKey::Index(0),
        int_extent(),
    ))
}

#[test]
fn variant_project_notifies_exactly_what_a_stream_of_variants_changed_over_growth() {
    check(&variant_project, Values::Variants, Expect::Exact);
}

fn variant_is(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    Box::new(VariantIs::new(
        inputs.remove(0),
        crate::ccl::FieldKey::Index(0),
    ))
}

#[test]
fn variant_is_notifies_exactly_what_a_stream_of_variants_changed_over_growth() {
    check(&variant_is, Values::Variants, Expect::Exact);
}

fn variant_wrap(level: CurryLevel) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    move |mut inputs| {
        Box::new(VariantWrap::new_at(
            inputs.remove(0),
            crate::ccl::FieldKey::Index(0),
            union_of_ints(),
            level,
        ))
    }
}

#[test]
fn variant_wrap_notifies_exactly_what_a_stream_of_payloads_changed_over_growth() {
    check(
        &variant_wrap(CurryLevel::new(1)),
        Values::Ints,
        Expect::Exact,
    );
}

/// A scalar input that is unknown and then takes a value, which it can announce only as
/// everything: a scalar that has been called complete does not change.
fn scalar_script(
    unknown: Tile,
    known: Tile,
    tiling: Tiling,
) -> (Vec<(Tiling, Vec<Tile>)>, Vec<Step>) {
    let step = Step {
        input: 0,
        changed: Projection::Everything,
    };
    (vec![(tiling, vec![unknown, known])], vec![step])
}

/// At the outermost level the payload becomes one union value, which has no keys. A scalar input
/// announces only everything, so keeping and widening send the same region here: the decision is
/// pinned by `variant_wrap_at_the_outermost_level_sends_everything`, and this checks the answers.
#[test]
fn variant_wrap_at_the_outermost_level_is_sound_over_a_changing_scalar() {
    for v in [1, 2, 3] {
        let (feeds, steps) = scalar_script(
            Tile::Scalar(ColumnValue::Ints(vec![])),
            Tile::Scalar(ColumnValue::Ints(vec![v])),
            Tiling::Scalar(int_extent()),
        );
        assert_notification_sound(
            &variant_wrap(CurryLevel::OUTERMOST),
            &feeds,
            &steps,
            &[Expect::Widens],
        );
    }
}

/// A bare union has no keys of its own. As above, a scalar input announces only everything: the
/// decision is pinned by `variant_project_over_a_bare_union_sends_everything`.
#[test]
fn variant_project_over_a_bare_union_is_sound_over_a_changing_scalar() {
    let union = |values: Vec<i64>| {
        let rows = (0..values.len()).collect();
        Tile::Scalar(ColumnValue::Union(crate::ccl::TagMap::from_arms(vec![(
            crate::ccl::FieldKey::Index(0),
            crate::interpreter::UnionArm::new(rows, ColumnValue::Ints(values)),
        )])))
    };
    for v in [1, 2, 3] {
        let (feeds, steps) = scalar_script(
            union(vec![]),
            union(vec![v]),
            Tiling::Scalar(Extent::Union(union_of_ints())),
        );
        assert_notification_sound(&variant_project, &feeds, &steps, &[Expect::Widens]);
        assert_notification_sound(&variant_is, &feeds, &steps, &[Expect::Widens]);
    }
}

fn uncurry_at(level: CurryLevel) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    move |mut inputs| Box::new(Uncurry::new_at(inputs.remove(0), level))
}

/// Beneath a standing level the outer keys stand, and the pairing happens inside each group.
#[test]
fn uncurry_beneath_a_level_notifies_the_outer_key_of_a_group_that_gained_an_element() {
    let uncurry = uncurry_at(CurryLevel::new(1));
    for (seed, steps, growth) in [
        (1, 14, Growth::OneAtATime),
        (2, 10, Growth::Bursts),
        (3, 14, Growth::CompletenessAndEmpty),
        (4, 14, Growth::OneAtATime),
    ] {
        let (tiles, script) = grow(seed, steps, growth, Values::Nested3);
        let feeds = [(stream_tiling(Values::Nested3), tiles)];
        assert_notification_sound(&uncurry, &feeds, &script, &[Expect::Exact]);
    }
}

fn checked_lookup(mut inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    let keys = inputs.remove(1);
    let option = Extent::Union(crate::ccl::TagMap::from_arms(vec![
        (
            crate::ccl::FieldKey::Name(crate::ccl::V_NONE),
            Extent::Base(BaseType::Unit),
        ),
        (crate::ccl::FieldKey::Name(crate::ccl::V_SOME), int_extent()),
    ]));
    Box::new(CheckedLookup::split(inputs.remove(0), keys, option))
}

/// The answer takes the keys' shape: each answer sits at its key's position, and the collection is
/// read whole, so a change to it is a change at every key.
#[test]
fn a_lookup_notifies_its_keys_region_and_everything_for_its_collection_over_growth() {
    let shapes = [(Values::Ints, None), (Values::Positions, None)];
    check_many(&checked_lookup, &shapes, &[Expect::Widens, Expect::Exact]);
}

/// The keys of a stream as the function `IterateExtent` over a source's domain answers: each key
/// maps to itself.
fn as_identity(tile: Tile) -> Tile {
    let Tile::DataFunction {
        domain,
        domain_predicate,
        deleted,
        ..
    } = tile
    else {
        panic!("a collection, got {tile:?}");
    };
    Tile::data_function(
        domain.clone(),
        Box::new(Tile::Scalar(domain)),
        domain_predicate,
        deleted,
    )
}

/// The result's keys are the input's, and the rows are read from the source at them.
#[test]
fn map_result_with_source_notifies_exactly_what_its_keys_changed_over_growth() {
    use crate::interpreter::{TestDataSource, Value};
    use std::sync::{Arc, Mutex};
    let source = Arc::new(Mutex::new(TestDataSource::new(
        "source1",
        crate::ccl::Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    source.lock_now().add_data(
        &(0..12)
            .map(|k| (Value::UInt(k), Value::Int(k as i64 * 10)))
            .collect::<Vec<_>>(),
    );
    let tiling = IterateExtent::new(Extent::DataSourceDomain(source.clone()))
        .tiling()
        .clone();
    let build = |mut inputs: Vec<Box<dyn TileOperator>>| -> Box<dyn TileOperator> {
        Box::new(MapResultWithSource::new(source.clone(), inputs.remove(0)))
    };
    for (seed, steps, growth) in [
        (1, 10, Growth::OneAtATime),
        (2, 8, Growth::Bursts),
        (3, 12, Growth::CompletenessAndEmpty),
    ] {
        let (tiles, script) = grow(seed, steps, growth, Values::Ints);
        let feeds = [(
            tiling.clone(),
            tiles.into_iter().map(as_identity).collect::<Vec<_>>(),
        )];
        assert_notification_sound(&build, &feeds, &script, &[Expect::Exact]);
    }
}

/// `SelectField("_0")` over `MakeRecord(a, b)`, directly and through a memo and a fan-out's slot.
fn select_over_make_record(
    through: Through,
) -> impl Fn(Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    move |inputs| {
        let record: Box<dyn TileOperator> = Box::new(MakeRecord::new(inputs));
        let record: Box<dyn TileOperator> = match through {
            Through::Nothing => record,
            Through::Memo => Box::new(Memo::new(record)),
            Through::FanOutSlot => FanOut::new(record).slot(),
        };
        Box::new(SelectField::new(record, "_0"))
    }
}

#[derive(Clone, Copy)]
enum Through {
    Nothing,
    Memo,
    FanOutSlot,
}

/// A change to the field that is selected arrives as that field's region, and a change to the
/// other field wakes nothing.
fn check_product_routing(through: Through) {
    let shapes = [(Values::Ints, None), (Values::Ints, None)];
    check_many(
        &select_over_make_record(through),
        &shapes,
        &[Expect::Exact, Expect::Silent],
    );
}

#[test]
fn select_field_over_make_record_notifies_the_selected_fields_region_only() {
    check_product_routing(Through::Nothing);
}

#[test]
fn select_field_over_a_memo_of_make_record_notifies_the_selected_fields_region_only() {
    check_product_routing(Through::Memo);
}

#[test]
fn select_field_over_a_fan_out_of_make_record_notifies_the_selected_fields_region_only() {
    check_product_routing(Through::FanOutSlot);
}

/// The other field changes first and nothing pulls, then the selected field changes.
#[test]
fn a_change_to_the_selected_field_after_one_to_the_other_still_notifies() {
    let none = Predicate::False;
    let a = vec![
        int_stream(&[], none.clone()),
        int_stream(&[(2, 20)], none.clone()),
    ];
    let b = vec![
        int_stream(&[], none.clone()),
        int_stream(&[(7, 70)], none.clone()),
    ];
    let feeds = [
        (stream_tiling(Values::Ints), a),
        (stream_tiling(Values::Ints), b),
    ];
    let steps = [(1, keys_region(&[7])), (0, keys_region(&[2]))]
        .into_iter()
        .map(|(input, changed)| Step { input, changed })
        .collect::<Vec<_>>();
    for through in [Through::Nothing, Through::Memo, Through::FanOutSlot] {
        assert_notification_sound(
            &select_over_make_record(through),
            &feeds,
            &steps,
            &[Expect::Exact, Expect::Silent],
        );
    }
}

/// Behind the gates of a consumer that pulls, with no pull between the steps, the consumer hears
/// every change: a gate that passed the region of one field must still pass the region of the
/// other. `MakeRecord` is selected from directly, through a memo and through a fan-out's slot.
#[test]
fn a_consumer_that_pulls_hears_every_field_of_a_record_behind_the_gates() {
    let shapes = [(Values::Ints, None), (Values::Ints, None)];
    let (repeated_feeds, repeated_steps) = repeated_region_script();
    for through in [Through::Nothing, Through::Memo, Through::FanOutSlot] {
        // One change announced as everything and the next as the keys it added, with a pull
        // between them: a gate that a pull does not reset suppresses the second.
        assert_notifications_survive_the_gates(
            &select_over_make_record(through),
            &repeated_feeds,
            &repeated_steps,
            &[0],
        );
        for (seed, steps, growth) in [
            (1, 8, Growth::OneAtATime),
            (2, 6, Growth::Bursts),
            (3, 10, Growth::CompletenessAndEmpty),
            (4, 8, Growth::OneAtATime),
        ] {
            let (tiles, script) = grow_many(seed, &shapes, steps, growth);
            let feeds: Vec<(Tiling, Vec<Tile>)> = shapes
                .iter()
                .zip(tiles)
                .map(|((values, _), tiles)| (stream_tiling(*values), tiles))
                .collect();
            let pulls: Vec<usize> = (2..script.len()).step_by(3).collect();
            for pulls_after in [&[][..], &pulls[..]] {
                assert_notifications_survive_the_gates(
                    &select_over_make_record(through),
                    &feeds,
                    &script,
                    pulls_after,
                );
            }
        }
    }
}

/// The same behind the gates for the other operators whose gate matters: the ones that share one
/// consumer between several inputs and the memo.
#[test]
fn a_consumer_that_pulls_hears_every_change_to_every_input_behind_the_gates() {
    let two = [(Values::Ints, None), (Values::Ints, None)];
    let operators: Vec<Box<Build>> = vec![
        Box::new(make_record),
        Box::new(zip),
        Box::new(|inputs| Box::new(Memo::new(make_record(inputs)))),
    ];
    for build in &operators {
        for (seed, steps, growth) in [(5, 10, Growth::OneAtATime), (6, 8, Growth::Bursts)] {
            let (tiles, script) = grow_many(seed, &two, steps, growth);
            let feeds: Vec<(Tiling, Vec<Tile>)> = two
                .iter()
                .zip(tiles)
                .map(|((values, _), tiles)| (stream_tiling(*values), tiles))
                .collect();
            let pulls: Vec<usize> = (2..script.len()).step_by(3).collect();
            assert_notifications_survive_the_gates(&**build, &feeds, &script, &[]);
            assert_notifications_survive_the_gates(&**build, &feeds, &script, &pulls);
        }
    }
}

/// The feeds and steps of a script in which one change is announced as everything and the next as
/// the keys it added, so that after a pull between them the second is inside what passed before.
fn repeated_region_script() -> (Vec<(Tiling, Vec<Tile>)>, Vec<Step>) {
    let none = Predicate::False;
    let a = vec![
        int_stream(&[], none.clone()),
        int_stream(&[(2, 20)], none.clone()),
        int_stream(&[(2, 20), (5, 50)], none.clone()),
    ];
    let b = vec![int_stream(&[], none.clone())];
    let feeds = vec![
        (stream_tiling(Values::Ints), a),
        (stream_tiling(Values::Ints), b),
    ];
    let steps = [(0, Projection::Everything), (0, keys_region(&[5]))]
        .into_iter()
        .map(|(input, changed)| Step { input, changed })
        .collect::<Vec<_>>();
    (feeds, steps)
}

/// A pull opens the gates again: a region inside what passed before the pull, here the keys an
/// earlier notification of everything covered, must reach the consumer after it.
#[test]
fn a_gate_that_a_pull_reopened_passes_a_region_inside_what_passed_before_it() {
    let (feeds, steps) = repeated_region_script();
    for through in [Through::Nothing, Through::Memo, Through::FanOutSlot] {
        assert_notifications_survive_the_gates(
            &select_over_make_record(through),
            &feeds,
            &steps,
            &[0],
        );
    }
}

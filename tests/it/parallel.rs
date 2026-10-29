//! The inline driver on small programs: a `main` pipeline pulled by row range through chains and
//! merged at the breaker equals the same pipeline pulled whole.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use indoc::{formatdoc, indoc};

use cambra::{
    ccl::{
        AggregateKind,
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    },
    interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
        Value,
        parallel::{BreakerKind, Config, PooledRun, plan_inline},
    },
};

/// `[x + 1 for x in [0, 1, …, rows - 1]]`: a finite source, two streaming maps, `main`.
fn program(rows: u64) -> String {
    let items: Vec<String> = (0..rows).map(|i| i.to_string()).collect();
    format!("[x + 1 for x in [{}]]", items.join(", "))
}

/// `fold([x + 1 for x in [0, 1, …, rows - 1]])`: the same chain into an aggregate.
fn folded(fold: &str, rows: u64) -> String {
    format!("{fold}({})", program(rows))
}

/// The collection as `(position, value)` pairs in position order, whatever order the tile
/// holds them in.
fn entries(tile: &Tile) -> Vec<(u64, i64)> {
    let Tile::DataFunction {
        domain, codomain, ..
    } = tile
    else {
        panic!("a collection, got {tile:?}");
    };
    let (ColumnValue::UInts(keys), Tile::Scalar(ColumnValue::Ints(values))) =
        (domain, codomain.as_ref())
    else {
        panic!("positions to ints, got {tile:?}");
    };
    let mut pairs: Vec<(u64, i64)> = keys.iter().copied().zip(values.iter().copied()).collect();
    pairs.sort_unstable();
    pairs
}

/// `source`'s `main` output pulled whole on this thread, as the scheduler loop pulls it.
fn whole_pull(source: String) -> Tile {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(source);
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    ctx.scheduler().check_for_notifications();
    let producer = compiled
        .main_mut()
        .and_then(|output| output.producer.as_mut())
        .expect("a main output");
    let tile = producer.get(producer.tiling().universal_guard());
    assert!(
        tile.is_terminal(),
        "a literal source is complete on its first pull"
    );
    tile
}

/// The collection program's `main` output pulled whole, as position-ordered pairs.
fn pulled_whole(rows: u64) -> Vec<(u64, i64)> {
    entries(&whole_pull(program(rows)))
}

/// `code` run through the inline driver with morsels of `morsel_rows` rows until `main` is
/// terminal, and what `main` then holds.
fn dispatched(code: &str, morsel_rows: u64) -> Tile {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled =
        compile_program(&mut ctx, &LoadedProgram::test(code), consumer).expect("compiles");
    let config = Config { morsel_rows };
    let mut run = PooledRun::start(&mut ctx, &mut compiled, &mut None, &config, Box::new(|| {}))
        .expect("a pipeline");
    let mut main = run.take_main().expect("a main output");
    let universal = main.tiling().universal_guard();
    for _ in 0..4096 {
        ctx.scheduler().check_for_notifications();
        run.lap();
        let tile = main.get(universal.clone());
        if tile.is_terminal() {
            return tile;
        }
    }
    panic!("the run of {code} finishes");
}

/// `Domain([first, last])`.
fn range(first: u64, last: u64) -> TileGuard {
    let at_or_below = |v: u64| Predicate::at_or_below(Value::UInt(v));
    let admitted = match first {
        0 => at_or_below(last),
        _ => at_or_below(last).minus(&at_or_below(first - 1)),
    };
    TileGuard::Function(FunctionGuard::Domain(admitted))
}

#[test]
fn two_chains_pulled_at_disjoint_guards_merge_to_the_whole_pull() {
    let rows = 100;
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(program(rows));
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let output = compiled.main_mut().expect("a main output");
    let tiling = output.op.tiling().clone();
    let mut chains: Vec<_> = (0..2)
        .map(|_| {
            output
                .op
                .subscribe(tiling.universal_guard(), Box::new(|| {}), ctx.scheduler())
        })
        .collect();
    let mut merged = tiling.empty_tile();
    for (chain, (first, last)) in chains.iter_mut().zip([(0, 49), (50, 99)]) {
        let guard = range(first, last);
        let tile = chain.get(guard.clone());
        assert_eq!(
            entries(&tile).len(),
            50,
            "a chain answers the guard's rows and no others: {tile:?}"
        );
        merged.merge(tile);
        chain.release(guard);
        // The next pull on the same chain, past the released interval, is what every worker
        // does per morsel, and what the completeness checks in `get` watch.
        let next = chain.get(range(first, rows - 1));
        assert_eq!(entries(&next).len() as u64, rows - 1 - last);
    }
    assert_eq!(entries(&merged), pulled_whole(rows));
}

#[test]
fn a_morsel_pipeline_produces_what_one_pull_produces() {
    let rows = 1000;
    let tile = dispatched(&program(rows), 7);
    assert!(
        tile.is_terminal(),
        "the collector calls the collection complete"
    );
    assert_eq!(entries(&tile), pulled_whole(rows));
}

/// A fold is combined once every morsel is folded: the three kinds a literal admits give what
/// the one pull gives, and the result is terminal, with morsels of seven rows over a thousand
/// rows and over three.
#[test]
fn a_fold_equals_what_one_pull_folds() {
    for fold in ["sum", "max", "min"] {
        for rows in [1000, 3] {
            let tile = dispatched(&folded(fold, rows), 7);
            assert!(
                tile.is_terminal(),
                "{fold} over {rows}: the fold is complete: {tile:?}"
            );
            assert_eq!(tile, whole_pull(folded(fold, rows)), "{fold} over {rows}");
        }
    }
}

#[test]
fn the_plan_reads_the_fold_off_the_extract() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(folded("sum", 3));
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let plan = plan_inline(&compiled.operator_graph).expect("a fold is a breaker the pool runs");
    assert_eq!(plan.pipeline_count(), 1);
    let BreakerKind::Fold {
        kind, accumulator, ..
    } = plan.main_breaker()
    else {
        panic!("a fold, not the sink");
    };
    assert_eq!(*kind, AggregateKind::Sum);
    assert_eq!(*accumulator, Tiling::Scalar(Extent::Base(BaseType::Int)));
}

#[test]
fn a_program_with_another_breaker_is_not_a_morsel_pipeline() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test("[y + 1 for y in [1, 5] ++ [3, 4]]");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let refused = plan_inline(&compiled.operator_graph)
        .err()
        .expect("a union is an operator the pool does not run");
    assert!(
        refused.to_string().contains("is not a streaming operator"),
        "{refused}"
    );
}

/// A scalar `main` is a `Constant` with no rows to cut, and the plan says so.
#[test]
fn a_constant_main_is_refused_as_no_source_of_rows() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(indoc! {"
        a = 3
        a + 1
    "});
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let refused = plan_inline(&compiled.operator_graph)
        .err()
        .expect("a constant is not streamed");
    assert!(
        refused.to_string().contains("no source of rows"),
        "{refused}"
    );
}

/// `xs = [x + 1 for x …]` read by `[a * 2 for a in xs]`: the pipeline that fills the `Memo` and
/// the pipeline behind it run on the pool, and the answer is the one pull of the whole program.
fn shared(rows: u64, tail: &str) -> String {
    let items: Vec<String> = (0..rows).map(|i| i.to_string()).collect();
    format!("xs = [x + 1 for x in [{}]]\n{tail}", items.join(", "))
}

#[test]
fn a_shared_value_runs_as_two_pipelines_and_equals_the_serial_answer() {
    for rows in [0, 1, 6, 7, 8, 100, 1000] {
        let program = shared(rows, "[a * 2 for a in xs]");
        let tile = dispatched(&program, 7);
        assert!(
            tile.is_terminal(),
            "{rows} rows: the collection is complete"
        );
        assert_eq!(entries(&tile), entries(&whole_pull(program)), "{rows} rows");
    }
}

/// A fold behind a memo folds what the pipeline before it merged.
#[test]
fn a_fold_behind_a_shared_value_equals_the_serial_answer() {
    for fold in ["sum", "max", "min"] {
        for rows in [1, 7, 500] {
            let program = shared(rows, &format!("{fold}([a * 2 for a in xs])"));
            let tile = dispatched(&program, 7);
            assert!(
                tile.is_terminal(),
                "{fold} over {rows}: the fold is complete"
            );
            assert_eq!(tile, whole_pull(program), "{fold} over {rows}");
        }
    }
}

/// [`dispatched`] with a morsel of three rows.
fn dispatched_inline(code: &str) -> Tile {
    dispatched(code, 3)
}

/// Collections that hold collections, dispatched, equal the serial pull as `Tile ==` compares
/// them: the inner level states itself complete. A morsel states the inner level correctly
/// (`Qualified { enclosing: [0, 1], here: True }`), and `Tile::merge` drops that statement as
/// covered by the outer level when the breaker absorbs the morsel (`drop_covered_completion`). The
/// two tiles mean the same under the closure rule and differ in representation, so the breaker
/// states every level complete when it completes (`Materialized::snapshot`, `PoolBreaker::finish`).
/// The differential suite found the difference in the first shape.
const NESTED_COLLECTIONS: [&str; 4] = [
    "xs = [(a=1, b=[1, 2]), (a=3, b=[4, 5])]; xs",
    "[[1, 2], [3, 4]]",
    "[(1, [1, 2]), (2, [3, 4])]",
    indoc! {"
        xs = [[1, 2], [3, 4]]
        [a for a in xs]
    "},
];

#[test]
fn a_dispatched_collection_holding_collections_states_its_inner_levels_complete() {
    for code in NESTED_COLLECTIONS {
        let mut dispatched = dispatched_inline(code);
        dispatched.compact();
        assert_eq!(dispatched, whole_pull(code.to_string()), "{code}");
    }
}

fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

/// The inline driver takes the `main` producer a live program moved out of its output to drive it
/// and answers `main` from its own producer. A program the driver refuses keeps its producer, and
/// the scheduler loop drives it.
#[test]
fn a_refused_live_program_keeps_its_producer_and_an_admitted_one_is_driven_by_the_pool() {
    use cambra::live_program::{LiveProgram, MAIN_BRANCH};

    let config = Config { morsel_rows: 4 };
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &LoadedProgram::test(program(8)), &no_main).expect("compiles");
    assert!(live.main_producer_mut(MAIN_BRANCH).is_some());
    let mut run = live
        .start_inline(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .expect("a finite map is a morsel pipeline");
    for _ in 0..16 {
        ctx.scheduler().check_for_notifications();
        run.lap();
    }
    let producer = live
        .main_producer_mut(MAIN_BRANCH)
        .expect("the pool's producer answers `main`");
    let tile = producer.get(producer.tiling().universal_guard());
    assert_eq!(entries(&tile), pulled_whole(8));

    let mut ctx = GlobalContext::default();
    let grouped = "[y + 1 for y in [1, 5] ++ [3, 4]]";
    let mut live =
        LiveProgram::start(&mut ctx, &LoadedProgram::test(grouped), &no_main).expect("compiles");
    live.start_inline(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .err()
        .expect("a union is not a morsel pipeline");
    assert!(
        live.main_producer_mut(MAIN_BRANCH).is_some(),
        "a refused program keeps the producer the scheduler loop drives"
    );
}

/// `[x + 1 for x in source1()]` over a source whose keys are `key_extent`.
fn over_a_source(key_extent: Extent) -> (GlobalContext, cambra::ccl::context::CompiledProgram) {
    use cambra::interpreter::TestDataSource;
    use std::sync::{Arc, Mutex};

    let mut ctx = GlobalContext::default();
    ctx.register_source(Arc::new(Mutex::new(
        TestDataSource::new(
            "source1",
            cambra::ccl::Type::Base(cambra::ccl::BaseType::Int),
            Extent::Base(BaseType::Int),
        )
        .with_key_extent(key_extent),
    )));
    let loaded = LoadedProgram::test("[x + 1 for x in source1()]");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    (ctx, compiled)
}

/// A source read at each key of its domain is a streaming operator: the chain `IterateExtent`,
/// `MapResultWithSource`, `MapResult` is a morsel pipeline.
#[test]
fn a_chain_over_a_source_is_a_morsel_pipeline() {
    let (_ctx, compiled) = over_a_source(Extent::Base(BaseType::Int));
    let plan = plan_inline(&compiled.operator_graph).expect("a source is streamed");
    assert!(matches!(plan.main_breaker(), BreakerKind::Collect));
}

/// A source whose keys are not totally ordered cannot be cut into morsels, so the pool refuses the
/// program and leaves the producer the live program moved out to drive it.
#[test]
fn a_source_with_unordered_keys_stays_on_the_compiling_thread() {
    use cambra::interpreter::TestDataSource;
    use cambra::live_program::{LiveProgram, MAIN_BRANCH};
    use std::sync::{Arc, Mutex};

    let keys = Extent::Record(
        [(
            cambra::interpreter::tuple_field(0),
            Extent::Base(BaseType::Int),
        )]
        .into_iter()
        .collect(),
    );
    let mut ctx = GlobalContext::default();
    ctx.register_source(Arc::new(Mutex::new(
        TestDataSource::new(
            "source1",
            cambra::ccl::Type::Base(cambra::ccl::BaseType::Int),
            Extent::Base(BaseType::Int),
        )
        .with_key_extent(keys),
    )));
    let mut live = LiveProgram::start(
        &mut ctx,
        &LoadedProgram::test("[x + 1 for x in source1()]"),
        &no_main,
    )
    .expect("compiles");
    let config = Config { morsel_rows: 4 };
    let refused = live
        .start_inline(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .err()
        .expect("a source of unordered keys has no morsels");
    assert!(
        refused.to_string().contains("cut into morsels"),
        "{refused}"
    );
    assert!(
        live.main_producer_mut(MAIN_BRANCH).is_some(),
        "the program's own producer is untouched"
    );
}

/// Run `code` through the inline driver over a source holding the keys 1, 2 and 3, whose yield
/// predicate is everything, with nothing arriving later.
fn dispatched_over_held_rows(code: &str) -> Tile {
    use cambra::interpreter::TestDataSource;
    use std::sync::{Arc, Mutex};

    let mut ctx = GlobalContext::default();
    let source = Arc::new(Mutex::new(TestDataSource::new(
        "source1",
        cambra::ccl::Type::Base(cambra::ccl::BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    source.lock().expect("no other holder").add_data(&[
        (Value::UInt(1), Value::Int(10)),
        (Value::UInt(2), Value::Int(20)),
        (Value::UInt(3), Value::Int(30)),
    ]);
    source
        .lock()
        .expect("no other holder")
        .set_yield_predicate(Predicate::True);
    ctx.register_source(source);
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled =
        compile_program(&mut ctx, &LoadedProgram::test(code), consumer).expect("compiles");
    let config = Config { morsel_rows: 2 };
    let mut run = PooledRun::start(&mut ctx, &mut compiled, &mut None, &config, Box::new(|| {}))
        .expect("a source that cuts morsels is a morsel pipeline");
    let mut main = run.take_main().expect("a main output");
    let universal = main.tiling().universal_guard();
    for _ in 0..100 {
        ctx.scheduler().check_for_notifications();
        run.lap();
        let tile = main.get(universal.clone());
        if tile.is_terminal() {
            return tile;
        }
    }
    panic!("the run of {code} finishes: nothing closed the pipeline's source");
}

/// The rows the source holds are all there will be: the driver claims them, answers, and closes the
/// source instead of waiting for arrivals.
#[test]
fn a_source_that_holds_rows_returns_them_and_finishes() {
    let tile = dispatched_over_held_rows("[x + 1 for x in source1()]");
    assert_eq!(entries(&tile), [(1, 11), (2, 21), (3, 31)]);
}

/// The rows a source holds when the pool starts are claimable although nothing notified of them,
/// and the answer is not stated complete without them.
#[test]
fn rows_held_before_the_pool_starts_are_not_lost() {
    let tile = dispatched_over_held_rows("[x for x in source1()]");
    assert_eq!(entries(&tile), [(1, 10), (2, 20), (3, 30)]);
}

/// A chain of keys-keeping operators over a literal list of variants, run on four workers with a
/// morsel that divides no row count, equals the serial pull: `VariantWrap` builds each variant
/// and `VariantProject` reads it back through a `match`.
#[test]
fn a_chain_through_variant_wrap_and_project_equals_the_serial_answer() {
    let rows = 20;
    let items: Vec<String> = (0..rows).map(|i| format!("`a({i})")).collect();
    let programs = [
        // `VariantProject` over a literal list of variants.
        formatdoc! {"
            def unwrap(m):
                match m:
                    case `a(v):
                        v
            xs = [{}]
            sum([unwrap(m) for m in xs])
        ", items.join(", ")},
        // `VariantWrap` over a range, read back by a `match`.
        formatdoc! {"
            def unwrap(m):
                match m:
                    case `a(v):
                        v
            sum([unwrap(`a(x * 2)) for x in {}])
        ", format!("[{}]", (0..rows).map(|i| i.to_string()).collect::<Vec<_>>().join(", "))},
    ];
    for source in programs {
        let mut ctx = GlobalContext::default();
        let loaded = LoadedProgram::test(source.clone());
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
        let kinds = plan_inline(&compiled.operator_graph).expect("variant operators are streamed");
        assert!(matches!(kinds.main_breaker(), BreakerKind::Fold { .. }));
        let pooled = dispatched(&source, 7);
        assert!(pooled.is_terminal(), "the fold is complete");
        assert_eq!(pooled, whole_pull(source));
    }
}

/// `code` is admitted by the plan, and with a morsel that divides no row count its answer equals
/// the serial pull.
fn pooled_equals_serial(code: String) {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(code.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    plan_inline(&compiled.operator_graph).unwrap_or_else(|why| panic!("{code} is admitted: {why}"));
    let mut pooled = dispatched(&code, 7);
    let mut serial = whole_pull(code.clone());
    pooled.compact();
    serial.compact();
    assert!(
        pooled.is_terminal(),
        "{code}: the pooled answer is complete"
    );
    match pooled {
        Tile::DataFunction { .. } => assert_eq!(entries(&pooled), entries(&serial), "{code}"),
        _ => assert_eq!(pooled, serial, "{code}"),
    }
}

fn range_list(rows: u64) -> String {
    let items: Vec<String> = (0..rows).map(|i| i.to_string()).collect();
    format!("[{}]", items.join(", "))
}

/// `Restrict` keeps the keys whose predicate holds: a morsel's region names keys that were
/// filtered out, which have no row, and the pooled collection equals the serial one.
#[test]
fn a_chain_through_restrict_equals_the_serial_answer() {
    let list = range_list(100);
    for code in [
        format!("[x for x in {list} if x > 70]"),
        format!("[x + 1 for x in {list} if x > 10 if x < 90]"),
        format!("[x for x in {list} if x < 0]"),
        // Every other key is filtered out, so each morsel's region names keys with no row.
        format!("[x for x in {list} if x // 2 * 2 == x]"),
        format!("sum([x for x in {list} if x > 70])"),
    ] {
        pooled_equals_serial(code);
    }
}

/// `MapResultToConst` compares or pairs each row with a constant: the constant is read whole by
/// every morsel.
#[test]
fn a_chain_through_map_result_to_const_equals_the_serial_answer() {
    let list = range_list(100);
    for code in [
        format!("sum([1 for x in {list} if x >= 50])"),
        format!("sum([1 for x in {list} if x + 1 >= 50])"),
    ] {
        pooled_equals_serial(code);
    }
}

/// What `plan` says of `code`: the reason it refuses, or `None` when it admits.
fn refusal(code: &str) -> Option<String> {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(code.to_string());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    plan_inline(&compiled.operator_graph)
        .err()
        .map(|refused| refused.to_string())
}

/// The operand `MapResultToConst` applies must be a `Constant`: a value that another pipeline
/// computes, as a sum read by each element, is a build side the plan does not stream, and so is
/// an operand that is itself a chain.
#[test]
fn a_map_result_to_const_applies_a_constant_and_nothing_else() {
    for (code, reason) in [
        (
            indoc! {"
                n = sum([1, 2, 3])
                [(x, n) for x in [1, 2, 3]]
            "},
            "a `MapResultToConst` applies a `FanOutSlot`",
        ),
        (
            "[(x, sum([1, 2])) for x in [1, 2, 3]]",
            "a `MapResultToConst` applies a `ExtractAggregate`",
        ),
        (
            "[[(x, 1) for x in [1, 2]] for y in [1, 2]]",
            "a `MapResultToConst` applies a `MapResult`",
        ),
    ] {
        let refused = refusal(code).unwrap_or_else(|| panic!("{code} is refused"));
        assert!(refused.contains(reason), "{code}: {refused}");
    }
}

/// A streaming operator works on each key of a collection: at the outermost level a `VariantWrap`
/// wraps a value whole and a `MapResult` applies to a scalar, so the plan refuses them, and the
/// same operators beneath a level are admitted.
#[test]
fn a_streaming_operator_at_the_outermost_level_is_refused() {
    for (code, operator) in [
        ("`a(sum([1, 2]))", "VariantWrap"),
        ("sum([1, 2]) >= 2", "MapResult"),
    ] {
        let refused = refusal(code).unwrap_or_else(|| panic!("{code} is refused"));
        assert!(
            refused.contains(&format!("a `{operator}` at the outermost level")),
            "{code}: {refused}"
        );
    }
    for code in ["[`a(x) for x in [1, 2, 3]]", "[x >= 2 for x in [1, 2, 3]]"] {
        assert_eq!(refusal(code), None, "{code} is admitted");
    }
}

/// A chain that reads a `Memo` at its own keys is a keyed read: the plan admits it when the memo's
/// pipeline keeps every key of the source the chain iterates, and refuses the other shapes with the
/// reason.
#[test]
fn a_keyed_read_is_admitted_over_a_memo_that_keeps_every_key() {
    assert_eq!(
        refusal(indoc! {"
            xs = [1, 2, 3, 4]
            [y * 2 for y in xs if y > 2]
        "}),
        None
    );
    for (code, reason) in [
        (
            indoc! {"
                x = [z for z in [1, 2, 3] if z > 1]
                sum([y for y in x if y < 3])
            "},
            "whose pipeline can drop a key",
        ),
        (
            indoc! {"
                k: Int = 1
                x = box([1, 2, 3])
                sum([y for y in x if y > k])
            "},
            // A constant another pipeline computes is read whole by every row: a build side.
            "a `MapResultToConst` applies a `FanOutSlot`",
        ),
    ] {
        let refused = refusal(code).unwrap_or_else(|| panic!("{code} is refused"));
        assert!(refused.contains(reason), "{code}: {refused}");
    }
}

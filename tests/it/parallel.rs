//! The morsel prototype: a `main` pipeline pulled by row range through several chains and
//! merged at the collector equals the same pipeline pulled whole on one thread.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use indoc::indoc;

use cambra::{
    ccl::{
        AggregateKind,
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    },
    interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
        Value,
        parallel::{Breaker, Config, PooledRun, plan, run_main},
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

/// `source` run on four workers with a morsel size that does not divide its rows.
fn four_workers(source: String) -> Tile {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(source);
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let config = Config {
        threads: 4,
        morsel_rows: 7,
    };
    run_main(&mut ctx, &mut compiled, &config).expect("a morsel pipeline")
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
fn four_workers_produce_what_one_pull_produces() {
    let rows = 1000;
    let tile = four_workers(program(rows));
    assert!(
        tile.is_terminal(),
        "the collector calls the collection complete"
    );
    assert_eq!(entries(&tile), pulled_whole(rows));
}

/// A fold is kept per worker and combined once every morsel is folded: the three kinds a
/// literal admits give what the one pull gives, and the result is terminal. With three rows
/// and four workers, a worker takes no package and hands in its seed, which the combine must
/// take as a unit.
#[test]
fn four_workers_fold_what_one_pull_folds() {
    for fold in ["sum", "max", "min"] {
        for rows in [1000, 3] {
            let tile = four_workers(folded(fold, rows));
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
    let plan = plan(&compiled.operator_graph).expect("a fold is a breaker the pool runs");
    assert_eq!(plan.pipeline_count(), 1);
    let Breaker::Fold { kind, accumulator } = plan.main_breaker() else {
        panic!("a fold, not the sink");
    };
    assert_eq!(*kind, AggregateKind::Sum);
    assert_eq!(*accumulator, Tiling::Scalar(Extent::Base(BaseType::Int)));
}

#[test]
fn one_worker_produces_what_one_pull_produces() {
    let rows = 50;
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(program(rows));
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let config = Config {
        threads: 1,
        morsel_rows: 4096,
    };
    let tile = run_main(&mut ctx, &mut compiled, &config).expect("a morsel pipeline");
    assert_eq!(entries(&tile), pulled_whole(rows));
}

#[test]
fn a_program_with_another_breaker_is_not_a_morsel_pipeline() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test("[sum(g) for g in groupby([1, 2, 3, 4], \\x -> x // 2)]");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let refused = plan(&compiled.operator_graph)
        .err()
        .expect("a group-by has breakers the pool does not run");
    assert!(
        refused.to_string().contains("is not a streaming operator"),
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
        let tile = four_workers(program.clone());
        assert!(
            tile.is_terminal(),
            "{rows} rows: the collection is complete"
        );
        assert_eq!(entries(&tile), entries(&whole_pull(program)), "{rows} rows");
    }
}

/// A fold behind the breaker folds what the pipeline before it materialized.
#[test]
fn a_fold_behind_a_shared_value_equals_the_serial_answer() {
    for fold in ["sum", "max", "min"] {
        for rows in [1, 7, 500] {
            let program = shared(rows, &format!("{fold}([a * 2 for a in xs])"));
            let tile = four_workers(program.clone());
            assert!(
                tile.is_terminal(),
                "{fold} over {rows}: the fold is complete"
            );
            assert_eq!(tile, whole_pull(program), "{fold} over {rows}");
        }
    }
}

/// One worker serves both pipelines in turn.
#[test]
fn one_worker_serves_both_pipelines_of_a_shared_value() {
    let program = shared(50, "[a * 2 for a in xs]");
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(program.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let config = Config {
        threads: 1,
        morsel_rows: 4,
    };
    let tile = run_main(&mut ctx, &mut compiled, &config).expect("two morsel pipelines");
    assert_eq!(entries(&tile), entries(&whole_pull(program)));
}

/// `code` run through the inline driver on one thread with a morsel of three rows until `main` is
/// terminal, and what `main` then holds.
fn dispatched_inline(code: &str) -> Tile {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled =
        compile_program(&mut ctx, &LoadedProgram::test(code), consumer).expect("compiles");
    let config = Config {
        threads: 1,
        morsel_rows: 3,
    };
    let mut run = PooledRun::start(&mut ctx, &mut compiled, &mut None, &config, Box::new(|| {}))
        .expect("a pipeline");
    let mut main = run.take_main();
    let universal = main.tiling().universal_guard();
    for _ in 0..100 {
        ctx.scheduler().check_for_notifications();
        run.lap();
        let tile = main.get(universal.clone());
        if tile.is_terminal() {
            return tile;
        }
    }
    panic!("the run of {code} finishes");
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

/// The threaded collector states the inner levels complete too (`PoolBreaker::finish`).
#[test]
fn a_threaded_collection_holding_collections_states_its_inner_levels_complete() {
    for code in NESTED_COLLECTIONS {
        let mut pooled = four_workers(code.to_string());
        pooled.compact();
        assert_eq!(pooled, whole_pull(code.to_string()), "{code}");
    }
}

fn no_main() -> Box<dyn Consumer> {
    Box::new(|| {})
}

/// The pool takes the `main` producer a live program moved out of its output to drive it: it
/// registered a release record that would pin a source, and the pool owns the pipeline's record.
/// A program the pool refuses keeps its producer, and the scheduler loop drives it.
#[test]
fn the_pool_drops_the_main_producer_of_a_live_program_it_runs_and_a_refused_one_keeps_it() {
    use cambra::live_program::{LiveProgram, MAIN_BRANCH};

    let config = Config {
        threads: 2,
        morsel_rows: 4,
    };
    let mut ctx = GlobalContext::default();
    let mut live =
        LiveProgram::start(&mut ctx, &LoadedProgram::test(program(8)), &no_main).expect("compiles");
    assert!(live.main_producer_mut(MAIN_BRANCH).is_some());
    live.run_main_on_pool(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .expect("a finite map is a morsel pipeline");
    assert!(
        live.main_producer_mut(MAIN_BRANCH).is_none(),
        "the pool dropped the producer that held the pipeline's record"
    );

    let mut ctx = GlobalContext::default();
    let grouped = "[sum(g) for g in groupby([1, 2, 3, 4], \\x -> x // 2)]";
    let mut live =
        LiveProgram::start(&mut ctx, &LoadedProgram::test(grouped), &no_main).expect("compiles");
    live.run_main_on_pool(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .expect_err("a group-by is not a morsel pipeline");
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
    let plan = plan(&compiled.operator_graph).expect("a source is streamed");
    assert!(matches!(plan.main_breaker(), Breaker::Collect));
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
    let config = Config {
        threads: 2,
        morsel_rows: 4,
    };
    let refused = live
        .run_main_on_pool(MAIN_BRANCH, &mut ctx, &config)
        .expect("the branch exists")
        .expect_err("a source of unordered keys has no morsels");
    assert!(
        refused.to_string().contains("cut into morsels"),
        "{refused}"
    );
    assert!(
        live.main_producer_mut(MAIN_BRANCH).is_some(),
        "the program's own producer is untouched"
    );
}

/// Run `code` over a source holding the keys 1, 2 and 3, whose yield predicate is everything, with
/// `run_main` and no delivery, failing instead of hanging.
fn run_main_over_held_rows(code: &'static str) -> Tile {
    use cambra::interpreter::TestDataSource;
    use std::sync::{Arc, Mutex, mpsc};
    use std::time::Duration;

    let (done, finished) = mpsc::channel();
    std::thread::spawn(move || {
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
        let loaded = LoadedProgram::test(code);
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
        let config = Config {
            threads: 2,
            morsel_rows: 2,
        };
        let _ = done.send(run_main(&mut ctx, &mut compiled, &config));
    });
    finished
        .recv_timeout(Duration::from_secs(30))
        .expect("run_main finished: nothing closed the pipeline's source")
        .expect("a source that cuts morsels is a morsel pipeline")
}

/// `run_main` has no delivery, so the rows the source holds are all there will be: the pool claims
/// them, answers, and closes the source instead of waiting for arrivals.
#[test]
fn run_main_over_a_source_that_holds_rows_returns_them_and_finishes() {
    let tile = run_main_over_held_rows("[x + 1 for x in source1()]");
    assert_eq!(entries(&tile), [(1, 11), (2, 21), (3, 31)]);
}

/// The rows a source holds when the pool starts are claimable although nothing notified of them,
/// and the answer is not stated complete without them.
#[test]
fn rows_held_before_the_pool_starts_are_not_lost() {
    let tile = run_main_over_held_rows("[x for x in source1()]");
    assert_eq!(entries(&tile), [(1, 10), (2, 20), (3, 30)]);
}

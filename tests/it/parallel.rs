//! The morsel prototype: a `main` pipeline pulled by row range through several chains and
//! merged at the collector equals the same pipeline pulled whole on one thread.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use cambra::{
    ccl::{
        AggregateKind,
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    },
    interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FunctionGuard, Predicate, Tile, TileGuard, Tiling,
        Value,
        parallel::{Breaker, Config, plan_main, run_main},
    },
};
use indoc::indoc;

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
    let pipeline = plan_main(&compiled.operator_graph).expect("a fold is a breaker the pool runs");
    let Breaker::Fold { kind, accumulator } = pipeline.breaker else {
        panic!("a fold, not the sink");
    };
    assert_eq!(kind, AggregateKind::Sum);
    assert_eq!(accumulator, Tiling::Scalar(Extent::Base(BaseType::Int)));
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
    let refused = plan_main(&compiled.operator_graph)
        .err()
        .expect("a group-by has breakers the pool does not run");
    assert!(
        refused.to_string().contains("is not a streaming operator"),
        "{refused}"
    );
}

/// A chain that reads a shared node would notify the pool through a fan-out, whose input consumer
/// drops a second notification between pulls, so the plan refuses it.
#[test]
fn a_chain_that_reads_a_shared_node_is_not_a_morsel_pipeline() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(indoc! {"
        xs = [x + 1 for x in [1, 2, 3, 4]]
        [a * 2 for a in xs]
    "});
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let refused = plan_main(&compiled.operator_graph)
        .err()
        .expect("a shared chain is not a streaming pipeline");
    assert!(
        refused
            .to_string()
            .contains("`FanOutSlot` is not a streaming operator"),
        "{refused}"
    );
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

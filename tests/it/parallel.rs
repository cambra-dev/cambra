//! The morsel prototype: a `main` pipeline pulled by row range through several chains and
//! merged at the collector equals the same pipeline pulled whole on one thread.
//! See `src/interpreter/design-parallel.md`, "The morsel prototype".

use cambra::{
    ccl::{
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    },
    interpreter::{
        ColumnValue, Consumer, FunctionGuard, Predicate, Tile, TileGuard, Value,
        parallel::{Config, plan_main, run_main},
    },
};

/// `[x + 1 for x in [0, 1, …, rows - 1]]`: a finite source, two streaming maps, `main`.
fn program(rows: u64) -> String {
    let items: Vec<String> = (0..rows).map(|i| i.to_string()).collect();
    format!("[x + 1 for x in [{}]]", items.join(", "))
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

/// The program's `main` output pulled whole on this thread, as the scheduler loop pulls it.
fn pulled_whole(rows: u64) -> Vec<(u64, i64)> {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(program(rows));
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
    entries(&tile)
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
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test(program(rows));
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let config = Config {
        threads: 4,
        // Not a divisor of the row count, so the last morsel is short.
        morsel_rows: 7,
    };
    let tile = run_main(&mut ctx, &mut compiled, &config).expect("a morsel pipeline");
    assert!(
        tile.is_terminal(),
        "the collector calls the collection complete"
    );
    assert_eq!(entries(&tile), pulled_whole(rows));
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
fn a_program_with_a_breaker_is_not_a_morsel_pipeline() {
    let mut ctx = GlobalContext::default();
    let loaded = LoadedProgram::test("sum([x + 1 for x in [1, 2, 3]])");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let compiled = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let refused = plan_main(&compiled.operator_graph).expect_err("an aggregate is a breaker");
    assert!(
        refused.to_string().contains("not a streaming operator"),
        "{refused}"
    );
}

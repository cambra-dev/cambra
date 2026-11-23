// Scratch: times one program's dispatched run at a given number of workers. Not part of any change.
//
// PROGRAM names one of `PROGRAMS`, ROWS sets each source's row count, DOP the workers, MORSEL the
// morsel rows. Prints one line: program, rows, dop, compile and run times, and the answer.
use std::time::Instant;

use cambra::ccl::Type;
use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{BaseType, Consumer, Extent, Predicate, TestDataSource, Value};

// `{XS}` is a list literal of ROWS values and `{YS}` one of INNER values: a literal's domain is a
// range of positions, which a pipeline needs to run on several workers.
const PROGRAMS: &[(&str, &str, usize)] = &[
    (
        "lit_map_max",
        "out = test_sink()\nxs = [{XS}]\nout << max([x * 2 for x in xs])\n",
        0,
    ),
    (
        "lit_map_sum",
        "out = test_sink()\nxs = [{XS}]\nout << sum([x * 2 for x in xs])\n",
        0,
    ),
    (
        "lit_filter_sum",
        "out = test_sink()\nxs = [{XS}]\nout << sum([x for x in xs if x > 1500])\n",
        0,
    ),
    (
        "lit_groupby_sum",
        "out = test_sink()\nxs = [{XS}]\nout << [sum(g) for g in groupby(xs, \\x -> x // 30)]\n",
        0,
    ),
    (
        "lit_cross_max",
        "out = test_sink()\nxs = [{XS}]\nys = [{YS}]\nout << max([x * y + x for x in xs for y in ys])\n",
        0,
    ),
    (
        "lit_nest_sum",
        "out = test_sink()\nxs = [{XS}]\nys = [{YS}]\nout << [sum([x * y for y in ys]) for x in xs]\n",
        0,
    ),
    (
        "map_max",
        "out = test_sink()\nout << max([x * 2 for x in source1()])\n",
        1,
    ),
    (
        "filter_max",
        "out = test_sink()\nout << max([x for x in source1() if x > 1500])\n",
        1,
    ),
    (
        "groupby_max",
        "out = test_sink()\nout << max([max([v for v in g]) for g in groupby(source1(), \\v -> v // 30)])\n",
        1,
    ),
    (
        "join_max",
        "out = test_sink()\nout << max([b for a in source1() for b in source2() if a == b])\n",
        2,
    ),
    (
        "nest_max",
        "out = test_sink()\nout << max([max([y * x for y in source2()]) for x in source1()])\n",
        2,
    ),
    (
        "map_list",
        "out = test_sink()\nout << [x * 2 for x in source1()]\n",
        1,
    ),
    (
        "map_sum",
        "out = test_sink()\nout << sum([x * 2 for x in source1()])\n",
        1,
    ),
    (
        "filter_sum",
        "out = test_sink()\nout << sum([x for x in source1() if x > 1500])\n",
        1,
    ),
    (
        "groupby_sum",
        "out = test_sink()\nout << sum([sum([v for v in g]) for g in groupby(source1(), \\v -> v // 30)])\n",
        1,
    ),
    (
        "join_sum",
        "out = test_sink()\nout << sum([b for a in source1() for b in source2() if a == b])\n",
        2,
    ),
    (
        "mut_loop",
        "out = test_sink()\ntotal := 0\nfor n in source1():\n    total += n\nout << total\n",
        1,
    ),
    (
        "nest_sum",
        "out = test_sink()\nout << sum([sum([y * x for y in source2()]) for x in source1()])\n",
        2,
    ),
];

fn literal(rows: usize, salt: i64) -> String {
    (0..rows)
        .map(|i| ((i as i64 + salt).wrapping_mul(2654435761) % 3000).to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

fn env(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn load(ctx: &mut GlobalContext, name: &str, rows: usize, modulus: i64) {
    let source = TestDataSource::new(name, Type::Base(BaseType::Int), Extent::Base(BaseType::Int));
    ctx.register_source(source.clone());
    for start in (0..rows).step_by(1 << 16) {
        let end = (start + (1 << 16)).min(rows);
        let data: Vec<(Value, Value)> = (start..end)
            .map(|i| {
                let v = (i as i64).wrapping_mul(2654435761) % modulus;
                (Value::UInt(i as u64), Value::Int(v))
            })
            .collect();
        source
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .add_data(&data);
    }
    source
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .set_yield_predicate(Predicate::True);
}

#[test]
#[ignore]
fn dop_bench() {
    let name = std::env::var("PROGRAM").unwrap_or_else(|_| "map_max".to_owned());
    let (_, code, sources) = PROGRAMS
        .iter()
        .find(|(program, _, _)| *program == name)
        .unwrap_or_else(|| panic!("no program {name}"));
    let rows = env("ROWS", 100_000);
    let inner = env("INNER", rows);
    let dop = env("DOP", 1);
    let morsel = env("MORSEL", 1024);
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    if *sources > 0 {
        load(&mut ctx, "source1", rows, 3000);
    }
    if *sources > 1 {
        load(&mut ctx, "source2", inner, 3000);
    }
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let code = code
        .replace("{XS}", &literal(rows, 0))
        .replace("{YS}", &literal(inner, 7));
    let loaded = LoadedProgram::test(code);
    let t = Instant::now();
    let mut program = compile_program(&mut ctx, &loaded, consumer).expect("compiles");
    let compile = t.elapsed();
    if std::env::var("WAIT").is_ok() {
        std::thread::sleep(std::time::Duration::from_secs(3));
    }
    let t = Instant::now();
    let ran = cambra::interpreter::dispatcher::run_program_with_workers(&mut program, morsel, dop);
    let run = t.elapsed();
    println!(
        "BENCH program={name} rows={rows} inner={inner} dop={dop} morsel={morsel} compile_ms={:.1} run_ms={:.1} ok={} answer={:?}",
        compile.as_secs_f64() * 1e3,
        run.as_secs_f64() * 1e3,
        ran.is_ok(),
        sink.value().ok(),
    );
}

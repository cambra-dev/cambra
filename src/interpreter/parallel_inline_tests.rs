//! The inline driver: a program's pipelines served by the thread that drives the scheduler loop,
//! one worker and no threads. See `src/interpreter/design-parallel.md`, "The inline driver".

// The shared-state check skips `#[cfg(test)]` items, and this file holds nothing else.
#[cfg(test)]
mod inline {
    use std::sync::{Arc, Mutex};

    use indoc::{formatdoc, indoc};

    use super::super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::tile_operators::test_helpers::int_entries;
    use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, TestDataSource, Value};

    fn compiled(ctx: &mut GlobalContext, code: &str) -> CompiledProgram {
        compile_program(ctx, &LoadedProgram::test(code), Box::new(|| {})).expect("compiles")
    }

    /// The program's `main` pulled whole, as the scheduler loop pulls it, until it is terminal.
    fn serial(code: &str) -> Tile {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, code);
        ctx.scheduler().check_for_notifications();
        let producer = program
            .main_mut()
            .and_then(|output| output.producer.as_mut())
            .expect("a main output");
        crate::interpreter::pull_laps(ctx.scheduler(), &mut **producer, 1024, Tile::is_terminal)
    }

    /// The loop the binary runs with `CAMBRA_DISPATCH=inline`: deliver, serve the pool, pull the
    /// sinks, pull `main`.
    fn drive(
        ctx: &mut GlobalContext,
        run: &mut PooledRun,
        main: &mut dyn TileProducer,
        laps: usize,
    ) -> Tile {
        let universal = main.tiling().universal_guard();
        for _ in 0..laps {
            ctx.scheduler().check_for_notifications();
            run.lap();
            ctx.scheduler().pull_sinks();
            let tile = main.get(universal.clone());
            if tile.is_terminal() {
                return tile;
            }
        }
        panic!("`main` did not finish within {laps} laps");
    }

    /// `code` on the inline driver, with morsels of `morsel_rows` rows.
    fn inline(code: &str, morsel_rows: u64) -> Tile {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, code);
        let config = Config {
            threads: 1,
            morsel_rows,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        let mut main = run.take_main().expect("a main output");
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(run.lap(), Lap::Done, "every pipeline finished");
        tile
    }

    fn entries(tile: &Tile) -> Vec<(u64, i64)> {
        let mut pairs = match tile.is_empty() {
            true => Vec::new(),
            false => int_entries(tile),
        };
        pairs.sort_unstable();
        pairs
    }

    fn list(rows: u64) -> String {
        let items: Vec<String> = (0..rows).map(|i| i.to_string()).collect();
        format!("[{}]", items.join(", "))
    }

    /// A collection read through the breaker's output equals the serial pull, for morsels that do
    /// and do not divide the rows.
    #[test]
    fn a_map_over_a_list_equals_the_serial_answer() {
        for rows in [0, 1, 7, 8, 100] {
            let code = format!("[x + 1 for x in {}]", list(rows));
            for morsel_rows in [1, 7, 4096] {
                let tile = inline(&code, morsel_rows);
                assert_eq!(
                    entries(&tile),
                    entries(&serial(&code)),
                    "{rows} rows, {morsel_rows}-row morsels"
                );
            }
        }
    }

    /// A fold is answered once its pipeline finishes, from the partials combined.
    #[test]
    fn a_fold_is_answered_when_its_pipeline_finishes() {
        for fold in ["sum", "max", "min"] {
            for rows in [1, 9, 200] {
                let code = format!("{fold}([x + 1 for x in {}])", list(rows));
                assert_eq!(inline(&code, 4), serial(&code), "{fold} over {rows}");
            }
        }
    }

    /// A value the program names and reads is a breaker between two pipelines, and the answer is
    /// the serial one.
    #[test]
    fn a_shared_value_runs_as_two_pipelines() {
        for rows in [0, 1, 9, 100] {
            let code = formatdoc! {"
                xs = [x + 1 for x in {}]
                [a * 2 for a in xs]
            ", list(rows)};
            for morsel_rows in [1, 7] {
                assert_eq!(
                    entries(&inline(&code, morsel_rows)),
                    entries(&serial(&code)),
                    "{rows} rows, {morsel_rows}-row morsels"
                );
            }
        }
    }

    /// The output of the pipeline that ends in `main`: the one breaker an inline run of a
    /// collection has.
    fn main_output(run: &PooledRun) -> Arc<Materialized> {
        match run.breakers.last() {
            Some(PoolBreaker::Materialize { output }) => output.clone(),
            _ => panic!("the last pipeline of a collection materializes `main`"),
        }
    }

    /// `main` reads the final breaker's output through a reader of its own, which is registered
    /// before the first morsel, and releases what it read: after the run the output holds no key,
    /// and a pull after answers empty.
    #[test]
    fn main_releases_what_it_read_and_a_pull_after_answers_empty() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, &format!("[x + 1 for x in {}]", list(20)));
        let config = Config {
            threads: 1,
            morsel_rows: 4,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        let output = main_output(&run);
        assert_eq!(output.reader_count(), 1, "`main` reads the breaker");
        let mut main = run.take_main().expect("a main output");
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(entries(&tile).len(), 20);
        assert_eq!(
            output.held_keys(),
            20,
            "nothing was released before `main` did"
        );
        let universal = main.tiling().universal_guard();
        main.release(universal.clone());
        assert_eq!(
            output.held_keys(),
            0,
            "the release reclaims what `main` read"
        );
        assert!(main.get(universal).is_empty());
    }

    /// A program the pool refuses keeps its producer and the graph, and the serial loop drives it.
    #[test]
    fn a_refused_program_keeps_its_producer() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(
            &mut ctx,
            "[sum(g) for g in groupby([1, 2, 3, 4], \\x -> x // 2)]",
        );
        let mut held = program.main_mut().and_then(|o| o.producer.take());
        let config = Config {
            threads: 1,
            morsel_rows: 4,
        };
        let refused = PooledRun::start(&mut ctx, &mut program, &mut held, &config, Box::new(|| {}))
            .err()
            .expect("a group-by is not a pipeline");
        assert!(refused.to_string().contains("is not a streaming operator"));
        let mut held = held.expect("the producer the loop drives is kept");
        let code = "[sum(g) for g in groupby([1, 2, 3, 4], \\x -> x // 2)]";
        let mut tile =
            crate::interpreter::pull_laps(ctx.scheduler(), &mut *held, 1024, Tile::is_terminal);
        let mut expected = serial(code);
        tile.compact();
        expected.compact();
        assert_eq!(
            tile, expected,
            "the kept producer answers as the serial loop does"
        );
    }

    /// A pipeline over a source whose rows arrive from outside stays open: a lap with nothing
    /// published is idle, a lap after an arrival runs its morsels, `main` holds the rows that
    /// arrived and is not terminal, and the lap after that is idle again.
    #[test]
    fn a_lap_is_idle_until_an_arrival_is_published() {
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let mut program = compiled(&mut ctx, "[x + 1 for x in source1()]");
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("a source that cuts morsels is admitted");
        let mut main = run.take_main().expect("a main output");
        let universal = main.tiling().universal_guard();
        ctx.scheduler().check_for_notifications();
        assert_eq!(run.lap(), Lap::Idle, "nothing has arrived");

        let rows: Vec<(Value, Value)> = (0..5)
            .map(|k| (Value::UInt(k as u64), Value::Int(k * 10)))
            .collect();
        source.lock_wait().add_data(&rows);
        source
            .lock_wait()
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(4)));
        ctx.scheduler().check_for_notifications();
        assert_eq!(run.lap(), Lap::Ran);
        ctx.scheduler().pull_sinks();
        let tile = main.get(universal.clone());
        assert_eq!(entries(&tile).len(), 5, "{tile:?}");
        assert!(!tile.is_terminal(), "the source can still deliver");
        assert_eq!(run.lap(), Lap::Idle);
    }

    /// A program over `source1()` with a context that holds the source, and the source.
    fn over_source1(code: &str) -> (GlobalContext, CompiledProgram, Arc<Mutex<TestDataSource>>) {
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let program = compiled(&mut ctx, code);
        (ctx, program, source)
    }

    fn arrive(source: &Mutex<TestDataSource>, keys: std::ops::Range<i64>) {
        let rows: Vec<(Value, Value)> = keys
            .map(|k| (Value::UInt(k as u64), Value::Int(k * 10)))
            .collect();
        source.lock_wait().add_data(&rows);
    }

    /// A source that states itself complete (a yield predicate of everything) ends the pipeline
    /// over it, and `main` is terminal as the serial pull of the same program is.
    #[test]
    fn a_source_that_states_itself_complete_ends_its_pipeline() {
        for code in [
            "[x + 1 for x in source1()]",
            "sum([x + 1 for x in source1()])",
        ] {
            let (mut ctx, mut program, source) = over_source1(code);
            arrive(&source, 0..5);
            source.lock_wait().set_yield_predicate(Predicate::True);
            ctx.scheduler().check_for_notifications();
            let serial = {
                let producer = program
                    .main_mut()
                    .and_then(|output| output.producer.as_mut())
                    .expect("a main output");
                crate::interpreter::pull_laps(
                    ctx.scheduler(),
                    &mut **producer,
                    1024,
                    Tile::is_terminal,
                )
            };

            let (mut ctx, mut program, source) = over_source1(code);
            arrive(&source, 0..5);
            source.lock_wait().set_yield_predicate(Predicate::True);
            let config = Config {
                threads: 1,
                morsel_rows: 2,
            };
            let mut run =
                PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
                    .expect("admitted");
            let mut main = run.take_main().expect("a main output");
            let inline = drive(&mut ctx, &mut run, &mut *main, 100);
            assert_eq!(run.lap(), Lap::Done, "{code}: the pipeline finished");
            assert!(inline.is_terminal() && serial.is_terminal(), "{code}");
            match inline {
                Tile::DataFunction { .. } => {
                    assert_eq!(entries(&inline), entries(&serial), "{code}");
                }
                _ => assert_eq!(inline, serial, "{code}"),
            }
        }
    }

    /// A fold over a source answers when the source ends and not before: `main` holds nothing
    /// while rows arrive across laps, and the sum of every row once the yield predicate is
    /// everything.
    #[test]
    fn a_fold_over_a_source_answers_once_the_source_closes() {
        let (mut ctx, mut program, source) = over_source1("sum([x + 1 for x in source1()])");
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        let mut main = run.take_main().expect("a main output");
        let universal = main.tiling().universal_guard();
        for (arrived, upto) in [(0..3, 2), (3..5, 4)] {
            arrive(&source, arrived);
            source
                .lock_wait()
                .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
            ctx.scheduler().check_for_notifications();
            assert_eq!(run.lap(), Lap::Ran);
            ctx.scheduler().pull_sinks();
            let tile = main.get(universal.clone());
            assert!(
                tile.is_empty() && !tile.is_terminal(),
                "the fold answers when the source closes: {tile:?}"
            );
        }
        source.lock_wait().set_yield_predicate(Predicate::True);
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![105])));
    }

    /// A pass without a run leaves the sink pulls the delivery queued where they are, as the plain
    /// loop does, and a pass with one serves them after its lap.
    #[test]
    fn a_pass_without_a_run_leaves_a_queued_sink_pull_for_the_next_delivery() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        let pulls = Arc::new(AtomicUsize::new(0));
        let counted = pulls.clone();
        let sink: crate::interpreter::SharedConsumer = Arc::new(Mutex::new(move || {
            counted.fetch_add(1, Ordering::Relaxed);
        }));

        let mut ctx = GlobalContext::default();
        ctx.scheduler().sink_pull_queue().request(sink.clone());
        assert!(!PooledRun::serve_pass(None, ctx.scheduler()));
        assert_eq!(pulls.load(Ordering::Relaxed), 0, "the refused loop waits");
        assert!(ctx.scheduler().pull_sinks(), "the next delivery serves it");
        assert_eq!(pulls.load(Ordering::Relaxed), 1);

        let mut program = compiled(&mut ctx, "[x + 1 for x in [1, 2, 3]]");
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        ctx.scheduler().sink_pull_queue().request(sink);
        assert!(PooledRun::serve_pass(Some(&mut run), ctx.scheduler()));
        assert_eq!(pulls.load(Ordering::Relaxed), 2, "a pass with a run pulls");
    }

    /// A dispatcher that failed ends the lap with `Failed`, not `Done`: the run's answer is
    /// discarded.
    #[test]
    fn a_lap_of_a_failed_dispatcher_says_so() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, "[x + 1 for x in [1, 2, 3]]");
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        run.dispatcher.fail();
        assert_eq!(run.lap(), Lap::Failed);
    }

    /// A shared value over a literal list is two pipelines, and the check counts one that reads a
    /// source: the pipeline behind the `Memo` starts at a slot that reads a breaker.
    #[test]
    fn the_check_counts_the_pipelines_that_read_a_source() {
        let mut ctx = GlobalContext::default();
        let program = compiled(
            &mut ctx,
            indoc! {"
                xs = [x + 1 for x in [1, 2, 3]]
                [a * 2 for a in xs]
            "},
        );
        let main = program.outputs.iter().find(|o| o.is_main()).expect("main");
        assert_eq!(check_pipelines(&*main.op).ok(), Some(1));
    }

    /// A program that writes `x + 1` of every row of `source1()` to the sink `out`, with the source
    /// and the sink registered.
    fn writes_to_a_sink(
        code: &str,
    ) -> (
        GlobalContext,
        CompiledProgram,
        Arc<Mutex<TestDataSource>>,
        Arc<crate::interpreter::TestSink>,
    ) {
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let sink = ctx.register_test_sink("out");
        let program = compiled(&mut ctx, code);
        (ctx, program, source, sink)
    }

    /// The bindings of a collection value, in an order that does not depend on arrival.
    fn bindings(value: Value) -> Vec<String> {
        let Value::Function(bindings) = value else {
            panic!("a collection, got {value:?}");
        };
        let mut rendered: Vec<String> = bindings.iter().map(|b| format!("{b:?}")).collect();
        rendered.sort();
        rendered
    }

    const SINK_CODE: &str = indoc! {"
        out = test_sink()
        for x in source1():
            out << x + 1
    "};

    /// The value the sink holds after the serial loop ran the program over the rows `0..rows` of
    /// `source1()`, the source closed.
    fn serial_sink_value(rows: i64) -> Value {
        let (mut ctx, _program, source, sink) = writes_to_a_sink(SINK_CODE);
        arrive(&source, 0..rows);
        source.lock_wait().set_yield_predicate(Predicate::True);
        for _ in 0..16 {
            ctx.scheduler().check_for_notifications();
        }
        sink.value().expect("the serial loop completed the sink")
    }

    /// A sink is pulled through a reader of its pipeline's breaker: rows that arrive across laps
    /// reach it once each, and it is complete when the source ends, holding what the serial loop's
    /// sink holds.
    #[test]
    fn a_sink_receives_each_row_once_and_is_complete_when_the_source_ends() {
        let (mut ctx, mut program, source, sink) = writes_to_a_sink(SINK_CODE);
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        assert!(run.take_main().is_none(), "the program has no `main`");
        for (arrived, upto) in [(0..3, 2), (3..7, 6)] {
            arrive(&source, arrived);
            source
                .lock_wait()
                .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
            ctx.scheduler().check_for_notifications();
            assert_eq!(run.lap(), Lap::Ran);
            ctx.scheduler().pull_sinks();
            assert!(
                sink.value().is_err(),
                "the sink is not complete while the source can still deliver"
            );
        }
        source.lock_wait().set_yield_predicate(Predicate::True);
        for _ in 0..8 {
            ctx.scheduler().check_for_notifications();
            run.lap();
            ctx.scheduler().pull_sinks();
        }
        assert_eq!(
            bindings(sink.value().expect("complete")),
            bindings(serial_sink_value(7))
        );
        assert_eq!(sink.rows_handed(), 7, "each row is handed to the sink once");
    }

    /// `code` compiled over a source that already holds the keys `held`, with its yield predicate
    /// at the last of them and a reader `lagging` that has released nothing, so the source keeps
    /// every row. Compiling pulls each sink, which hands it the held rows.
    fn compiled_over_held_rows(
        code: &str,
        sinks: &[&str],
        held: std::ops::Range<i64>,
    ) -> (
        GlobalContext,
        CompiledProgram,
        Arc<Mutex<TestDataSource>>,
        Vec<Arc<crate::interpreter::TestSink>>,
    ) {
        use crate::interpreter::DataSourceDomainExtentImpl;
        let source = Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let handles = sinks
            .iter()
            .map(|name| ctx.register_test_sink(*name))
            .collect();
        let last = held.end - 1;
        let some = !held.is_empty();
        arrive(&source, held);
        {
            let mut source = source.lock_wait();
            if some {
                source.set_yield_predicate(Predicate::at_or_below(Value::UInt(last as u64)));
            }
            source.release("lagging", Predicate::False);
        }
        let program = compiled(&mut ctx, code);
        (ctx, program, source, handles)
    }

    /// Run `program` on the pool, deliver the rows `3..5` with the source complete, and serve
    /// until it settles.
    fn finish_over_arrivals(
        ctx: &mut GlobalContext,
        program: &mut CompiledProgram,
        source: &Arc<Mutex<TestDataSource>>,
    ) {
        let config = Config {
            threads: 1,
            morsel_rows: 2,
        };
        let mut run = PooledRun::start(ctx, program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        arrive(source, 3..5);
        source.lock_wait().set_yield_predicate(Predicate::True);
        for _ in 0..8 {
            ctx.scheduler().check_for_notifications();
            run.lap();
            ctx.scheduler().pull_sinks();
        }
    }

    /// The rows a source held when the program compiled were handed to the sink then, and the pool
    /// that replaces the serial producer starts its records where that producer had released:
    /// another reader holds the source's agreement back, so nothing else keeps the held rows from
    /// being offered again.
    #[test]
    fn rows_held_at_compile_reach_the_sink_once() {
        let (mut ctx, mut program, source, sinks) =
            compiled_over_held_rows(SINK_CODE, &["out"], 0..3);
        ctx.scheduler().pull_sinks();
        assert_eq!(sinks[0].rows_handed(), 3, "compiling pulled the held rows");
        finish_over_arrivals(&mut ctx, &mut program, &source);
        assert_eq!(sinks[0].rows_handed(), 5, "each row reaches the sink once");
        assert_eq!(
            bindings(sinks[0].value().expect("complete")),
            bindings(serial_sink_value(5))
        );
    }

    /// Two sinks over two chains each inherit what their own serial chain had released, and each
    /// receives every row once.
    #[test]
    fn each_sink_inherits_what_its_own_chain_released() {
        let code = indoc! {"
            first = test_sink()
            second = test_sink()
            for x in source1():
                first << x + 1
            for y in source1():
                second << y + 2
        "};
        let (mut ctx, mut program, source, sinks) =
            compiled_over_held_rows(code, &["first", "second"], 0..3);
        ctx.scheduler().pull_sinks();
        assert_eq!(
            [sinks[0].rows_handed(), sinks[1].rows_handed()],
            [3, 3],
            "compiling pulled the held rows into each sink"
        );
        finish_over_arrivals(&mut ctx, &mut program, &source);
        assert_eq!(
            [sinks[0].rows_handed(), sinks[1].rows_handed()],
            [5, 5],
            "each sink received every row once"
        );
    }

    /// A serial producer that had released nothing leaves the pool's records at nothing: rows that
    /// arrive after the pool starts are the only rows, and each arrives once.
    #[test]
    fn a_pool_over_a_producer_that_released_nothing_starts_at_nothing() {
        let (mut ctx, mut program, source, sinks) =
            compiled_over_held_rows(SINK_CODE, &["out"], 0..0);
        finish_over_arrivals(&mut ctx, &mut program, &source);
        assert_eq!(sinks[0].rows_handed(), 2, "the rows 3..5");
    }
}

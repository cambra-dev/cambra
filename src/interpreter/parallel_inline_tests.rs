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
        let config = Config { morsel_rows };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        let mut main = run.take_main().expect("a main output");
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert!(run.lap() == Lap::Done, "every pipeline finished");
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

    /// A fold into `main` is answered once its pipeline finishes.
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

    /// `main` is the cache of the breaker that ends its pipeline: the rows are held until `main`
    /// releases them, the release reclaims them, and a pull after answers empty.
    #[test]
    fn main_releases_what_it_read_and_a_pull_after_answers_empty() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, &format!("[x + 1 for x in {}]", list(20)));
        let config = Config { morsel_rows: 4 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        let mut main = run.take_main().expect("a main output");
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(entries(&tile).len(), 20);
        assert_eq!(
            run.held_keys(),
            20,
            "nothing was released before `main` did"
        );
        let universal = main.tiling().universal_guard();
        main.release(universal.clone());
        assert_eq!(run.held_keys(), 0, "the release reclaims what `main` read");
        assert!(main.get(universal).is_empty());
    }

    /// A program the pool refuses keeps its producer and the graph, and the serial loop drives it.
    #[test]
    fn a_refused_program_keeps_its_producer() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, "3 + 1");
        let mut held = program.main_mut().and_then(|o| o.producer.take());
        let config = Config { morsel_rows: 4 };
        let refused = PooledRun::start(&mut ctx, &mut program, &mut held, &config, Box::new(|| {}))
            .err()
            .expect("a constant is not a pipeline");
        assert!(refused.to_string().contains("no source of rows"));
        let mut held = held.expect("the producer the loop drives is kept");
        let code = "3 + 1";
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
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("a source that cuts morsels is admitted");
        let mut main = run.take_main().expect("a main output");
        let universal = main.tiling().universal_guard();
        ctx.scheduler().check_for_notifications();
        assert!(run.lap() == Lap::Idle, "nothing has arrived");

        let rows: Vec<(Value, Value)> = (0..5)
            .map(|k| (Value::UInt(k as u64), Value::Int(k * 10)))
            .collect();
        source.lock_wait().add_data(&rows);
        source
            .lock_wait()
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(4)));
        ctx.scheduler().check_for_notifications();
        assert!(run.lap() == Lap::Ran);
        ctx.scheduler().pull_sinks();
        let tile = main.get(universal.clone());
        assert_eq!(entries(&tile).len(), 5, "{tile:?}");
        assert!(!tile.is_terminal(), "the source can still deliver");
        assert!(run.lap() == Lap::Idle);
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
            let config = Config { morsel_rows: 2 };
            let mut run =
                PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
                    .expect("admitted");
            let mut main = run.take_main().expect("a main output");
            let inline = drive(&mut ctx, &mut run, &mut *main, 100);
            assert!(run.lap() == Lap::Done, "{code}: the pipeline finished");
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
        let config = Config { morsel_rows: 2 };
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
            assert!(run.lap() == Lap::Ran);
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
        let config = Config { morsel_rows: 2 };
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
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .expect("admitted");
        run.dispatcher.fail();
        assert!(run.lap() == Lap::Failed);
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
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        assert!(run.take_main().is_none(), "the program has no `main`");
        for (arrived, upto) in [(0..3, 2), (3..7, 6)] {
            arrive(&source, arrived);
            source
                .lock_wait()
                .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
            ctx.scheduler().check_for_notifications();
            assert!(run.lap() == Lap::Ran);
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

    /// A memo that reads a live source runs in sink mode behind the rows as they arrive: a lap
    /// polls the memo's pipeline for the arrivals its input does not report, so the sink behind
    /// the memo receives each row once and holds what the serial loop's sink holds. Two memos in a
    /// chain do the same.
    #[test]
    fn a_memo_over_a_live_source_in_sink_mode_delivers_each_row_once() {
        let programs = [
            indoc! {"
                xs = [x + 1 for x in source1()]
                out = test_sink()
                for x in xs:
                    out << x * 2
            "},
            indoc! {"
                xs = [x + 1 for x in source1()]
                ys = [x * 2 for x in xs]
                out = test_sink()
                for y in ys:
                    out << y + 3
            "},
        ];
        for code in programs {
            let (mut serial_ctx, _serial_program, serial_source, serial_sink) =
                writes_to_a_sink(code);
            arrive(&serial_source, 0..7);
            serial_source
                .lock_wait()
                .set_yield_predicate(Predicate::True);
            for _ in 0..16 {
                serial_ctx.scheduler().check_for_notifications();
            }
            let expected = bindings(serial_sink.value().expect("the serial loop completed"));

            let (mut ctx, mut program, source, sink) = writes_to_a_sink(code);
            let config = Config { morsel_rows: 2 };
            let mut run =
                PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
                    .unwrap_or_else(|why| panic!("{why}"));
            for (arrived, upto) in [(0..3, 2), (3..7, 6)] {
                arrive(&source, arrived);
                source
                    .lock_wait()
                    .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
                ctx.scheduler().check_for_notifications();
                for _ in 0..4 {
                    run.lap();
                    ctx.scheduler().pull_sinks();
                }
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
            assert_eq!(bindings(sink.value().expect("complete")), expected);
            assert_eq!(sink.rows_handed(), 7, "each row is handed to the sink once");
        }
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

    /// Run `program` on the pool, deliver the rows `more` with the source complete, and serve
    /// until it settles.
    fn finish_over_arrivals(
        ctx: &mut GlobalContext,
        program: &mut CompiledProgram,
        source: &Arc<Mutex<TestDataSource>>,
        more: std::ops::Range<i64>,
    ) {
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(ctx, program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        arrive(source, more);
        source.lock_wait().set_yield_predicate(Predicate::True);
        for _ in 0..8 {
            ctx.scheduler().check_for_notifications();
            run.lap();
            ctx.scheduler().pull_sinks();
        }
    }

    /// The rows a source held when the program compiled were handed to the sink then. The memo that
    /// wraps the serial producer keeps its release records, so a reader that holds the source's
    /// agreement back does not make the held rows offered again.
    #[test]
    fn rows_held_at_compile_reach_the_sink_once() {
        let (mut ctx, mut program, source, sinks) =
            compiled_over_held_rows(SINK_CODE, &["out"], 0..3);
        ctx.scheduler().pull_sinks();
        assert_eq!(sinks[0].rows_handed(), 3, "compiling pulled the held rows");
        finish_over_arrivals(&mut ctx, &mut program, &source, 3..5);
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
        finish_over_arrivals(&mut ctx, &mut program, &source, 3..5);
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
        finish_over_arrivals(&mut ctx, &mut program, &source, 3..5);
        assert_eq!(sinks[0].rows_handed(), 2, "the rows 3..5");
    }

    const KEYED_CODE: &str = indoc! {"
        xs = source1()
        [y * 2 for y in xs if y > 12]
    "};

    /// The collection `KEYED_CODE` answers over the rows `0..rows` of `source1()` (the value
    /// `10 * key`), by key, from the serial loop.
    fn serial_keyed(rows: i64) -> Vec<(u64, i64)> {
        let (mut ctx, mut program, source) = over_source1(KEYED_CODE);
        arrive(&source, 0..rows);
        source.lock_wait().set_yield_predicate(Predicate::True);
        let producer = program
            .main_mut()
            .and_then(|output| output.producer.as_mut())
            .expect("a main output");
        let tile = crate::interpreter::pull_laps(
            ctx.scheduler(),
            &mut **producer,
            1024,
            Tile::is_terminal,
        );
        entries(&tile)
    }

    /// A chain that reads a memo at its own keys runs behind the pipeline that fills the memo:
    /// rows that arrive in waves, with morsels of two rows, give the serial answer, every row is
    /// read and released, and no morsel of the downstream pipeline names a key the memo has not
    /// merged (it would read a row that is not there). The memo's pushes are what name the keys.
    #[test]
    fn a_keyed_read_runs_behind_the_keys_its_memo_has_merged() {
        let whole = std::iter::once(0..7).collect::<Vec<_>>();
        for waves in [whole, vec![0..1, 1..4, 4..7], vec![0..3, 3..4, 4..7]] {
            let (mut ctx, mut program, source) = over_source1(KEYED_CODE);
            let config = Config { morsel_rows: 2 };
            let mut run =
                PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
                    .unwrap_or_else(|why| panic!("{why}"));
            let mut main = run.take_main().expect("a main output");
            let universal = main.tiling().universal_guard();
            for wave in waves.iter().cloned() {
                let upto = wave.end as u64 - 1;
                arrive(&source, wave);
                source
                    .lock_wait()
                    .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
                ctx.scheduler().check_for_notifications();
                run.lap();
                ctx.scheduler().pull_sinks();
            }
            source.lock_wait().set_yield_predicate(Predicate::True);
            let tile = drive(&mut ctx, &mut run, &mut *main, 100);
            assert_eq!(entries(&tile), serial_keyed(7), "{waves:?}");
            main.release(universal);
            assert_eq!(run.held_keys(), 0, "{waves:?}: every row was released");
        }
    }

    /// The arrivals of the source a keyed chain iterates notify its head with the keys that
    /// arrived, and those keys are not the ones the memo has merged. A keyed head publishes what
    /// is ready for any notification: a source that reports `Keys [0, 3]` of an arrival the memo's
    /// pipeline has not run yet must not make the keyed pipeline's source claim key 3 early.
    #[test]
    fn a_keyed_head_publishes_what_the_memo_has_ready_for_raw_arrival_keys() {
        use crate::interpreter::{FunctionGuard, Projection, tiling::Predicate as P};
        let (mut ctx, mut program, source) = over_source1(KEYED_CODE);
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        let mut main = run.take_main().expect("a main output");
        arrive(&source, 0..4);
        source
            .lock_wait()
            .set_yield_predicate(Predicate::at_or_below(Value::UInt(3)));
        // The region names keys the memo's pipeline has not merged: no lap has run.
        let keys = P::intervals(intervalsets::IntervalSet::from(
            intervalsets::Interval::closed(Value::UInt(0), Value::UInt(3)),
        ));
        let region = Projection::of(&TileGuard::Function(FunctionGuard::Domain(keys)))
            .expect("keys name a projection");
        ctx.scheduler().notify_source_consumers("source1", &region);
        run.lap();
        source.lock_wait().set_yield_predicate(Predicate::True);
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(entries(&tile), serial_keyed(4));
    }

    /// Two sinks that read one memo at keys share the memo's pipeline, which inherits what both
    /// serial chains had released: each sink is handed every row it is owed once, though the rows
    /// they filter out differ.
    #[test]
    fn two_sinks_over_one_memo_each_receive_their_rows_once() {
        let code = indoc! {"
            first = test_sink()
            second = test_sink()
            xs = source1()
            for x in xs:
                if x > 12:
                    first << x
            for y in xs:
                if y > 22:
                    second << y
        "};
        let (mut ctx, mut program, source, sinks) =
            compiled_over_held_rows(code, &["first", "second"], 0..5);
        ctx.scheduler().pull_sinks();
        assert_eq!(
            [sinks[0].rows_handed(), sinks[1].rows_handed()],
            [3, 2],
            "compiling pulled the held rows each sink filters in"
        );
        finish_over_arrivals(&mut ctx, &mut program, &source, 5..8);
        assert_eq!(
            [sinks[0].rows_handed(), sinks[1].rows_handed()],
            [6, 5],
            "each sink received the rows it filters in, once"
        );
    }

    /// A value the program names and reads runs as two pipelines with the memo as the breaker of
    /// the first, and answers as the serial loop does.
    #[test]
    fn a_memo_pipeline_equals_the_serial_answer() {
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

    /// A source that cannot cut morsels is refused, and the program then runs on the scheduler
    /// loop and answers as a serial run does.
    #[test]
    fn a_source_that_cannot_cut_morsels_is_refused_and_the_program_runs_serially() {
        let source = Arc::new(Mutex::new(
            TestDataSource::new(
                "source1",
                crate::ccl::Type::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            )
            .declining_morsels(),
        ));
        let mut ctx = GlobalContext::default();
        ctx.register_source(source.clone());
        let mut program = compiled(&mut ctx, "[x + 1 for x in source1()]");
        arrive(&source, 0..3);
        source.lock_wait().set_yield_predicate(Predicate::True);
        let config = Config { morsel_rows: 2 };
        let refused = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .err()
            .expect("a source that cannot cut morsels is not a morsel pipeline");
        assert!(
            refused.to_string().contains("cut into morsels"),
            "{refused}"
        );
        let producer = program
            .main_mut()
            .and_then(|output| output.producer.as_mut())
            .expect("the program keeps the producer the scheduler loop drives");
        let tile = crate::interpreter::pull_laps(ctx.scheduler(), producer.as_mut(), 8, |tile| {
            !tile.is_empty()
        });
        assert_eq!(entries(&tile), [(0, 1), (1, 11), (2, 21)]);
    }

    /// A value the program names and reads, over a live source, leaves no retained key at the
    /// source once the run is released, and no release record once the context is dropped.
    #[test]
    fn a_memo_over_a_source_leaves_no_record_and_no_key() {
        let (mut ctx, mut program, source) = over_source1(indoc! {"
            xs = [x + 1 for x in source1()]
            [a * 2 for a in xs]
        "});
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        let mut main = run.take_main().expect("a main output");
        let universal = main.tiling().universal_guard();
        arrive(&source, 0..5);
        source.lock_wait().set_yield_predicate(Predicate::True);
        ctx.scheduler().check_for_notifications();
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert_eq!(entries(&tile), [(0, 2), (1, 22), (2, 42), (3, 62), (4, 82)]);
        main.release(universal);
        drop(main);
        drop(run);
        assert_eq!(
            source.lock_wait().retained_keys(),
            0,
            "the memo released the rows it merged"
        );
        // The memo's producer, which owns the chain that reads the source, lives in the context's
        // fan-outs and holds its record, fully released, until the context drops.
        drop(program);
        drop(ctx);
        assert_eq!(source.lock_wait().release_records(), 0);
    }

    /// A fold into `main` over a live source states its result terminal when the source's arrivals
    /// have ended, and its value is the serial loop's.
    #[test]
    fn a_fold_over_a_live_source_is_terminal_when_the_source_ends() {
        let (mut ctx, mut program, source) = over_source1("sum([x for x in source1()])");
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .unwrap_or_else(|why| panic!("{why}"));
        let mut main = run.take_main().expect("a main output");
        let universal = main.tiling().universal_guard();
        for (arrived, upto) in [(0..3, 2), (3..5, 4)] {
            arrive(&source, arrived);
            source
                .lock_wait()
                .set_yield_predicate(Predicate::at_or_below(Value::UInt(upto)));
            ctx.scheduler().check_for_notifications();
            for _ in 0..4 {
                run.lap();
            }
            assert!(
                !main.get(universal.clone()).is_terminal(),
                "the source can still deliver"
            );
        }
        source.lock_wait().set_yield_predicate(Predicate::True);
        let tile = drive(&mut ctx, &mut run, &mut *main, 100);
        assert!(tile.is_terminal());
        let Tile::Scalar(ColumnValue::Ints(sum)) = tile else {
            panic!("a scalar sum")
        };
        assert_eq!(sum, [100]);
    }

    /// A group-by is two pipelines that end in the `Converse` and in the grouped fold, and `main`
    /// answers as the serial loop does at morsel sizes that do and do not divide the groups.
    #[test]
    fn a_group_by_equals_the_serial_answer() {
        for items in [1, 4, 9, 20] {
            let code = formatdoc! {"
                [sum(g) for g in groupby({}, \\x -> x // 3)]
            ", list(items)};
            for morsel_rows in [1, 2, 7] {
                assert_eq!(
                    entries_by_group(&inline(&code, morsel_rows)),
                    entries_by_group(&serial(&code)),
                    "{items} items, {morsel_rows}-row morsels"
                );
            }
        }
    }

    /// The groups of a collection of sums as `(key, sum)` pairs, whatever order they are held in.
    fn entries_by_group(tile: &Tile) -> Vec<(Value, i64)> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(sums)) = codomain.as_ref() else {
            panic!("sums, got {tile:?}")
        };
        let mut pairs: Vec<(Value, i64)> = (0..domain.len())
            .map(|row| (domain.index_at(row), sums[row]))
            .collect();
        pairs.sort_by(|a, b| a.partial_cmp(b).expect("keys compare"));
        pairs
    }

    /// The consumer given to the run is woken by the breaker of `main`'s pipeline: its rounds say
    /// `main` has rows to read, and the terminal round says it is complete.
    #[test]
    fn the_consumer_of_main_is_woken_from_the_breakers_rounds() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, &format!("[x + 1 for x in {}]", list(6)));
        let woken = Arc::new(Mutex::new(0usize));
        let counter = woken.clone();
        let config = Config { morsel_rows: 2 };
        let mut run = PooledRun::start(
            &mut ctx,
            &mut program,
            &mut None,
            &config,
            Box::new(move || *counter.lock_now() += 1),
        )
        .expect("admitted");
        let mut main = run.take_main().expect("a main output");
        assert_eq!(*woken.lock_now(), 0, "nothing ran yet");
        drive(&mut ctx, &mut run, &mut *main, 100);
        assert!(*woken.lock_now() >= 1, "a round woke the consumer");
    }

    /// A program whose output has no producer to wrap is refused before anything is taken, not
    /// by a panic.
    #[test]
    fn an_output_without_a_producer_is_refused() {
        let mut ctx = GlobalContext::default();
        let mut program = compiled(&mut ctx, &format!("[x + 1 for x in {}]", list(4)));
        let held = program.main_mut().and_then(|output| output.producer.take());
        let config = Config { morsel_rows: 2 };
        let refused = PooledRun::start(&mut ctx, &mut program, &mut None, &config, Box::new(|| {}))
            .err()
            .expect("no producer for `main`");
        assert!(refused.to_string().contains("no producer"), "{refused}");
        drop(held);
    }
}

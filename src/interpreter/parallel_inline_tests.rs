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
    use crate::interpreter::{BaseType, ColumnValue, Extent, TestDataSource, Value};

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
        let mut main = run.take_main();
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
        let mut main = run.take_main();
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
        let mut main = run.take_main();
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
            let mut main = run.take_main();
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
        let mut main = run.take_main();
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
}

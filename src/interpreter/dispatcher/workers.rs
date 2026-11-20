//! The run's threads: the coordinator and the worker threads it starts, each claiming from the
//! run's dispatcher until the run ends. The dispatcher decides what may run at once; a thread only
//! claims, runs the claim through the run's execution, and waits. See
//! `src/interpreter/design-dispatcher.md`, "Who claims what".
use super::partitioned::Partitioned;
use super::plan::Execution;
use super::*;
use std::thread::{Scope, ScopedJoinHandle};

/// What a thread's claim did ([`Execution::run`]).
pub(super) enum Claimed {
    /// It ran a package or a finish.
    Ran,
    /// Nothing was claimable since the generation.
    Wait(Generation),
    Done,
    Failed,
}

/// The run's worker threads.
pub(super) struct WorkerPool {
    /// How many threads the run has, the coordinator included: it starts one fewer worker thread.
    /// With one, the coordinator claims everything and no thread starts.
    count: usize,
}

impl WorkerPool {
    pub(super) fn new(count: usize) -> Self {
        assert!(count > 0, "a run has at least one worker");
        Self { count }
    }

    /// Start the workers in `scope`. Each claims until the run is done, has failed, or its claims
    /// are stopped, and reaches breakers through `root` as the coordinator does.
    /// [`join`](Self::join) takes the handles. A thread the system refuses leaves the run with the
    /// workers it has, the coordinator at least.
    pub(super) fn spawn<'scope, 'env>(
        &'env self,
        scope: &'scope Scope<'scope, 'env>,
        dispatcher: &'env Dispatcher,
        execution: &'env Execution,
        partitioned: &'env Partitioned,
        root: &'env SharedReach<'env>,
    ) -> Vec<ScopedJoinHandle<'scope, ()>> {
        // Panicking on a refused thread would leave the workers already started asleep, and the
        // scope waiting for them.
        let mut handles = Vec::new();
        for worker in 0..self.count - 1 {
            match thread::Builder::new().spawn_scoped(scope, move || {
                work(dispatcher, execution, partitioned, root, worker)
            }) {
                Ok(handle) => handles.push(handle),
                Err(_) => break,
            }
        }
        handles
    }

    /// Join the workers, and resume a worker's panic on this thread.
    pub(super) fn join(handles: Vec<ScopedJoinHandle<'_, ()>>) {
        let mut panicked = None;
        for handle in handles {
            if let Err(payload) = handle.join() {
                panicked.get_or_insert(payload);
            }
        }
        if let Some(payload) = panicked {
            std::panic::resume_unwind(payload);
        }
    }

    /// The index the coordinator's claims count under, after the worker threads'.
    pub(super) fn coordinator(&self) -> usize {
        self.count - 1
    }
}

/// One worker's claims, until the run ends.
fn work(
    dispatcher: &Dispatcher,
    execution: &Execution,
    partitioned: &Partitioned,
    root: &SharedReach<'_>,
    worker: usize,
) {
    in_a_run(|| {
        // A panic fails the run, so no claimant waits for what this worker held.
        let _worker = dispatcher.worker();
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            execution.reach(pipeline, root, call);
        };
        let mut preferred = None;
        loop {
            let next = dispatcher.try_claim(preferred);
            match execution.run(
                dispatcher,
                &mut reach,
                partitioned,
                next,
                &mut preferred,
                worker,
            ) {
                Claimed::Ran => {}
                Claimed::Wait(generation) => dispatcher.wait(generation),
                Claimed::Done | Claimed::Failed => return,
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use indoc::formatdoc;

    use super::super::run_program_with_workers;
    use crate::ccl::{
        context::{GlobalContext, compile_program},
        load::LoadedProgram,
    };

    fn evaluate(source: &str, dop: usize) -> super::super::Run {
        let mut context = GlobalContext::default();
        let mut program =
            compile_program(&mut context, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        run_program_with_workers(&mut program, 8, dop).unwrap()
    }
    #[test]
    fn compiled_programs_use_shared_native_breakers_at_each_dop() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        for tail in [
            "[y + 1 for y in ys]",
            "max(ys)",
            "sum(ys)",
            "max([max(g) for g in groupby(ys, \\x -> x - (x // 8) * 8)])",
        ] {
            let source = format!("xs = [{values}]\nys = [x * 2 for x in xs]\n{tail}");
            let inline = evaluate(&source, 1);
            assert!(
                inline.planned.iter().all(|p| p.worker_claims == 0),
                "one worker consumes on the coordinator: {tail}"
            );
            let expected = inline.main.map(crate::interpreter::sort_function_by_domain);
            for dop in [2, 4] {
                let run = evaluate(&source, dop);
                assert_eq!(
                    run.main.map(crate::interpreter::sort_function_by_domain),
                    expected,
                    "DOP {dop}: {tail}"
                );
                assert!(
                    run.planned.iter().any(|p| p.worker_claims > 0),
                    "no native worker: {tail}"
                );
            }
        }
    }
    #[test]
    fn native_pipelines_publish_before_dependencies_close() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let run = evaluate(
            &format!("xs = [{values}]\nys = [x * 2 for x in xs]\n[y + 1 for y in ys]"),
            4,
        );
        assert!(
            run.planned.iter().any(|p| p.workers_used > 1),
            "{:#?}",
            run.planned
        );
        assert!(
            run.planned.iter().any(|p| p.incremental_claims > 0),
            "{:#?}",
            run.planned
        );
    }
    /// A `:=` loop over a collection the workers build answers at more than one worker what it
    /// answers at one: its body runs as serial work, and its source's packages are partitioned.
    #[test]
    fn a_loop_answers_at_each_dop_what_it_answers_at_one() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            ys = [x * 2 for x in xs]
            total := 0
            for y in ys:
                total += y
            total
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            let run = evaluate(&source, dop);
            assert_eq!(run.main, expected, "DOP {dop}");
            assert!(
                run.planned.iter().any(|p| p.worker_claims > 0),
                "DOP {dop}: the source of the loop runs on the workers"
            );
        }
    }

    /// A `:=` loop whose body holds breakers the workers run, a materialized comprehension and a
    /// `max` over it, answers at more than one worker what it answers at one: each round's work
    /// is queued once the scope releases its store, and the step waits for what the round's
    /// consumes left held.
    #[test]
    fn a_loop_body_on_the_workers_answers_what_it_answers_at_one() {
        let values = (0..256)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            total := 0
            for x in xs:
                total += max([x * k for k in [1, 2, 3]])
            total
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            for _ in 0..4 {
                let run = evaluate(&source, dop);
                assert_eq!(run.main, expected, "DOP {dop}");
                // Each of the 256 rounds gives the body's breakers a package each, counted under
                // the loop's request pipeline.
                let body: usize = run
                    .planned
                    .iter()
                    .filter(|planned| planned.name.starts_with("InductionRequest"))
                    .map(|planned| planned.worker_claims)
                    .sum();
                assert!(
                    body >= 256,
                    "DOP {dop}: the body runs on the workers: {:?}",
                    run.planned
                );
            }
        }
    }

    /// A transaction writer whose body holds breakers the workers run answers at more than one
    /// worker what it answers at one: each attempt's work is queued once the writer releases its
    /// store, and the commit waits for what the attempt's consumes left held.
    #[test]
    fn a_transaction_body_on_the_workers_answers_what_it_answers_at_one() {
        let values = (0..128)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = formatdoc! {"
            xs = [{values}]
            t: Mut(Int, Txn) := 0
            for x in xs:
                with begin():
                    t := t + max([x * k for k in [1, 2, 3]])
            await_final(t)
        "};
        let expected = evaluate(&source, 1).main;
        for dop in [2, 4] {
            for _ in 0..4 {
                let run = evaluate(&source, dop);
                assert_eq!(run.main, expected, "DOP {dop}");
                // Each of the 128 attempts gives the body's breaker a package, counted under the
                // writer's pipeline.
                let body: usize = run
                    .planned
                    .iter()
                    .filter(|planned| planned.name.starts_with("Commit"))
                    .map(|planned| planned.worker_claims)
                    .sum();
                assert!(
                    body >= 128,
                    "DOP {dop}: the body runs on the workers: {:?}",
                    run.planned
                );
            }
        }
    }

    /// A panic in a claim a worker consumes ends the run with that panic on the calling thread,
    /// and the pool it unwinds through joins its workers: a later run on the thread completes.
    #[test]
    fn a_worker_panic_ends_the_run_with_that_panic() {
        let values = (0..512)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let failed = std::panic::catch_unwind(|| {
            evaluate(
                &formatdoc! {"
                    xs = [{values}]
                    ys = [x // (x - x) for x in xs]
                    [y + 1 for y in ys]
                "},
                4,
            )
        })
        .err()
        .expect("a division by zero in a worker's claim fails the run");
        assert_eq!(
            failed.downcast_ref::<&str>().copied(),
            Some("attempt to divide by zero")
        );
        let run = evaluate(
            &formatdoc! {"
                xs = [{values}]
                ys = [x * 2 for x in xs]
                max(ys)
            "},
            4,
        );
        assert!(run.planned.iter().any(|p| p.worker_claims > 0));
    }
}

//! Compiled finite programs with shared operator plans, worker-local state and shared breakers.

use super::runtime::{RuntimeContext, RuntimePipeline, WorkerContext};
use super::{Dispatcher, Next, PipelineId, WorkPackage};
use crate::ccl::context::CompiledProgram;
use crate::interpreter::Tile;
use std::sync::mpsc;
use std::thread;

/// The final answer and work admitted across the shared pipeline graph.
pub struct ParallelRun {
    pub main: Tile,
    pub claims: usize,
    pub workers_used: usize,
    /// Data claims consumed by each pipeline, in dependency order.
    pub pipeline_claims: Vec<usize>,
    /// Producer states initialized by each pipeline, at most one per worker.
    pub pipeline_instances: Vec<usize>,
    /// Claims admitted while at least one upstream pipeline remains open.
    pub incremental_claims: usize,
    /// Worker-local aggregate batches integrated into shared breakers.
    pub aggregate_flushes: usize,
    /// Input morsels folded into worker-local aggregate buffers.
    pub aggregate_claims: usize,
}

/// Evaluate a finite pure main with shared intermediate breakers and immutable operator plans.
/// Each worker owns private producer state. Live and retained-state programs remain refused.
pub fn run_program_parallel(
    program: &CompiledProgram,
    workers: usize,
    morsel_rows: usize,
) -> Result<ParallelRun, String> {
    if workers == 0 || morsel_rows == 0 {
        return Err("workers and morsel rows must be positive".into());
    }
    let [output] = program.outputs.as_slice() else {
        return Err("parallel execution requires one pure main output".into());
    };
    if !output.is_main() || output.sink_consumer.is_some() {
        return Err("parallel sink execution is not enabled".into());
    }
    let mut context = RuntimeContext::default();
    let factory = output.op.runtime_operator(&mut context)?;
    let main_index = context.main(factory, output.op.tiling());
    let nodes = &context.pipelines;
    let dispatcher = configure(nodes, morsel_rows);
    let stats = execute(&dispatcher, nodes, workers)?;
    let mut main = nodes[main_index].output.snapshot();
    main.compact();
    if !main.is_terminal() {
        return Err("parallel output did not become terminal".into());
    }
    let aggregate_claims = stats
        .claims
        .iter()
        .enumerate()
        .filter(|(p, _)| nodes[*p].aggregate.is_some())
        .map(|(_, n)| *n)
        .sum();
    Ok(ParallelRun {
        main,
        claims: stats.claims.iter().sum(),
        workers_used: stats.workers,
        pipeline_claims: stats.claims,
        pipeline_instances: stats.instances,
        incremental_claims: stats.incremental_claims,
        aggregate_flushes: stats.aggregate_flushes,
        aggregate_claims,
    })
}

fn configure(nodes: &[RuntimePipeline], morsel_rows: usize) -> Dispatcher {
    let mut dispatcher = Dispatcher::new(
        nodes.iter().map(|node| node.input.reads.clone()).collect(),
        morsel_rows,
    );
    for (p, node) in nodes.iter().enumerate() {
        for source in &node.input.sources {
            source.output.register(p, source.empty.clone());
        }
        if !node.input.reads.is_empty() {
            dispatcher.wait_for_inputs(PipelineId(p));
            for &read in &node.input.reads {
                nodes[read]
                    .output
                    .register(p, nodes[read].tiling.empty_guard());
                if !node.input.region_reads.contains(&read)
                    || !node.input_tiling.is_data_function()
                    || !node.reads_regions()
                {
                    dispatcher.completes_whole_only(PipelineId(p), PipelineId(read));
                }
            }
        }
    }
    for (p, node) in nodes.iter().enumerate() {
        let guards = node.seeds(morsel_rows);
        if node.input.reads.is_empty() {
            for guard in guards {
                dispatcher.notify(PipelineId(p), &guard);
            }
            dispatcher.close(PipelineId(p));
        } else {
            for guard in guards {
                dispatcher.queue_for(PipelineId(p), &guard);
            }
        }
    }
    dispatcher
}

enum Job {
    Consume(WorkPackage),
    Finish(usize),
    Flush(usize),
}
enum Outcome {
    Applied(WorkPackage),
    Buffered(WorkPackage),
    Flushed(usize),
    Finished(usize),
}
struct Completion {
    slot: usize,
    outcome: Outcome,
    failed: bool,
    built: bool,
}

fn complete_pipeline(dispatcher: &Dispatcher, nodes: &[RuntimePipeline], p: usize) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        nodes[p].output.finish(&nodes[p].tiling);
        for source in &nodes[p].input.sources {
            source.output.release(p, &source.universal);
        }
        for &read in &nodes[p].input.reads {
            nodes[read]
                .output
                .release(p, &nodes[read].tiling.universal_guard());
        }
        for &reader in &dispatcher.infos[p].readers {
            dispatcher.record_complete(reader, p, None);
        }
        dispatcher.finish(dispatcher.pushes(PipelineId(p)));
    }))
    .is_ok()
}

fn settle_claim(dispatcher: &Dispatcher, nodes: &[RuntimePipeline], claim: WorkPackage) {
    let p = claim.pipeline.0;
    if nodes[p].publishes_regions() {
        for &reader in &dispatcher.infos[p].readers {
            if nodes[reader].input.region_reads.contains(&p)
                && nodes[reader].input_tiling.is_data_function()
                && nodes[reader].reads_regions()
            {
                dispatcher.record_complete(reader, p, Some(&claim.guard));
            }
        }
    }
    for &read in &nodes[p].input.region_reads {
        if nodes[p].input_tiling.is_data_function() && nodes[read].tiling.is_data_function() {
            nodes[read].output.release(p, &claim.guard);
        }
    }
    if nodes[p].input_tiling.is_data_function() {
        for source in &nodes[p].input.region_sources {
            source.output.release(p, &claim.guard);
        }
    }
    dispatcher.acknowledge(claim);
}

#[derive(Default)]
struct BufferedClaims {
    claims: Vec<WorkPackage>,
    since: usize,
}
fn pending_flush(
    idle: &[usize],
    buffers: &[Vec<BufferedClaims>],
    epoch: usize,
    budget: usize,
    force: bool,
) -> Option<(usize, usize, usize)> {
    idle.iter().enumerate().find_map(|(at, &slot)| {
        buffers
            .iter()
            .position(|pipeline| {
                let pending = &pipeline[slot];
                !pending.claims.is_empty()
                    && (force || pending.claims.len() >= 4 || epoch - pending.since >= budget)
            })
            .map(|p| (at, slot, p))
    })
}

struct ExecutionStats {
    claims: Vec<usize>,
    instances: Vec<usize>,
    workers: usize,
    incremental_claims: usize,
    aggregate_flushes: usize,
}

fn execute(
    dispatcher: &Dispatcher,
    nodes: &[RuntimePipeline],
    workers: usize,
) -> Result<ExecutionStats, String> {
    let descriptions: Vec<_> = nodes
        .iter()
        .map(|node| {
            (
                node.input.clone(),
                node.output.clone(),
                node.aggregate.clone(),
            )
        })
        .collect();
    thread::scope(|scope| {
        let (done_tx, done_rx) = mpsc::sync_channel(workers);
        let mut jobs = Vec::new();
        for slot in 0..workers {
            let (tx, rx) = mpsc::sync_channel::<Job>(1);
            let done = done_tx.clone();
            let descriptions = descriptions.clone();
            scope.spawn(move || {
                let mut worker = WorkerContext::default();
                for job in rx {
                    let p = match &job {
                        Job::Consume(claim) => claim.pipeline.0,
                        Job::Finish(p) | Job::Flush(p) => *p,
                    };
                    let mut built = false;
                    let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        super::in_a_run(|| match &job {
                            Job::Consume(claim) => {
                                built = match &descriptions[p].2 {
                                    Some(aggregate) => worker.accumulate(
                                        p,
                                        &descriptions[p].0,
                                        claim.guard.clone(),
                                        aggregate,
                                    ),
                                    None => worker.consume(
                                        p,
                                        &descriptions[p].0,
                                        claim.guard.clone(),
                                        &descriptions[p].1,
                                    ),
                                };
                            }
                            Job::Flush(_) => worker.flush(p, &descriptions[p].1),
                            Job::Finish(_) => {
                                worker.finish(p);
                            }
                        })
                    }))
                    .is_err();
                    let outcome = match job {
                        Job::Consume(claim) if descriptions[p].2.is_some() => {
                            Outcome::Buffered(claim)
                        }
                        Job::Consume(claim) => Outcome::Applied(claim),
                        Job::Finish(p) => Outcome::Finished(p),
                        Job::Flush(p) => Outcome::Flushed(p),
                    };
                    if done
                        .send(Completion {
                            slot,
                            outcome,
                            failed,
                            built,
                        })
                        .is_err()
                    {
                        break;
                    }
                }
            });
            jobs.push(tx);
        }
        drop(done_tx);
        let mut idle: Vec<_> = (0..workers).collect();
        let mut used = vec![false; workers];
        let mut claims = vec![0; nodes.len()];
        let mut instances = vec![0; nodes.len()];
        let mut owners = vec![vec![false; workers]; nodes.len()];
        let mut finishing: Vec<Option<usize>> = vec![None; nodes.len()];
        let mut finish_waiting = vec![vec![false; workers]; nodes.len()];
        let mut active = 0;
        let mut failed = false;
        let mut preferred = 0;
        let mut incremental_claims = 0;
        let mut aggregate_flushes = 0;
        let mut epoch = 0;
        let mut buffers: Vec<Vec<BufferedClaims>> = (0..nodes.len())
            .map(|_| (0..workers).map(|_| BufferedClaims::default()).collect())
            .collect();
        // A failed shared write can poison a breaker before its failure completion arrives.
        // Admission statistics, publication and releases all belong to the same failure boundary.
        let coordinated =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<(), String> {
                loop {
                    if !failed && !idle.is_empty() {
                        let control = idle.iter().enumerate().find_map(|(at, &slot)| {
                            finish_waiting
                                .iter()
                                .position(|pending| pending[slot])
                                .map(|p| (at, slot, p))
                        });
                        if let Some((at, slot, p)) = control {
                            idle.swap_remove(at);
                            finish_waiting[p][slot] = false;
                            jobs[slot]
                                .send(Job::Finish(p))
                                .map_err(|_| "parallel worker disconnected")?;
                            active += 1;
                            continue;
                        }
                        if let Some((at, slot, p)) =
                            pending_flush(&idle, &buffers, epoch, 4 * workers, false)
                        {
                            idle.swap_remove(at);
                            jobs[slot]
                                .send(Job::Flush(p))
                                .map_err(|_| "parallel worker disconnected")?;
                            active += 1;
                            continue;
                        }
                        let next = (0..nodes.len())
                            .find_map(|p| {
                                dispatcher.try_begin_finish(p).then_some(Next::Finish {
                                    pipeline: PipelineId(p),
                                    consumed: None,
                                })
                            })
                            .unwrap_or_else(|| dispatcher.try_claim(Some(PipelineId(preferred))));
                        match next {
                            Next::Package(claim) => {
                                let p = claim.pipeline.0;
                                preferred = (p + 1) % nodes.len();
                                epoch += 1;
                                if nodes[p]
                                    .input
                                    .reads
                                    .iter()
                                    .any(|read| !nodes[*read].output.is_finished())
                                {
                                    incremental_claims += 1;
                                }
                                let slot = idle.pop().unwrap();
                                used[slot] = true;
                                claims[p] += 1;
                                jobs[slot]
                                    .send(Job::Consume(claim))
                                    .map_err(|_| "parallel worker disconnected")?;
                                active += 1;
                                continue;
                            }
                            Next::Finish { pipeline, .. } => {
                                assert!(
                                    finishing[pipeline.0].is_none(),
                                    "a pipeline finalizes once"
                                );
                                let count =
                                    owners[pipeline.0].iter().filter(|owner| **owner).count();
                                finishing[pipeline.0] = Some(count);
                                finish_waiting[pipeline.0] = owners[pipeline.0].clone();
                                if count == 0 && !complete_pipeline(dispatcher, nodes, pipeline.0) {
                                    failed = true;
                                    dispatcher.fail();
                                }
                                continue;
                            }
                            Next::Done => {
                                assert_eq!(active, 0);
                                break;
                            }
                            Next::Failed => failed = true,
                            Next::Wait(_) => {
                                if let Some((at, slot, p)) =
                                    pending_flush(&idle, &buffers, epoch, 4 * workers, true)
                                {
                                    idle.swap_remove(at);
                                    jobs[slot]
                                        .send(Job::Flush(p))
                                        .map_err(|_| "parallel worker disconnected")?;
                                    active += 1;
                                    continue;
                                }
                            }
                        }
                    }
                    if active == 0 {
                        if failed {
                            break;
                        } else {
                            dispatcher.fail();
                            return Err("parallel dispatcher stalled".into());
                        }
                    }
                    let done = done_rx
                        .recv()
                        .map_err(|_| "parallel completions disconnected")?;
                    active -= 1;
                    idle.push(done.slot);
                    if done.failed {
                        failed = true;
                        dispatcher.fail();
                    }
                    match done.outcome {
                        Outcome::Applied(claim) | Outcome::Buffered(claim) => {
                            let p = claim.pipeline.0;
                            if done.built {
                                instances[p] += 1;
                                owners[p][done.slot] = true;
                            }
                            if !failed {
                                if nodes[p].aggregate.is_some() {
                                    let buffer = &mut buffers[p][done.slot];
                                    if buffer.claims.is_empty() {
                                        buffer.since = epoch;
                                    }
                                    buffer.claims.push(claim);
                                } else {
                                    settle_claim(dispatcher, nodes, claim);
                                }
                            }
                        }
                        Outcome::Flushed(p) if !failed => {
                            aggregate_flushes += 1;
                            if nodes[p]
                                .aggregate
                                .as_ref()
                                .is_some_and(|agg| agg.inner_partition)
                                && let Some(guard) = nodes[p].output.completed_groups()
                            {
                                for &reader in &dispatcher.infos[p].readers {
                                    if nodes[reader].input.region_reads.contains(&p)
                                        && nodes[reader].reads_regions()
                                    {
                                        dispatcher.record_complete(reader, p, Some(&guard));
                                    }
                                }
                            }
                            for claim in buffers[p][done.slot].claims.drain(..) {
                                settle_claim(dispatcher, nodes, claim);
                            }
                        }
                        Outcome::Flushed(_) => {}
                        Outcome::Finished(p) if !failed => {
                            let left = finishing[p]
                                .as_mut()
                                .expect("a finish completion belongs to a finishing pipeline");
                            *left -= 1;
                            if *left == 0 && !complete_pipeline(dispatcher, nodes, p) {
                                failed = true;
                                dispatcher.fail();
                            }
                        }
                        Outcome::Finished(_) => {}
                    }
                }
                Ok(())
            }));
        if !matches!(coordinated, Ok(Ok(()))) {
            failed = true;
            dispatcher.fail();
        }

        drop(jobs);
        // Do not touch shared state while draining: another command may have poisoned its lock.
        while active > 0 {
            if done_rx.recv().is_err() {
                break;
            }
            active -= 1;
        }
        if failed {
            Err("parallel execution failed; applied output cannot be retried".into())
        } else {
            Ok(ExecutionStats {
                claims,
                instances,
                workers: used.into_iter().filter(|used| *used).count(),
                incremental_claims,
                aggregate_flushes,
            })
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::SubscribeContext;
    use crate::interpreter::dispatcher::run_program;
    use indoc::indoc;

    #[test]
    fn sole_preserves_a_collection_valued_element() {
        use crate::ccl::AggregateKind;
        use crate::interpreter::tile_operators::{Aggregate, Constant, TileOperator};
        use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Tiling};
        let inner_shape = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let inner = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            Predicate::True,
            Default::default(),
        );
        let input = Constant::collection(
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(inner),
                Predicate::True,
                Default::default(),
            ),
            Tiling::data_function(Extent::uint_range(1), inner_shape),
        );
        let mut op = Aggregate::new(Box::new(input), AggregateKind::Sole);
        let shape = op.tiling().clone();
        let mut native = op.subscribe(
            shape.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let expected = super::super::in_a_run(|| native.get(shape.universal_guard()));
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test("0"), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        program.outputs[0].op = Box::new(op);
        for workers in [1, 2, 4] {
            assert_eq!(
                run_program_parallel(&program, workers, 1).unwrap().main,
                expected
            );
        }
    }

    #[test]
    fn aggregate_compacts_rows_deleted_by_a_function_predicate() {
        use crate::ccl::AggregateKind;
        use crate::interpreter::tile_operators::{Aggregate, Constant, Filter, TileOperator};
        use crate::interpreter::{
            BaseType, ColumnValue, CurryLevel, Extent, FunctionDef, Predicate, Tiling, UnaryOpKind,
            Value,
        };
        let input = Constant::collection(
            Tile::data_function(
                ColumnValue::Bools(vec![false, true]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 100]))),
                Predicate::True,
                Default::default(),
            ),
            Tiling::data_function(
                Extent::Base(BaseType::Bool),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let predicate = Constant::new(
            Value::ComputableFunction(FunctionDef::UnaryOp(UnaryOpKind::Not)),
            Extent::Function {
                domain: Box::new(Extent::Base(BaseType::Bool)),
                codomain: Box::new(Extent::Base(BaseType::Bool)),
            },
        );
        let mut op = Aggregate::new(
            Box::new(Filter::new_at(
                Box::new(input),
                Box::new(predicate),
                CurryLevel::OUTERMOST,
            )),
            AggregateKind::Max,
        );
        let shape = op.tiling().clone();
        let mut native = op.subscribe(
            shape.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let expected = super::super::in_a_run(|| native.get(shape.universal_guard()));
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test("0"), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        program.outputs[0].op = Box::new(op);
        for workers in [1, 2, 4] {
            assert_eq!(
                run_program_parallel(&program, workers, 1).unwrap().main,
                expected
            );
        }
    }

    #[test]
    fn compiled_hash_group_aggregate_matches_serial() {
        // Noncontiguous groups force separate morsels and workers to contribute to the same key.
        let values = (0..64).map(|i| i.to_string()).collect::<Vec<_>>().join(",");
        let source = format!(r"max([max(g) for g in groupby([{values}], \x -> x - (x // 8) * 8)])");
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        let expected = run_program(&mut program, 1).unwrap().main.unwrap();
        for dop in [1, 2, 4] {
            let run = run_program_parallel(&program, dop, 2).unwrap();
            assert_eq!(run.main, expected);
            assert!(
                run.aggregate_claims > 8,
                "grouped inputs must use inner morsels"
            );
            assert!(run.aggregate_flushes < run.aggregate_claims);
        }
    }

    #[test]
    fn positional_lookup_streams_ready_function_regions_and_releases_them() {
        use crate::interpreter::tile_operators::{Constant, IterateExtent, MapResult, Memo};
        use crate::interpreter::{BaseType, ColumnValue, CurryLevel, Extent, Predicate, Tiling};
        let shape = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let expected = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2, 3]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![101, 102, 103, 104]))),
            Predicate::True,
            Default::default(),
        );
        let table = Memo::new(Box::new(Constant::collection(expected.clone(), shape)));
        let op = MapResult::new_at(
            Box::new(IterateExtent::new(Extent::uint_range(4))),
            Box::new(table),
            CurryLevel::new(1),
        );
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test("0"), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        program.outputs[0].op = Box::new(op);
        let run = run_program_parallel(&program, 1, 1).unwrap();
        assert!(
            run.incremental_claims > 0,
            "positional lookups can read ready rows without waiting for table closure"
        );
        assert_eq!(run.main, expected);
    }

    #[test]
    fn outermost_replacement_keeps_its_whole_input_across_output_morsels() {
        use crate::interpreter::tile_operators::{
            Constant, MapResultToConst, MapResultToConstMode, Memo,
        };
        use crate::interpreter::{BaseType, ColumnValue, CurryLevel, Extent, Predicate, Tiling};
        let collection = |values: Vec<i64>| {
            let tile = Tile::data_function(
                ColumnValue::UInts((0..values.len() as u64).collect()),
                Box::new(Tile::Scalar(ColumnValue::Ints(values.clone()))),
                Predicate::True,
                Default::default(),
            );
            let shape = Tiling::data_function(
                Extent::uint_range(values.len() as u64),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            );
            Constant::collection(tile, shape)
        };
        let input = Memo::new(Box::new(collection(vec![1, 2])));
        let op = MapResultToConst::new_at(
            Box::new(input),
            Box::new(collection(vec![10, 20, 30])),
            MapResultToConstMode::Replace,
            CurryLevel::OUTERMOST,
        );
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test("0"), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        program.outputs[0].op = Box::new(op);
        let run = run_program_parallel(&program, 1, 1).unwrap();
        assert_eq!(
            run.incremental_claims, 0,
            "a whole-collection input cannot be read at a ready prefix"
        );
        assert_eq!(
            run.main,
            Tile::data_function(
                ColumnValue::UInts(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::True,
                Default::default()
            )
        );
    }

    #[test]
    fn source_regions_remain_held_for_readers_with_unstarted_and_future_morsels() {
        use super::super::runtime::{RuntimeBase, constant};
        use crate::interpreter::tile_operators::OperatorBase;
        use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate};
        let shape = crate::interpreter::Tiling::data_function(
            Extent::uint_range(8),
            crate::interpreter::Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let tile = Tile::data_function(
            ColumnValue::UInts((0..8).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints((0..8).collect()))),
            Predicate::True,
            Default::default(),
        );
        let source = constant(
            tile,
            RuntimeBase::freeze(&OperatorBase::new(shape.clone())).unwrap(),
            None,
        );
        let held = source.sources[0].output.clone();
        let mut plan = RuntimeContext::default();
        plan.main(source.clone(), &shape);
        plan.main(source, &shape);
        let dispatcher = configure(&plan.pipelines, 4);
        let mut worker = WorkerContext::default();
        let Next::Package(first) = dispatcher.try_claim(Some(PipelineId(0))) else {
            panic!("first claim")
        };
        worker.consume(
            0,
            &plan.pipelines[0].input,
            first.guard.clone(),
            &plan.pipelines[0].output,
        );
        settle_claim(&dispatcher, &plan.pipelines, first);
        assert_eq!(
            held.snapshot().cell_count(),
            16,
            "the second reader has not started yet"
        );
        let Next::Package(second) = dispatcher.try_claim(Some(PipelineId(1))) else {
            panic!("second claim")
        };
        worker.consume(
            1,
            &plan.pipelines[1].input,
            second.guard.clone(),
            &plan.pipelines[1].output,
        );
        settle_claim(&dispatcher, &plan.pipelines, second);
        assert_eq!(
            held.snapshot().cell_count(),
            8,
            "the shared prefix can be reclaimed but future morsels remain"
        );
    }

    #[test]
    fn aggregate_workers_reuse_local_buffers_and_flush_before_finishing() {
        let rows = (0..32)
            .map(|row| format!("[{}, {}, {}]", row, row + 100, row + 3))
            .collect::<Vec<_>>()
            .join(",");
        for source in [
            format!(
                "max([x * 3 + 1 for x in [{}]])",
                (0..256)
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            format!("[max(row) for row in [{rows}]]"),
        ] {
            let mut cx = GlobalContext::default();
            let mut program =
                compile_program(&mut cx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
            let _operators = cx.take_operator_map();
            let expected = run_program(&mut program, 4).unwrap().main.unwrap();
            for dop in [1, 2, 4] {
                let run = run_program_parallel(&program, dop, 4).unwrap();
                assert_eq!(run.main, expected, "DOP{dop}: {source}");
                assert!(
                    run.aggregate_flushes > 1,
                    "buffers must flush during execution"
                );
                assert!(
                    run.aggregate_flushes < run.aggregate_claims,
                    "a local map must span several morsels"
                );
            }
        }
    }

    #[test]
    fn empty_scalar_extreme_fails_after_buffer_drain() {
        let mut cx = GlobalContext::default();
        let program = compile_program(
            &mut cx,
            &LoadedProgram::test(r#"min([x for x in ["a","b"] if x == "z"])"#),
            Box::new(|| {}),
        )
        .unwrap();
        let _operators = cx.take_operator_map();
        assert!(run_program_parallel(&program, 4, 1).is_err());
    }

    #[test]
    fn downstream_morsels_run_before_upstream_pipeline_finishes() {
        let values = (0..256)
            .map(|i| i.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = indoc::formatdoc! {"
            xs = [{values}]
            ys = [x * 3 for x in xs]
            a = [y + 1 for y in ys]
            b = [y * 2 for y in ys]
            (a1=a, a2=a, b1=b, b2=b)
        "};
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        let parallel = run_program_parallel(&program, 2, 8).unwrap();
        assert!(
            parallel.incremental_claims > 0,
            "downstream execution must not wait for upstream finish"
        );
        let serial = run_program(&mut program, 8).unwrap().main.unwrap();
        assert_eq!(parallel.main, serial);
    }

    #[test]
    fn native_chl_chains_match_serial() {
        for source in [
            "1 + 2",
            "[x * 2 + 1 for x in [1, 2, 3, 4, 5, 6]]",
            "max([x * 2 for x in [1, 2, 3, 4]])",
            indoc! {r#"
            xs = [1, 2, 3, 4, 5, 6]
            [x * 3 for x in xs if x > 2]
        "#},
        ] {
            let mut cx = GlobalContext::default();
            let mut program =
                compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
            let _operators = cx.take_operator_map();
            let parallel = run_program_parallel(&program, 4, 1)
                .unwrap_or_else(|error| panic!("{source}: {error}"));
            let serial = run_program(&mut program, 1).unwrap().main.unwrap();
            assert_eq!(parallel.main, serial, "{source}");
        }
    }
    #[test]
    fn finite_collection_claims_use_several_workers() {
        let mut cx = GlobalContext::default();
        let source = "[x * 2 for x in [1, 2, 3, 4, 5, 6, 7, 8]]";
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        let before = program.outputs[0]
            .producer
            .as_ref()
            .unwrap()
            .obsolete_guard()
            .clone();
        let parallel = run_program_parallel(&program, 4, 1).unwrap();
        assert!(parallel.claims >= 8);
        assert!(parallel.workers_used > 1);
        assert_eq!(
            program.outputs[0]
                .producer
                .as_ref()
                .unwrap()
                .obsolete_guard(),
            &before
        );
        assert_eq!(
            parallel.main,
            run_program(&mut program, 1).unwrap().main.unwrap()
        );
    }

    #[test]
    fn empty_and_nested_finite_outputs_match_serial() {
        for source in [
            "[x * 2 for x in [1, 2, 3] if x > 10]",
            "[[7, 8] for x in [1, 2, 3]]",
            "(answer=7, rows=[1, 2, 3])",
            "max([x * 2 for x in [1, 2, 3]])",
        ] {
            for workers in [1, 2, 4] {
                let mut cx = GlobalContext::default();
                let mut program =
                    compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {}))
                        .unwrap();
                let _operators = cx.take_operator_map();
                let result = run_program_parallel(&program, workers, 1)
                    .unwrap_or_else(|error| panic!("{source}: {error}"));
                assert_eq!(
                    result.main,
                    run_program(&mut program, 1).unwrap().main.unwrap(),
                    "{source}"
                );
            }
        }
    }

    #[test]
    fn invalid_configuration_refuses_before_execution() {
        let mut cx = GlobalContext::default();
        let program =
            compile_program(&mut cx, &LoadedProgram::test("1 + 2"), Box::new(|| {})).unwrap();
        assert!(run_program_parallel(&program, 0, 1).is_err());
        assert!(run_program_parallel(&program, 1, 0).is_err());
    }

    #[test]
    fn sum_refusal_preserves_the_serial_overflow_contract() {
        let mut cx = GlobalContext::default();
        let source = "sum([9223372036854775807, 0, 1, -1])";
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        assert!(
            run_program_parallel(&program, 4, 2)
                .err()
                .unwrap()
                .contains("Sum")
        );
        assert!(
            run_program(&mut program, 2)
                .unwrap()
                .main
                .unwrap()
                .is_terminal()
        );
    }

    #[test]
    fn unsupported_iteration_refuses_before_worker_start() {
        use crate::interpreter::tile_operators::{IterateExtent, TileOperator};
        use crate::interpreter::{BaseType, Extent};
        for extent in [
            Extent::Base(BaseType::Int),
            Extent::Record(
                [("bad".into(), Extent::Base(BaseType::UInt))]
                    .into_iter()
                    .collect(),
            ),
        ] {
            assert!(
                IterateExtent::new(extent)
                    .runtime_operator(&mut RuntimeContext::default())
                    .is_err()
            );
        }
    }

    #[test]
    fn live_sources_refuse_without_reading_or_releasing_the_retained_graph() {
        use crate::interpreter::{BaseType, Extent, test_source::TestDataSource};
        use std::{cell::RefCell, rc::Rc};
        let mut cx = GlobalContext::default();
        cx.register_source(Rc::new(RefCell::new(TestDataSource::new(
            "feed",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ))));
        let program = compile_program(
            &mut cx,
            &LoadedProgram::test("[x + 1 for x in feed()]"),
            Box::new(|| {}),
        )
        .unwrap();
        let _operators = cx.take_operator_map();
        let before = program.outputs[0]
            .producer
            .as_ref()
            .unwrap()
            .obsolete_guard()
            .clone();
        assert!(run_program_parallel(&program, 4, 1).is_err());
        assert_eq!(
            program.outputs[0]
                .producer
                .as_ref()
                .unwrap()
                .obsolete_guard(),
            &before
        );
    }

    #[test]
    fn a_poisoned_upstream_after_publication_returns_failure_and_joins() {
        use crate::ccl::AggregateKind;
        use crate::interpreter::tile_operators::{
            Aggregate, Constant, TileOperator, test_helpers::keys_between,
        };
        use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Tiling};
        let shape = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let op = Aggregate::new(
            Box::new(Constant::collection(
                Tile::data_function(
                    ColumnValue::UInts(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
                    Predicate::True,
                    Default::default(),
                ),
                shape,
            )),
            AggregateKind::Sole,
        );
        let mut context = RuntimeContext::default();
        let reader = op.runtime_operator(&mut context).unwrap();
        let main = context.main(reader, op.tiling());
        let upstream = &context.pipelines[0];
        let mut a = WorkerContext::default();
        let mut b = WorkerContext::default();
        let aggregate = upstream.aggregate.as_ref().unwrap();
        a.accumulate(0, &upstream.input, keys_between(0, 0), aggregate);
        b.accumulate(0, &upstream.input, keys_between(1, 1), aggregate);
        a.flush(0, &upstream.output);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                b.flush(0, &upstream.output);
            }))
            .is_err()
        );
        // Reproduce the race state: downstream work is already ready when a later write fails,
        // before the coordinator receives that write's failure completion.
        let mut dispatcher = Dispatcher::new(vec![vec![], vec![0]], 1);
        dispatcher.wait_for_inputs(PipelineId(main));
        dispatcher.queue_for(PipelineId(main), &op.tiling().universal_guard());
        dispatcher.record_complete(main, 0, None);
        assert!(execute(&dispatcher, &context.pipelines, 4).is_err());
    }

    #[test]
    fn native_worker_failure_joins_without_changing_retained_inputs() {
        let mut cx = GlobalContext::default();
        let program = compile_program(
            &mut cx,
            &LoadedProgram::test("[10 // x for x in [1, 0, 2, 3]]"),
            Box::new(|| {}),
        )
        .unwrap();
        let _operators = cx.take_operator_map();
        let before = program.outputs[0]
            .producer
            .as_ref()
            .unwrap()
            .obsolete_guard()
            .clone();
        assert!(run_program_parallel(&program, 4, 1).is_err());
        assert_eq!(
            program.outputs[0]
                .producer
                .as_ref()
                .unwrap()
                .obsolete_guard(),
            &before
        );
    }

    #[test]
    fn shared_boundaries_are_interned_and_native_chains_are_reused() {
        let values = (0..64)
            .map(|value| value.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let source = indoc::formatdoc! {r#"
            xs = [{values}]
            ys = [x * 3 for x in xs]
            a = [y + 1 for y in ys]
            b = [y * 2 for y in ys]
            (a1=a, a2=a, b1=b, b2=b)
        "#};
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        let mut context = RuntimeContext::default();
        let first = program.outputs[0]
            .op
            .runtime_operator(&mut context)
            .unwrap();
        let count = context.pipelines.len();
        let second = program.outputs[0]
            .op
            .runtime_operator(&mut context)
            .unwrap();
        assert_eq!(
            context.pipelines.len(),
            count,
            "exporting another reader preserves existing breaker identities"
        );
        assert_eq!(first.reads, second.reads);
        context.main(first, program.outputs[0].op.tiling());
        let mut readers = vec![0; context.pipelines.len()];
        for node in &context.pipelines {
            for &read in &node.input.reads {
                readers[read] += 1;
            }
        }
        assert!(
            readers.iter().any(|count| *count > 1),
            "the compiled branches read the same intermediate breaker"
        );
        let result = run_program_parallel(&program, 4, 1).unwrap();
        assert_eq!(result.pipeline_claims.len(), context.pipelines.len());
        assert!(result.pipeline_instances.iter().all(|count| *count <= 4));
        assert!(
            result
                .pipeline_claims
                .iter()
                .zip(&result.pipeline_instances)
                .any(|(claims, instances)| claims > instances),
            "several claims use the same owned native chain"
        );
        assert_eq!(
            result.main,
            run_program(&mut program, 1).unwrap().main.unwrap()
        );
    }

    #[test]
    fn repeated_claims_preserve_collection_operand_retention() {
        for workers in [1, 2, 4] {
            for morsel in [1, 3, usize::MAX] {
                let source = indoc! {r#"
                    xs = [1, 2, 3, 4, 5, 6, 7, 8]
                    ys = [x * 2 for x in xs]
                    [(value=y + 1, fixed=[10, 20]) for y in ys]
                "#};
                let mut cx = GlobalContext::default();
                let mut program =
                    compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {}))
                        .unwrap();
                let _operators = cx.take_operator_map();
                let result = run_program_parallel(&program, workers, morsel).unwrap();
                let serial = run_program(&mut program, morsel).unwrap().main.unwrap();
                assert_eq!(result.main.to_guard(), serial.to_guard());
                // A complete parent can make explicit nested completion statements redundant.
                assert_eq!(
                    crate::interpreter::tile_operators::materialize_collections(result.main),
                    crate::interpreter::tile_operators::materialize_collections(serial)
                );
            }
        }
    }

    #[test]
    fn private_inline_fan_out_keeps_an_unused_operand_lazy() {
        use crate::interpreter::tile_operators::{
            Constant, FanOut, MapResult, MapResultToConst, MapResultToConstMode, TileOperator,
        };
        use crate::interpreter::{
            ArithmeticKind, BaseType, BinOpKind, ColumnValue, CurryLevel, Extent, FunctionDef,
            Predicate, Value, tuple_field,
        };
        let integer = Extent::Base(BaseType::Int);
        let pair = Extent::Record(
            [
                (tuple_field(0), integer.clone()),
                (tuple_field(1), integer.clone()),
            ]
            .into_iter()
            .collect(),
        );
        let values = Value::Record(
            [
                (tuple_field(0), Value::Int(1)),
                (tuple_field(1), Value::Int(0)),
            ]
            .into_iter()
            .collect(),
        );
        let division = MapResult::new_at(
            Box::new(Constant::new(values, pair.clone())),
            Box::new(Constant::new(
                Value::ComputableFunction(FunctionDef::BinOp(BinOpKind::Arithmetic(
                    ArithmeticKind::FloorDiv,
                ))),
                Extent::Function {
                    domain: Box::new(pair),
                    codomain: Box::new(integer.clone()),
                },
            )),
            CurryLevel::OUTERMOST,
        );
        let fan = FanOut::new(Box::new(division));
        let driver_shape = crate::interpreter::Tiling::data_function(
            Extent::uint_range(2),
            crate::interpreter::Tiling::Scalar(integer),
        );
        let empty = Tile::data_function(
            ColumnValue::UInts(vec![]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![]))),
            Predicate::True,
            Default::default(),
        );
        let mut op = MapResultToConst::new_at(
            Box::new(Constant::collection(empty, driver_shape)),
            fan.slot(),
            MapResultToConstMode::Replace,
            CurryLevel::new(1),
        );
        let tiling = op.tiling().clone();
        let mut native = op.subscribe(
            tiling.universal_guard(),
            Box::new(|| {}),
            &mut SubscribeContext::new(),
        );
        let expected = super::super::in_a_run(|| native.get(tiling.universal_guard()));
        assert!(expected.is_empty() && expected.is_terminal());
        let mut context = RuntimeContext::default();
        let factory = op.runtime_operator(&mut context).unwrap();
        assert!(
            context.pipelines.is_empty(),
            "a private inline fan-out adds no eager execution stage"
        );
        let root = context.main(factory, &tiling);
        let dispatcher = configure(&context.pipelines, 1);
        execute(&dispatcher, &context.pipelines, 2).unwrap();
        assert_eq!(context.pipelines[root].output.snapshot(), expected);
    }

    #[test]
    fn an_empty_driver_does_not_force_an_undefined_group_body() {
        let source = "[max([y for y in [1] if y > 2]) for x in [1, 2] if x > 10]";
        let mut cx = GlobalContext::default();
        let mut program =
            compile_program(&mut cx, &LoadedProgram::test(source), Box::new(|| {})).unwrap();
        let _operators = cx.take_operator_map();
        let expected = run_program(&mut program, 1).unwrap().main.unwrap();
        let result = run_program_parallel(&program, 4, 1).unwrap();
        assert_eq!(result.main.to_guard(), expected.to_guard());
        assert_eq!(
            crate::interpreter::tile_operators::materialize_collections(result.main),
            crate::interpreter::tile_operators::materialize_collections(expected)
        );
    }

    #[test]
    #[ignore = "manual benchmark of actual compiled CHL"]
    fn benchmark_compiled_chl() {
        for (workload, rows) in [("pointwise", 2048), ("pointwise", 8192), ("groupby", 8192)] {
            let values = (0..rows)
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let source = if workload == "pointwise" {
                let mut expr = "x".to_string();
                for _ in 0..12 {
                    expr = format!("({expr} * 3 + 7)");
                }
                format!("[{expr} for x in [{values}]]")
            } else {
                format!(r"max([max(g) for g in groupby([{values}], \x -> x - (x // 32) * 32)])")
            };
            let mut cx = GlobalContext::default();
            let mut program =
                compile_program(&mut cx, &LoadedProgram::test(&source), Box::new(|| {})).unwrap();
            let _operators = cx.take_operator_map();
            let expected = run_program(&mut program, 256).unwrap().main.unwrap();
            for workers in [1, 2, 4] {
                // Warm-up is excluded; compilation and the serial parity control are also untimed.
                assert_eq!(
                    run_program_parallel(&program, workers, 256).unwrap().main,
                    expected
                );
                let mut samples = Vec::new();
                for sample in 0..5 {
                    let start = std::time::Instant::now();
                    let run = run_program_parallel(&program, workers, 256).unwrap();
                    samples.push(start.elapsed().as_secs_f64());
                    assert_eq!(run.main, expected);
                    if sample == 4 {
                        println!(
                            "compiled-chl workload={workload} rows={rows} workers={workers} claims={:?} instances={:?} incremental={} aggregate_claims={} flushes={}",
                            run.pipeline_claims,
                            run.pipeline_instances,
                            run.incremental_claims,
                            run.aggregate_claims,
                            run.aggregate_flushes,
                        );
                    }
                }
                samples.sort_by(f64::total_cmp);
                println!(
                    "compiled-chl workload={workload} rows={rows} workers={workers} median_s={:.6} samples_s={samples:?}",
                    samples[2]
                );
            }
        }
    }
}

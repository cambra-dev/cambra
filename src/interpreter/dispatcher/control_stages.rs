//! Coordinator consumption stages inside one transaction pipeline.
//!
//! Planning resolves the existing canonical breakers once. Execution reserves and acknowledges
//! their work on the run's dispatcher, while the enclosing store package stays outstanding.

use super::*;
use crate::interpreter::tile_operators::TileProducer;

#[doc(hidden)]
#[derive(Clone)]
pub struct ControlStage {
    pub(super) pipeline: PipelineId,
    pub(super) breaker: BreakerHandle,
    pub(super) input: InputId,
    previous: Option<PipelineId>,
}

pub(crate) struct ControlStages {
    stages: Vec<ControlStage>,
    writers: Vec<Vec<PipelineId>>,
    dispatcher: std::sync::Weak<Dispatcher>,
}

impl ControlStages {
    pub(crate) fn plan(writers: &mut [Box<dyn TileProducer>], dispatcher: &mut Dispatcher) -> Self {
        struct Plan<'a> {
            dispatcher: &'a mut Dispatcher,
            stages: Vec<ControlStage>,
            planned: HashMap<usize, Vec<PipelineId>>,
        }
        impl Plan<'_> {
            fn under(&mut self, producer: &mut dyn TileProducer) -> Vec<PipelineId> {
                if producer.recurrence_of().is_some()
                    || producer.store_read().is_some()
                    || producer
                        .base()
                        .placement
                        .as_ref()
                        .is_some_and(|at| at.get().is_some())
                {
                    return Vec::new();
                }
                let Some(handle) = producer.worker_breaker() else {
                    let mut below = Vec::new();
                    producer
                        .visit_input_producers_mut(&mut |_, input| below.extend(self.under(input)));
                    below.sort_by_key(|id| id.0);
                    below.dedup_by_key(|id| id.0);
                    return below;
                };
                let address = Arc::as_ptr(&handle).cast::<()>() as usize;
                if let Some(planned) = self.planned.get(&address) {
                    return planned.clone();
                }
                let mut breaker = handle.write().unwrap_or_else(PoisonError::into_inner);
                let mut previous = None;
                for index in 0..breaker.inputs() {
                    let input = InputId(index);
                    let role = breaker.consumption_role(input).map(str::to_owned);
                    let mut reads = Vec::new();
                    breaker.visit_input_producers_mut(&mut |name, producer| {
                        if role.as_ref().is_none_or(|role| role == name) {
                            reads.extend(self.under(producer));
                        }
                    });
                    reads.extend(previous);
                    reads.sort_by_key(|id| id.0);
                    reads.dedup_by_key(|id| id.0);
                    let pipeline = self.dispatcher.add_pipeline(reads);
                    self.dispatcher.order(pipeline);
                    if !self.dispatcher.is_source(pipeline) {
                        self.dispatcher.take_arrivals(pipeline);
                    }
                    // These stages belong to an outstanding parent claim. Only its consume
                    // phase may claim them; unrelated work and workers cannot enter the cycle.
                    self.dispatcher.hold_pipeline(pipeline, true);
                    self.stages.push(ControlStage {
                        pipeline,
                        breaker: handle.clone(),
                        input,
                        previous,
                    });
                    previous = Some(pipeline);
                }
                let roots: Vec<_> = previous.into_iter().collect();
                self.planned.insert(address, roots.clone());
                roots
            }
        }
        let mut plan = Plan {
            dispatcher,
            stages: Vec::new(),
            planned: HashMap::new(),
        };
        let writers = writers
            .iter_mut()
            .map(|writer| plan.under(&mut **writer))
            .collect();
        Self {
            stages: plan.stages,
            writers,
            dispatcher: std::sync::Weak::new(),
        }
    }

    pub(crate) fn handlers(&self) -> Vec<ControlStage> {
        self.stages.clone()
    }

    pub(crate) fn bind(&mut self, dispatcher: std::sync::Weak<Dispatcher>) {
        self.dispatcher = dispatcher;
    }

    pub(crate) fn consume(&self, writer: usize) {
        let dispatcher = self
            .dispatcher
            .upgrade()
            .expect("control stages belong to an active run");
        let mut visited = std::collections::HashSet::new();
        for &pipeline in &self.writers[writer] {
            self.consume_stage(&dispatcher, pipeline, &mut visited);
        }
    }

    fn consume_stage(
        &self,
        dispatcher: &Dispatcher,
        pipeline: PipelineId,
        visited: &mut std::collections::HashSet<usize>,
    ) {
        if !visited.insert(pipeline.0) {
            return;
        }
        let stage = self
            .stages
            .iter()
            .find(|stage| stage.pipeline.0 == pipeline.0)
            .expect("a planned control stage");
        // A later input can become enabled by consuming the preceding input: ExtractFinal's
        // default is demanded only after its source has finished without a value.
        if let Some(previous) = stage.previous {
            self.consume_stage(dispatcher, previous, visited);
        }
        if !stage
            .breaker
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .input_enabled(stage.input)
        {
            return;
        }
        for &read in &dispatcher.infos[pipeline.0].reads {
            self.consume_stage(dispatcher, PipelineId(read), visited);
        }
        let mut breaker = stage
            .breaker
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        let guard = breaker.input_tiling(stage.input).universal_guard();
        dispatcher.queue_round(pipeline, &guard);
        // The parent owns this held stage. Claim through the same queue/accounting machinery
        // without releasing its hold to the general claim loop.
        let package = dispatcher
            .claim_in(pipeline.0)
            .expect("a control stage queues one ready package");
        breaker.refresh_sources();
        breaker.consume(stage.input, package.guard.clone());
        dispatcher.acknowledge(package);
    }

    pub(crate) fn close(&self) {
        let dispatcher = self
            .dispatcher
            .upgrade()
            .expect("control stages belong to an active run");
        for stage in &self.stages {
            dispatcher.close(stage.pipeline);
            dispatcher.hold_pipeline(stage.pipeline, false);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{ProjectionSpy, two_levels_of_ints};
    use crate::interpreter::tile_operators::{MemoProducer, share_breaker};

    #[test]
    fn consumption_uses_shared_dispatcher_queues_and_reads_only_observe() {
        let (tile, tiling) = two_levels_of_ints();
        let (input, pulled, _) = ProjectionSpy::new(tile.clone(), tiling.clone());
        let mut writers = vec![share_breaker(MemoProducer::over(Box::new(input), &tiling))];
        let mut dispatcher = Dispatcher::new(Vec::new(), 1);
        let mut stages = ControlStages::plan(&mut writers, &mut dispatcher);
        let dispatcher = Arc::new(dispatcher);
        stages.bind(Arc::downgrade(&dispatcher));
        let pipeline = stages.stages[0].pipeline;

        assert_eq!(
            writers[0].get(tiling.universal_guard()),
            tiling.empty_tile()
        );
        assert!(pulled.read().unwrap().is_empty());
        in_a_run(|| stages.consume(0));
        assert_eq!(writers[0].get(tiling.universal_guard()), tile);
        assert_eq!(pulled.read().unwrap().len(), 1);
        assert_eq!(
            dispatcher.states[pipeline.0]
                .acknowledged
                .load(Ordering::SeqCst),
            1
        );
        assert_eq!(dispatcher.states[pipeline.0].outstanding(), 0);

        // A clean memo demands neither another package nor another upstream read.
        in_a_run(|| stages.consume(0));
        assert_eq!(pulled.read().unwrap().len(), 1);
        assert_eq!(
            dispatcher.states[pipeline.0]
                .acknowledged
                .load(Ordering::SeqCst),
            1
        );
        stages.close();
        let Next::Finish { pipeline, .. } = dispatcher.try_claim(None) else {
            panic!("a settled control stage finishes after closing");
        };
        dispatcher.finish(dispatcher.pushes(pipeline));
        assert!(matches!(dispatcher.try_claim(None), Next::Done));
    }
}

//! Reusable pipeline-local subscriptions of shared native operator definitions.
use super::*;
use crate::ccl::AggregateKind;

/// A breaker's independently executable input, selected by the production planner.
#[doc(hidden)]
#[derive(Clone)]
pub struct WorkerPlan {
    pub(crate) input: Arc<dyn TileOperator>,
    pub(crate) fold: WorkerFold,
}
#[derive(Clone)]
pub(crate) enum WorkerFold {
    Materialize,
    Scalar {
        kind: AggregateKind,
        output: Tiling,
    },
    Groups {
        operator: Arc<MapAggregate>,
        output: Tiling,
    },
}

/// A worker's contribution and the input now safe to release after integrating it.
#[doc(hidden)]
pub struct WorkerDelta {
    pub(crate) released: TileGuard,
    pub(crate) payload: WorkerPayload,
}
pub(crate) enum WorkerPayload {
    Tile(Tile),
    Scalar(Tile),
    Groups(MapAggregateState),
}

pub(crate) struct PipelineWorker {
    input: Box<dyn TileProducer>,
    fold: WorkerFold,
    groups: Option<MapAggregateState>,
    // Inline aliases are private to this subscription, including their lifetime owners.
    _context: SubscribeContext,
}
impl PipelineWorker {
    pub(crate) fn new(plan: &WorkerPlan, mut context: SubscribeContext) -> Self {
        context.worker = true;
        let input = plan.input.clone().subscribe(
            plan.input.tiling().universal_guard(),
            Box::new(|| {}),
            &mut context,
        );
        let groups = match &plan.fold {
            WorkerFold::Groups { operator, .. } => Some(MapAggregateState::new(operator.clone())),
            _ => None,
        };
        Self {
            input,
            fold: plan.fold.clone(),
            groups,
            _context: context,
        }
    }
    pub(crate) fn execute(&mut self, guards: impl Iterator<Item = TileGuard>) -> WorkerDelta {
        let mut released = self.input.tiling().empty_guard();
        let mut answer = None;
        for guard in guards {
            let mut tile = self.input.get(guard);
            let stated = tile.to_guard();
            released = released.union(&stated);
            self.input.release(stated);
            match &self.fold {
                WorkerFold::Materialize => match &mut answer {
                    None => answer = Some(tile),
                    Some(answer) => answer.merge(tile),
                },
                WorkerFold::Scalar { kind, output } => {
                    let accumulator = answer.get_or_insert_with(|| {
                        let Tiling::Aggregation { accumulator, .. } = output else {
                            unreachable!()
                        };
                        kind.initial_accumulator(accumulator)
                    });
                    tile.compact();
                    Aggregate::accumulate_tile(*kind, accumulator, tile);
                }
                WorkerFold::Groups { output, .. } => {
                    tile.compact();
                    self.groups.as_mut().unwrap().apply(&tile, output);
                }
            }
        }
        let payload = match self.fold {
            WorkerFold::Materialize => WorkerPayload::Tile(answer.expect("a batch has work")),
            WorkerFold::Scalar { .. } => WorkerPayload::Scalar(answer.expect("a batch has work")),
            WorkerFold::Groups { .. } => {
                WorkerPayload::Groups(self.groups.as_mut().unwrap().drain())
            }
        };
        WorkerDelta { released, payload }
    }
}

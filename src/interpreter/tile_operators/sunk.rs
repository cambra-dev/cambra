//! The placeholder a breaker pipeline of the inline driver holds where a chain would be.

use super::*;

/// What a pipeline whose breaker is in sink mode holds in place of a chain: the breaker owns the
/// pipeline's input chain, so the dispatcher runs the pipeline through the breaker and never pulls
/// a producer of this operator.
pub(crate) struct Sunk {
    base: OperatorBase,
}

impl Sunk {
    pub(crate) fn new(tiling: Tiling) -> Self {
        Self {
            base: OperatorBase::new(tiling),
        }
    }
}

impl TileOperator for Sunk {
    impl_operator_base!();

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

    fn visit_inputs_mut(&mut self, _visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {}

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        _consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(SunkProducer {
            base: ProducerBase::new(
                SunkProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
        })
    }
}

struct SunkProducer {
    base: ProducerBase,
}

impl TileProducer for SunkProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        panic!("a breaker pipeline in sink mode runs through its breaker, not through a chain")
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
}

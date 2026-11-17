use super::*;
use crate::interpreter::dispatcher::BreakerHandle;

/// Own one breaker subscription in a cell shared by its reader and the execution plan.
/// The breaker retains only a weak reference to its cell.
pub(crate) fn share_breaker(producer: impl BreakingProducer + 'static) -> Box<dyn TileProducer> {
    let tiling = producer.tiling().clone();
    let handle: BreakerHandle = Rc::new(RefCell::new(producer));
    handle.borrow_mut().base_mut().breaker_handle = Some(Rc::downgrade(&handle));
    Box::new(BreakerReader {
        base: ProducerBase::unowned(BreakerReader::alloc_id(), &tiling),
        handle,
    })
}

/// A downstream reader of a shared breaker. Tile validation and probes belong to the breaker.
struct BreakerReader {
    base: ProducerBase,
    // shared-state-ok: the producer subscription itself, with all values read through get.
    handle: BreakerHandle,
}

impl TileProducer for BreakerReader {
    impl_producer_base!();

    fn get(&mut self, guard: TileGuard) -> Tile {
        #[cfg(debug_assertions)]
        pull_levels::check_input_level(pull_levels::address_of(self), || self.name(), &guard);
        self.handle.borrow_mut().get(guard)
    }
    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        self.handle.borrow_mut().get(guard)
    }
    fn release_impl(&mut self, guard: TileGuard) {
        self.handle.borrow_mut().release(guard);
    }
    fn restates(&self) -> Restates {
        self.handle.borrow().restates()
    }
    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("breaker", &*self.handle.borrow());
    }
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        self.handle.borrow().inspect(opts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{TestTileProducer, two_levels_of_ints};

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "beneath what its `input_level` declares")]
    fn a_shared_reader_preserves_the_consumers_declared_input_level() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
        struct IncorrectRead {
            base: ProducerBase,
            input: Box<dyn TileProducer>,
        }
        impl TileProducer for IncorrectRead {
            impl_producer_base!();
            fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
                visit("input", &*self.input);
            }
            fn get_impl(&mut self, _: TileGuard) -> Tile {
                self.input
                    .get(
                        CurryLevel::new(1).wrap_guard(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::point(Value::UInt(0)),
                        ))),
                    )
            }
            fn release_impl(&mut self, _: TileGuard) {}
        }
        let (tile, tiling) = two_levels_of_ints();
        let input = ProjectionSpy::new(tile, tiling.clone()).0;
        let reader = share_breaker(MemoProducer::over(Box::new(input), &tiling));
        let mut consumer = IncorrectRead {
            base: ProducerBase::unowned(IncorrectRead::alloc_id(), &tiling),
            input: reader,
        };
        consumer.get(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::UInt(0)),
        )));
    }

    #[test]
    fn a_reader_and_the_plan_share_one_breaker_without_retaining_it_after_drop() {
        let (tile, tiling) = two_levels_of_ints();
        let producer = MemoProducer::over(
            Box::new(TestTileProducer::new(tile.clone(), tiling.clone())),
            &tiling,
        );
        let mut reader = share_breaker(producer);
        let mut weak = None;
        reader.visit_input_producers(&mut |_, producer| {
            weak = producer.base().breaker_handle.clone()
        });
        let weak = weak.expect("the concrete breaker retains its weak handle");
        let handle = weak.upgrade().expect("the reader owns its breaker");
        handle.borrow_mut().enter_consuming_mode();
        handle
            .borrow_mut()
            .consume_impl(InputId::ONLY, tiling.universal_guard());
        assert_eq!(reader.get(tiling.universal_guard()), tile);
        reader.release(tiling.universal_guard());
        assert!(handle.borrow().obsolete_guard().is_universal());
        drop(reader);
        assert!(
            weak.upgrade().is_some(),
            "the plan's handle keeps the subscription"
        );
        drop(handle);
        assert!(
            weak.upgrade().is_none(),
            "the subscription does not retain itself"
        );
    }
}

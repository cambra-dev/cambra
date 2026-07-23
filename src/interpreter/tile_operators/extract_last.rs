use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// ExtractLast / ExtractLastProducer
// ---------------------------------------------------------------------------

/// Extracts the last value from a changelog store's dense read (or any
/// `SealedFunction`) output, converting the accumulated `SealedFunction` tiling
/// back to a `Scalar` — the scalar-final read of a mutation loop's accumulator.
///
/// When the source becomes terminal but emits no values (the empty-source
/// case, e.g. `for i in []: x += 1`), the `default` operator's scalar value
/// is emitted instead.  This keeps mutation loops total: the post-loop
/// accumulator always has a defined value, equal to the loop's initial
/// value when the body never ran.
///
/// Used as the terminal stage of a loop: `ExtractLast(body.step, init)`.
pub struct ExtractLast {
    /// Operator producing the `SealedFunction` tiling to extract from.
    source: Box<dyn TileOperator>,
    /// Fallback scalar operator, pulled when `source` is terminal and
    /// emits zero values.  Must have a `Scalar` tiling whose extent
    /// matches `source`'s codomain extent.
    default: Box<dyn TileOperator>,
    /// Output tiling — the codomain of the source SealedFunction (always `Scalar`).
    tiling: Tiling,
}

impl ExtractLast {
    /// Construct a new `ExtractLast` wrapping `source`, with `default`
    /// as the fallback for the empty-source case.
    ///
    /// `source` must have a `SealedFunction` tiling and `default` must
    /// have a `Scalar` tiling with the same extent as `source`'s codomain.
    /// The output tiling becomes that scalar codomain.
    pub fn new(source: Box<dyn TileOperator>, default: Box<dyn TileOperator>) -> Self {
        let tiling = match source.tiling() {
            Tiling::SealedFunction { codomain, .. } => *codomain.clone(),
            other => panic!("ExtractLast source must have SealedFunction tiling, got {other}"),
        };
        debug_assert_eq!(
            default.tiling(),
            &tiling,
            "ExtractLast default tiling must match source codomain tiling",
        );
        Self {
            source,
            default,
            tiling,
        }
    }
}

impl TileOperator for ExtractLast {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("source", self.source.inspect(opts))
            .child("default", self.default.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Both branches need their own notification path: any progress on
        // either side may unblock the consumer (source becoming terminal,
        // default resolving its scalar value).  We give source the shared
        // consumer handle since it's the primary trigger; default uses a
        // no-op notifier because its readiness only matters at the moment
        // we discover an empty source — by then we're already in `get_impl`
        // and will pull it directly.
        let source_producer =
            self.source
                .subscribe(self.source.tiling().universal_guard(), consumer, scheduler);
        let default_producer = self.default.subscribe(
            self.default.tiling().universal_guard(),
            Box::new(|| {}),
            scheduler,
        );
        Box::new(ExtractLastProducer {
            base: ProducerBase::new(ExtractLastProducer::alloc_id(), &self.tiling),
            source: source_producer,
            default: default_producer,
            final_value: None,
            released: false,
        })
    }
}

struct ExtractLastProducer {
    base: ProducerBase,
    source: Box<dyn TileProducer>,
    /// Default-value producer, pulled when `source` becomes terminal
    /// and emits zero values.  Subscribed eagerly alongside `source`;
    /// `get` is deferred until we know we need it.
    default: Box<dyn TileProducer>,
    /// Cached final scalar value.  `None` until the source becomes
    /// terminal; `Some(_)` thereafter.  Every subsequent `get` returns
    /// this same value until the consumer releases us with a universal
    /// guard — which then sets [`Self::released`] and we go quiet.
    /// Same emit-until-released protocol as [`Constant`], so consumers
    /// that pull repeatedly (e.g. sibling `Last` projections off a
    /// shared multi-accumulator mutation-loop) see a stable value
    /// instead of an empty source after the first terminal pull.
    final_value: Option<Value>,
    /// Set to `true` by [`Self::release_impl`] on a universal release.
    /// Returns an empty scalar from every subsequent `get`.  The
    /// surrounding `Memo` normally issues this universal release as
    /// soon as it has merged the value into its own cache, so
    /// post-release emissions are rare in normal data flow.
    released: bool,
}

impl TileProducer for ExtractLastProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("source", self.source.inspect(opts))
            .child("default", self.default.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let empty = Tile::Scalar(ColumnValue::from_values(vec![], &self.tiling().extent()));
        if self.released {
            return empty;
        }
        // Already extracted: keep re-emitting the same scalar until we
        // are released.  Downstream `Memo` typically releases on first
        // sight of a non-empty tile, so this branch only stays active
        // across pulls when the consumer doesn't release immediately
        // (e.g. while a sibling pipeline is still converging).
        if let Some(v) = &self.final_value {
            return Tile::Scalar(ColumnValue::single(v.clone()));
        }
        let source_tiling = self.source.tiling().clone();
        let source_tile = self.source.get(source_tiling.universal_guard());
        if !source_tile.is_terminal() {
            // Source hasn't converged yet — emit an empty scalar of the
            // correct extent.  Our own tiling *is* the source's codomain
            // (always `Scalar`), so its extent gives us the value-space
            // directly without going through `Tiling::codomain` (which
            // would return `None` for a `Scalar`).
            //
            // Incremental release: we only ever need the *last* (highest-domain)
            // value, so every position below the highest one seen so far is dead —
            // release it. This is a promise never to re-request those positions;
            // the source decides what upstream storage that frees (for a changelog
            // dense read, the store prefix below the tail's carry source). Without
            // it, a never-terminating loop would pin the whole changelog until a
            // terminal that never comes.
            if let Tile::SealedFunction {
                domain, deleted, ..
            } = &source_tile
            {
                let max_pos = (0..domain.len())
                    .filter(|i| !deleted.contains(*i))
                    .filter_map(|i| match domain.index_at(i) {
                        Value::UInt(p) => Some(p),
                        _ => None,
                    })
                    .max();
                if let Some(max_pos) = max_pos
                    && max_pos >= 1
                {
                    self.source
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::LessThanEq(Value::UInt(max_pos - 1)),
                        )));
                }
            }
            return empty;
        }
        // Source is terminal — we've seen the final tile, so we'll
        // never need more data from it.  Release universally so
        // upstream chains (`FanOut`, `Memo`, mutation-loop body
        // sub-graphs) can in turn release their inputs and ultimately
        // reach the underlying data source.  Release is idempotent, so
        // a repeated call from the consumer's outer pull loop is fine.
        self.source.release(source_tiling.universal_guard());
        let Tile::SealedFunction {
            codomain, deleted, ..
        } = source_tile
        else {
            panic!("ExtractLast source must be a SealedFunction tile");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        let n = cv.len();
        // Try to extract the last non-deleted value from the source.
        // TODO don't assume sorting; we need to sort by the domain value instead.
        if let Some(last_idx) = (0..n).rev().find(|&i| !deleted.contains(i)) {
            let value = cv.index_at(last_idx);
            self.final_value = Some(value.clone());
            return Tile::Scalar(ColumnValue::single(value));
        }
        // Source is terminal *and* empty (the loop body ran zero
        // times).  Pull the default scalar and emit that instead, then
        // release the default so its upstream chain can release too.
        let default_tiling = self.default.tiling().clone();
        let default_tile = self.default.get(default_tiling.universal_guard());
        match scalar_tile_to_column_value(default_tile).as_single() {
            Some(value) => {
                self.default.release(default_tiling.universal_guard());
                self.final_value = Some(value.clone());
                Tile::Scalar(ColumnValue::single(value))
            }
            // Default hasn't converged yet — emit empty.  Outer pull
            // loop will retry; once default resolves, we'll cache it.
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.released = true;
            self.source.release(self.source.tiling().universal_guard());
            self.default
                .release(self.default.tiling().universal_guard());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;
    use crate::interpreter::tile_operators::{FunctionGuard, Predicate};
    use crate::interpreter::{BaseType, Extent};

    /// A non-terminal `SealedFunction` source with domain `[0, 1, 2]`, recording
    /// every domain-release watermark it receives. Never becomes terminal, so it
    /// exercises `ExtractLast`'s incremental (pre-terminal) release path.
    struct PartialSource {
        tiling: Tiling,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    struct PartialSourceProducer {
        base: ProducerBase,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    impl TileOperator for PartialSource {
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(PartialSourceProducer {
                base: ProducerBase::new(PartialSourceProducer::alloc_id(), &self.tiling),
                releases: self.releases.clone(),
            })
        }
    }

    impl TileProducer for PartialSourceProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::SealedFunction {
                domain: ColumnValue::from_uints(vec![0, 1, 2]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                domain_predicate: Predicate::False, // never terminal
                deleted: bit_set::BitSet::new(),
            }
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(
                w,
            )))) = &obsolete_guard
            {
                self.releases.borrow_mut().push(*w);
            }
        }
    }

    /// On a non-terminal pull, `ExtractLast` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_last_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Rc::new(RefCell::new(Vec::<usize>::new()));
        let source = PartialSource {
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(value_tiling.clone()),
            },
            releases: releases.clone(),
        };
        let default = Constant::new(Value::Int(0), Extent::Base(BaseType::Int));
        let mut op = ExtractLast::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Non-terminal source → ExtractLast emits empty but releases `[0, max)`.
        let tile = producer.get(producer.tiling().universal_guard());
        assert!(
            !tile.is_terminal(),
            "a non-terminal source stays non-terminal"
        );
        assert_eq!(
            releases.borrow().last().copied(),
            Some(1),
            "ExtractLast must release below the running max (positions 0, 1), keeping position 2"
        );
    }
}

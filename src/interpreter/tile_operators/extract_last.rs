use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// ExtractLast / ExtractLastProducer
// ---------------------------------------------------------------------------

/// Extracts the last value from a [`Recurse`] (or any `SealedFunction`) output,
/// converting the accumulated `SealedFunction` tiling back to a `Scalar`.
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

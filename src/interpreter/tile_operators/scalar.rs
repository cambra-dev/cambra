use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Extent, FunctionDef, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// A tile operator that always produces the same scalar value.
pub struct Constant {
    /// The fixed value emitted on every `get`.
    value: Value,
    /// The extent (type) of the produced value.
    pub extent: Extent,
    /// The tiling — always `Tiling::Scalar`.
    pub tiling: Tiling,
}

impl Constant {
    /// Create a new `Constant` operator for the given value.
    /// TODO `extent` should be `Extent::for_value(&value)`, but we don't have sufficient
    /// type derivation information for Value::ComputableFunction yet.
    pub fn new(value: Value, extent: Extent) -> Self {
        let tiling = Tiling::Scalar(extent.clone());
        Self {
            value,
            extent,
            tiling,
        }
    }
}

impl TileOperator for Constant {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node.annotate(format!("{}", self.value))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        consumer.notify();
        Box::new(ConstantProducer {
            base: ProducerBase::new(ConstantProducer::alloc_id(), &self.tiling),
            value: self.value.clone(),
            released: false,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        if let Value::ComputableFunction(func) = &self.value {
            match func {
                FunctionDef::RecordField(f) => Some(vec![TilePathStep::Record(f.clone())]),
                _ => None,
            }
        } else {
            None
        }
    }
}

struct ConstantProducer {
    base: ProducerBase,
    value: Value,
    released: bool,
}

impl TileProducer for ConstantProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node.annotate(format!("{}", self.value))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        if self.released {
            self.tiling().empty_tile()
        } else {
            Tile::Scalar(ColumnValue::single(self.value.clone()))
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.released = true;
        }
    }
}

/// Unwraps a `SealedFunction` with `domain = Units(1)` to produce its single codomain element.
///
/// The input must have a `SealedFunction` tiling with `domain = Extent::Units(1)`.
/// The output tiling is the codomain of that `SealedFunction`.
pub struct ToScalar {
    /// The `SealedFunction`-typed input to unwrap.
    input: Box<dyn TileOperator>,
    /// Output tiling: the codomain of the input's `SealedFunction` tiling.
    tiling: Tiling,
}

impl ToScalar {
    /// Construct a `ToScalar` operator.
    ///
    /// Panics if `input` does not have a `SealedFunction` tiling.
    /// The domain `Units(1)` constraint is checked at `get`-time.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().codomain().unwrap_or_else(|| {
            panic!(
                "ToScalar input had non-function tiling {:?}",
                input.tiling()
            )
        });
        Self { input, tiling }
    }
}

impl TileOperator for ToScalar {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(ToScalarProducer {
            base: ProducerBase::new(ToScalarProducer::alloc_id(), &self.tiling),
            input: input_producer,
        })
    }
}

/// Wraps each element of a payload input into a tagged [`Value::Union`] at a
/// fixed variant position, producing a `Scalar(Union)` tile — the runtime
/// realization of a scalar [`crate::ccl::TypedExprNode::VariantCtor`].
///
/// A lone `VariantCtor(tag, payload)` denotes a *singleton* variant value that
/// inference width-subtypes into its consumer's full tag set. By op-conversion
/// the node's type is that full [`Extent::Union`], so the constructor names a
/// fixed position `tag` within `variant_extents`: `variant_extents[tag]` is fed
/// by `input`, and every other variant contributes an empty column (no element
/// of this scalar carries their tag). The tag *names* are erased at this
/// boundary — a union value dispatches by position — so the wrapper only needs
/// the resolved index.
pub struct VariantWrap {
    /// The payload operator feeding `variants[tag]`.
    input: Box<dyn TileOperator>,
    /// The resolved 0-based position of the constructed tag in the full union.
    tag: usize,
    /// Per-variant extents of the full union; `input` feeds position `tag`.
    variant_extents: Vec<Extent>,
    /// Output tiling — always `Scalar(Union(variant_extents))`.
    tiling: Tiling,
}

impl VariantWrap {
    /// Construct a `VariantWrap` placing `input`'s scalar payload at variant
    /// position `tag` within a union of `variant_extents`.
    pub fn new(input: Box<dyn TileOperator>, tag: usize, variant_extents: Vec<Extent>) -> Self {
        assert!(
            tag < variant_extents.len(),
            "VariantWrap: tag index {tag} out of range for {} variants",
            variant_extents.len()
        );
        let tiling = Tiling::Scalar(Extent::Union(variant_extents.clone()));
        Self {
            input,
            tag,
            variant_extents,
            tiling,
        }
    }
}

impl TileOperator for VariantWrap {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("payload", self.input.inspect(opts))
            .annotate(format!("tag {}", self.tag))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(VariantWrapProducer {
            base: ProducerBase::new(VariantWrapProducer::alloc_id(), &self.tiling),
            input,
            tag: self.tag,
            variant_extents: self.variant_extents.clone(),
        })
    }
}

struct VariantWrapProducer {
    base: ProducerBase,
    /// The subscribed payload producer.
    input: Box<dyn TileProducer>,
    tag: usize,
    variant_extents: Vec<Extent>,
}

impl TileProducer for VariantWrapProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("payload", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let payload =
            scalar_tile_to_column_value(self.input.get(self.input.tiling().universal_guard()));
        let n = payload.len();
        // Every element of this scalar carries `tag`, so `variants[tag]` is the
        // whole payload column and the other variant columns are empty. Matches
        // the `ColumnValue::Union` invariant: `variants[j].len()` equals the
        // count of `j`s in `tags`.
        let variants: Vec<ColumnValue> = self
            .variant_extents
            .iter()
            .enumerate()
            .map(|(i, ext)| {
                if i == self.tag {
                    payload.clone()
                } else {
                    ColumnValue::from_values(Vec::new(), ext)
                }
            })
            .collect();
        Tile::Scalar(ColumnValue::Union {
            tags: vec![self.tag; n],
            variants,
        })
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

struct ToScalarProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
}

impl TileProducer for ToScalarProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain, codomain, ..
        } = input_result
        else {
            panic!("ToScalarProducer expected SealedFunction")
        };
        assert_eq!(domain, ColumnValue::Units(1));
        *codomain
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The input is always read in full (universal guard), so only a universal
        // release can be propagated meaningfully.
        if obsolete_guard.is_universal() {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

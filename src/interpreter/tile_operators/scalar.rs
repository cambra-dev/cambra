use bit_set::BitSet;

use super::*;
use crate::ccl::{FieldKey, TagMap};
use crate::interpreter::UnionArm;
use crate::{
    interpreter::{BaseType, ColumnValue, Consumer, Extent, FunctionDef, Scheduler, Value},
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
/// fixed tag — the sum-**introduction** primitive, the dual of [`VariantProject`]
/// and the runtime realization of a
/// [`crate::ccl::TypedExprNode::VariantCtor`].
///
/// A `VariantCtor(tag, payload)` names one arm of `variant_extents` (inference
/// width-subtypes the singleton into its consumer's full tag set, so by
/// op-conversion the node's type is that full [`Extent::Union`]): the `tag` arm
/// takes every row, and every other arm is present but empty.
///
/// **Two input shapes**, mirroring [`VariantProject`]:
/// - `Scalar(payload)` — a bare payload column (the scalar `VariantCtor`). The
///   output is `Scalar(Union)`.
/// - `SealedFunction { D ⇒ Scalar(payload) }` — a payload *stream* (a
///   `VariantCtor` inside a lambda body, ``λ p → `cᵢ(eᵢ(p))``, so it can sit as the
///   RHS of a `≫` and flat-merge with sibling arms). The wrap runs element-wise
///   over the codomain, **preserving the domain** `D`: the output is
///   `SealedFunction { D ⇒ Scalar(Union) }`.
pub struct VariantWrap {
    /// The payload operator feeding `variants[tag]`.
    input: Box<dyn TileOperator>,
    /// The tag being constructed.
    tag: FieldKey,
    /// Per-variant extents of the full union; `input` feeds the `tag` arm.
    variant_extents: TagMap<Extent>,
    /// Output tiling — `Scalar(Union)` for a scalar payload, or
    /// `SealedFunction { D ⇒ Scalar(Union) }` for a payload stream.
    tiling: Tiling,
}

impl VariantWrap {
    /// Construct a `VariantWrap` placing `input`'s payload at the `tag` arm of a
    /// union of `variant_extents`. The output tiling follows the
    /// payload's: a `Scalar` payload yields `Scalar(Union)`; a payload *stream*
    /// `SealedFunction { D ⇒ Scalar(_) }` yields `SealedFunction { D ⇒
    /// Scalar(Union) }` (the wrap is element-wise over the codomain).
    pub fn new(
        input: Box<dyn TileOperator>,
        tag: FieldKey,
        variant_extents: TagMap<Extent>,
    ) -> Self {
        assert!(
            variant_extents.get(&tag).is_some(),
            "VariantWrap: tag `{tag}` is not an arm of the union being constructed"
        );
        let union_ext = Extent::Union(variant_extents.clone());
        let tiling = match input.tiling() {
            Tiling::SealedFunction { domain, .. } => Tiling::SealedFunction {
                domain: domain.clone(),
                codomain: Box::new(Tiling::Scalar(union_ext)),
            },
            _ => Tiling::Scalar(union_ext),
        };
        Self {
            input,
            tag,
            variant_extents,
            tiling,
        }
    }
}

/// Wrap a dense `payload` column at the `tag` arm: that arm owns every row and
/// every other arm is present but empty — which is what keeps the column total
/// over `variant_extents`' tags, so a downstream merge or append has an arm to
/// pair with. The partition invariant (`rows` covering `0..n` exactly) is
/// re-checked here rather than assumed.
fn wrap_variant_column(
    payload: ColumnValue,
    tag: &FieldKey,
    variant_extents: &TagMap<Extent>,
) -> ColumnValue {
    let n = payload.len();
    let cv = ColumnValue::Union(variant_extents.map(|k, ext| {
        if k == tag {
            // The constructed tag owns every row.
            UnionArm::new((0..n).collect(), payload.clone())
        } else {
            UnionArm::empty_for(ext)
        }
    }));
    cv.debug_assert_union_invariants();
    cv
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
            tag: self.tag.clone(),
            variant_extents: self.variant_extents.clone(),
        })
    }
}

struct VariantWrapProducer {
    base: ProducerBase,
    /// The subscribed payload producer.
    input: Box<dyn TileProducer>,
    tag: FieldKey,
    variant_extents: TagMap<Extent>,
}

impl TileProducer for VariantWrapProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("payload", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        match self.input.get(self.input.tiling().universal_guard()) {
            // Scalar payload column → `Scalar(Union)` (the scalar `VariantCtor`).
            tile @ Tile::Scalar(_) | tile @ Tile::Record(_) => {
                let payload = scalar_tile_to_column_value(tile);
                Tile::Scalar(wrap_variant_column(
                    payload,
                    &self.tag,
                    &self.variant_extents,
                ))
            }
            // Payload *stream* → wrap the codomain element-wise, preserving the
            // domain `D`, so the constructor composes as `payload ≫ variant_wrap`.
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                let payload = scalar_tile_to_column_value(*codomain);
                Tile::SealedFunction {
                    domain,
                    codomain: Box::new(Tile::Scalar(wrap_variant_column(
                        payload,
                        &self.tag,
                        &self.variant_extents,
                    ))),
                    domain_predicate,
                    deleted,
                }
            }
            other => panic!("VariantWrap: unexpected payload tile {other:?}"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// The read-dual of [`VariantWrap`]: projects one arm out of a tagged-union
/// value stream, restricting to the sub-domain of positions that carry that tag.
///
/// This is the elimination primitive for a scrutinee-`Case` over a
/// [`crate::ccl::Type::Variant`] — the `variant_project(𝑐ᵢ)` step of
/// `match 𝑑 { 𝑐ᵢ(𝑤ᵢ) → 𝑒ᵢ }  ⤳  ⧺ᵢ ( 𝑑 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ) )`
/// (a `≫`-chain: `𝑑` is the eliminated scrutinee morphism, and the two elements
/// after it are functions of its output).
/// It is a *single* step, not a restrict followed by a projection — see below.
/// The output is a `SealedFunction { 𝑑 ⇒ P_𝑐ᵢ }`: arm `𝑐ᵢ`'s inner payload column,
/// keyed by the scrutinee positions that carried tag `𝑐ᵢ`.
///
/// **Two input shapes, both yielding a `SealedFunction` keyed by the scrutinee's
/// domain:**
/// - `Scalar(Union)` — a bare union column (the `VariantCtor`/`VariantWrap`
///   shape). The domain is *implicit* `0..N`, so the projected keys are the
///   `UInt` positions carrying the tag.
/// - `SealedFunction { D ⇒ Scalar(Union) }` — a union *stream* whose element
///   domain `D` is explicit (a variant field of a record stream, `x.f`). The
///   projected keys are the **actual `D` keys** at the tagged positions,
///   *not* synthetic positions — so the projected payload co-iterates by key
///   with the outer element `x` under a `zip`/`FanIn` (the outer-binder arm
///   `λ (x, wᵢ) → eᵢ`), which inner-joins on shared keys.
///
/// **Restrict and project are one operation here.** A [`ColumnValue::Union`] arm
/// stores its payloads densely *against the rows that carry them*
/// ([`UnionArm`]), so reading the arm **is** the tag restriction: the rows come
/// out as the projected keys and the payloads as the projected values, in one
/// step. There is no separate boolean `Restrict` and no tag-discriminating
/// `Predicate`.
///
/// A domain-level `Restrict` could not express this anyway: the tag lives in the
/// scrutinee's *codomain* (the union value), not its domain, and `Restrict`
/// consumes a boolean-producing operator over the domain.
///
/// **An absent arm projects empty, and is not an error.** The scrutinee may be a
/// width-subtype of what this projection was built for, in which case it simply
/// never carries this tag (see [`TagMap`], "Why keyed rather than positional").
/// The empty result is shaped by the arm's *declared* payload extent, which the
/// projection carries for exactly that reason: an absent arm offers no column to
/// take a shape from.
///
/// A downstream `map(λ wᵢ → eᵢ)` post-composes the arm body over the codomain,
/// and a **flat** [`UnionOperator`] re-totals the disjoint per-tag sub-domains
/// back to the full domain (the tags partition it exhaustively, so the union is
/// total by construction).
pub struct VariantProject {
    /// The scrutinee operator, producing a `Scalar(Union)` tile or a
    /// `SealedFunction { D ⇒ Scalar(Union) }` tile.
    input: Box<dyn TileOperator>,
    /// The tag to project.
    tag: FieldKey,
    /// The `tag` arm's declared payload extent — the output codomain, kept
    /// alongside the tiling so an empty result can be built at the right column
    /// shape without destructuring it back out.
    payload_extent: Extent,
    /// Output tiling — `SealedFunction { <scrutinee domain> ⇒ the `tag` arm }`.
    tiling: Tiling,
}

impl VariantProject {
    /// Construct a `VariantProject` reading arm `tag` out of the scrutinee's
    /// union. The projected sub-domain is keyed by the scrutinee's own domain: a
    /// bare `Scalar(Union)` scrutinee has the implicit `UInt` `0..N` domain,
    /// while a `SealedFunction { D ⇒ Scalar(Union) }` scrutinee keeps `D`. All
    /// arms of one `match` share the scrutinee's domain extent, so they
    /// flat-merge back to the full domain.
    /// `payload_extent` is the projected arm's extent, taken from the node's own
    /// type rather than looked up in the scrutinee's extent — because the
    /// scrutinee legitimately **may not carry this tag**. A scrutinee that is a
    /// width-subtype of what the `match` was written for simply never produces the
    /// tag, and the projection is empty; the operator still needs a codomain
    /// extent to describe that empty result, and only the type knows it.
    pub fn new(input: Box<dyn TileOperator>, tag: FieldKey, payload_extent: Extent) -> Self {
        let domain_extent = match input.tiling() {
            Tiling::Scalar(Extent::Union(_)) => Extent::Base(BaseType::UInt),
            Tiling::SealedFunction { domain, codomain } => match codomain.as_ref() {
                Tiling::Scalar(Extent::Union(_)) => domain.clone(),
                other => panic!(
                    "VariantProject: SealedFunction scrutinee must have a Scalar(Union) codomain, \
                     got {other:?}"
                ),
            },
            other => panic!("VariantProject: scrutinee must be a (Sealed)Union, got {other:?}"),
        };
        let tiling = Tiling::SealedFunction {
            domain: domain_extent,
            codomain: Box::new(Tiling::Scalar(payload_extent.clone())),
        };
        Self {
            input,
            tag,
            payload_extent,
            tiling,
        }
    }
}

impl TileOperator for VariantProject {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("scrutinee", self.input.inspect(opts))
            .annotate(format!("arm {}", self.tag))
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
        Box::new(VariantProjectProducer {
            base: ProducerBase::new(VariantProjectProducer::alloc_id(), &self.tiling),
            input,
            tag: self.tag.clone(),
            payload_extent: self.payload_extent.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        // Not identity: the output codomain is arm `tag`'s *payload*, unrelated to
        // the domain key (`d ⇒ variants[tag]`, not `d ⇒ d`). `Some([])` would
        // assert codomain == key and let a downstream predicate-pushdown consumer
        // push a codomain predicate onto the domain (the wrong axis). Like
        // `VariantWrap` (which also rewrites the codomain), it has no
        // domain↔codomain correlation to advertise.
        None
    }
}

struct VariantProjectProducer {
    base: ProducerBase,
    /// The subscribed scrutinee producer.
    input: Box<dyn TileProducer>,
    tag: FieldKey,
    /// The `tag` arm's declared payload extent, for shaping an empty result when
    /// the scrutinee carries no arm for `tag`. It has to be the *declared* one:
    /// an absent arm offers no column to take a shape from, and an empty column
    /// of the wrong kind (the untyped `Variants` catch-all rather than, say,
    /// `Ints`) fails the like-for-like concatenation a downstream merge does.
    payload_extent: Extent,
}

impl TileProducer for VariantProjectProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("scrutinee", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let tile = self.input.get(self.input.tiling().universal_guard());
        // The scrutinee's own domain keys (explicit for a union *stream*, so the
        // projected payload co-iterates by key with the outer element) and its
        // union codomain. A bare `Scalar(Union)` has an implicit `0..N` domain,
        // supplied below as the positions themselves.
        let (domain_col, domain_predicate, deleted, cv) = match tile {
            Tile::Scalar(cv) => (None, Predicate::True, BitSet::new(), cv),
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => (
                Some(domain),
                domain_predicate,
                deleted,
                scalar_tile_to_column_value(*codomain),
            ),
            other => panic!("VariantProject expects a (Sealed)Union input, got {other:?}"),
        };
        let ColumnValue::Union(arms) = cv else {
            panic!("VariantProject expects a Union codomain, got {cv:?}");
        };
        // The arm records exactly which rows carry this tag and, by position
        // within it, where each one's payload sits — so the projection is a
        // filter over the arm rather than a walk that reconstructs the
        // correspondence.
        //
        // **An absent arm is not an error**: the scrutinee is a width-subtype of
        // what this projection was built for, so it simply never carries this tag
        // and the restriction is empty. That is what makes variant width
        // subtyping free at runtime.
        let mut key_positions: Vec<usize> = Vec::new();
        let mut slots: Vec<usize> = Vec::new();
        if let Some(arm) = arms.get(&self.tag) {
            for (pos, slot) in arm.row_slots() {
                if !deleted.contains(pos) {
                    key_positions.push(pos);
                    slots.push(slot);
                }
            }
        }
        let out_domain = match domain_col {
            // Explicit stream domain: gather the actual keys at the kept positions.
            Some(d) => d.select_indices(key_positions.iter().copied(), key_positions.len()),
            // Implicit `Scalar(Union)` domain: the kept positions *are* the keys.
            None => ColumnValue::from_uints(key_positions),
        };
        let out_codomain = match arms.get(&self.tag) {
            Some(arm) => arm
                .values()
                .select_indices(slots.iter().copied(), slots.len()),
            // No arm for this tag: an empty codomain shaped by the arm's own
            // declared payload extent.
            None => ColumnValue::from_values(Vec::new(), &self.payload_extent),
        };
        Tile::SealedFunction {
            domain: out_domain,
            codomain: Box::new(Tile::Scalar(out_codomain)),
            domain_predicate,
            deleted: BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The scrutinee is always read in full (universal guard); only a
        // universal release propagates meaningfully.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::TestTileProducer;

    /// A test operator that yields one fixed tile, so a `VariantProject`/union
    /// chain can be `subscribe`d and driven end-to-end.
    struct FixedOp {
        tile: Tile,
        tiling: Tiling,
    }

    impl TileOperator for FixedOp {
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            mut consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            consumer.notify();
            Box::new(TestTileProducer::new(
                self.tile.clone(),
                self.tiling.clone(),
            ))
        }
    }

    /// A mixed `[commit(Int) | abort(Unit)]` stream: positions 0,2 carry
    /// `commit`, position 1 carries `abort`.
    fn commit_abort_scrutinee() -> FixedOp {
        let tile = Tile::Scalar(ColumnValue::positional_union(
            &[0, 1, 0],
            vec![ColumnValue::Ints(vec![10, 30]), ColumnValue::Units(1)],
        ));
        let tiling = Tiling::Scalar(Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Unit),
        ])));
        FixedOp { tile, tiling }
    }

    /// ``VariantProject(`commit)`` narrows to the tag-0 sub-domain (positions 0, 2)
    /// and reads back the arm-0 inner column `[10, 30]`.
    #[test]
    fn variant_project_commit_arm() {
        let scrut = Box::new(commit_abort_scrutinee());
        let mut op = VariantProject::new(scrut, FieldKey::Index(0), Extent::Base(BaseType::Int));
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let tile = producer.get(producer.tiling().universal_guard());

        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction, got {tile:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 2]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Ints(vec![10, 30])));
    }

    /// ``VariantProject(`abort)`` narrows to the tag-1 sub-domain (position 1) and
    /// reads back the (unit) arm-1 column.
    #[test]
    fn variant_project_abort_arm() {
        let scrut = Box::new(commit_abort_scrutinee());
        let mut op = VariantProject::new(scrut, FieldKey::Index(1), Extent::Base(BaseType::Unit));
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let tile = producer.get(producer.tiling().universal_guard());

        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected SealedFunction, got {tile:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![1]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Units(1)));
    }

    /// **A tag the scrutinee's value does not carry projects empty**, and is not
    /// an error — the runtime half of variant width subtyping, and the reason
    /// `VariantProject` can be built against a wider declared arm set than any
    /// particular column happens to inhabit.
    ///
    /// The tile here is a ``{`abort}``-only column under a
    /// ``{`abort | `commit{Int}}`` tiling: the exact shape a width-subtype value
    /// has. Projecting `` `commit `` must yield an empty sub-domain, shaped by
    /// the projection's *declared*
    /// codomain (`Int`) so a downstream flat merge still has a like-for-like
    /// column to concatenate — an arm that cannot occur contributes nothing
    /// rather than breaking the fan-out.
    #[test]
    fn variant_project_of_an_absent_arm_is_empty_not_an_error() {
        let commit = FieldKey::Name("commit".into());
        let abort = FieldKey::Name("abort".into());
        // The column carries *only* `abort` — `commit` is absent, not empty.
        let tile = Tile::Scalar(ColumnValue::Union(TagMap::from_arms(vec![(
            abort.clone(),
            UnionArm::new(vec![0], ColumnValue::Units(1)),
        )])));
        let tiling = Tiling::Scalar(Extent::Union(TagMap::from_arms(vec![
            (commit.clone(), Extent::Base(BaseType::Int)),
            (abort, Extent::Base(BaseType::Unit)),
        ])));

        let mut op = VariantProject::new(
            Box::new(FixedOp { tile, tiling }),
            commit,
            Extent::Base(BaseType::Int),
        );
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::SealedFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected SealedFunction, got {out:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![]));
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![])),
            "the empty codomain is shaped by the declared arm extent (Int), not \
             by the tag that happened to be present"
        );
    }

    /// The full fan-out: two `VariantProject` arms over the same scrutinee,
    /// flat-unioned, re-total the disjoint tag partitions back to the full
    /// `0..N` position range in order. Uses same-extent arms (both `Int`) so no
    /// per-arm `map` is needed to reconcile codomains — this isolates the
    /// restrict+project+union re-totaling mechanism.
    #[test]
    fn variant_elim_fanout_re_totals() {
        // tags [0,1,0,1] → commit(10), abort'(20), commit(30), abort'(40),
        // with both arms carrying Int so the union codomain is uniform.
        let tile = Tile::Scalar(ColumnValue::positional_union(
            &[0, 1, 0, 1],
            vec![
                ColumnValue::Ints(vec![10, 30]),
                ColumnValue::Ints(vec![20, 40]),
            ],
        ));
        let tiling = Tiling::Scalar(Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ])));

        let arm0: Box<dyn TileOperator> = Box::new(VariantProject::new(
            Box::new(FixedOp {
                tile: tile.clone(),
                tiling: tiling.clone(),
            }),
            FieldKey::Index(0),
            Extent::Base(BaseType::Int),
        ));
        let arm1: Box<dyn TileOperator> = Box::new(VariantProject::new(
            Box::new(FixedOp { tile, tiling }),
            FieldKey::Index(1),
            Extent::Base(BaseType::Int),
        ));

        let mut union = UnionOperator::new_flat(vec![arm0, arm1]);
        let mut sched = Scheduler::new();
        let mut producer = union.subscribe(
            union.tiling().universal_guard(),
            Box::new(|| {}),
            &mut sched,
        );
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::SealedFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected SealedFunction, got {out:?}");
        };
        // Disjoint tag partitions {0,2} and {1,3} re-total to the full 0..4 range,
        // sorted by position, with each position's arm value.
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1, 2, 3]));
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))
        );
    }

    /// **Outer-binder alignment.** Over a variant *stream* keyed by an explicit
    /// (non-`0..N`) domain, `VariantProject` keeps the real domain keys, so the
    /// projected payload co-iterates by key with the outer element under a
    /// `FanIn` (the `⟨id, x.f ≫ variant_project(cᵢ)⟩ ▷ zip` shape). This is the
    /// mechanism the outer-binder arm `λ (x, wᵢ) → eᵢ` relies on; the `FanIn`
    /// inner-joins on the shared keys, so the outer arm need not be pre-restricted.
    #[test]
    fn variant_project_stream_preserves_keys_and_zips() {
        // A union stream over arbitrary UInt keys [10, 11, 12]: commit(100),
        // abort, commit(120). The explicit keys (not 0..N) prove real-key
        // preservation.
        let union_stream_tile = Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![10, 11, 12]),
            codomain: Box::new(Tile::Scalar(ColumnValue::positional_union(
                &[0, 1, 0],
                vec![ColumnValue::Ints(vec![100, 120]), ColumnValue::Units(1)],
            ))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let union_stream_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Union(TagMap::from_positional(
                vec![Extent::Base(BaseType::Int), Extent::Base(BaseType::Unit)],
            )))),
        };

        // ``VariantProject(`commit)`` keeps the *actual* keys 10 and 12.
        let vp = VariantProject::new(
            Box::new(FixedOp {
                tile: union_stream_tile.clone(),
                tiling: union_stream_tiling.clone(),
            }),
            FieldKey::Index(0),
            Extent::Base(BaseType::Int),
        );
        assert_eq!(
            vp.tiling(),
            &Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            }
        );

        // The outer element stream (e.g. `x.time`) over the *same* keys.
        let outer_tile = Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![10, 11, 12]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let outer_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };

        // ⟨outer, x.decision ≫ variant_project(`commit)⟩ ▷ zip — the FanIn joins
        // the full outer stream with the tag-restricted payload on shared keys.
        let mut fan = FanIn::new(vec![
            Box::new(FixedOp {
                tile: outer_tile,
                tiling: outer_tiling,
            }),
            Box::new(vp),
        ]);
        let mut sched = Scheduler::new();
        let mut producer =
            fan.subscribe(fan.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::SealedFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected SealedFunction, got {out:?}");
        };
        // Only the commit keys survive the join, aligned by key: (time, payload)
        // = (1, 100) at key 10 and (3, 120) at key 12.
        assert_eq!(domain, ColumnValue::from_uints(vec![10, 12]));
        let Tile::Record(fields) = *codomain else {
            panic!("expected a Record codomain, got {codomain:?}");
        };
        assert_eq!(fields["_0"], Tile::Scalar(ColumnValue::Ints(vec![1, 3])));
        assert_eq!(
            fields["_1"],
            Tile::Scalar(ColumnValue::Ints(vec![100, 120]))
        );
    }
}

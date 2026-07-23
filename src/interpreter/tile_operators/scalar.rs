use bit_set::BitSet;

use super::*;
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
/// fixed variant position — the sum-**introduction** primitive, the dual of
/// [`VariantProject`] and the runtime realization of a
/// [`crate::ccl::TypedExprNode::VariantCtor`].
///
/// A `VariantCtor(tag, payload)` names a fixed position `tag` within
/// `variant_extents` (inference width-subtypes the singleton into its consumer's
/// full tag set, so by op-conversion the node's type is that full
/// [`Extent::Union`]): `variants[tag]` is fed by `input`, every other variant
/// contributes an empty column.
///
/// **Two input shapes**, mirroring [`VariantProject`]:
/// - `Scalar(payload)` — a bare payload column (the scalar `VariantCtor`). The
///   output is `Scalar(Union)`.
/// - `SealedFunction { D ⇒ Scalar(payload) }` — a payload *stream* (a
///   `VariantCtor` inside a lambda body, `λ p → .Cᵢ(eᵢ(p))`, so it can sit as the
///   RHS of a `≫` and flat-merge with sibling arms). The wrap runs element-wise
///   over the codomain, **preserving the domain** `D`: the output is
///   `SealedFunction { D ⇒ Scalar(Union) }`.
pub struct VariantWrap {
    /// The payload operator feeding `variants[tag]`.
    input: Box<dyn TileOperator>,
    /// The resolved 0-based position of the constructed tag in the full union.
    tag: usize,
    /// Per-variant extents of the full union; `input` feeds position `tag`.
    variant_extents: Vec<Extent>,
    /// Output tiling — `Scalar(Union)` for a scalar payload, or
    /// `SealedFunction { D ⇒ Scalar(Union) }` for a payload stream.
    tiling: Tiling,
}

impl VariantWrap {
    /// Construct a `VariantWrap` placing `input`'s payload at variant position
    /// `tag` within a union of `variant_extents`. The output tiling follows the
    /// payload's: a `Scalar` payload yields `Scalar(Union)`; a payload *stream*
    /// `SealedFunction { D ⇒ Scalar(_) }` yields `SealedFunction { D ⇒
    /// Scalar(Union) }` (the wrap is element-wise over the codomain).
    pub fn new(input: Box<dyn TileOperator>, tag: usize, variant_extents: Vec<Extent>) -> Self {
        assert!(
            tag < variant_extents.len(),
            "VariantWrap: tag index {tag} out of range for {} variants",
            variant_extents.len()
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

/// Wrap a dense `payload` column at variant position `tag`: `variants[tag]` is
/// the whole column, every other variant is empty. Every element carries `tag`
/// (`tags = [tag; n]`), matching the [`ColumnValue::Union`] invariant
/// (`variants[j].len()` equals the count of `j`s in `tags`).
fn wrap_variant_column(
    payload: ColumnValue,
    tag: usize,
    variant_extents: &[Extent],
) -> ColumnValue {
    let n = payload.len();
    let variants: Vec<ColumnValue> = variant_extents
        .iter()
        .enumerate()
        .map(|(i, ext)| {
            if i == tag {
                payload.clone()
            } else {
                ColumnValue::from_values(Vec::new(), ext)
            }
        })
        .collect();
    ColumnValue::Union {
        tags: vec![tag; n],
        variants,
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
        match self.input.get(self.input.tiling().universal_guard()) {
            // Scalar payload column → `Scalar(Union)` (the scalar `VariantCtor`).
            tile @ Tile::Scalar(_) | tile @ Tile::Record(_) => {
                let payload = scalar_tile_to_column_value(tile);
                Tile::Scalar(wrap_variant_column(
                    payload,
                    self.tag,
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
                        self.tag,
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
/// [`crate::ccl::Type::Variant`] — the `restrict(is_tag Cᵢ) ▷ project_arm(Cᵢ)`
/// step of `match 𝑑 { Cᵢ(𝑤ᵢ) → 𝑒ᵢ }  ⤳  ⧺ᵢ ( 𝑑 ▷ restrict(is_tag Cᵢ) ▷
/// project_arm(Cᵢ) ▷ (λ 𝑤ᵢ → 𝑒ᵢ) )`. The output is a
/// `SealedFunction { d ⇒ variants[i] }` — arm `i`'s inner payload column keyed
/// by the scrutinee position that carried tag `i`.
///
/// **Two input shapes, both yielding a `SealedFunction` keyed by the scrutinee's
/// domain:**
/// - `Scalar(Union)` — a bare union column (the `VariantCtor`/`VariantWrap`
///   shape). The domain is *implicit* `0..N`, so the projected keys are the
///   `UInt` positions carrying tag `i`.
/// - `SealedFunction { D ⇒ Scalar(Union) }` — a union *stream* whose element
///   domain `D` is explicit (a variant field of a record stream, `x.f`). The
///   projected keys are the **actual `D` keys** at the tag-`i` positions,
///   *not* synthetic positions — so the projected payload co-iterates by key
///   with the outer element `x` under a `zip`/`FanIn` (the outer-binder arm
///   `λ (x, wᵢ) → eᵢ`), which inner-joins on shared keys.
///
/// **Restrict and project are one operation here.** [`ColumnValue::Union`]
/// already stores each arm's payloads *densely* (`variants[i].len()` equals the
/// count of `i`s in `tags`, in appearance order), so reading `variants[i]`
/// *is* the tag-`i` restriction — there is no separate boolean `Restrict` step
/// and no `Predicate::Union`. A domain-level `Restrict` could not express this
/// anyway: the tag lives in the scrutinee's *codomain* (the union value), not
/// its domain, and `Restrict` consumes a boolean-producing operator over the
/// domain, not a tag `Predicate`.
///
/// A downstream `map(λ wᵢ → eᵢ)` post-composes the arm body over the codomain,
/// and a **flat** [`UnionOperator`] re-totals the disjoint per-tag sub-domains
/// back to the full domain (the tags partition it exhaustively, so the union is
/// total by construction).
pub struct VariantProject {
    /// The scrutinee operator, producing a `Scalar(Union)` tile or a
    /// `SealedFunction { D ⇒ Scalar(Union) }` tile.
    input: Box<dyn TileOperator>,
    /// The 0-based variant position to project.
    tag: usize,
    /// Output tiling — `SealedFunction { <scrutinee domain> ⇒ variants[tag] }`.
    tiling: Tiling,
}

impl VariantProject {
    /// Construct a `VariantProject` reading arm `tag` out of the scrutinee's
    /// union. The projected sub-domain is keyed by the scrutinee's own domain: a
    /// bare `Scalar(Union)` scrutinee has the implicit `UInt` `0..N` domain,
    /// while a `SealedFunction { D ⇒ Scalar(Union) }` scrutinee keeps `D`. All
    /// arms of one `match` share the scrutinee's domain extent, so they
    /// flat-merge back to the full domain.
    pub fn new(input: Box<dyn TileOperator>, tag: usize) -> Self {
        let (domain_extent, variant_extents) = match input.tiling() {
            Tiling::Scalar(Extent::Union(exts)) => (Extent::Base(BaseType::UInt), exts.clone()),
            Tiling::SealedFunction { domain, codomain } => match codomain.as_ref() {
                Tiling::Scalar(Extent::Union(exts)) => (domain.clone(), exts.clone()),
                other => panic!(
                    "VariantProject: SealedFunction scrutinee must have a Scalar(Union) codomain, \
                     got {other:?}"
                ),
            },
            other => panic!("VariantProject: scrutinee must be a (Sealed)Union, got {other:?}"),
        };
        assert!(
            tag < variant_extents.len(),
            "VariantProject: tag index {tag} out of range for {} variants",
            variant_extents.len()
        );
        let tiling = Tiling::SealedFunction {
            domain: domain_extent,
            codomain: Box::new(Tiling::Scalar(variant_extents[tag].clone())),
        };
        Self { input, tag, tiling }
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
            tag: self.tag,
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
    tag: usize,
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
        let ColumnValue::Union { tags, variants } = cv else {
            panic!("VariantProject expects a Union codomain, got {cv:?}");
        };
        // Walk positions once, keeping live tag-`i` positions. `key_positions`
        // indexes the scrutinee's domain column; `variant_locals` indexes the
        // dense `variants[tag]` column (its `k`-th element is the `k`-th
        // *appearance* of tag `i`, deleted or not — so we track the running
        // per-tag count independently of the `deleted` filter).
        let mut key_positions: Vec<usize> = Vec::new();
        let mut variant_locals: Vec<usize> = Vec::new();
        let mut variant_local = 0usize;
        for (pos, &t) in tags.iter().enumerate() {
            if t == self.tag {
                if !deleted.contains(pos) {
                    key_positions.push(pos);
                    variant_locals.push(variant_local);
                }
                variant_local += 1;
            }
        }
        let out_domain = match domain_col {
            // Explicit stream domain: gather the actual keys at the kept positions.
            Some(d) => d.select_indices(key_positions.iter().copied(), key_positions.len()),
            // Implicit `Scalar(Union)` domain: the kept positions *are* the keys.
            None => ColumnValue::from_uints(key_positions),
        };
        let out_codomain =
            variants[self.tag].select_indices(variant_locals.iter().copied(), variant_locals.len());
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

    /// A mixed `[Commit(Int) | Abort(Unit)]` stream: positions 0,2 carry
    /// `Commit`, position 1 carries `Abort`.
    fn commit_abort_scrutinee() -> FixedOp {
        let tile = Tile::Scalar(ColumnValue::Union {
            tags: vec![0, 1, 0],
            variants: vec![ColumnValue::Ints(vec![10, 30]), ColumnValue::Units(1)],
        });
        let tiling = Tiling::Scalar(Extent::Union(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Unit),
        ]));
        FixedOp { tile, tiling }
    }

    /// `VariantProject(Commit)` narrows to the tag-0 sub-domain (positions 0, 2)
    /// and reads back the arm-0 inner column `[10, 30]`.
    #[test]
    fn variant_project_commit_arm() {
        let scrut = Box::new(commit_abort_scrutinee());
        let mut op = VariantProject::new(scrut, 0);
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

    /// `VariantProject(Abort)` narrows to the tag-1 sub-domain (position 1) and
    /// reads back the (unit) arm-1 column.
    #[test]
    fn variant_project_abort_arm() {
        let scrut = Box::new(commit_abort_scrutinee());
        let mut op = VariantProject::new(scrut, 1);
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

    /// The full fan-out: two `VariantProject` arms over the same scrutinee,
    /// flat-unioned, re-total the disjoint tag partitions back to the full
    /// `0..N` position range in order. Uses same-extent arms (both `Int`) so no
    /// per-arm `map` is needed to reconcile codomains — this isolates the
    /// restrict+project+union re-totaling mechanism.
    #[test]
    fn variant_elim_fanout_re_totals() {
        // tags [0,1,0,1] → Commit(10), Abort'(20), Commit(30), Abort'(40),
        // with both arms carrying Int so the union codomain is uniform.
        let tile = Tile::Scalar(ColumnValue::Union {
            tags: vec![0, 1, 0, 1],
            variants: vec![
                ColumnValue::Ints(vec![10, 30]),
                ColumnValue::Ints(vec![20, 40]),
            ],
        });
        let tiling = Tiling::Scalar(Extent::Union(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ]));

        let arm0: Box<dyn TileOperator> = Box::new(VariantProject::new(
            Box::new(FixedOp {
                tile: tile.clone(),
                tiling: tiling.clone(),
            }),
            0,
        ));
        let arm1: Box<dyn TileOperator> =
            Box::new(VariantProject::new(Box::new(FixedOp { tile, tiling }), 1));

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
    /// `FanIn` (the `⟨x, x.f ▷ variant_project(i)⟩ ▷ zip` shape). This is the
    /// mechanism the outer-binder arm `λ (x, wᵢ) → eᵢ` relies on; the `FanIn`
    /// inner-joins on the shared keys, so the outer arm need not be pre-restricted.
    #[test]
    fn variant_project_stream_preserves_keys_and_zips() {
        // A union stream over arbitrary UInt keys [10, 11, 12]: Commit(100),
        // Abort, Commit(120). The explicit keys (not 0..N) prove real-key
        // preservation.
        let union_stream_tile = Tile::SealedFunction {
            domain: ColumnValue::from_uints(vec![10, 11, 12]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Union {
                tags: vec![0, 1, 0],
                variants: vec![ColumnValue::Ints(vec![100, 120]), ColumnValue::Units(1)],
            })),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let union_stream_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Union(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Unit),
            ]))),
        };

        // `VariantProject(Commit)` keeps the *actual* keys 10 and 12.
        let vp = VariantProject::new(
            Box::new(FixedOp {
                tile: union_stream_tile.clone(),
                tiling: union_stream_tiling.clone(),
            }),
            0,
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

        // ⟨outer, x.decision ▷ variant_project(Commit)⟩ ▷ zip — the FanIn joins
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
        // Only the Commit keys survive the join, aligned by key: (time, payload)
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

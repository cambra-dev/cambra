use bit_set::BitSet;

use super::*;
use crate::ccl::{FieldKey, TagMap};
use crate::interpreter::operator_graph::value;
use crate::interpreter::{UnionArm, UnionArmTile};
use crate::{
    interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FunctionDef, Predicate, Scheduler, Value,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// A tile operator that always produces the same tile.
///
/// A constant is a tile at whatever shape its tiling names: a scalar for a literal value,
/// and levels for a collection a literal writes out in full ([`Constant::collection`]).
pub struct Constant {
    /// The fixed tile emitted on every `get`.
    tile: Tile,
    base: OperatorBase,
}

impl Constant {
    /// A constant scalar.
    ///
    /// The extent is a *parameter* rather than derived from `value`, because a value
    /// does not determine one: a `Value::Union` knows the arm it occupies but not the
    /// arm set it belongs to, and a `Value::Function` binding table knows its own
    /// keys but not the domain they are drawn from. Every caller has the node's type,
    /// which does.
    pub fn new(value: Value, extent: Extent) -> Self {
        Self::of(
            Tile::Scalar(ColumnValue::single(value)),
            Tiling::Scalar(extent),
        )
    }

    /// A constant collection: the table a list literal denotes, emitted as the tile it is
    /// rather than as a column of materialized values something downstream has to open.
    pub fn collection(tile: Tile, tiling: Tiling) -> Self {
        Self::of(tile, tiling)
    }

    /// A constant **collection** over a bindings table: one level keyed by the table's own
    /// domain.
    ///
    /// Every operator downstream derives its tiling from its input's, so this is what
    /// decides whether the table or its outputs are what a consumer iterates. A
    /// comprehension over a loaded `Map` is the case that separates the two: at the scalar
    /// tiling of [`Constant::new`] it transforms the table as one value and the arithmetic
    /// under it meets a `Value::Function`, while here it transforms each output and keeps
    /// the domain.
    ///
    /// Which of the two a constant is cannot be read off the value, so the call site states
    /// it.
    pub fn from_bindings(bindings: Value, extent: Extent) -> Self {
        let (Value::Function(table), Extent::Function { domain, codomain }) = (&bindings, &extent)
        else {
            panic!(
                "a collection constant is a bindings table at a function extent, got {bindings:?} \
                 at {extent}"
            );
        };
        let (keys, values): (Vec<Value>, Vec<Value>) = table
            .iter()
            .map(|b| (b.input.clone(), b.output.clone()))
            .unzip();
        // `Predicate::True` because a constant is decided in full on the pull that yields it:
        // the bindings are the whole collection, so there is no key it has yet to answer.
        let tile = Tile::data_function(
            ColumnValue::from_values(keys, domain),
            Box::new(Tile::Scalar(ColumnValue::from_values(values, codomain))),
            Predicate::True,
            BitSet::new(),
        );
        let tiling = Tiling::DataFunction {
            domain: (**domain).clone(),
            codomain: Box::new(Tiling::Scalar((**codomain).clone())),
        };
        Self::of(tile, tiling)
    }

    fn of(tile: Tile, tiling: Tiling) -> Self {
        debug_assert!(
            tile.check_from(&tiling),
            "a constant's tile is its tiling's: {tile:?} vs {tiling}"
        );
        Self {
            tile,
            base: OperatorBase::new(tiling),
        }
    }

    /// The single value, where this constant is a scalar holding one.
    fn as_value(&self) -> Option<Value> {
        match &self.tile {
            Tile::Scalar(cv) if cv.len() == 1 => Some(cv.index_at(0)),
            _ => None,
        }
    }
}

impl TileOperator for Constant {
    impl_operator_base!();

    fn inspect_annotation(&self) -> Option<String> {
        Some(match self.as_value() {
            Some(v) => v.to_string(),
            None => format!("{}", self.tiling()),
        })
    }

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        consumer.notify();
        Box::new(ConstantProducer {
            base: ProducerBase::new(
                ConstantProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            tile: self.tile.clone(),
            released: false,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        match self.as_value() {
            Some(Value::ComputableFunction(FunctionDef::RecordField(f))) => {
                Some(vec![TilePathStep::Record(f)])
            }
            _ => None,
        }
    }
}

struct ConstantProducer {
    base: ProducerBase,
    tile: Tile,
    released: bool,
}

impl TileProducer for ConstantProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.tile.cell_count())
    }

    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node.annotate(format!("{}", self.tiling()))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // A collection's consumers release the keys they are done with, so the whole
        // table is not what a later pull may return. `release` has already accumulated
        // every guard into `obsolete_guard`, and returning released rows is what `get`'s
        // post-condition forbids.
        if self.tiling().is_data_function() {
            let mut tile = self.tile.clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            return tile;
        }
        if self.released {
            self.tiling().empty_tile()
        } else {
            self.tile.clone()
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A collection is released a key at a time, and `get_impl` filters against the
        // guard `release` accumulates, so there is nothing to record here. A scalar has one
        // position and no way to name part of it, which is what makes its only release the
        // whole of it.
        if self.tiling().is_data_function() {
            return;
        }
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
        }
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
/// - `DataFunction { D ⇒ Scalar(payload) }` — a payload *stream* (a
///   `VariantCtor` inside a lambda body, ``λ p → `cᵢ(eᵢ(p))``, so it can sit as the
///   RHS of a `≫` and flat-merge with sibling arms). The wrap runs element-wise
///   over the codomain, **preserving the domain** `D`: the output is
///   `DataFunction { D ⇒ Scalar(Union) }`.
pub struct VariantWrap {
    /// The payload operator feeding `variants[tag]`.
    input: Box<dyn TileOperator>,
    /// The tag being constructed.
    tag: FieldKey,
    /// Per-variant extents of the full union; `input` feeds the `tag` arm.
    variant_extents: TagMap<Extent>,
    /// The levels the payload stream sits under, which the wrap leaves standing. `0` for
    /// a bare payload value, `1` for an ordinary collection of them, and one more for each
    /// enclosing level a nested recurrence's body runs under.
    level: CurryLevel,
    /// Output tiling — the input's levels above `level`, over `Scalar(Union)`.
    base: OperatorBase,
}

impl VariantWrap {
    /// Construct a `VariantWrap` placing `input`'s payload at the `tag` arm of a union of
    /// `variant_extents`, at `level`: the levels above it stand, and the values at it become
    /// one union column. At level 0 a bare payload yields `Scalar(Union)`; at level 1 a
    /// payload stream `D ⤇ P` yields `D ⤇ Union`, wrapped element by element.
    pub fn new_at(
        input: Box<dyn TileOperator>,
        tag: FieldKey,
        variant_extents: TagMap<Extent>,
        level: CurryLevel,
    ) -> Self {
        assert!(
            variant_extents.get(&tag).is_some(),
            "VariantWrap: tag `{tag}` is not an arm of the union being constructed"
        );
        let union_ext = Extent::Union(variant_extents.clone());
        // The levels above `level` stand and the payload at it becomes the union: a column
        // where no payload holds a collection, and a union of arm tiles where one does, so a
        // collection payload stays the level it is. The depth is the caller's to state: a
        // collection of payloads and a payload that is itself a collection are both
        // `Tile::DataFunction`, so only the type separates them, and reading one level by hand
        // would drop the rest of a nested body's.
        //
        // The wrapped tag's arm keeps the payload's own tiling, which its producer chose (a
        // record of tiles, say, where the extent alone reads one column of records).
        let union_tiling = match Tiling::from_extent(&union_ext) {
            Tiling::Union(arms) => Tiling::Union(arms.map(|arm_tag, arm| match arm_tag == &tag {
                true => input.tiling().values_at(level).clone(),
                false => arm.clone(),
            })),
            column => column,
        };
        let tiling = with_values_at(input.tiling(), level, union_tiling);
        Self {
            base: OperatorBase::new(tiling),
            input,
            tag,
            variant_extents,
            level,
        }
    }
}

/// How many collection levels a guard reaches through before it names a value.
///
/// A guard shallower than an operator's level names only the levels that operator
/// leaves standing, so it crosses unchanged.
fn guard_depth(g: &TileGuard) -> usize {
    match g {
        TileGuard::Function(FunctionGuard::Codomain(inner)) => 1 + guard_depth(inner),
        TileGuard::Or(arms) => arms.iter().map(guard_depth).max().unwrap_or(0),
        _ => 0,
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
    impl_operator_base!();

    fn inspect_annotation(&self) -> Option<String> {
        Some(format!("tag {}", self.tag))
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
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
            base: ProducerBase::new(
                VariantWrapProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            level: self.level,
            input,
            tag: self.tag.clone(),
            variant_extents: self.variant_extents.clone(),
        })
    }
}

struct VariantWrapProducer {
    /// See [`VariantWrap::level`].
    level: CurryLevel,
    base: ProducerBase,
    /// The subscribed payload producer.
    input: Box<dyn TileProducer>,
    tag: FieldKey,
    variant_extents: TagMap<Extent>,
}

impl TileProducer for VariantWrapProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("payload", &*self.input);
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut tile = self.input.get(self.input.tiling().universal_guard());
        // Which of the two cases this is was decided at construction, from the input's
        // tiling, and is read back from the output's: a payload **stream** keeps its domain
        // and wraps element-wise (so the constructor composes as `payload ≫ variant_wrap`),
        // while a payload **value** becomes one union. The tile cannot say — a stream of
        // payloads and a payload that is itself a collection are both `Tile::DataFunction`,
        // and only the tiling separates them.
        // At the outermost level the payload is one row, the whole value, and once it is
        // released there is nothing left to wrap: a released collection reads as an empty one,
        // and wrapping that would deliver the row's tag again. What it stated complete stays
        // so, as a released collection's statement does.
        if self.level == CurryLevel::OUTERMOST
            && matches!(self.tiling(), Tiling::Union(_))
            && self.obsolete_guard().is_universal()
        {
            let mut released = self.tiling().empty_tile();
            released.map_level_predicates(&mut |_, _| Predicate::True);
            return released;
        }
        let slot = tile.values_at_mut(self.level);
        let payload = std::mem::replace(slot, Tile::Scalar(ColumnValue::Units(0)));
        *slot = match self.tiling().values_at(self.level) {
            // A collection payload stays a level, as a record field holding one does, so it
            // grows as it arrives rather than waiting to be whole.
            Tiling::Union(arm_tilings) => wrap_variant_tile(payload, &self.tag, arm_tilings),
            _ => Tile::Scalar(wrap_variant_column(
                scalar_tile_to_column_value(payload),
                &self.tag,
                &self.variant_extents,
            )),
        };
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Wrapping is element-wise and **domain-preserving**: output position `d`
        // is payload position `d`. So a domain release translates verbatim — and
        // it has to, since this producer re-emits whatever the payload answers
        // with. Swallowing it (as a whole-input reader may) would leave the
        // payload producing released positions and this operator handing them
        // back, which is the one thing a release forbids.
        let upstream_guard = match obsolete_guard {
            g if g.is_empty() => self.input.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            // Any guard that stays inside the **standing** levels names structure the
            // wrap left untouched, so it forwards verbatim. Only one that reaches the
            // wrapped level is shaped against the union extent rather than the payload's,
            // and nothing builds one of those.
            g if guard_depth(&g) < self.level.index() => g,
            // At the wrapped level a union guard names one region per tag, and the payload's
            // is the wrapped tag's: the other arms hold nothing this operator built.
            g if matches!(self.tiling().values_at(self.level), Tiling::Union(_)) => {
                onto_wrapped_arm(g, 0, self.level.index(), &self.tag, self.input.tiling())
            }
            g => todo!("Unimplemented guard in VariantWrapProducer: {g:?}"),
        };
        self.input.release(upstream_guard);
    }
}

/// `payload`, one tile over every row, as the arm `tag` of a union of `arm_tilings`: that arm
/// carries every row and every other arm none, so the union stays total over its tags.
fn wrap_variant_tile(payload: Tile, tag: &FieldKey, arm_tilings: &TagMap<Tiling>) -> Tile {
    let rows = payload.rows();
    let mut payload = Some(payload);
    Tile::Union(arm_tilings.map(|arm_tag, arm_tiling| match arm_tag == tag {
        true => {
            let payload = payload.take().expect("one arm is the wrapped tag");
            // A payload delivered as a materialized map opens into the level its arm holds.
            let tile = match (&payload, arm_tiling.holds_a_level()) {
                (Tile::Scalar(cells), true) => open_collections(cells, &arm_tiling.extent()),
                _ => payload,
            };
            UnionArmTile {
                rows: (0..rows).collect(),
                tile,
            }
        }
        false => UnionArmTile {
            rows: Vec::new(),
            tile: arm_tiling.empty_at_no_rows(),
        },
    }))
}

/// `guard`, standing `depth` levels down a wrap's output, restated over its payload: the
/// standing levels pass through, and at the wrapped level, `level`, the payload's region is the
/// union guard's arm for `tag`. `payload` is the input's tiling.
fn onto_wrapped_arm(
    guard: TileGuard,
    depth: usize,
    level: usize,
    tag: &FieldKey,
    payload: &Tiling,
) -> TileGuard {
    let at = || payload.values_at(CurryLevel::new(depth));
    match guard {
        g if g.is_empty() => at().empty_guard(),
        g if g.is_universal() => at().universal_guard(),
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| onto_wrapped_arm(arm, depth, level, tag, payload))
                .collect(),
        ),
        TileGuard::Union(arms) if depth == level => {
            arms.get(tag).cloned().unwrap_or_else(|| at().empty_guard())
        }
        TileGuard::Function(FunctionGuard::Codomain(inner)) if depth < level => {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(onto_wrapped_arm(
                *inner,
                depth + 1,
                level,
                tag,
                payload,
            ))))
        }
        g @ TileGuard::Function(FunctionGuard::Domain(_)) if depth < level => g,
        g => unreachable!(
            "a guard over a wrapped union is a chain down to it ending in a union guard, got \
             {g:?} at depth {depth} of {level}"
        ),
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
/// The output is a `DataFunction { 𝑑 ⇒ P_𝑐ᵢ }`: arm `𝑐ᵢ`'s inner payload column,
/// keyed by the scrutinee positions that carried tag `𝑐ᵢ`.
///
/// **Two input shapes, both yielding a `DataFunction` keyed by the scrutinee's
/// domain:**
/// - `Scalar(Union)` or `Union` — one variant value (the `VariantCtor`/`VariantWrap`
///   shape). Projecting it is applying the projection: the output is the payload,
///   with no key of its own, and holds nothing while the value carries another tag.
/// - `DataFunction { D ⇒ Scalar(Union) }` — a union *stream* whose element
///   domain `D` is explicit (a variant field of a record stream, `x.f`). The
///   projected keys are the **actual `D` keys** at the tagged positions,
///   *not* synthetic positions — so the projected payload co-iterates by key
///   with the outer element `x` under a `zip`/`Zip` (the outer-binder arm
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
    /// `DataFunction { D ⇒ Scalar(Union) }` tile.
    input: Box<dyn TileOperator>,
    /// The tag to project.
    tag: FieldKey,
    /// The `tag` arm's declared payload extent — the output codomain, kept
    /// alongside the tiling so an empty result can be built at the right column
    /// shape without destructuring it back out.
    payload_extent: Extent,
    /// The level the union sits at, and `None` for a bare `Scalar(Union)` scrutinee. The
    /// levels above it stand: a projection rebuilds its keys from the rows it keeps, which
    /// has no meaning across a grouping, so each enclosing row is projected on its own.
    level: Option<CurryLevel>,
    /// The projected level, empty — what an enclosing row the scrutinee has not reached
    /// contributes to the regrouped result. For a bare union, the payload while the union
    /// holds none: nothing delivered yet.
    empty_level: Option<Tile>,
    /// Output tiling — `DataFunction { <scrutinee domain> ⇒ the `tag` arm }`, or the arm
    /// itself for a bare union.
    base: OperatorBase,
}

impl VariantProject {
    /// Construct a `VariantProject` reading arm `tag` out of the scrutinee's
    /// union. The projected sub-domain is keyed by the scrutinee's own domain: a
    /// `DataFunction { D ⇒ Scalar(Union) }` scrutinee keeps `D`, and a bare union,
    /// one value, projects to its payload alone. All
    /// arms of one `match` share the scrutinee's domain extent, so they
    /// flat-merge back to the full domain.
    /// `payload_extent` is the projected arm's extent, taken from the node's own
    /// type rather than looked up in the scrutinee's extent — because the
    /// scrutinee legitimately **may not carry this tag**. A scrutinee that is a
    /// width-subtype of what the `match` was written for simply never produces the
    /// tag, and the projection is empty; the operator still needs a codomain
    /// extent to describe that empty result, and only the type knows it.
    pub fn new(input: Box<dyn TileOperator>, tag: FieldKey, payload_extent: Extent) -> Self {
        // The scrutinee is a union, either bare or as the values of a function of any
        // arity. The output keeps that arity and narrows only the codomain, so a union
        // per innermost element projects per innermost element.
        // The payload carries its own levels where it is a collection: an arm holding one is
        // handed to its consumer as a level rather than as a map in a cell
        // ([`Tiling::from_extent`]).
        //
        // An arm held as a tile keeps the tiling its union states for it, which is the shape its
        // payload's producer gave it.
        let arm_tiling = |union: &Tiling| match union {
            Tiling::Union(arms) => arms
                .get(&tag)
                .cloned()
                .unwrap_or_else(|| Tiling::from_extent(&payload_extent)),
            _ => Tiling::from_extent(&payload_extent),
        };
        let tiling = match input.tiling() {
            // A bare union is one value, and projecting it is applying the projection to it:
            // the output is the payload, with no position of its own.
            union @ (Tiling::Scalar(Extent::Union(_)) | Tiling::Union(_)) => arm_tiling(union),
            t @ Tiling::DataFunction { .. } => {
                assert!(
                    matches!(
                        t.deepest_values(),
                        Tiling::Scalar(Extent::Union(_)) | Tiling::Union(_)
                    ),
                    "VariantProject: a scrutinee's values must be a union, got {t:?}"
                );
                let arm = arm_tiling(t.deepest_values());
                with_values_at(t, CurryLevel::values_of(t), arm)
            }
            other => panic!("VariantProject: a scrutinee must be a union, got {other:?}"),
        };
        // The level the union sits at — the **scrutinee's** innermost, not the output's,
        // which a collection payload opens one deeper. The levels above it stand: a
        // projection rebuilds its own keys from the rows it keeps, which has no meaning
        // across a grouping, so a scrutinee under standing levels is projected one
        // enclosing row at a time ([`Tile::regroup_beneath`]).
        let level = CurryLevel::innermost_of(input.tiling());
        let empty_level = Some(match level {
            Some(l) => tiling.values_at(l).empty_at_no_rows(),
            None => tiling.empty_tile(),
        });
        Self {
            base: OperatorBase::new(tiling),
            input,
            tag,
            payload_extent,
            level,
            empty_level,
        }
    }
}

impl TileOperator for VariantProject {
    impl_operator_base!();

    fn inspect_annotation(&self) -> Option<String> {
        Some(format!("arm {}", self.tag))
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("scrutinee", &*self.input));
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
            base: ProducerBase::new(
                VariantProjectProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input,
            tag: self.tag.clone(),
            payload_extent: self.payload_extent.clone(),
            level: self.level,
            empty_level: self.empty_level.clone(),
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
    level: Option<CurryLevel>,
    empty_level: Option<Tile>,
}

impl VariantProjectProducer {
    /// The payloads of the scrutinee's rows carrying the tag.
    fn project(&mut self) -> Tile {
        let tile = self.input.get(self.input.tiling().universal_guard());
        // Under standing levels the projection runs one enclosing row at a time: its keys
        // are the rows it keeps, and which rows those are is a fact about one group.
        if let (Some(level), Some(empty)) = (self.level, self.empty_level.as_ref())
            && level != CurryLevel::OUTERMOST
        {
            return tile.regroup_beneath(level, empty.clone(), &mut |row| match tile
                .group_at(level, row)
            {
                Some(group) => self.project_level(group.into_owned()),
                None => empty.clone(),
            });
        }
        self.project_level(tile)
    }
}

impl TileProducer for VariantProjectProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("scrutinee", &*self.input);
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut out = self.project();
        // Part of a payload released names no part of the scrutinee, so the scrutinee keeps
        // the row and the payload is projected again on the next pull (`release_impl`);
        // what the consumer let go is taken back out here.
        if !self.base.obsolete_guard.is_empty() {
            out.remove_guarded(self.base.obsolete_guard.clone());
        }
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A **domain** release passes straight through. This producer's output domain is the
        // scrutinee's own keys at the rows carrying `tag` (`get_impl` gathers them from the
        // scrutinee's domain column), so a released output key names a scrutinee key
        // directly. The sibling projections of one `match` share that scrutinee through a
        // `FanOut`, whose `release_impl` intersects the branches' guards, so a key reaches
        // the scrutinee only once *every* arm is done with it — this arm releasing a key it
        // did not carry does not take it from the arm that did.
        //
        // A bare `Scalar(Union)` scrutinee has no domain column — `get_impl` supplies the
        // positions themselves — so it takes no domain guard and falls to the whole-tile
        // case below.
        if let TileGuard::Function(FunctionGuard::Domain(_)) = &obsolete_guard
            && matches!(self.input.tiling(), Tiling::DataFunction { .. })
        {
            self.input.release(obsolete_guard);
            return;
        }
        // Beneath standing levels the keys are the scrutinee's too, down to its values; the
        // payload beneath them is not the scrutinee's variant, so only a release of all of it
        // reaches the scrutinee's values.
        if matches!(self.input.tiling(), Tiling::DataFunction { .. })
            && !obsolete_guard.is_universal()
            && !obsolete_guard.is_empty()
        {
            let input = self.input.tiling();
            let guard = crate::interpreter::tiling::through_shared_levels(
                obsolete_guard,
                input.levels(),
                input,
            );
            self.input.release(guard);
            return;
        }
        // Part of a bare union's payload names no part of the union, which stays requested;
        // `get_impl` takes the released part back out of each projection.
        if self.level.is_none() && !obsolete_guard.is_universal() {
            return;
        }
        // Anything else is all-or-nothing: there is no other sub-region of the scrutinee
        // this producer could stop requesting.
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

impl VariantProjectProducer {
    /// One level of the scrutinee projected: the keys carrying `tag`, against their
    /// payloads.
    fn project_level(&self, tile: Tile) -> Tile {
        // The scrutinee's own domain keys (explicit for a union *stream*, so the
        // projected payload co-iterates by key with the outer element) and its
        // union codomain. A bare union is one value, at position 0.
        let (domain_col, domain_predicate, deleted, scrutinee) = match tile {
            Tile::Scalar(cv) => (
                None,
                Predicate::True,
                BitSet::new(),
                scrutinee_of(Tile::Scalar(cv)),
            ),
            // A bare union's positions are known once its row is.
            arms @ Tile::Union(_) => {
                let known = match arms.is_empty() {
                    true => Predicate::False,
                    false => Predicate::True,
                };
                (None, known, BitSet::new(), scrutinee_of(arms))
            }
            Tile::DataFunction {
                row_starts,
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                assert_eq!(
                    row_starts.len(),
                    1,
                    "VariantProject rebuilds its keys from the positions it keeps, which has \
                     no meaning inside a grouping"
                );
                (
                    Some(domain),
                    domain_predicate,
                    deleted,
                    scrutinee_of(*codomain),
                )
            }
            other => panic!("VariantProject expects a union input, got {other:?}"),
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
        let arm_rows: Vec<usize> = match &scrutinee {
            Scrutinee::Column(arms) => arms
                .get(&self.tag)
                .map_or_else(Vec::new, |arm| arm.rows().to_vec()),
            Scrutinee::Tiles(arms) => arms
                .get(&self.tag)
                .map_or_else(Vec::new, |arm| arm.rows.clone()),
        };
        let mut key_positions: Vec<usize> = Vec::new();
        let mut slots: Vec<usize> = Vec::new();
        for (slot, &pos) in arm_rows.iter().enumerate() {
            if !deleted.contains(pos) {
                key_positions.push(pos);
                slots.push(slot);
            }
        }
        // An opened payload, and an arm of a bare union, state their completeness over their
        // own rows, which the projection's keys now reach. An arm under a keyed scrutinee
        // already states it over those keys' paths.
        let stated_over_own_rows =
            domain_col.is_none() || matches!(scrutinee, Scrutinee::Column(_));
        let out_domain = match domain_col {
            // Explicit stream domain: gather the actual keys at the kept positions.
            Some(d) => d.select_indices(key_positions.iter().copied(), key_positions.len()),
            // Implicit `Scalar(Union)` domain: the kept positions *are* the keys.
            None => ColumnValue::uints_from_rows(key_positions),
        };
        // A payload held as a tile is handed out as the level it is. One held as a column is
        // opened the way every other materialized value is ([`Tiling::from_extent`]). An
        // absent arm's empty result is shaped by the arm's own declared payload extent.
        let out_codomain = match &scrutinee {
            Scrutinee::Tiles(arms) => match arms.get(&self.tag) {
                Some(arm) => arm.tile.select_rows(&slots),
                None => Tiling::from_extent(&self.payload_extent).empty_at_no_rows(),
            },
            Scrutinee::Column(arms) => {
                let values = match arms.get(&self.tag) {
                    Some(arm) => arm
                        .values()
                        .select_indices(slots.iter().copied(), slots.len()),
                    None => ColumnValue::from_values(Vec::new(), &self.payload_extent),
                };
                open_collections(&values, &self.payload_extent)
            }
        };
        // A bare union's payload is the value: its one row, or none while the scrutinee is
        // unknown. A scrutinee known to carry another tag holds no rows of a collection
        // payload, as a keyed scrutinee's projection holds none at a row of another tag, and
        // that is complete: a conditional's leg gated off is this projection, and the union
        // of the legs waits on each one.
        if self.level.is_none() {
            let known = match &scrutinee {
                Scrutinee::Column(arms) => arms.values().any(|arm| !arm.rows().is_empty()),
                Scrutinee::Tiles(arms) => arms.values().any(|arm| !arm.rows.is_empty()),
            };
            return match (slots.is_empty(), known, self.tiling()) {
                (false, _, _) => out_codomain,
                (true, true, Tiling::DataFunction { domain, codomain }) => Tile::data_function(
                    ColumnValue::from_values(Vec::new(), domain),
                    Box::new(codomain.empty_at_no_rows()),
                    Predicate::True,
                    BitSet::new(),
                ),
                (true, _, _) => self.empty_level.clone().expect("set for every scrutinee"),
            };
        }
        let mut out = Tile::data_function(
            out_domain,
            Box::new(out_codomain),
            domain_predicate,
            BitSet::new(),
        );
        if stated_over_own_rows {
            out.qualify_codomain_by_keys();
        }
        out
    }
}

/// A union scrutinee's arms, held as a column or, where a payload holds a collection, as tiles.
enum Scrutinee {
    Column(TagMap<UnionArm>),
    Tiles(TagMap<UnionArmTile>),
}

/// The union `values` holds, as a column or as arm tiles.
fn scrutinee_of(values: Tile) -> Scrutinee {
    match values {
        Tile::Union(arms) => Scrutinee::Tiles(arms),
        other => match scalar_tile_to_column_value(other) {
            ColumnValue::Union(arms) => Scrutinee::Column(arms),
            cv => panic!("VariantProject expects a Union codomain, got {cv:?}"),
        },
    }
}

/// ``variant_is(c) : Union({cᵢ: Pᵢ}) ⇒ Bool`` — whether each position of a union
/// stream carries the arm named `c`.
///
/// The **total** counterpart of [`VariantProject`]: same scrutinee, same domain
/// out as in, `true` on the rows the arm holds and `false` on the rest. Why a
/// total test rather than a projection is on
/// [`Builtin::VariantIs`](crate::ccl::Builtin::VariantIs).
///
/// **An absent arm is not an error** — it answers `false` everywhere, matching
/// [`VariantProject`]'s empty projection on a width-subtype scrutinee.
pub struct VariantIs {
    /// The scrutinee operator, producing a union (a column or arm tiles), bare or under
    /// any number of collection levels.
    input: Box<dyn TileOperator>,
    /// The tag to test for.
    tag: FieldKey,
    /// Identity and the output tiling — the scrutinee's, with `Bool` in place of the union:
    /// `Scalar(Bool)` or `DataFunction { <scrutinee domain> ⇒ … ⇒ Bool }`.
    base: OperatorBase,
}

impl VariantIs {
    /// Construct a `VariantIs` testing arm `tag` of the scrutinee's union. The output has the
    /// scrutinee's shape with `Bool` in place of the union: a test answers every position, so
    /// it keeps every key, and a scalar scrutinee gets a scalar answer. [`VariantProject`]
    /// differs on a collection payload, which it hands out with the payload's own keys.
    pub fn new(input: Box<dyn TileOperator>, tag: FieldKey) -> Self {
        let tiling = input.tiling();
        assert!(
            matches!(
                tiling.deepest_values(),
                Tiling::Scalar(Extent::Union(_)) | Tiling::Union(_)
            ),
            "VariantIs: a scrutinee's values must be a union, got {tiling:?}"
        );
        // The union sits under the levels the scrutinee stands at, however many: a match
        // inside a nested loop tests one value per innermost position.
        let tiling = change_tiling_result(tiling, |_| Tiling::Scalar(Extent::Base(BaseType::Bool)));
        Self {
            base: OperatorBase::new(tiling),
            input,
            tag,
        }
    }
}

impl TileOperator for VariantIs {
    impl_operator_base!();

    fn inspect_annotation(&self) -> Option<String> {
        Some(format!("is arm {}", self.tag))
    }

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("scrutinee", &*self.input));
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input = self.input.subscribe(intent_guard, consumer, scheduler);
        Box::new(VariantIsProducer {
            base: ProducerBase::new(
                VariantIsProducer::alloc_id(),
                &self.base.tiling,
                &self.base,
                scheduler,
            ),
            input,
            tag: self.tag.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        // The codomain is a tag test, unrelated to the domain key, so there is no
        // domain↔codomain correlation to advertise — as for `VariantProject`.
        None
    }
}

struct VariantIsProducer {
    base: ProducerBase,
    /// The subscribed scrutinee producer.
    input: Box<dyn TileProducer>,
    tag: FieldKey,
}

impl TileProducer for VariantIsProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("scrutinee", &*self.input);
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        // A test answers every position, so the scrutinee's levels, keys, groupings and
        // deletions stand as they are, and only its values change: each union value becomes
        // whether it carries the tag. A union of arm tiles holds levels inside its arms, but
        // its tags are one per row like a column's, which is all this reads.
        let mut tile = self.input.get(projection_guard);
        let values = tile.deepest_values_mut();
        let union = std::mem::replace(values, Tile::Scalar(ColumnValue::Bools(Vec::new())));
        // The arm records which rows carry the tag, so the test is a membership
        // check per position rather than a walk over the payloads.
        let (carried, rows): (BitSet, usize) = match scrutinee_of(union) {
            Scrutinee::Column(arms) => (
                arms.get(&self.tag)
                    .map(|arm| arm.row_slots().map(|(pos, _)| pos).collect())
                    .unwrap_or_default(),
                arms.values()
                    .flat_map(|a| a.rows())
                    .max()
                    .map_or(0, |m| m + 1),
            ),
            Scrutinee::Tiles(arms) => (
                arms.get(&self.tag)
                    .map(|arm| arm.rows.iter().copied().collect())
                    .unwrap_or_default(),
                arms.values().map(|a| a.rows.len()).sum(),
            ),
        };
        *values = Tile::Scalar(ColumnValue::Bools(
            (0..rows).map(|p| carried.contains(p)).collect(),
        ));
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Every key in is a key out, so a released region of the output names
        // exactly the region of the scrutinee that produced it. Only the values
        // differ in shape: an answer is one cell where the union it tests may be
        // arm tiles, and that cell's region is the whole of the union at its rows.
        let input = self.input.tiling();
        let upstream = match obsolete_guard {
            g if g.is_empty() => input.empty_guard(),
            g if g.is_universal() => input.universal_guard(),
            g => onto_tested_union(g, input),
        };
        self.input.release(upstream);
    }
}

/// `guard`, a region of a [`VariantIs`] output, restated over the union it tests (`input`):
/// the levels pass through, and an answer's cell is the whole union value at its row.
fn onto_tested_union(guard: TileGuard, input: &Tiling) -> TileGuard {
    match (guard, input) {
        (TileGuard::Or(arms), _) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| onto_tested_union(arm, input))
                .collect(),
        ),
        (g @ TileGuard::Function(FunctionGuard::Domain(_)), Tiling::DataFunction { .. }) => g,
        (
            TileGuard::Function(FunctionGuard::Codomain(inner)),
            Tiling::DataFunction { codomain, .. },
        ) => TileGuard::Function(FunctionGuard::Codomain(Box::new(onto_tested_union(
            *inner, codomain,
        )))),
        (TileGuard::Scalar(pred), union) => whole_at_rows(union, &pred),
        (g, t) => unreachable!("a VariantIs release is shaped as its output, got {g:?} over {t:?}"),
    }
}

/// The guard naming all of a value of `tiling` under the paths `pred` names a keyless leaf at.
fn whole_at_rows(tiling: &Tiling, pred: &Predicate) -> TileGuard {
    match tiling {
        Tiling::Scalar(_) => TileGuard::Scalar(pred.clone()),
        Tiling::Aggregation { .. } => TileGuard::Aggregation(pred.clone()),
        Tiling::DataFunction { .. } | Tiling::Store { .. } => {
            TileGuard::Function(FunctionGuard::Domain(pred.clone()))
        }
        Tiling::Record(fields) => TileGuard::Record(
            fields
                .iter()
                .map(|(name, field)| (name.clone(), whole_at_rows(field, pred)))
                .collect(),
        ),
        Tiling::Union(arms) => TileGuard::Union(arms.map(|_, arm| whole_at_rows(arm, pred))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};

    /// A test operator that yields one fixed tile, so a `VariantProject`/union
    /// chain can be `subscribe`d and driven end-to-end.
    struct FixedOp {
        tile: Tile,
        tiling: Tiling,
    }

    impl TileOperator for FixedOp {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
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

    /// A union column as a stream keyed `0..N`; a bare union is one value.
    fn union_stream(column: ColumnValue, extent: Extent) -> FixedOp {
        let keys = ColumnValue::from_uints((0..column.len() as u64).collect());
        FixedOp {
            tile: Tile::data_function(
                keys,
                Box::new(Tile::Scalar(column)),
                Predicate::True,
                BitSet::new(),
            ),
            tiling: Tiling::data_function(Extent::Base(BaseType::UInt), Tiling::Scalar(extent)),
        }
    }

    /// A mixed `[commit(Int) | abort(Unit)]` stream: positions 0,2 carry
    /// `commit`, position 1 carries `abort`.
    fn commit_abort_scrutinee() -> FixedOp {
        union_stream(
            ColumnValue::positional_union(
                &[0, 1, 0],
                vec![ColumnValue::Ints(vec![10, 30]), ColumnValue::Units(1)],
            ),
            Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Unit),
            ])),
        )
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

        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected Function, got {tile:?}");
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

        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected Function, got {tile:?}");
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
        let scrutinee = union_stream(
            ColumnValue::Union(TagMap::from_arms(vec![(
                abort.clone(),
                UnionArm::new(vec![0], ColumnValue::Units(1)),
            )])),
            Extent::Union(TagMap::from_arms(vec![
                (commit.clone(), Extent::Base(BaseType::Int)),
                (abort, Extent::Base(BaseType::Unit)),
            ])),
        );

        let mut op = VariantProject::new(Box::new(scrutinee), commit, Extent::Base(BaseType::Int));
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected Function, got {out:?}");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![]));
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![])),
            "the empty values are shaped by the declared arm extent (Int), not \
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
        let scrutinee = || {
            union_stream(
                ColumnValue::positional_union(
                    &[0, 1, 0, 1],
                    vec![
                        ColumnValue::Ints(vec![10, 30]),
                        ColumnValue::Ints(vec![20, 40]),
                    ],
                ),
                Extent::Union(TagMap::from_positional(vec![
                    Extent::Base(BaseType::Int),
                    Extent::Base(BaseType::Int),
                ])),
            )
        };

        let arm0: Box<dyn TileOperator> = Box::new(VariantProject::new(
            Box::new(scrutinee()),
            FieldKey::Index(0),
            Extent::Base(BaseType::Int),
        ));
        let arm1: Box<dyn TileOperator> = Box::new(VariantProject::new(
            Box::new(scrutinee()),
            FieldKey::Index(1),
            Extent::Base(BaseType::Int),
        ));

        let mut union = UnionOperator::new_flat(vec![arm0, arm1], Extent::Base(BaseType::Int));
        let mut sched = Scheduler::new();
        let mut producer = union.subscribe(
            union.tiling().universal_guard(),
            Box::new(|| {}),
            &mut sched,
        );
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected Function, got {out:?}");
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
    /// `Zip` (the `⟨id, x.f ≫ variant_project(cᵢ)⟩` shape). This is the
    /// mechanism the outer-binder arm `λ (x, wᵢ) → eᵢ` relies on; the `Zip`
    /// inner-joins on the shared keys, so the outer arm need not be pre-restricted.
    #[test]
    fn variant_project_stream_preserves_keys_and_zips() {
        // A union stream over arbitrary UInt keys [10, 11, 12]: commit(100),
        // abort, commit(120). The explicit keys (not 0..N) prove real-key
        // preservation.
        let union_stream_tile = Tile::data_function(
            ColumnValue::from_uints(vec![10, 11, 12]),
            Box::new(Tile::Scalar(ColumnValue::positional_union(
                &[0, 1, 0],
                vec![ColumnValue::Ints(vec![100, 120]), ColumnValue::Units(1)],
            ))),
            Predicate::True,
            BitSet::new(),
        );
        let union_stream_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Unit),
            ]))),
        );

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
            &Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int))
            )
        );

        // The outer element stream (e.g. `x.time`) over the *same* keys.
        let outer_tile = Tile::data_function(
            ColumnValue::from_uints(vec![10, 11, 12]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
            Predicate::True,
            BitSet::new(),
        );
        let outer_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );

        // ⟨outer, x.decision ≫ variant_project(`commit)⟩ — the Zip joins
        // the full outer collection with the tag-restricted payload on shared keys.
        let ops: Vec<Box<dyn TileOperator>> = vec![
            Box::new(FixedOp {
                tile: outer_tile,
                tiling: outer_tiling,
            }),
            Box::new(vp),
        ];
        let mut fan = Zip::new_at(
            (0..2).map(crate::interpreter::tuple_field).collect(),
            ops,
            CurryLevel::new(1),
        );
        let mut sched = Scheduler::new();
        let mut producer =
            fan.subscribe(fan.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let out = producer.get(producer.tiling().universal_guard());

        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected Function, got {out:?}");
        };
        // Only the commit keys survive the join, aligned by key: (time, payload)
        // = (1, 100) at key 10 and (3, 120) at key 12.
        assert_eq!(domain, ColumnValue::from_uints(vec![10, 12]));
        let Tile::Record { fields, .. } = *codomain else {
            panic!("expected Record values, got {codomain:?}");
        };
        assert_eq!(fields["_0"], Tile::Scalar(ColumnValue::Ints(vec![1, 3])));
        assert_eq!(
            fields["_1"],
            Tile::Scalar(ColumnValue::Ints(vec![100, 120]))
        );
    }

    /// A partial domain release forwards to the scrutinee. The projection is
    /// **key-preserving** — output key `d` is scrutinee key `d`, and no output
    /// key past `d` reads a scrutinee key at or below it — so "never asked for
    /// keys ≤ w again" says the same thing on both sides. It narrows the domain
    /// rather than preserving it, unlike
    /// [`variant_wrap_forwards_a_partial_domain_release_to_its_payload`], and
    /// that is what a *count*-based guard would turn on; a domain guard is over
    /// keys, so it forwards verbatim.
    ///
    /// This is what lets a projection sit inside an induction writer body, whose
    /// driver reclaims the prefix it has consumed.
    #[test]
    fn variant_project_forwards_a_partial_domain_release_to_its_scrutinee() {
        let scrut_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Union(TagMap::from_arms(vec![(
                FieldKey::Index(0),
                Extent::Base(BaseType::Int),
            )]))),
        );
        let (spy, released) = ReleaseSpy::new(
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Union(TagMap::from_arms(vec![(
                    FieldKey::Index(0),
                    UnionArm::new(vec![0, 1], ColumnValue::Ints(vec![10, 20])),
                )])))),
                Predicate::False,
                BitSet::new(),
            ),
            scrut_tiling.clone(),
        );
        let out_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let mut producer = VariantProjectProducer {
            base: ProducerBase::unowned(VariantProjectProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            tag: FieldKey::Index(0),
            payload_extent: Extent::Base(BaseType::Int),
            level: CurryLevel::innermost_of(&out_tiling),
            empty_level: None,
        };

        let prefix = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            Value::UInt(0),
        )));
        producer.release(prefix.clone());

        assert_eq!(
            released.borrow().as_slice(),
            &[prefix],
            "a domain release must reach the scrutinee unchanged"
        );
    }

    /// The variant `{`none | `some{0..2 ⤇ Int}}` over a collection payload.
    fn some_of_a_collection() -> TagMap<Extent> {
        TagMap::from_arms(vec![
            (FieldKey::Name("none".into()), Extent::Base(BaseType::Unit)),
            (
                FieldKey::Name("some".into()),
                Extent::Function {
                    domain: Box::new(Extent::uint_range(2)),
                    codomain: Box::new(Extent::Base(BaseType::Int)),
                },
            ),
        ])
    }

    /// The collection `{0 ↦ 10}`, its key `1` still to come.
    fn growing_collection() -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            Predicate::False,
            BitSet::new(),
        )
    }

    /// **A collection payload is wrapped as it arrives.** The arm holds it as a level, so the
    /// wrap delivers the keys it has with the tag, rather than holding the value back until the
    /// collection is complete as a materialized cell would have to.
    #[test]
    fn a_collection_payload_is_wrapped_while_it_grows() {
        let some = FieldKey::Name("some".into());
        let extents = some_of_a_collection();
        let payload_tiling = Tiling::from_extent(extents.get(&some).unwrap());
        let mut op = VariantWrap::new_at(
            Box::new(FixedOp {
                tile: growing_collection(),
                tiling: payload_tiling,
            }),
            some.clone(),
            extents,
            CurryLevel::OUTERMOST,
        );
        assert!(matches!(op.tiling(), Tiling::Union(_)), "{}", op.tiling());
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        let tile = producer.get(producer.tiling().universal_guard());
        let Some((tag, arm, slot)) = tile.union_arm_at(0) else {
            panic!("the wrapped value's one row carries a tag: {tile:?}");
        };
        assert_eq!((tag, slot), (&some, 0));
        assert_eq!(
            arm.tile,
            growing_collection(),
            "the payload is its own level, unopened"
        );
        assert!(!tile.is_terminal(), "the collection is still growing");
    }

    /// **A projection hands out an arm's level as it is.** Projecting one variant value is
    /// applying the projection to it, so the payload is the output, with nothing opened or
    /// copied.
    #[test]
    fn projecting_a_collection_arm_hands_out_its_level() {
        let some = FieldKey::Name("some".into());
        let extents = some_of_a_collection();
        let tiling = Tiling::from_extent(&Extent::Union(extents.clone()));
        let tile = Tile::Union(TagMap::from_arms(vec![
            (
                FieldKey::Name("none".into()),
                UnionArmTile {
                    rows: Vec::new(),
                    tile: Tile::Scalar(ColumnValue::Units(0)),
                },
            ),
            (
                some.clone(),
                UnionArmTile {
                    rows: vec![0],
                    tile: growing_collection(),
                },
            ),
        ]));
        let mut op = VariantProject::new(
            Box::new(FixedOp { tile, tiling }),
            some.clone(),
            extents.get(&some).unwrap().clone(),
        );
        let mut sched = Scheduler::new();
        let mut producer = op.subscribe(op.tiling().universal_guard(), Box::new(|| {}), &mut sched);
        assert_eq!(
            producer.get(producer.tiling().universal_guard()),
            growing_collection()
        );
    }

    /// `VariantWrap` is domain-preserving, so output position `d` is payload
    /// position `d` and a **partial** domain release forwards verbatim. This is
    /// the shape a writer's decision stream has: the commit operator releases
    /// one committed position at a time, and if the wrap swallows that, the
    /// payload keeps producing the released position and the wrap hands it back
    /// — the one thing a release forbids.
    #[test]
    fn variant_wrap_forwards_a_partial_domain_release_to_its_payload() {
        let commit = FieldKey::Name("commit".into());
        let payload_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, released) = ReleaseSpy::new(
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
                Predicate::False,
                BitSet::new(),
            ),
            payload_tiling.clone(),
        );
        let out_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Union(TagMap::from_arms(vec![(
                commit.clone(),
                Extent::Base(BaseType::Int),
            )]))),
        );
        let mut producer = VariantWrapProducer {
            level: CurryLevel::new(1),
            base: ProducerBase::unowned(VariantWrapProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            tag: commit.clone(),
            variant_extents: TagMap::from_arms(vec![(commit, Extent::Base(BaseType::Int))]),
        };

        let prefix = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(
            Value::UInt(0),
        )));
        producer.release(prefix.clone());

        assert_eq!(
            released.borrow().as_slice(),
            &[prefix],
            "a domain release must reach the payload unchanged, not be swallowed \
             as a whole-input read would"
        );
    }
}

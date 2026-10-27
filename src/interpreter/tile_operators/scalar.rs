use bit_set::BitSet;

use super::*;
use crate::ccl::{FieldKey, TagMap};
use crate::interpreter::UnionArm;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{
        BaseType, ColumnValue, Consumer, Extent, FunctionDef, Predicate, Projection, Scheduler,
        Value,
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

    /// A collection constant answers the keys the projection admits, which is how a worker reads
    /// the table a list literal denotes one morsel at a time. A scalar constant has one position,
    /// so its projection is the whole value or nothing.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        // A collection's consumers release the keys they are done with, so the whole
        // table is not what a later pull may return. `release` has already accumulated
        // every guard into `obsolete_guard`, and returning released rows is what `get`'s
        // post-condition forbids.
        let mut tile = if self.tiling().is_data_function() {
            let mut tile = self.tile.clone();
            tile.remove_guarded(self.obsolete_guard().clone());
            tile
        } else if self.released {
            self.tiling().empty_tile()
        } else {
            self.tile.clone()
        };
        tile.restrict_to(&projection, self.tiling());
        tile
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
        // The levels above `level` stand and the payload at it becomes one union column.
        // The depth is the caller's to state: a collection of payloads and a payload that is
        // itself a collection are both `Tile::DataFunction`, so only the type separates them,
        // and reading one level by hand would drop the rest of a nested body's.
        let tiling = with_values_at(input.tiling(), level, Tiling::Scalar(union_ext));
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

    /// A payload stream keeps its keys, so the input is pulled at the projection. A payload
    /// that is itself a collection becomes one union column with no keys, so it is read whole.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let input_guard = match self.tiling().is_data_function() {
            true => projection.guard(self.input.tiling()),
            false => self.input.tiling().universal_guard(),
        };
        let mut tile = self.input.get(input_guard);
        // **A collection payload is a value only once it is whole.** The arm holds it as one
        // materialized cell, which cannot grow, so a row's cell is emitted once that row's
        // collection is complete and not before. At the outermost level the payload is one
        // row, the whole input, and once it is released there is nothing left to wrap: a
        // released collection reads as an empty one, which is not the value it was.
        if self.input.tiling().values_at(self.level).holds_a_level() {
            match self.level.enclosing() {
                None if !tile.is_terminal() || self.obsolete_guard().is_universal() => {
                    return self.tiling().empty_tile();
                }
                None => {}
                Some(rows) => {
                    let complete = tile.completion_at(rows);
                    let paths = tile.paths_at(rows);
                    let whole = (0..paths.len())
                        .map(|key| complete.contains_path(&paths[key]))
                        .collect::<Vec<bool>>();
                    tile.values_at_mut(rows).retain_keys(&whole);
                }
            }
        }
        // Which of the two cases this is was decided at construction, from the input's
        // tiling, and is read back from the output's: a payload **stream** keeps its domain
        // and wraps element-wise (so the constructor composes as `payload ≫ variant_wrap`),
        // while a payload **value** becomes one union column. The tile cannot say — a stream
        // of payloads and a payload that is itself a collection are both `Tile::DataFunction`,
        // and only the tiling separates them.
        //
        // Either way the payload becomes a value: an arm rides its row as one, so a payload
        // carrying a collection materializes here rather than staying a level.
        let slot = tile.values_at_mut(self.level);
        let payload =
            materialize_collections(std::mem::replace(slot, Tile::Scalar(ColumnValue::Units(0))));
        *slot = Tile::Scalar(wrap_variant_column(
            payload,
            &self.tag,
            &self.variant_extents,
        ));
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
            g => todo!("Unimplemented guard in VariantWrapProducer: {g:?}"),
        };
        self.input.release(upstream_guard);
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
/// - `Scalar(Union)` — a bare union column (the `VariantCtor`/`VariantWrap`
///   shape). The domain is *implicit* `0..N`, so the projected keys are the
///   `UInt` positions carrying the tag.
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
    /// contributes to the regrouped result.
    empty_level: Option<Tile>,
    /// Output tiling — `DataFunction { <scrutinee domain> ⇒ the `tag` arm }`.
    base: OperatorBase,
}

impl VariantProject {
    /// Construct a `VariantProject` reading arm `tag` out of the scrutinee's
    /// union. The projected sub-domain is keyed by the scrutinee's own domain: a
    /// bare `Scalar(Union)` scrutinee has the implicit `UInt` `0..N` domain,
    /// while a `DataFunction { D ⇒ Scalar(Union) }` scrutinee keeps `D`. All
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
        // per innermost element projects per innermost element. The output is a function
        // either way: a bare union is keyed by the implicit `0..N` positions the tile
        // materializes.
        let tiling = match input.tiling() {
            Tiling::Scalar(Extent::Union(_)) => Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(payload_extent.clone()),
            ),
            t @ Tiling::DataFunction { .. } => {
                assert!(
                    matches!(t.deepest_values(), Tiling::Scalar(Extent::Union(_))),
                    "VariantProject: a scrutinee's values must be a Scalar(Union), got {t:?}"
                );
                // The payload carries its own levels where it is a collection: an arm
                // holding one is opened for its consumer rather than left a map in a cell
                // ([`Tiling::from_extent`]).
                change_tiling_result(t, |_| Tiling::from_extent(&payload_extent))
            }
            other => panic!("VariantProject: a scrutinee must be a union, got {other:?}"),
        };
        // The level the union sits at — the **scrutinee's** innermost, not the output's,
        // which a collection payload opens one deeper. The levels above it stand: a
        // projection rebuilds its own keys from the rows it keeps, which has no meaning
        // across a grouping, so a scrutinee under standing levels is projected one
        // enclosing row at a time ([`Tile::regroup_beneath`]).
        let level = CurryLevel::innermost_of(input.tiling());
        let empty_level = level.map(|l| tiling.values_at(l).empty_at_no_rows());
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
    fn project(&mut self, projection: &Projection) -> Tile {
        let input_guard = match self.input.tiling().is_data_function() {
            true => projection.guard(self.input.tiling()),
            false => self.input.tiling().universal_guard(),
        };
        let tile = self.input.get(input_guard);
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

    /// A union stream keeps its keys at the rows carrying the tag, so the scrutinee is pulled at
    /// the projection. A bare union has implicit positions for keys, so it is read whole and
    /// the positions cut after.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut out = self.project(&projection);
        // Part of a payload released names no part of the scrutinee, so the scrutinee keeps
        // the row and the payload is projected again on the next pull (`release_impl`);
        // what the consumer let go is taken back out here.
        if !self.base.obsolete_guard.is_empty() {
            out.remove_guarded(self.base.obsolete_guard.clone());
        }
        out.restrict_to(&projection, self.tiling());
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
        // positions themselves — so the scrutinee takes no domain guard. The positions a
        // consumer released are cut from the answer by the producer's own obsolete guard, and
        // the scrutinee is released whole by the whole-tile case below.
        if let TileGuard::Function(FunctionGuard::Domain(_)) = &obsolete_guard {
            if matches!(self.input.tiling(), Tiling::DataFunction { .. }) {
                self.input.release(obsolete_guard);
            }
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
        // union codomain. A bare `Scalar(Union)` has an implicit `0..N` domain,
        // supplied below as the positions themselves.
        let (domain_col, domain_predicate, deleted, cv) = match tile {
            Tile::Scalar(cv) => (None, Predicate::True, BitSet::new(), cv),
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
                    scalar_tile_to_column_value(*codomain),
                )
            }
            other => panic!("VariantProject expects a union input, got {other:?}"),
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
            None => ColumnValue::uints_from_rows(key_positions),
        };
        let out_codomain = match arms.get(&self.tag) {
            Some(arm) => arm
                .values()
                .select_indices(slots.iter().copied(), slots.len()),
            // No arm for this tag: an empty codomain shaped by the arm's own
            // declared payload extent.
            None => ColumnValue::from_values(Vec::new(), &self.payload_extent),
        };
        // The payload is opened the way every other materialized value is
        // ([`Tiling::from_extent`]), so a collection riding an arm reaches its consumer as
        // a level rather than as a map in a cell it would have to open first.
        let mut out = Tile::data_function(
            out_domain,
            Box::new(open_collections(&out_codomain, &self.payload_extent)),
            domain_predicate,
            BitSet::new(),
        );
        out.qualify_codomain_by_keys();
        out
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
    /// The scrutinee operator, producing a `Scalar(Union)` tile or a
    /// `DataFunction { D ⇒ Scalar(Union) }` tile.
    input: Box<dyn TileOperator>,
    /// The tag to test for.
    tag: FieldKey,
    /// Identity and the output tiling — `DataFunction { <scrutinee domain> ⇒ Bool }`.
    base: OperatorBase,
}

impl VariantIs {
    /// Construct a `VariantIs` testing arm `tag` of the scrutinee's union. The
    /// domain is the scrutinee's own, as [`VariantProject::new`] derives it; the
    /// codomain is `Bool` rather than the arm's payload, and unlike a projection
    /// every key of the domain is answered.
    pub fn new(input: Box<dyn TileOperator>, tag: FieldKey) -> Self {
        // As [`VariantProject::new`], with `Bool` in place of the arm's payload.
        let tiling = match input.tiling() {
            Tiling::Scalar(Extent::Union(_)) => Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Bool)),
            ),
            t @ Tiling::DataFunction { codomain, .. } => {
                assert!(
                    matches!(codomain.as_ref(), Tiling::Scalar(Extent::Union(_))),
                    "VariantIs: a scrutinee must have a Scalar(Union) codomain, got {codomain:?}"
                );
                change_tiling_result(t, |_| Tiling::Scalar(Extent::Base(BaseType::Bool)))
            }
            other => panic!("VariantIs: a scrutinee must be a union, got {other:?}"),
        };
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
        let tile = self.input.get(projection_guard);
        let (domain_col, domain_predicate, deleted, cv) = match tile {
            Tile::Scalar(cv) => (None, Predicate::True, BitSet::new(), cv),
            Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
                ..
            } => {
                assert!(
                    !codomain.holds_a_level(),
                    "VariantIs rebuilds its domain from the positions it keeps, which has \
                     no meaning above one level"
                );
                (
                    Some(domain),
                    domain_predicate,
                    deleted,
                    scalar_tile_to_column_value(*codomain),
                )
            }
            other => panic!("VariantIs expects a union input, got {other:?}"),
        };
        let ColumnValue::Union(arms) = cv else {
            panic!("VariantIs expects a Union codomain, got {cv:?}");
        };
        // The arm records which rows carry the tag, so the test is a membership
        // check per surviving position rather than a walk over the payloads.
        let carried: BitSet = arms
            .get(&self.tag)
            .map(|arm| arm.row_slots().map(|(pos, _)| pos).collect())
            .unwrap_or_default();
        let positions: Vec<usize> = match &domain_col {
            Some(d) => (0..d.len()).filter(|p| !deleted.contains(*p)).collect(),
            None => (0..arms
                .values()
                .flat_map(|a| a.rows())
                .max()
                .map_or(0, |m| m + 1))
                .filter(|p| !deleted.contains(*p))
                .collect(),
        };
        let answers: Vec<bool> = positions.iter().map(|p| carried.contains(*p)).collect();
        let out_domain = match domain_col {
            Some(d) => d.select_indices(positions.iter().copied(), positions.len()),
            None => ColumnValue::uints_from_rows(positions),
        };
        Tile::data_function(
            out_domain,
            Box::new(Tile::Scalar(ColumnValue::Bools(answers))),
            domain_predicate,
            BitSet::new(),
        )
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Every key in is a key out, so a released region of the output names
        // exactly the region of the scrutinee that produced it. `VariantProject`
        // forwards a release on the same key-preserving argument, over the
        // narrower domain it emits.
        self.input.release(obsolete_guard);
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

/// How a constant is pulled in a morsel pipeline: a list literal is the function operand of a
/// `map`, looked up at the keys of the morsel, and a function value is a scalar read whole.
#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        int_entries, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, FunctionGuard};

    /// The constant the literal `[10, 20, 30, 40, 50]` denotes.
    fn list_literal() -> ConstantProducer {
        let tile = ints_by_position(&[10, 20, 30, 40, 50], true);
        let tiling = Tiling::data_function(
            Extent::uint_range(5),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        ConstantProducer {
            base: ProducerBase::unowned(ConstantProducer::alloc_id(), &tiling),
            tile,
            released: false,
        }
    }

    fn completeness(tile: &Tile) -> Predicate {
        let Tile::DataFunction {
            domain_predicate, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        domain_predicate.clone()
    }

    /// Each worker's `map` looks the literal up at its own morsel, and the morsels together read
    /// the whole table.
    #[test]
    fn a_list_literal_answers_the_morsel_it_is_looked_up_at() {
        let mut literal = list_literal();
        let first = literal.get(keys_between(0, 2));
        assert_eq!(int_entries(&first), [(0, 10), (1, 20), (2, 30)]);
        let TileGuard::Function(FunctionGuard::Domain(morsel)) = keys_between(0, 2) else {
            unreachable!("a morsel is a domain guard")
        };
        assert_eq!(
            completeness(&first),
            morsel,
            "the literal is decided in full, so the morsel is complete"
        );
        literal.release(keys_between(0, 2));
        let rest = literal.get(keys_between(3, 9));
        assert_eq!(int_entries(&rest), [(3, 40), (4, 50)]);
    }

    /// A lookup of scattered keys, as a `map` over a stream whose positions are not contiguous
    /// makes it, answers those keys and no others.
    #[test]
    fn scattered_keys_are_answered_alone() {
        let mut literal = list_literal();
        let scattered = Predicate::point(Value::UInt(1)).union(&Predicate::point(Value::UInt(4)));
        let tile = literal.get(TileGuard::Function(FunctionGuard::Domain(scattered)));
        assert_eq!(int_entries(&tile), [(1, 20), (4, 50)]);
    }

    #[test]
    fn a_released_key_is_not_answered_inside_a_projection() {
        let mut literal = list_literal();
        literal.release(keys_between(1, 1));
        let tile = literal.get(keys_between(0, 2));
        assert_eq!(int_entries(&tile), [(0, 10), (2, 30)]);
    }

    /// A function value, such as the `x ↦ x + 1` a `map` applies, is one position: the whole value
    /// or nothing, and a release retires it.
    #[test]
    fn a_scalar_constant_is_read_whole_or_not_at_all() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut seven = ConstantProducer {
            base: ProducerBase::unowned(ConstantProducer::alloc_id(), &tiling),
            tile: Tile::Scalar(ColumnValue::Ints(vec![7])),
            released: false,
        };
        assert_eq!(
            seven.get(tiling.universal_guard()),
            Tile::Scalar(ColumnValue::Ints(vec![7]))
        );
        seven.release(tiling.universal_guard());
        assert_eq!(seven.get(tiling.empty_guard()), tiling.empty_tile());
    }

    #[test]
    fn nothing_names_no_keys_of_a_collection() {
        let mut literal = list_literal();
        let nothing = literal.tiling().empty_guard();
        assert_eq!(literal.get(nothing), literal.tiling().empty_tile());
    }
}

/// The variant operators as a `match` over a decision stream uses them: a payload stream is
/// wrapped into a tagged stream (`commit(w)`), the tags are tested (`variant_is`), and each arm
/// projects its payload back out (`variant_project`). A worker pulls each at one morsel.
#[cfg(test)]
mod variant_projection_tests {
    use super::*;
    use crate::ccl::TagMap;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, ints_by_position, keys_between,
    };

    const ROWS: u64 = 8;

    fn commit() -> FieldKey {
        FieldKey::Name("commit".into())
    }

    fn abort() -> FieldKey {
        FieldKey::Name("abort".into())
    }

    /// ``{`commit{Int} | `abort}``, the decision a writer's body answers.
    fn decision_extent() -> Extent {
        Extent::Union(TagMap::from_arms(vec![
            (commit(), Extent::Base(BaseType::Int)),
            (abort(), Extent::Base(BaseType::Unit)),
        ]))
    }

    fn decisions_tiling() -> Tiling {
        Tiling::data_function(Extent::uint_range(ROWS), Tiling::Scalar(decision_extent()))
    }

    /// `commit(w) for w in ws`: a payload stream wrapped as the `commit` arm.
    fn wrapped_payloads() -> (VariantWrapProducer, GuardLog) {
        let payload_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let values: Vec<i64> = (0..ROWS as i64).map(|i| 10 * i).collect();
        let (payloads, pulled, _) =
            ProjectionSpy::new(ints_by_position(&values, true), payload_tiling);
        (
            VariantWrapProducer {
                level: CurryLevel::new(1),
                base: ProducerBase::unowned(VariantWrapProducer::alloc_id(), &decisions_tiling()),
                input: Box::new(payloads),
                tag: commit(),
                variant_extents: TagMap::from_arms(vec![
                    (commit(), Extent::Base(BaseType::Int)),
                    (abort(), Extent::Base(BaseType::Unit)),
                ]),
            },
            pulled,
        )
    }

    fn keys(tile: &Tile) -> ColumnValue {
        let Tile::DataFunction { domain, .. } = tile else {
            panic!("a collection, got {tile:?}")
        };
        domain.clone()
    }

    /// Each row holds a collection, wrapped as one value once it is whole. Row 0's is complete
    /// and row 1's is still open, so only row 0 is emitted: the arm holds a row's collection
    /// as one cell that cannot grow. The statement is the input's, which does not name row 1.
    #[test]
    fn a_row_whose_collection_is_open_is_not_emitted_or_stated_complete() {
        let tiling = |outer: u64| {
            Tiling::data_function(
                Extent::uint_range(outer),
                Tiling::data_function(
                    Extent::uint_range(4),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                ),
            )
        };
        let rows = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::exactly(&[Value::UInt(0)]),
            BitSet::new(),
        );
        let (collections, _, _) = ProjectionSpy::new(rows, tiling(2));
        let out_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Union(TagMap::from_arms(vec![(
                commit(),
                Extent::Base(BaseType::Int),
            )]))),
        );
        let mut wrap = VariantWrapProducer {
            level: CurryLevel::new(1),
            base: ProducerBase::unowned(VariantWrapProducer::alloc_id(), &out_tiling),
            input: Box::new(collections),
            tag: commit(),
            variant_extents: TagMap::from_arms(vec![(commit(), Extent::Base(BaseType::Int))]),
        };
        let tile = wrap.get(out_tiling.universal_guard());
        assert_eq!(keys(&tile), ColumnValue::UInts(vec![0]));
        let Tile::DataFunction {
            domain_predicate, ..
        } = &tile
        else {
            panic!("a collection, got {tile:?}")
        };
        assert!(
            !domain_predicate.contains_path(&[Value::UInt(1)]),
            "row 1 is withheld, so it is not complete: {domain_predicate:?}"
        );
    }

    #[test]
    fn a_wrapped_payload_stream_is_read_at_the_morsel() {
        let (mut wrap, pulled) = wrapped_payloads();
        let morsel = wrap.get(keys_between(2, 4));
        assert_eq!(keys(&morsel), ColumnValue::UInts(vec![2, 3, 4]));
        assert_eq!(*pulled.borrow(), [keys_between(2, 4)]);
    }

    #[test]
    fn a_wrapped_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 1), keys_between(5, 40)] {
            assert_conforms(|| Box::new(wrapped_payloads().0), guard);
        }
    }

    /// The decisions `commit(0), abort, commit(20), abort, …`: even positions commit their
    /// position times ten, odd positions abort.
    fn decisions() -> Tile {
        let commits: Vec<usize> = (0..ROWS as usize).step_by(2).collect();
        let aborts: Vec<usize> = (1..ROWS as usize).step_by(2).collect();
        let payloads: Vec<i64> = commits.iter().map(|row| 10 * *row as i64).collect();
        Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::Scalar(ColumnValue::Union(TagMap::from_arms(vec![
                (
                    commit(),
                    UnionArm::new(commits, ColumnValue::Ints(payloads)),
                ),
                (
                    abort(),
                    UnionArm::new(aborts.clone(), ColumnValue::Units(aborts.len())),
                ),
            ])))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// One arm of `match d { commit(w) → …; abort → … }`: the payload of the rows carrying
    /// `tag`, read from the decision stream.
    fn arm(tag: FieldKey, payload: Extent) -> (VariantProjectProducer, GuardLog) {
        let out = Tiling::data_function(Extent::uint_range(ROWS), Tiling::Scalar(payload.clone()));
        let (scrutinee, pulled, _) = ProjectionSpy::new(decisions(), decisions_tiling());
        (
            VariantProjectProducer {
                base: ProducerBase::unowned(VariantProjectProducer::alloc_id(), &out),
                input: Box::new(scrutinee),
                tag,
                payload_extent: payload,
                level: CurryLevel::innermost_of(&out),
                empty_level: None,
            },
            pulled,
        )
    }

    fn commit_arm() -> (VariantProjectProducer, GuardLog) {
        arm(commit(), Extent::Base(BaseType::Int))
    }

    fn abort_arm() -> (VariantProjectProducer, GuardLog) {
        arm(abort(), Extent::Base(BaseType::Unit))
    }

    #[test]
    fn an_arm_reads_its_rows_of_the_morsel_from_the_decision_stream() {
        let (mut commits, pulled) = commit_arm();
        let morsel = commits.get(keys_between(2, 5));
        let Tile::DataFunction {
            domain, codomain, ..
        } = &morsel
        else {
            panic!("a collection")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![2, 4]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::Ints(vec![20, 40])));
        assert_eq!(*pulled.borrow(), [keys_between(2, 5)]);
    }

    /// The tags partition the stream, so the arms of one `match` pulled at one morsel hold
    /// disjoint keys that together are the morsel's.
    #[test]
    fn the_arms_of_a_match_partition_the_morsel() {
        let morsel = |mut arm: VariantProjectProducer| -> Vec<u64> {
            let Tile::DataFunction {
                domain: ColumnValue::UInts(keys),
                ..
            } = arm.get(keys_between(2, 5))
            else {
                panic!("a collection of positions")
            };
            keys
        };
        let (mut held, mut other) = (morsel(commit_arm().0), morsel(abort_arm().0));
        held.append(&mut other);
        held.sort_unstable();
        assert_eq!(held, [2, 3, 4, 5]);
    }

    #[test]
    fn an_arm_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 3), keys_between(6, 30)] {
            assert_conforms(|| Box::new(commit_arm().0), guard.clone());
            assert_conforms(|| Box::new(abort_arm().0), guard);
        }
    }

    /// A scrutinee with no keys of its own, a bare union value, supplies positions for them:
    /// it has no guard to receive, so it is read whole and the positions are cut after.
    #[test]
    fn a_bare_union_is_read_whole_and_its_positions_cut() {
        let bare_tiling = Tiling::Scalar(decision_extent());
        let make = || {
            let Tile::DataFunction { codomain, .. } = decisions() else {
                unreachable!("decisions are a stream")
            };
            let out = Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            );
            let (scrutinee, pulled, _) = ProjectionSpy::new(*codomain, bare_tiling.clone());
            (
                VariantProjectProducer {
                    base: ProducerBase::unowned(VariantProjectProducer::alloc_id(), &out),
                    input: Box::new(scrutinee),
                    tag: commit(),
                    payload_extent: Extent::Base(BaseType::Int),
                    level: CurryLevel::innermost_of(&out),
                    empty_level: None,
                },
                pulled,
            )
        };
        let (mut commits, pulled) = make();
        let morsel = commits.get(keys_between(1, 4));
        let Tile::DataFunction { domain, .. } = &morsel else {
            panic!("a collection")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![2, 4]));
        assert_eq!(*pulled.borrow(), [bare_tiling.universal_guard()]);
        assert_conforms(|| Box::new(make().0), keys_between(1, 4));

        // The consumer releases a morsel before the next. The scrutinee has no keys to take the
        // release, and the released positions stay out of the answer.
        commits.release(keys_between(1, 4));
        let next = commits.get(keys_between(5, 7));
        let Tile::DataFunction { domain, .. } = &next else {
            panic!("a collection")
        };
        assert!(
            (0..domain.len()).all(|i| matches!(domain.index_at(i), Value::UInt(key) if key >= 5)),
            "only the second morsel's positions: {domain:?}"
        );
    }

    #[test]
    fn nothing_projects_nothing() {
        let (mut commits, pulled) = commit_arm();
        let nothing = commits.tiling().empty_guard();
        assert_eq!(commits.get(nothing), commits.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    fn nothing_wraps_nothing() {
        let (mut wrap, pulled) = wrapped_payloads();
        let nothing = wrap.tiling().empty_guard();
        assert_eq!(wrap.get(nothing), wrap.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}

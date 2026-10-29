use bit_set::BitSet;
use log::trace;
use std::collections::HashMap;
use std::iter::repeat_n;

use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{
    ColumnValue, Consumer, Extent, Projection, Scheduler, Value, live_keys, shared_consumer,
    tuple_field,
};

/// Inverts a function operator, producing a lookup-function from codomain to domain.
///
/// For an input `domain → codomain`, `Converse` produces a
/// `DataFunction { domain: codomain, codomain: domain }`.  Each codomain
/// value maps to the list of domain values that produce it.
pub struct Converse {
    /// Output tiling: `DataFunction { domain: input.codomain, codomain: input.domain }`,
    /// beneath the standing levels above `level`.
    base: OperatorBase,
    /// The function input to invert.
    input: Box<dyn TileOperator>,
    /// The level inverted — see [`Converse::new_at`].
    level: CurryLevel,
}

impl Converse {
    /// Create a `Converse` operator that inverts `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_at(input, CurryLevel::OUTERMOST)
    }

    /// [`Converse::new`] at `level`, leaving every level above it standing: each enclosing
    /// row's collection is inverted on its own. A group-by whose source varies per row of
    /// an enclosing collection is this.
    pub fn new_at(input: Box<dyn TileOperator>, level: CurryLevel) -> Self {
        let (domain, codomain) = input
            .tiling()
            .values_at(level)
            .split_function_extent()
            .unwrap_or_else(|| {
                panic!(
                    "Converse expected a function at {level}, got {:?}",
                    input.tiling()
                )
            });
        let inverted = Tiling::DataFunction {
            domain: codomain,
            codomain: Box::new(Tiling::DataFunction {
                domain: domain.clone(),
                codomain: Box::new(Tiling::Scalar(domain)),
            }),
        };
        Self {
            base: OperatorBase::new(with_values_at(input.tiling(), level, inverted)),
            input,
            level,
        }
    }
}

impl TileOperator for Converse {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Beneath standing levels the input's outermost keys are the result's; inverting the
        // outermost collection re-keys.
        let keeps_keys = self.level != CurryLevel::OUTERMOST;
        Box::new(ConverseProducer::new(
            ProducerBase::new(
                ConverseProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            self.input.subscribe(
                self.tiling().universal_guard(),
                consumer_keeping_keys_if(keeps_keys, consumer),
                scheduler,
            ),
            self.level,
            self.tiling().values_at(self.level).empty_at_no_rows(),
        ))
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(vec![TilePathStep::Codomain])
    }
}

/// Producer for [`Converse`]: inverts a collection into a collection of collections.
struct ConverseProducer {
    base: ProducerBase,
    /// The upstream producer whose output is inverted.
    input: Box<dyn TileProducer>,
    /// Each input row last read, as the path `[value, key]` it stands at in the output. A
    /// release names output paths, and an input row is released once the path it stands
    /// at is, which takes its value to read. Kept at the outermost level only.
    held: Vec<(Value, Value)>,
    /// The level inverted — see [`Converse::new_at`].
    level: CurryLevel,
    /// The inverted level to answer with where no enclosing row has been reached.
    empty_level: Tile,
    /// The input rows [`BreakingProducer::consume_impl`] merged and the consumer has not
    /// released, of the outermost level only.
    cached: Tile,
    /// Whether `consume_impl` has run: a consuming converse answers from `cached` and never
    /// pulls its input.
    consuming: bool,
}

/// A converse of the outermost level of `input` that nothing subscribed, answering at `tiling`,
/// for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn converse_of(
    input: Box<dyn TileProducer>,
    tiling: &Tiling,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(ConverseProducer::new(
        ProducerBase::unowned(ConverseProducer::alloc_id(), tiling),
        input,
        CurryLevel::OUTERMOST,
        tiling.values_at(CurryLevel::OUTERMOST).empty_at_no_rows(),
    )))
}

impl ConverseProducer {
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        level: CurryLevel,
        empty_level: Tile,
    ) -> Self {
        let cached = input.tiling().empty_tile();
        Self {
            base,
            input,
            held: Vec::new(),
            level,
            empty_level,
            cached,
            consuming: false,
        }
    }

    /// The keys of the held input rows `guard` covers. An input row stands at exactly one
    /// output path, under its own value, so it is released where that path is: under a
    /// released group, or named beneath one.
    fn held_rows_covered(&self, guard: &TileGuard) -> Vec<Value> {
        self.held
            .iter()
            .filter(|(value, key)| guard.covers_path(&[value.clone(), key.clone()]))
            .map(|(_, key)| key.clone())
            .collect()
    }
}

/// Sort row indices by typed key, detect group boundaries, and assemble the nested tile
/// for [`ConverseProducer`].
///
/// `K` is the native element type of the codomain column; using it directly
/// avoids boxing to [`Value`] for most column types. `codomain` and `domain`
/// are re-indexed via [`ColumnValue::select_indices`].
fn converse_group_by_key<K: PartialOrd>(
    keys: &[K],
    codomain: &ColumnValue,
    domain: &ColumnValue,
    domain_predicate: Predicate,
    input_deleted: &BitSet,
) -> Tile {
    let n = keys.len();
    // Sort row indices by codomain key; equal keys will be adjacent.
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_unstable_by(|&a, &b| keys[a].partial_cmp(&keys[b]).expect("Type mismatch"));
    // Identify group boundaries: a new group starts wherever the sorted key changes.
    let mut group_starts: Vec<usize> = Vec::new();
    for i in 0..n {
        if i == 0 || keys[order[i]] != keys[order[i - 1]] {
            group_starts.push(i);
        }
    }
    let num_groups = group_starts.len();
    // The outer keys: one value per group, which is what the inversion keys on.
    let domain1_col = codomain.select_indices(group_starts.iter().map(|&s| order[s]), num_groups);
    // Remap deleted bits: output position j corresponds to input row order[j].
    let output_deleted: BitSet = order
        .iter()
        .enumerate()
        .filter(|(_, src)| input_deleted.contains(**src))
        .map(|(j, _)| j)
        .collect();
    // The inner keys: the original keys, reordered to match the sorted groups.
    let domain2_col = domain.select_indices(order.into_iter(), n);
    // A decided input row never moves to another group, so `[k, d]` is final under every
    // `k` once `d` is: the inner level carries the input's predicate unqualified. A group
    // is final only when no undecided row remains that could still join it.
    let outer_predicate = if domain_predicate.is_true() {
        Predicate::True
    } else {
        Predicate::False
    };
    Tile::data_function(
        domain1_col,
        Box::new(Tile::grouped(
            group_starts,
            domain2_col.clone(),
            Box::new(Tile::Scalar(domain2_col)),
            domain_predicate,
            output_deleted,
        )),
        outer_predicate,
        BitSet::new(),
    )
}

/// Invert one collection `𝐷 ⤇ 𝐾` into `𝐾 ⤇ (𝐷 ⤇ 𝐷)`, with the rows it read as the paths
/// `[value, key]` they stand at in the output. A group [`Tile::group_at`] takes out of a
/// nest is such a collection, with the other enclosing rows emptied, so the row runs are
/// not read.
fn converse_collection(input_tile: Tile) -> (Tile, Vec<(Value, Value)>) {
    let held: Vec<(Value, Value)>;
    let out = match input_tile {
        Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
            ..
        } => {
            held = match &*codomain {
                Tile::Scalar(values) => live_keys(&domain, &deleted)
                    .map(|(row, key)| (values.index_at(row), key))
                    .collect(),
                _ => Vec::new(),
            };

            match *codomain {
                Tile::Scalar(codomain) => {
                    // Dispatch on the native element type of the codomain column so that
                    // sorting uses typed comparison (PartialOrd) and avoids boxing to Value
                    // wherever the inner type is already ordered natively.
                    match &codomain {
                        ColumnValue::Units(n) => {
                            // All codomains are unit; create one group with all rows in order.
                            let keys = vec![(); *n];
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                        ColumnValue::Ints(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::UInts(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Strings(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Bools(bv) => converse_group_by_key(
                            bv,
                            &codomain,
                            &domain,
                            domain_predicate,
                            &deleted,
                        ),
                        ColumnValue::Variants(v) => {
                            // Value is PartialOrd; pass the inner vec directly.
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Records(_) => {
                            // No native slice to borrow; materialise one Value per row for sorting.
                            // TODO: benchmark this and figure out a way to avoid if needed.
                            let n = codomain.len();
                            let keys: Vec<Value> = (0..n).map(|i| codomain.index_at(i)).collect();
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                        ColumnValue::FunctionBindings { .. } => {
                            panic!(
                                "Cannot converse a function whose codomain is a function binding"
                            )
                        }
                        ColumnValue::Union { .. } => {
                            // Materialise one tagged Value per row for sorting.
                            let n = codomain.len();
                            let keys: Vec<Value> = (0..n).map(|i| codomain.index_at(i)).collect();
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                    }
                }
                _ => panic!("Can only converse functions with scalar codomains"),
            }
        }
        _ => panic!("Can only converse functions"),
    };
    (out, held)
}

impl TileProducer for ConverseProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(2 * self.held.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// Inverting the outermost collection makes the values it holds the keys, and which rows
    /// carry which value is known only once the rows are read: the input is read whole and the
    /// groups cut after. The rows a cut group does not name stay unreleased at the input, so a
    /// later pull reads them again. Beneath standing levels the projection names keys the
    /// inversion leaves standing, so the input is pulled at it.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        let input_guard = match self.level.enclosing() {
            None => self.input.tiling().universal_guard(),
            Some(_) => projection.guard(self.input.tiling()),
        };
        let input_tile = self.input.get(input_guard);
        let mut out = match self.level.enclosing() {
            None => {
                debug_assert!(
                    matches!(&input_tile, Tile::DataFunction { row_starts, .. } if row_starts.len() == 1),
                    "converse inverts one mapping, so its input is one collection: {input_tile:?}"
                );
                let (out, held) = converse_collection(input_tile);
                self.held = held;
                out
            }
            // Beneath standing levels each enclosing row's group is inverted on its own:
            // a row's group is a collection in its own right, as it is for `Uncurry`.
            Some(_) => {
                input_tile.regroup_beneath(self.level, self.empty_level.clone(), &mut |row| {
                    match input_tile.group_at(self.level, row) {
                        Some(group) => converse_collection(group.into_owned()).0,
                        None => self.empty_level.clone(),
                    }
                })
            }
        };
        // A group can be released while the input still grows, since `release_impl` frees
        // only the rows held; a row arriving later with a released value would otherwise
        // put the group back into a region the consumer has let go. That row is released
        // upstream on the pull that first holds it: the release reached `release_impl`
        // before the row arrived, so nothing else frees it.
        if !self.base.obsolete_guard.is_empty() {
            let released = self.base.obsolete_guard.clone();
            let late = self.held_rows_covered(&released);
            if !late.is_empty() {
                let rows = late.into_iter().fold(Predicate::False, |all, key| {
                    all.union(&Predicate::point(key))
                });
                self.input
                    .release(TileGuard::Function(FunctionGuard::Domain(rows)));
            }
            out.remove_guarded(released);
        }
        out.restrict_to(&projection, self.tiling());
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if self.level != CurryLevel::OUTERMOST {
            // The levels above 𝐿 stand, and 𝐿's keys become values. Part of an enclosing row's
            // inversion names input rows by their values, which the outermost converse tracks
            // as `held` and a nested one does not yet.
            let input_guard = crate::interpreter::tiling::through_standing_levels(
                obsolete_guard,
                self.level.index(),
                self.input.tiling(),
                &mut |inverted| {
                    todo!(
                        "a nested Converse cannot yet release part of a row's inversion: {inverted:?}"
                    )
                },
            );
            return self.input.release(input_guard);
        }
        if self.consuming {
            self.held = converse_collection(self.cached.clone()).1;
        }
        let released = match obsolete_guard {
            g if g.is_universal() => {
                self.cached = self.input.tiling().empty_tile();
                return self.input.release(self.input.tiling().universal_guard());
            }
            ref g => self.held_rows_covered(g),
        };
        // A held row the guard covers is released here, and a row arriving later through the
        // late-row release in `get_impl`, once its value says which group it joins. This adds
        // the rows a guard names without waiting for that: a statement beneath the groups that
        // names no group says the same under every one, so it names those input keys whatever
        // group they land in, arrived or not. Every other shape names an input row only through
        // its group, so `False` here leaves it to the two paths above rather than dropping it.
        fn under_every_group(guard: &TileGuard) -> Predicate {
            match guard {
                TileGuard::Or(arms) => arms
                    .iter()
                    .map(under_every_group)
                    .fold(Predicate::False, |all, one| all.union(&one)),
                TileGuard::Function(FunctionGuard::Codomain(inner)) => match inner.as_ref() {
                    TileGuard::Function(FunctionGuard::Domain(keys)) => keys.unqualified_arms(),
                    _ => Predicate::False,
                },
                _ => Predicate::False,
            }
        }
        let rows = released
            .into_iter()
            .fold(under_every_group(&obsolete_guard), |all, key| {
                all.union(&Predicate::point(key))
            });
        self.cached
            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(rows.clone())));
        self.cached.compact();
        self.input
            .release(TileGuard::Function(FunctionGuard::Domain(rows)));
    }
}

impl BreakingProducer for ConverseProducer {
    /// Merges the input rows it answers at `guard`, a guard of the input's tiling, into the rows
    /// it holds, drops those whose group the consumer already released, and releases the input
    /// at what the answer stated. The input rows are the state: the groups are built from them on
    /// each offer, since which rows share a value is known only once they are read.
    ///
    /// # Panics
    ///
    /// For a converse beneath standing levels. Releasing part of one row's inversion is `todo!`
    /// in pull mode, so a consuming mode would have no release to serve it.
    fn consume_impl(&mut self, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        assert_eq!(
            self.level,
            CurryLevel::OUTERMOST,
            "a Converse beneath standing levels has no consuming mode"
        );
        self.consuming = true;
        if guard.is_empty() {
            return;
        }
        let mut answered = self.input.get(guard);
        let upstream_guard = answered.to_guard();
        answered.compact();
        self.cached.merge(answered);
        let released = self.base.obsolete_guard.clone();
        if !released.is_empty() {
            self.held = converse_collection(self.cached.clone()).1;
            let late = self.held_rows_covered(&released);
            if !late.is_empty() {
                let rows = late.into_iter().fold(Predicate::False, |all, key| {
                    all.union(&Predicate::point(key))
                });
                self.cached
                    .remove_guarded(TileGuard::Function(FunctionGuard::Domain(rows)));
                self.cached.compact();
            }
        }
        self.input.release(upstream_guard);
    }

    fn input_tiling(&self) -> Tiling {
        self.input.tiling().clone()
    }

    fn input_released(&self) -> TileGuard {
        self.input.obsolete_guard().clone()
    }

    /// The guard of the groups the held rows build.
    fn held(&self) -> TileGuard {
        converse_collection(self.cached.clone()).0.to_guard()
    }

    /// Cut at the groups the held rows build.
    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        let groups = converse_collection(self.cached.clone()).0;
        let keys = groups.live_keys().into_iter().flatten();
        cut_at_keys(guard, keys.map(|(_, key)| key), rows, self.tiling())
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let (mut out, held) = converse_collection(self.cached.clone());
        self.held = held;
        if !self.base.obsolete_guard.is_empty() {
            out.remove_guarded(self.base.obsolete_guard.clone());
        }
        out.restrict_to(&projection, self.tiling());
        out
    }
}

/// Replaces the codomain of a function with the domain values themselves,
/// creating an identity mapping where the codomain is a copy of the domain.
///
/// Takes a `DataFunction(domain → codomain)` and produces `DataFunction(domain → Scalar(domain))`.
/// The output domain is unchanged; the codomain becomes a scalar version of the same domain values.
pub struct MapDomain {
    /// Output tiling: `DataFunction { domain, codomain: Scalar(domain) }`, beneath the
    /// standing levels above `level`.
    base: OperatorBase,
    /// The function input.
    input: Box<dyn TileOperator>,
    /// The level whose values are replaced — see [`MapDomain::new_at`].
    level: CurryLevel,
}

impl MapDomain {
    /// Create a `MapDomain` operator that replaces the codomain with the domain values.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_at(input, CurryLevel::OUTERMOST)
    }

    /// [`MapDomain::new`] at `level`, leaving every level above it standing: each enclosing
    /// row's collection is re-viewed at its own keys.
    pub fn new_at(input: Box<dyn TileOperator>, level: CurryLevel) -> Self {
        let Tiling::DataFunction { domain, .. } = input.tiling().values_at(level) else {
            panic!(
                "MapDomain expected a function tiling at {level}, got {:?}",
                input.tiling()
            )
        };
        let domain = domain.clone();
        let tiling = with_values_at(
            input.tiling(),
            level,
            Tiling::data_function(domain.clone(), Tiling::Scalar(domain)),
        );
        Self {
            base: OperatorBase::new(tiling),
            input,
            level,
        }
    }
}

impl TileOperator for MapDomain {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Every level's keys stand.
        Box::new(MapDomainProducer {
            base: ProducerBase::new(
                MapDomainProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            level: self.level,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Producer for [`MapDomain`]: replaces a function's codomain with its domain.
struct MapDomainProducer {
    base: ProducerBase,
    /// The upstream producer whose codomain is replaced.
    input: Box<dyn TileProducer>,
    /// The level whose values are replaced — see [`MapDomain::new_at`].
    level: CurryLevel,
}

impl TileProducer for MapDomainProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// Every level's keys stand, so the input is pulled at the projection.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut tile = self.input.get(projection.guard(self.input.tiling()));
        // The keys stand, so only the values at the level are replaced, in place.
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile.values_at_mut(self.level)
        else {
            panic!("MapDomain expected a collection at {}", self.level)
        };
        **codomain = Tile::Scalar(domain.clone());
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The keys at 𝐿 stand as well as the levels above it: only the values beneath them
        // are replaced.
        let input_guard = crate::interpreter::tiling::through_standing_levels(
            obsolete_guard,
            self.level.index() + 1,
            self.input.tiling(),
            &mut |values| {
                todo!("MapDomain cannot yet release part of the keys it made values: {values:?}")
            },
        );
        self.input.release(input_guard);
    }
}

/// Flattens a collection of collections into one collection keyed by pairs.
///
/// Takes `A ⤇ B ⤇ C` and produces `{_0: A, _1: B} ⤇ C`: the two key extents are packed
/// into a record key, and the values stand as they were.
pub struct Uncurry {
    /// Output tiling: `DataFunction { domain: Record { _0: A, _1: B }, codomain: Scalar(C) }`,
    /// beneath the standing levels above `level`.
    base: OperatorBase,
    /// The two-level input.
    input: Box<dyn TileOperator>,
    /// The level the pair is formed at — see [`Uncurry::new_at`].
    level: CurryLevel,
}

impl Uncurry {
    /// Create an `Uncurry` operator that flattens two collection levels into one.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_at(input, CurryLevel::OUTERMOST)
    }

    /// [`Uncurry::new`] at `level`, leaving every level above it standing.
    ///
    /// A nest three deep pairs the innermost loop's positions with the loop around them,
    /// under the outermost as a standing level — so which two levels pair is the caller's
    /// to say, not always the top two.
    pub fn new_at(input: Box<dyn TileOperator>, level: CurryLevel) -> Self {
        // Flattening pairs a collection with the one inside it, so it takes exactly that:
        // a collection whose values are a collection. A deeper one flattens a level at a
        // time.
        let Tiling::DataFunction {
            domain: outer,
            codomain: inner,
        } = input.tiling().values_at(level)
        else {
            panic!(
                "Uncurry expected a collection at {level}, got {:?}",
                input.tiling()
            )
        };
        let Tiling::DataFunction {
            domain: inner_keys,
            codomain,
        } = inner.as_ref()
        else {
            panic!("Uncurry flattens two collections, got {:?}", input.tiling())
        };
        let pair_extent = Extent::Record(HashMap::from([
            (tuple_field(0), outer.clone()),
            (tuple_field(1), inner_keys.clone()),
        ]));
        let paired = Tiling::DataFunction {
            domain: pair_extent,
            codomain: codomain.clone(),
        };
        Self {
            base: OperatorBase::new(with_values_at(input.tiling(), level, paired)),
            input,
            level,
        }
    }
}

impl TileOperator for Uncurry {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Beneath standing levels the input's outermost keys are the result's; pairing the whole
        // tile re-keys.
        let keeps_keys = self.level != CurryLevel::OUTERMOST;
        Box::new(UncurryProducer {
            base: ProducerBase::new(
                UncurryProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: self.input.subscribe(
                self.tiling().universal_guard(),
                consumer_keeping_keys_if(keeps_keys, consumer),
                scheduler,
            ),
            level: self.level,
            empty_pair: self.tiling().values_at(self.level).empty_at_no_rows(),
        })
    }
}

/// Producer for [`Uncurry`]: flattens a two-level tile into a one-level tile with pair domain.
struct UncurryProducer {
    base: ProducerBase,
    /// The upstream producer whose two levels are flattened.
    input: Box<dyn TileProducer>,
    /// The level the pair is formed at — see [`Uncurry::new_at`].
    level: CurryLevel,
    /// The paired level to answer with where no enclosing row has been reached.
    empty_pair: Tile,
}

impl TileProducer for UncurryProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// Beneath standing levels the projection names keys the pairing leaves standing, so the
    /// input is pulled at it. Pairing the whole tile makes the pairs the keys: the projection
    /// is then over pairs, and what reaches the input is the admitted first components, which
    /// is every pair they head, and the pairs are cut after.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let input_guard = match (self.level == CurryLevel::OUTERMOST, &projection) {
            (false, _) => projection.guard(self.input.tiling()),
            (true, Projection::Keys(Predicate::Record(components))) => {
                let first = components
                    .get(&tuple_field(0))
                    .cloned()
                    .unwrap_or(Predicate::True);
                Projection::admitting(first).guard(self.input.tiling())
            }
            (true, _) => self.input.tiling().universal_guard(),
        };
        let input_tile = self.input.get(input_guard);
        // Pair beneath the standing levels, which stand unchanged: a row's group is a
        // curried collection in its own right, so the pairing below is the same one a
        // depth-zero `Uncurry` does to the whole tile.
        let mut result =
            input_tile.regroup_beneath(self.level, self.empty_pair.clone(), &mut |row| {
                match input_tile.group_at(self.level, row) {
                    Some(group) => pair_two_levels(group.into_owned()),
                    None => self.empty_pair.clone(),
                }
            });
        result.remove_guarded(self.base().obsolete_guard.clone());
        result.restrict_to(&projection, self.tiling());
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let input_guard = self.split_pair_guard(obsolete_guard);
        trace!("{} releasing up with: {input_guard:?}", self.name());
        self.input.release(input_guard);
    }
}

/// Pair a curried collection's two levels into one keyed by `(outer, inner)` pairs.
///
/// The whole of what [`Uncurry`] does, on a tile that is exactly those two levels. An
/// `Uncurry` beneath standing levels applies it to each enclosing row's group, which is such
/// a tile.
fn pair_two_levels(tile: Tile) -> Tile {
    let Tile::DataFunction {
        domain: domain1,
        codomain: inner,
        domain_predicate,
        ..
    } = tile
    else {
        panic!("Uncurry expected a collection, got {tile:?}")
    };
    let Tile::DataFunction {
        row_starts,
        domain: domain2,
        mut codomain,
        domain_predicate: inner_statement,
        ..
    } = *inner
    else {
        panic!("Uncurry flattens two collections")
    };
    let fields = (tuple_field(0), tuple_field(1));
    let fields = (fields.0.as_str(), fields.1.as_str());
    // Everything beneath the inner level named its paths by outer and inner key apart, and
    // the pair level names them together.
    codomain.map_level_predicates(&mut |depth, pred| pred.with_levels_paired(depth + 2, 0, fields));
    let offsets_vec = &row_starts;

    // One copy of a group's key per key inside it, so the pair column lines up with the
    // flattened codomain.
    let mut expansion_indices = Vec::new();
    for i in 0..domain1.len() {
        let group_start = offsets_vec[i];
        let group_end = if i + 1 < offsets_vec.len() {
            offsets_vec[i + 1]
        } else {
            domain2.len()
        };
        for _ in group_start..group_end {
            expansion_indices.push(i);
        }
    }
    let total_rows = expansion_indices.len();
    let expanded_domain1 = domain1.select_indices(expansion_indices.into_iter(), total_rows);

    let pair_domain = ColumnValue::Records(HashMap::from([
        (tuple_field(0), expanded_domain1),
        (tuple_field(1), domain2),
    ]));
    // A pair is complete where its outer key is — complete beneath, by the closure — or
    // where the inner level called it complete under its outer key.
    let pair_statement = Predicate::record(HashMap::from([
        (tuple_field(0), domain_predicate),
        (tuple_field(1), Predicate::True),
    ]))
    .union(&inner_statement.with_levels_paired(1, 0, fields));
    // The values stand as they were: they are already one entry per key of the flattened
    // domain, in the same order, and materializing them into a column is what a
    // level-carrying value — a nest whose elements are collections — has nowhere to go.
    Tile::data_function(pair_domain, codomain, pair_statement, BitSet::new())
}

impl UncurryProducer {
    /// The input guard a release of the paired level names.
    ///
    /// Standing levels are untouched by the pairing, so a guard naming one passes through
    /// and the guard beneath it is split. At the paired level itself a pair names one inner
    /// key under one outer key, so a release of pairs is exactly a release of those inner
    /// keys, under the standing rows that qualify it.
    fn split_pair_guard(&self, guard: TileGuard) -> TileGuard {
        crate::interpreter::tiling::through_standing_levels(
            guard,
            self.level.index(),
            self.input.tiling(),
            &mut |paired| self.split_pairs(paired),
        )
    }

    /// One arm of a released guard at the paired level, split back into the two levels the
    /// pairs were formed from.
    fn split_pairs(&self, guard: TileGuard) -> TileGuard {
        match guard {
            // Part of every pair's value: the same part of every inner key's value under every
            // outer key. What it names beneath the pairs names them by pair, and is split back
            // into the two components the pairs were formed from.
            TileGuard::Function(FunctionGuard::Codomain(inner)) => {
                let at = self.level.index();
                let fields = (tuple_field(0), tuple_field(1));
                let fields = (fields.0.as_str(), fields.1.as_str());
                let inner = inner.map_level_predicates(&mut |depth, pred| {
                    pred.with_levels_unpaired(at + 1 + depth, at, fields)
                });
                TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                    FunctionGuard::Codomain(Box::new(inner)),
                ))))
            }
            // Keys of the paired level: pairs, which name the input's outer and inner keys
            // together. Split back, each names one inner key under one outer key, so the
            // region is a release of the input's inner level. One naming every inner key of
            // an outer key names that key whole, and the canonical form the release takes
            // (`TileGuard::flatten_or`) spells it as the outer key.
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let at = self.level.index();
                let fields = (tuple_field(0), tuple_field(1));
                let pairs =
                    pred.with_levels_unpaired(at, at, (fields.0.as_str(), fields.1.as_str()));
                TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                    FunctionGuard::Domain(pairs),
                ))))
            }
            // `TileProducer::release` checks a guard against the producer's tiling, and
            // Uncurry's tiling is a collection at the paired level, so an arm reaching it is a
            // function guard.
            g => unreachable!(
                "Uncurry's tiling is a collection at {}, released by {g:?}",
                self.level
            ),
        }
    }
}

/// Filters a collection by a predicate over its keys, keeping the entries the predicate
/// maps to `true` together with their values.
///
/// The filter masks the keys at one level, which the caller states from where it is in the
/// program: an entry's own values may be collections too, so the level to filter is not the
/// innermost one. A `filter_values` masks the keys its elements stand at, and under `map`
/// those are the keys of each element collection, one level further in. The predicate takes
/// one of two forms.
///
/// - **A function value**, at the outermost level. It is applied to the input's keys, and
///   the answer is the mask over them.
/// - **A collection over the input's levels down to the masked one, with `Bool` beneath.**
///   Its innermost values are one boolean per key of the masked level, so they are the mask
///   over it: [`Tile::retain_keys`] drops entries from each row's group and leaves every
///   level above standing. Beneath the outermost level the survivors differ from row to
///   row, which is what a correlated filter and a per-group filter
///   (`sum([s.amount for s in g if s.qty > 2])` over a `groupby`) need.
///
/// TODO we should replace the function-value form with a Restrict node that filters based
/// on a function of the domain, rather than this which filters based on a function of the
/// codomain.
pub struct Filter {
    /// Output tiling, equal to the input tiling (filtering preserves the type).
    base: OperatorBase,
    /// The function input to filter.
    input: Box<dyn TileOperator>,
    /// The boolean predicate applied to each domain element.
    predicate: Box<dyn TileOperator>,
    /// The level whose keys the mask names.
    level: CurryLevel,
}

impl Filter {
    /// Retain the keys of `input` at `level` where `predicate` holds.
    ///
    /// Panics unless `predicate` answers exactly the keys at `level`: a function value only
    /// at the outermost level, and a collection whose innermost level is `level`, of an
    /// input that holds it.
    pub fn new_at(
        input: Box<dyn TileOperator>,
        predicate: Box<dyn TileOperator>,
        level: CurryLevel,
    ) -> Self {
        let tiling = input.tiling().clone();
        assert!(
            level.index() < tiling.levels(),
            "a filter masks the keys at {level}, which its input does not hold: {tiling}"
        );
        match predicate.tiling() {
            Tiling::DataFunction { .. } => assert_eq!(
                CurryLevel::innermost_of(predicate.tiling()),
                Some(level),
                "a filter's predicate answers each key at {level}, so that is its innermost \
                 level: {}",
                predicate.tiling(),
            ),
            _ => assert_eq!(
                level,
                CurryLevel::OUTERMOST,
                "a filter applies a function-valued predicate to its input's own keys, not to \
                 the keys at {level}",
            ),
        }
        Self {
            base: OperatorBase::new(tiling),
            input,
            predicate,
            level,
        }
    }
}

impl TileOperator for Filter {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
        visit(value("predicate", &*self.predicate));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        // A side that is a collection is pulled at the projection and shares the mask's keys; a
        // side that is not is read whole.
        let predicate_producer = subscribe_forwarding_keeping_keys_if(
            self.predicate.tiling().is_data_function(),
            &mut *self.predicate,
            &shared,
            scheduler,
        );
        let input_producer = subscribe_forwarding_keeping_keys_if(
            self.input.tiling().is_data_function(),
            &mut *self.input,
            &shared,
            scheduler,
        );
        Box::new(FilterProducer {
            base: ProducerBase::new(
                FilterProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            input: input_producer,
            predicate: predicate_producer,
            level: self.level,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

struct FilterProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    predicate: Box<dyn TileProducer>,
    level: CurryLevel,
}

impl TileProducer for FilterProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
        visit("predicate", &*self.predicate);
    }

    /// The predicate and the input share the keys of the level the mask names, so both are
    /// pulled at the projection.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }

        self.filtered(&projection)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if matches!(self.predicate.tiling(), Tiling::DataFunction { .. }) {
            // Both predicate and input share the same underlying domain source, so both
            // must be released together; releasing only one leaves the other's upstream
            // FanOutProducer release-guard stale, causing it to re-deliver already-consumed
            // data while the other side returns nothing on the next get().
            let keys = predicate_release(obsolete_guard.clone(), self.predicate.tiling());
            self.predicate.release(keys);
        }
        self.input.release(obsolete_guard);
    }
}

impl FilterProducer {
    /// The input's rows the predicate keeps, for the keys `projection` names.
    fn filtered(&mut self, projection: &Projection) -> Tile {
        let guard_for = |tiling: &Tiling| match tiling.is_data_function() {
            true => projection.guard(tiling),
            false => tiling.universal_guard(),
        };
        let pred_guard = guard_for(self.predicate.tiling());
        let i_guard = guard_for(self.input.tiling());
        let predicate_result = self.predicate.get(pred_guard);
        let input_result = self.input.get(i_guard);

        match (predicate_result, input_result) {
            // Scalar predicate applied element-wise to a collection's keys.
            (Tile::Scalar(pred), input @ Tile::DataFunction { .. }) => match pred.as_single() {
                Some(Value::ComputableFunction(f)) => {
                    let Tile::DataFunction { ref domain, .. } = input else {
                        unreachable!("matched above")
                    };
                    let func_result = f.apply(domain.clone());
                    let mask = func_result
                        .as_bools()
                        .unwrap_or_else(|| panic!("Expected boolean mask"));
                    let mut output = input;
                    output.mark_deleted(mask);
                    output
                }
                _ => panic!("Filter predicate is not a function"),
            },
            // The predicate is a collection over the input's levels down to the masked one,
            // so its innermost values are one boolean per key there, in key order — the mask
            // `retain_keys` takes, which re-offsets the groups a filter shortens.
            (pred @ Tile::DataFunction { .. }, mut input @ Tile::DataFunction { .. }) => {
                let Tile::DataFunction {
                    domain: pred_keys, ..
                } = pred.values_at(self.level)
                else {
                    unreachable!(
                        "the predicate's tiling holds a collection at {}",
                        self.level
                    )
                };
                let Tile::DataFunction { domain: keys, .. } = input.values_at(self.level) else {
                    unreachable!("the input's tiling holds a collection at {}", self.level)
                };
                // An input with nothing in it is already filtered — the predicate keeps
                // answering for entries whose rows have been handed on. A fast path:
                // `retain_answered` hands an empty input back unchanged too.
                if keys.is_empty() {
                    return input;
                }
                let pred_column = scalar_tile_to_column_value(pred.deepest_values().clone());
                let answers = pred_column
                    .as_bools()
                    .unwrap_or_else(|| panic!("Expected bools"));
                debug_assert_eq!(
                    pred_keys.len(),
                    answers.len(),
                    "one answer per predicate entry"
                );
                // **The mask is positional while the two sides hold the same entries.** A
                // cartesian product gives every row the same inner keys, so the masked level's
                // column alone would pass a predicate one row ahead of the input; the levels
                // down to it, groups and keys, do not. Equal levels hold equal paths, and
                // unequal levels over equal paths fall to `retain_answered`, which masks them
                // alike, so the paths are built only when the levels differ.
                let depth = self.level.index() + 1;
                let same_levels = (input.key_levels().into_iter().take(depth))
                    .eq(pred.key_levels().into_iter().take(depth));
                if same_levels {
                    input.values_at_mut(self.level).retain_keys(answers);
                    return input;
                }
                let input_paths = input.row_paths_at(depth);
                let pred_paths = pred.row_paths_at(depth);
                retain_answered(&mut input, self.level, &input_paths, &pred_paths, answers);
                input
            }
            _ => panic!("Invalid Filter input tiles"),
        }
    }
}

/// Mask `input`'s entries at `level` by the predicate's answer at the same path, where the
/// two sides hold different entries.
///
/// Each side is pulled from its own branch of the pairs, so either may have reached entries
/// the other has not. An answered entry keeps or drops by its own answer. An entry the
/// predicate has not answered yet is withheld ([`Tile::withhold`]): it arrives beneath the
/// same row once answered.
/// An answer for an entry the input has not reached waits in the predicate, which the filter
/// releases only by what its output hands on (`predicate_release`).
///
/// Each input path looks its answer up by path, so a pull is linear in the two sides however
/// many entries are undecided.
fn retain_answered(
    input: &mut Tile,
    level: CurryLevel,
    input_paths: &[Vec<Value>],
    pred_paths: &[Vec<Value>],
    answers: &[bool],
) {
    let answer_at: HashMap<&[Value], bool> = pred_paths
        .iter()
        .enumerate()
        .map(|(j, path)| (path.as_slice(), answers[j]))
        .collect();
    let Tile::DataFunction { deleted, .. } = input.values_at(level) else {
        unreachable!("the masked level is a collection")
    };
    let deleted = deleted.clone();
    let mut keep = vec![false; input_paths.len()];
    let mut withheld: Vec<&[Value]> = Vec::new();
    for (i, path) in input_paths.iter().enumerate() {
        match answer_at.get(path.as_slice()) {
            Some(&answer) => keep[i] = answer,
            None => {
                // The filter releases both sides by what it hands on, so a key the input
                // still holds, deleted or not, is one the predicate has not let go of.
                debug_assert!(
                    !deleted.contains(i),
                    "a key the input holds deleted is unanswered: {path:?}"
                );
                withheld.push(path)
            }
        }
    }
    input.withhold(level, &keep, &withheld);
}

/// What a filter's predicate no longer needs, given the release `guard` of the filter's
/// output: the keys the predicate shares with the input pass through, and beneath them only
/// a whole value does.
///
/// The predicate's cell at a key decides every part of that key's value, so the filter needs
/// it until the key's value is released whole. Part of a value names no part of the cell.
fn predicate_release(guard: TileGuard, predicate: &Tiling) -> TileGuard {
    match guard {
        g if g.is_universal() => predicate.universal_guard(),
        g if g.is_empty() => predicate.empty_guard(),
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| predicate_release(arm, predicate))
                .collect(),
        ),
        keys @ TileGuard::Function(FunctionGuard::Domain(_)) => keys,
        TileGuard::Function(FunctionGuard::Codomain(inner)) => match predicate {
            Tiling::DataFunction { codomain, .. } if codomain.is_data_function() => {
                TileGuard::Function(FunctionGuard::Codomain(Box::new(predicate_release(
                    *inner, codomain,
                ))))
            }
            _ => predicate.empty_guard(),
        },
        other => unreachable!(
            "a filter's output is a collection, so its guard is a function guard, got {other:?}"
        ),
    }
}

/// Applies a boolean predicate function to its own domain, producing an identity
/// function over the surviving elements.
///
/// Unlike [`Filter`], which requires a separately-provided input stream and predicate
/// stream that must share the same domain, `Restrict` derives the identity input
/// directly from the predicate's domain. This avoids domain-mismatch panics when the
/// predicate itself contains inner [`Filter`] operators that narrow the domain before
/// the boolean values are produced.
///
/// The predicate operator must produce a `DataFunction { domain: D, codomain: Bool }`.
/// `Restrict` returns `DataFunction { domain: D', codomain: D' }` where D' ⊆ D is the
/// subset of domain elements for which the predicate is `true`.
pub struct Restrict {
    /// Output tiling — `DataFunction(D, D)` mirroring an [`IterateExtent`] over D.
    base: OperatorBase,
    /// The boolean predicate over the domain to restrict.
    predicate: Box<dyn TileOperator>,
}

impl Restrict {
    /// Create a `Restrict` from a predicate operator.
    ///
    /// Panics unless `predicate` has a one-level `DataFunction` tiling.
    pub fn new(predicate: Box<dyn TileOperator>) -> Self {
        let domain_extent = match predicate.tiling() {
            Tiling::DataFunction { domain, codomain } if !codomain.holds_a_level() => {
                domain.clone()
            }
            other => panic!("Restrict expects a one-level DataFunction predicate, got {other:?}"),
        };
        let tiling = Tiling::data_function(domain_extent.clone(), Tiling::Scalar(domain_extent));
        Self {
            base: OperatorBase::new(tiling),
            predicate,
        }
    }
}

impl TileOperator for Restrict {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("predicate", &*self.predicate));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // The restricted domain is the predicate's keys that pass, so a region of them is a region of the result's.
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            consumer,
            scheduler,
        );
        Box::new(RestrictProducer {
            base: ProducerBase::new(
                RestrictProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            predicate: predicate_producer,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

struct RestrictProducer {
    base: ProducerBase,
    predicate: Box<dyn TileProducer>,
}

impl TileProducer for RestrictProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("predicate", &*self.predicate);
    }

    /// A restricted domain is the predicate's keys that pass, so the predicate is pulled at the
    /// projection.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let pred_result = self
            .predicate
            .get(projection.guard(self.predicate.tiling()));

        match pred_result {
            Tile::DataFunction {
                row_starts,
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                let pred_bools = scalar_tile_to_column_value(*codomain);
                let mask = pred_bools
                    .as_bools()
                    .unwrap_or_else(|| panic!("Restrict: expected boolean predicate values"));
                // Build identity: each surviving key maps to itself.
                let as_data = domain.clone();
                let mut output = Tile::grouped(
                    row_starts,
                    domain,
                    Box::new(Tile::Scalar(as_data)),
                    domain_predicate,
                    deleted,
                );
                output.mark_deleted(mask);
                output
            }
            _ => panic!("Restrict: predicate must produce a DataFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.predicate.release(obsolete_guard);
    }
}

/// Pair each key of `outer` with the keys of the collection `inner` holds for it, at one
/// level: the shape [`Product`] produces beneath whatever standing levels both sides
/// carry. `second` says whether a pair's second component is the key or the value under it.
///
/// Both sides are pulled from their own branch and need not have reached the same rows, so
/// only the rows *both* have carry a group. A row the inner side has not delivered has no
/// domain yet. A row whose collection is still arriving is paired with the keys it holds so
/// far and left open, so a later tile adds to its group
/// ([`Tile::append_open_level_beneath`]).
fn pair_one_level(outer: &Tile, inner: &Tile, pair: &Tiling, second: Paired) -> Tile {
    let (
        Tile::DataFunction {
            domain: outer_keys, ..
        },
        Tile::DataFunction {
            domain: inner_rows,
            codomain: groups,
            domain_predicate: inner_complete,
            ..
        },
    ) = (outer, inner)
    else {
        unreachable!(
            "Product's constructor requires both operands to tile as collections; \
             got {outer:?} and {inner:?}"
        )
    };
    let Tile::DataFunction {
        domain: group_keys,
        codomain: group_values,
        ..
    } = &**groups
    else {
        unreachable!(
            "Product's constructor requires an inner side holding a collection per \
             row; got {groups:?}"
        )
    };
    let mut row_of_inner: HashMap<Value, usize> = HashMap::with_capacity(inner_rows.len());
    for i in 0..inner_rows.len() {
        row_of_inner.insert(inner_rows.index_at(i), i);
    }
    let paired: Vec<usize> = (0..outer_keys.len())
        .filter(|r| row_of_inner.contains_key(&outer_keys.index_at(*r)))
        .collect();
    let runs: Vec<(usize, usize)> = paired
        .iter()
        .map(|r| {
            let i = row_of_inner[&outer_keys.index_at(*r)];
            groups.row_run(i)
        })
        .collect();
    let mut kept = vec![false; outer_keys.len()];
    for r in &paired {
        kept[*r] = true;
    }
    let mut emitted = outer.clone();
    emitted.retain_keys(&kept);
    // A row is complete once nothing more arrives beneath it, which takes both sides: the
    // enclosing row, and that row's collection on the inner side. The outer side's
    // statement alone calls a row complete whose inner collection has not arrived, and a
    // consumer releases what a statement calls complete, so that row's pairs are released
    // before they exist and never delivered. So the level is appended open: it calls
    // complete what both sides do and nothing more.
    if let Tile::DataFunction {
        domain_predicate, ..
    } = &mut emitted
    {
        *domain_predicate = domain_predicate.intersect(inner_complete);
    }
    let total: usize = runs.iter().map(|(a, b)| b - a).sum();
    emitted.append_open_level_beneath(CurryLevel::OUTERMOST, |codomain| {
        let key_indices: Vec<usize> = runs.iter().flat_map(|(a, b)| *a..*b).collect();
        let keys = group_keys.select_indices(key_indices.iter().copied(), total);
        let second = match second {
            Paired::Key => Tile::Scalar(keys.clone()),
            Paired::Value => group_values.select_rows(&key_indices),
        };
        let row_indices: Vec<usize> = runs
            .iter()
            .enumerate()
            .flat_map(|(r, (a, b))| repeat_n(r, b - a))
            .collect();
        // Each outer row's value now stands beneath the inner keys paired with it, so
        // what it states of its own paths gains the inner key as a component.
        let mut outer_values = codomain.select_rows(&row_indices);
        outer_values
            .map_level_predicates(&mut |depth, pred| pred.with_level_inserted(depth + 1, 1));
        let mut starts = Vec::with_capacity(runs.len());
        let mut at = 0;
        for (a, b) in &runs {
            starts.push(at);
            at += b - a;
        }
        Tile::grouped(
            starts,
            keys.clone(),
            Box::new(pair_tile(outer_values, second, pair)),
            Predicate::False,
            BitSet::new(),
        )
    })
}

/// The pair `{_0: element, _1: second}` in the representation `pair` names.
///
/// One rule, stated in [`Product`]'s constructor and read here: a materialized record column
/// unless a component carries a level, which a column has nowhere to put.
fn pair_tile(element: Tile, second: Tile, pair: &Tiling) -> Tile {
    match pair {
        Tiling::Record(_) => Tile::tuple(vec![element, second]),
        _ => Tile::Scalar(ColumnValue::Records(HashMap::from([
            (tuple_field(0), scalar_tile_to_column_value(element)),
            (tuple_field(1), scalar_tile_to_column_value(second)),
        ]))),
    }
}

/// What a [`Product`] pair holds beside the outer row's value: the key of the row's inner
/// collection, or the value that collection holds at that key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Paired {
    Key,
    Value,
}

/// Each row of one stream paired with every key of its group in another, or with every value
/// under those keys ([`Paired`]): the product that makes a correlated inner comprehension and
/// a nested loop compilable.
///
/// **A per-row inner side** ([`Product::per_row_at`]) gives each row a group of its own. A
/// **nested loop** has a domain that belongs to the row:
/// `for xs in rows: for x in xs` gives each row its own collection, and a data source whose
/// elements are lists gives them differing lengths with no witness and no `box` involved.
/// There is then no extent to enumerate — the element extent's domain is unbounded — so the
/// keys come from the tile.
///
/// The output tiling is the outer's levels with the inner domain put beneath the rows, over
/// `{_0: outer value, _1: inner key}`, or the inner value in `_1` for [`Paired::Value`]. A row is complete as soon as both sides call it
/// complete, and a row whose group is still arriving is paired with what it holds and left
/// open.
///
/// A collection every row reads, a correlated inner comprehension's inner source, reaches
/// this as one copy per row: `const` lifts it beside each row (`MapResultToConst`), which
/// streams it into every row as it arrives and releases it once everything is released.
pub struct Product {
    /// Output tiling: the outer's levels down to its rows, the inner domain beneath them,
    /// then the pairs.
    base: OperatorBase,
    /// The level the pairing adds ([`Product::per_row_at`]).
    paired: CurryLevel,
    /// The outer collection, one row per group.
    outer: Box<dyn TileOperator>,
    /// The per-row collections, aligned with `outer` row for row.
    inner: Box<dyn TileOperator>,
    /// What each pair holds beside the outer row's value.
    second: Paired,
}

impl Product {
    /// Pair every row of `outer` at `paired`'s enclosing level with the keys of the
    /// collection `inner` holds for it, at `paired`: the level the iteration being entered
    /// adds, which the caller states from where the pairing sits in the program.
    ///
    /// Not read off `outer`'s tiling: a row's value may be a collection of its own — a
    /// binding holding one per row, lifted into the loop beneath — so `outer` can carry
    /// levels below the row that the pairing does not go beneath.
    pub fn per_row_at(
        outer: Box<dyn TileOperator>,
        inner: Box<dyn TileOperator>,
        paired: CurryLevel,
    ) -> Self {
        let row_domain = Self::per_row_domain(&*inner, paired);
        Self::build(outer, inner, paired, row_domain, Paired::Key)
    }

    /// The domain of the collection a per-row inner side holds for each row, at `paired`.
    fn per_row_domain(inner: &dyn TileOperator, paired: CurryLevel) -> Extent {
        assert!(
            inner.tiling().levels() > paired.index(),
            "Product's inner side holds one collection per row of the outer at {paired}, \
             got {:?}",
            inner.tiling()
        );
        let Tiling::DataFunction {
            domain: row_domain, ..
        } = inner.tiling().values_at(paired)
        else {
            panic!(
                "Product reads each row's domain off a collection of collections, got {:?}",
                inner.tiling()
            )
        };
        row_domain.clone()
    }

    /// [`Self::per_row_at`], pairing every row of `outer` with the **values** of the
    /// collection `inner` holds for it rather than its keys, one pair per key.
    ///
    /// What [`Builtin::StrengthOver`](crate::ccl::Builtin::StrengthOver) compiles to, so the
    /// element function takes the row and a value: a generator over a sum that reads its
    /// enclosing scope (`src/ccl/design/optimization.md`,
    /// "A generator over a sum composes with its source") and a correlated inner
    /// comprehension (`src/ccl/planning/correlated.rs`). The output keeps the collection's
    /// keys as the paired level, so each row's result is a collection over its own
    /// collection's domain.
    pub fn per_row_values_at(
        outer: Box<dyn TileOperator>,
        inner: Box<dyn TileOperator>,
        paired: CurryLevel,
    ) -> Self {
        let row_domain = Self::per_row_domain(&*inner, paired);
        Self::build(outer, inner, paired, row_domain, Paired::Value)
    }

    fn build(
        outer: Box<dyn TileOperator>,
        inner: Box<dyn TileOperator>,
        paired: CurryLevel,
        row_domain: Extent,
        second: Paired,
    ) -> Self {
        let outer_tiling = outer.tiling();
        assert!(
            outer_tiling.is_data_function() && paired.index() >= 1,
            "Product pairs the rows of a collection, got {outer_tiling:?} at {paired}"
        );
        let element = outer_tiling.values_at(paired).clone();
        let second_tiling = match second {
            Paired::Key => Tiling::Scalar(row_domain.clone()),
            Paired::Value => {
                let Tiling::DataFunction { codomain, .. } = inner.tiling().values_at(paired) else {
                    unreachable!("a per-row inner side holds a collection per row")
                };
                (**codomain).clone()
            }
        };
        // The pair rides materialized in one column unless a component carries a level, which
        // a column has nowhere to put: a nest whose elements are collections pairs each of
        // them against its own keys, so the pair is a struct of arrays there.
        let pair = if element.holds_a_level() || second_tiling.holds_a_level() {
            Tiling::tuple(&[element, second_tiling])
        } else {
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), element.extent()),
                (tuple_field(1), second_tiling.extent()),
            ])))
        };
        let tiling = level_beneath(outer_tiling, paired.index() - 1, row_domain, pair);
        Self {
            base: OperatorBase::new(tiling),
            outer,
            inner,
            paired,
            second,
        }
    }
}

/// `tiling` with a level over `domain` put beneath level `at`, holding `codomain` in place of
/// the values `at` held.
fn level_beneath(tiling: &Tiling, at: usize, domain: Extent, codomain: Tiling) -> Tiling {
    let Tiling::DataFunction {
        domain: outer,
        codomain: inner,
    } = tiling
    else {
        panic!("level_beneath reaches a collection's level {at}, got {tiling}")
    };
    let codomain = match at {
        0 => Tiling::DataFunction {
            domain,
            codomain: Box::new(codomain),
        },
        _ => level_beneath(inner, at - 1, domain, codomain),
    };
    Tiling::DataFunction {
        domain: outer.clone(),
        codomain: Box::new(codomain),
    }
}

impl TileOperator for Product {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("outer", &*self.outer));
        visit(value("inner", &*self.inner));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        let level = self
            .paired
            .enclosing()
            .unwrap_or_else(|| unreachable!("the paired level is beneath a row"));
        let empty_level = self.tiling().values_at(level).empty_at_no_rows();
        Box::new(ProductProducer {
            base: ProducerBase::new(
                ProductProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            // Both sides are pulled at the projection, aligned row for row.
            outer: subscribe_forwarding_keeping_keys(&mut *self.outer, &shared, scheduler),
            inner: subscribe_forwarding_keeping_keys(&mut *self.inner, &shared, scheduler),
            level,
            empty_level,
            pair: self.tiling().deepest_values().clone(),
            second: self.second,
        })
    }
}

/// Producer for [`Product`].
struct ProductProducer {
    base: ProducerBase,
    outer: Box<dyn TileProducer>,
    inner: Box<dyn TileProducer>,
    /// The level of the rows being paired, one above the level the pairing adds
    /// ([`Product::paired`](field@Product::paired)). Both sides carry it and every level
    /// above it, so an inner loop inside a deeper nest pairs beneath the levels it leaves
    /// standing rather than at the top, where a key value repeats across enclosing rows and
    /// names no single row.
    level: CurryLevel,
    /// The paired level, empty — what an enclosing row that neither side has reached
    /// contributes to the regrouped result.
    empty_level: Tile,
    /// The pair's own tiling, which says whether it rides materialized in one column.
    pair: Tiling,
    /// What each pair holds beside the outer row's value.
    second: Paired,
}

impl TileProducer for ProductProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("outer", &*self.outer);
        visit("inner", &*self.inner);
    }

    /// The two sides are aligned row for row, so a projection of the rows is a projection of
    /// each side.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut outer_tile = self.outer.get(projection.guard(self.outer.tiling()));
        outer_tile.compact();
        let mut inner_tile = self.inner.get(projection.guard(self.inner.tiling()));
        inner_tile.compact();
        // The two sides are pulled from their own branches, so a row is matched by its path.
        let (outer_paths, inner_row_at) = match self.level.enclosing() {
            Some(enclosing) => (
                outer_tile.paths_at(enclosing),
                inner_tile.rows_by_path(enclosing),
            ),
            None => (vec![Vec::new()], HashMap::from([(Vec::new(), 0)])),
        };
        let mut tile =
            outer_tile.regroup_beneath(self.level, self.empty_level.clone(), &mut |row| {
                let inner_row = inner_row_at.get(&outer_paths[row]);
                let (Some(outer), Some(inner)) = (
                    outer_tile.group_at(self.level, row),
                    inner_row.and_then(|&at| inner_tile.group_at(self.level, at)),
                ) else {
                    // An enclosing row one side has not reached pairs nothing. The two are
                    // pulled from their own branches, so either may be ahead.
                    return self.empty_level.clone();
                };
                pair_one_level(&outer, &inner, &self.pair, self.second)
            });
        // Beneath a standing level both sides fill the row, so a row there is complete
        // where both call it complete; the outer side's statement alone is about half of it.
        // Each side's completeness at a level includes what the levels above it state, since
        // completeness is downward-closed ([`Tile::completion_at`]), so the two closures are
        // what intersect: a side that settles a path one level higher than the other states
        // it nowhere at this level.
        for depth in (0..self.level.index()).map(CurryLevel::new) {
            let complete = outer_tile
                .completion_at(depth)
                .intersect(&inner_tile.completion_at(depth));
            let Tile::DataFunction {
                domain_predicate, ..
            } = tile.values_at_mut(depth)
            else {
                unreachable!("the levels above the pair are collections")
            };
            *domain_predicate = complete;
        }
        tile.remove_guarded(self.obsolete_guard().clone());
        tile
    }

    /// A row releases to both sides: each holds that row's own contribution.
    ///
    /// The outer side shares the output's levels down to the rows, and the inner side one
    /// further, down to the keys paired with them, so a release of some of a row's pairs
    /// reaches the inner side's keys and leaves the outer row standing.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_universal() => {
                self.outer.release(self.outer.tiling().universal_guard());
                self.inner.release(self.inner.tiling().universal_guard());
            }
            g if g.is_empty() => {
                self.outer.release(self.outer.tiling().empty_guard());
                self.inner.release(self.inner.tiling().empty_guard());
            }
            g => {
                // `level` is the rows', so the outer side holds it and those above.
                let shared = self.level.index() + 1;
                let outer = crate::interpreter::tiling::through_shared_levels(
                    g.clone(),
                    shared,
                    self.outer.tiling(),
                );

                let inner = crate::interpreter::tiling::through_shared_levels(
                    g,
                    shared + 1,
                    self.inner.tiling(),
                );
                self.outer.release(outer);
                self.inner.release(inner);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
    use crate::interpreter::{BaseType, ColumnValue, Extent, domain_prefix};

    /// A release of the paired level beneath a standing level arrives as a path prefix
    /// (`domain_prefix`): the standing rows before the running one whole, and under the
    /// running one a staircase over the pair's fields. Each arm splits on its own, and a
    /// pair arm qualified by its standing row releases under that row only: outer keys whose
    /// inner collection it covers whole, and the inner keys it names of the outer key it
    /// does not.
    #[test]
    fn uncurry_splits_a_pair_prefix_beneath_a_standing_level() {
        let uint = || Extent::Base(BaseType::UInt);
        let input_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::data_function(uint(), Tiling::Scalar(uint())),
            ),
        );
        let pair_extent = Extent::Record(
            [(tuple_field(0), uint()), (tuple_field(1), uint())]
                .into_iter()
                .collect(),
        );
        let output_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(pair_extent, Tiling::Scalar(uint())),
        );
        let uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(
                input_tiling.empty_at_no_rows(),
                input_tiling,
            )),
            level: CurryLevel::new(1),
            empty_pair: output_tiling.empty_at_no_rows(),
        };
        let pair = Value::Record(HashMap::from([
            (tuple_field(0), Value::UInt(2)),
            (tuple_field(1), Value::UInt(0)),
        ]));
        let released = domain_prefix(vec![Value::UInt(1), pair]);
        let domain = |p: Predicate| TileGuard::Function(FunctionGuard::Domain(p));
        let codomain = |g: TileGuard| TileGuard::Function(FunctionGuard::Codomain(Box::new(g)));
        // Rows before 1 whole; under row 1, outer keys before 2 whole, and under outer key 2
        // the inner keys through 0.
        let expected = TileGuard::flatten_or(vec![
            domain(Predicate::below(Value::UInt(1))),
            codomain(domain(Predicate::qualified(
                Predicate::point(Value::UInt(1)),
                Predicate::below(Value::UInt(2)),
            ))),
            codomain(codomain(domain(Predicate::qualified(
                Predicate::qualified(
                    Predicate::point(Value::UInt(1)),
                    Predicate::point(Value::UInt(2)),
                ),
                Predicate::at_or_below(Value::UInt(0)),
            )))),
        ]);
        assert_eq!(
            TileGuard::flatten_or(vec![uncurry.split_pair_guard(released)]),
            expected
        );
    }

    fn uints(values: &[u64]) -> ColumnValue {
        ColumnValue::UInts(values.to_vec())
    }

    /// One level of `keys` grouped by `starts`, over `codomain`.
    fn level(starts: &[usize], keys: &[u64], codomain: Tile) -> Tile {
        Tile::grouped(
            starts.to_vec(),
            uints(keys),
            Box::new(codomain),
            Predicate::False,
            BitSet::new(),
        )
    }

    /// A collection keyed `1` and `2` over `codomain`.
    fn outer(codomain: Tile) -> Tile {
        Tile::data_function(
            uints(&[1, 2]),
            Box::new(codomain),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// `levels` collections of `UInt` keys over `UInt` values.
    fn uint_tiling(levels: usize) -> Tiling {
        (0..levels).fold(
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
            |codomain, _| Tiling::data_function(Extent::Base(BaseType::UInt), codomain),
        )
    }

    /// The predicate both cases filter by: two levels over the keys `1 ↦ [10, 20]` and
    /// `2 ↦ [10, 30]`, keeping `(1, 10)` and `(2, 30)`.
    fn per_row_predicate() -> TestTileProducer {
        let mask: Vec<bool> = [true, false, false, true].into_iter().collect();
        TestTileProducer::new(
            outer(level(
                &[0, 2],
                &[10, 20, 10, 30],
                Tile::Scalar(ColumnValue::Bools(mask)),
            )),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::data_function(
                    Extent::Base(BaseType::UInt),
                    Tiling::Scalar(Extent::Base(BaseType::Bool)),
                ),
            ),
        )
    }

    fn filter(input: Tile, levels: usize) -> Tile {
        filter_by(per_row_predicate(), input, levels)
    }

    fn filter_by(predicate: TestTileProducer, input: Tile, levels: usize) -> Tile {
        let tiling = uint_tiling(levels);
        let mut filter = FilterProducer {
            base: ProducerBase::unowned(FilterProducer::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(input, tiling.clone())),
            predicate: Box::new(predicate),
            level: CurryLevel::new(1),
        };
        filter.get(filter.tiling().universal_guard())
    }

    /// A two-level predicate masks each row's inner keys, so the survivors differ by row and
    /// the outer level stands.
    #[test]
    fn a_two_level_predicate_filters_each_rows_inner_keys() {
        let input = outer(level(
            &[0, 2],
            &[10, 20, 10, 30],
            Tile::Scalar(uints(&[100, 200, 300, 400])),
        ));
        assert_eq!(
            filter(input, 2),
            outer(level(&[0, 1], &[10, 30], Tile::Scalar(uints(&[100, 400])))),
        );
    }

    /// An input holding a level beneath the masked one is masked at the filter's level, not
    /// its innermost: each dropped key takes its group of the level below with it.
    #[test]
    fn a_filter_masks_its_own_level_above_deeper_ones() {
        let input = outer(level(
            &[0, 2],
            &[10, 20, 10, 30],
            level(
                &[0, 2, 3, 4],
                &[5, 6, 5, 7, 8, 9],
                Tile::Scalar(uints(&[1, 2, 3, 4, 5, 6])),
            ),
        ));
        assert_eq!(
            filter(input, 3),
            outer(level(
                &[0, 1],
                &[10, 30],
                level(&[0, 2], &[5, 6, 8, 9], Tile::Scalar(uints(&[1, 2, 5, 6]))),
            )),
        );
    }

    /// An input row the predicate has not answered yet is withheld: its entries are left out
    /// and its key out of the outer level's completeness, while the answered rows are masked
    /// by their own answers.
    #[test]
    fn a_filter_withholds_the_rows_its_predicate_has_not_answered() {
        let rows = |codomain: Tile, complete: Predicate| {
            Tile::data_function(
                uints(&[1, 2, 3]),
                Box::new(codomain),
                complete,
                BitSet::new(),
            )
        };
        let input = rows(
            level(
                &[0, 2, 4],
                &[10, 20, 10, 30, 10, 40],
                Tile::Scalar(uints(&[100, 200, 300, 400, 500, 600])),
            ),
            Predicate::True,
        );
        let unanswered = Predicate::flatten_or(vec![Predicate::exactly(&[Value::UInt(3)])]);
        assert_eq!(
            filter(input, 2),
            rows(
                level(&[0, 1, 2], &[10, 30], Tile::Scalar(uints(&[100, 400]))),
                Predicate::True.minus(&unanswered),
            ),
        );
    }

    /// A predicate a row ahead of the input, over a product: both sides hold four entries
    /// with the same inner keys, `[10, 20]` under each row, but under different rows. The
    /// input's row `1` is unanswered and withheld; its row `2` takes the predicate's answers
    /// for row `2`, which keep `(2, 10)`.
    #[test]
    fn a_predicate_a_row_ahead_over_a_product_answers_by_path() {
        let product = |rows: &[u64], inner: Tile| {
            Tile::data_function(uints(rows), Box::new(inner), Predicate::True, BitSet::new())
        };
        let mask: Vec<bool> = [true, false, false, true].into_iter().collect();
        let predicate = TestTileProducer::new(
            product(
                &[2, 3],
                level(
                    &[0, 2],
                    &[10, 20, 10, 20],
                    Tile::Scalar(ColumnValue::Bools(mask)),
                ),
            ),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::data_function(
                    Extent::Base(BaseType::UInt),
                    Tiling::Scalar(Extent::Base(BaseType::Bool)),
                ),
            ),
        );
        let input = product(
            &[1, 2],
            level(
                &[0, 2],
                &[10, 20, 10, 20],
                Tile::Scalar(uints(&[100, 200, 300, 400])),
            ),
        );
        let row_1 = Predicate::flatten_or(vec![Predicate::exactly(&[Value::UInt(1)])]);
        assert_eq!(
            filter_by(predicate, input, 2),
            Tile::data_function(
                uints(&[1, 2]),
                Box::new(level(&[0, 0], &[10], Tile::Scalar(uints(&[300])))),
                Predicate::True.minus(&row_1),
                BitSet::new(),
            ),
        );
    }

    /// An inner level that states its own completeness stops stating the paths of the entries
    /// withheld from it, as the outer level stops stating their rows.
    #[test]
    fn a_withheld_entry_leaves_a_stated_inner_completeness() {
        let rows = |codomain: Tile| {
            Tile::data_function(
                uints(&[1, 2, 3]),
                Box::new(codomain),
                Predicate::True,
                BitSet::new(),
            )
        };
        let inner = |starts: &[usize], keys: &[u64], values: &[u64], complete: Predicate| {
            Tile::grouped(
                starts.to_vec(),
                uints(keys),
                Box::new(Tile::Scalar(uints(values))),
                complete,
                BitSet::new(),
            )
        };
        let input = rows(inner(
            &[0, 2, 4],
            &[10, 20, 10, 30, 10, 40],
            &[100, 200, 300, 400, 500, 600],
            Predicate::True,
        ));
        let row_3 = Predicate::flatten_or(vec![Predicate::exactly(&[Value::UInt(3)])]);
        let entries_of_row_3 = Predicate::flatten_or(vec![
            Predicate::exactly(&[Value::UInt(3), Value::UInt(10)]),
            Predicate::exactly(&[Value::UInt(3), Value::UInt(40)]),
        ]);
        let Tile::DataFunction {
            codomain,
            domain_predicate,
            ..
        } = filter(input, 2)
        else {
            panic!("a filter keeps a collection a collection")
        };
        assert_eq!(domain_predicate, Predicate::True.minus(&row_3));
        assert_eq!(
            *codomain,
            inner(
                &[0, 1, 2],
                &[10, 30],
                &[100, 400],
                Predicate::True.minus(&entries_of_row_3),
            ),
        );
    }

    /// A release of some pairs under an outer key reaches the input as those inner keys under
    /// that key, and leaves the outer key live.
    #[test]
    fn uncurry_forwards_a_partial_group_release_as_its_inner_keys() {
        let uint = || Extent::Base(BaseType::UInt);
        let input_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::Scalar(uint())),
        );
        let pair_extent = Extent::Record(
            [(tuple_field(0), uint()), (tuple_field(1), uint())]
                .into_iter()
                .collect(),
        );
        let output_tiling = Tiling::data_function(pair_extent, Tiling::Scalar(uint()));
        let mut uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(
                input_tiling.empty_at_no_rows(),
                input_tiling,
            )),
            level: CurryLevel::OUTERMOST,
            empty_pair: output_tiling.empty_at_no_rows(),
        };
        let pair = Value::Record(HashMap::from([
            (tuple_field(0), Value::UInt(0)),
            (tuple_field(1), Value::UInt(1)),
        ]));
        uncurry.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(pair),
        )));
        let upstream = uncurry.input.obsolete_guard();
        assert!(
            upstream.covers_path(&[Value::UInt(0), Value::UInt(1)]),
            "{upstream:?}"
        );
        assert!(
            !upstream.covers_path(&[Value::UInt(0), Value::UInt(0)]),
            "{upstream:?}"
        );
        assert!(!upstream.covers_path(&[Value::UInt(0)]), "{upstream:?}");
    }

    #[test]
    fn uncurry_producer_basic() {
        // Test UncurryProducer.get_impl with a simple Function
        //
        // Creates a Function with:
        // - domain1: [1, 2] (two keys)
        // - offsets: [0, 2] (key 1 has 2 items, key 2 has 1 item [implicit end at domain2.len()])
        // - domain2: [10, 20, 30] (flattened second-level domain)
        // - codomain: [100, 200, 300] (flattened codomain)
        //
        // Expected expansion_indices: [0, 0, 1] (key 0 repeated 2 times, key 1 repeated 1 time)
        // Expected expanded_domain1: [1, 1, 2]
        // Expected pair domain: Record with _0=[1,1,2] and _1=[10,20,30]

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![10, 20, 30]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200, 300]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );

        let two_level_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let input_producer = TestTileProducer::new(two_level_tile, two_level_tiling.clone());

        // Create UncurryProducer with the test producer as input
        let output_tiling = Tiling::data_function(
            Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        let mut uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            level: CurryLevel::OUTERMOST,
            empty_pair: output_tiling.empty_at_no_rows(),
        };

        // Get the result from UncurryProducer
        let result = uncurry.get(uncurry.tiling().universal_guard());

        // Verify the result is a Function
        match result {
            Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } => {
                // Verify the domain is a Record with fields _0 and _1
                match domain {
                    ColumnValue::Records(fields) => {
                        assert_eq!(fields.len(), 2, "domain should have 2 fields");
                        assert!(
                            fields.contains_key(&tuple_field(0)),
                            "domain should have _0 field"
                        );
                        assert!(
                            fields.contains_key(&tuple_field(1)),
                            "domain should have _1 field"
                        );

                        // Verify expanded_domain1 (field _0): [1, 1, 2]
                        let field_0 = &fields[&tuple_field(0)];
                        if let ColumnValue::UInts(vals) = field_0 {
                            assert_eq!(vals, &vec![1, 1, 2], "_0 should be expanded domain1");
                        } else {
                            panic!("_0 field should be UInts");
                        }

                        // Verify domain2 (field _1): [10, 20, 30]
                        let field_1 = &fields[&tuple_field(1)];
                        if let ColumnValue::UInts(vals) = field_1 {
                            assert_eq!(vals, &vec![10, 20, 30], "_1 should be domain2");
                        } else {
                            panic!("_1 field should be UInts");
                        }
                    }
                    _ => panic!("domain should be a Record"),
                }

                // Verify codomain is a Scalar
                match *codomain {
                    Tile::Scalar(ColumnValue::UInts(ref vals)) => {
                        assert_eq!(vals, &vec![100, 200, 300], "codomain should match original");
                    }
                    _ => panic!("codomain should be Scalar(UInts)"),
                }

                // Verify domain_predicate is transformed appropriately
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::True),
                        (tuple_field(1), Predicate::True),
                    ])),
                    "domain_predicate should be preserved"
                );
            }
            _ => panic!("Expected a collection result"),
        }
    }

    #[test]
    fn uncurry_producer_with_single_elements() {
        // Test UncurryProducer with groups containing single elements
        //
        // - domain1: [A, B, C] (three keys)
        // - offsets: [0, 1, 2] (each key has exactly 1 item [last implicit end at domain2.len()])
        // - domain2: [X, Y, Z]
        // - codomain: [1, 2, 3]
        //
        // Expected expansion_indices: [0, 1, 2]
        // Expected expanded_domain1: [A, B, C]

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![100, 200, 300]),
            Box::new(Tile::grouped(
                vec![0, 1, 2],
                ColumnValue::UInts(vec![10, 20, 30]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![1, 2, 3]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );

        let two_level_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let input_producer = TestTileProducer::new(two_level_tile, two_level_tiling);

        let output_tiling = Tiling::data_function(
            Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        let mut uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            level: CurryLevel::OUTERMOST,
            empty_pair: output_tiling.empty_at_no_rows(),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::DataFunction {
                domain,
                domain_predicate,
                ..
            } => {
                match domain {
                    ColumnValue::Records(fields) => {
                        let field_0 = &fields[&tuple_field(0)];
                        if let ColumnValue::UInts(vals) = field_0 {
                            assert_eq!(
                                vals,
                                &vec![100, 200, 300],
                                "expanded domain1 should be unchanged"
                            );
                        } else {
                            panic!("_0 field should be UInts");
                        }

                        let field_1 = &fields[&tuple_field(1)];
                        if let ColumnValue::UInts(vals) = field_1 {
                            assert_eq!(vals, &vec![10, 20, 30], "domain2 should be unchanged");
                        } else {
                            panic!("_1 field should be UInts");
                        }
                    }
                    _ => panic!("domain should be a Record"),
                }

                // No outer key is complete and no inner level says anything, so no pair is.
                assert_eq!(domain_predicate, Predicate::False, "no pair is complete");
            }
            _ => panic!("Expected a collection result"),
        }
    }

    #[test]
    fn uncurry_domain_predicate_transformation_with_true() {
        // Test that UncurryProducer.get() transforms domain_predicate correctly
        // when the input has Predicate::True

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 1, 2],
                ColumnValue::UInts(vec![10, 20, 30]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200, 300]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );

        let two_level_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let input_producer = TestTileProducer::new(two_level_tile, two_level_tiling);

        let output_tiling = Tiling::data_function(
            Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        let mut uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            level: CurryLevel::OUTERMOST,
            empty_pair: output_tiling.empty_at_no_rows(),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::DataFunction {
                domain_predicate, ..
            } => {
                // Verify domain_predicate is transformed into a Record with both fields True
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::True),
                        (tuple_field(1), Predicate::True),
                    ])),
                    "domain_predicate should be transformed into Record(_0: True, _1: True)"
                );
            }
            _ => panic!("Expected a collection result"),
        }
    }

    #[test]
    fn uncurry_domain_predicate_transformation_with_false() {
        // Test that UncurryProducer.get() transforms domain_predicate correctly
        // when the input has Predicate::False

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::UInts(vec![10, 20]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );

        let two_level_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let input_producer = TestTileProducer::new(two_level_tile, two_level_tiling);

        let output_tiling = Tiling::data_function(
            Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        let mut uncurry = UncurryProducer {
            base: ProducerBase::unowned(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            level: CurryLevel::OUTERMOST,
            empty_pair: output_tiling.empty_at_no_rows(),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::DataFunction {
                domain_predicate, ..
            } => {
                // Neither level calls anything complete, so no pair is.
                assert_eq!(domain_predicate, Predicate::False, "no pair is complete");
            }
            _ => panic!("Expected a collection result"),
        }
    }

    /// Build a `ConverseProducer` wrapping the given input tile and call `get`.
    fn run_converse(input_tile: Tile, input_tiling: Tiling) -> Tile {
        let output_tiling = {
            let (domain, codomain) = input_tiling.split_function_extent().unwrap();
            Tiling::data_function(
                codomain,
                Tiling::data_function(domain.clone(), Tiling::Scalar(domain)),
            )
        };
        let mut producer = ConverseProducer::new(
            ProducerBase::unowned(ConverseProducer::alloc_id(), &output_tiling),
            Box::new(TestTileProducer::new(input_tile, input_tiling)),
            CurryLevel::OUTERMOST,
            output_tiling.empty_at_no_rows(),
        );
        producer.get(producer.tiling().universal_guard())
    }

    fn one_level_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// A released group stays released: a row the input delivers later with that group's
    /// value does not put the group back, and the input is released of that row.
    #[test]
    fn a_released_group_is_not_redelivered_when_a_row_joins_it() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let input_at = |keys: Vec<i64>, values: Vec<i64>| {
            Tile::data_function(
                ColumnValue::Ints(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::False,
                BitSet::new(),
            )
        };
        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let (input, next) = ScriptedProducer::new(input_at(vec![0], vec![10]), one_level_tiling());
        let mut producer = ConverseProducer::new(
            ProducerBase::unowned(ConverseProducer::alloc_id(), &output_tiling),
            Box::new(input),
            CurryLevel::OUTERMOST,
            output_tiling.empty_at_no_rows(),
        );
        let _ = producer.get(producer.tiling().universal_guard());
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::Int(10)),
        )));
        // Row 0 was released upstream; row 1 joins group 10 and row 2 starts group 20.
        *next.borrow_mut() = input_at(vec![1, 2], vec![10, 20]);
        let mut out = producer.get(producer.tiling().universal_guard());
        out.compact();
        let Tile::DataFunction { domain, .. } = &out else {
            panic!("converse yields a collection: {out:?}")
        };
        assert_eq!(domain, &ColumnValue::Ints(vec![20]), "{out:?}");
        // The release of group 10 reached `release_impl` before row 1 arrived, so the pull
        // that first holds row 1 is what releases it, and row 2's group is still live.
        let upstream = producer.input.obsolete_guard();
        assert!(
            upstream.covers_path(&[Value::Int(1)]) && !upstream.covers_path(&[Value::Int(2)]),
            "{upstream:?}"
        );
    }

    /// Rows `1 ↦ [0 ↦ 10, 1 ↦ 10, 2 ↦ 20]` and `2 ↦ [0 ↦ 10]`, both complete, over `Int`s.
    fn two_rows() -> (Tile, Tiling) {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::Ints(vec![0, 1, 2, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 10, 20, 10]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        (tile, tiling)
    }

    fn nested_converse() -> ConverseProducer {
        let (tile, tiling) = two_rows();
        let int = || Extent::Base(BaseType::Int);
        let output_tiling = Tiling::data_function(
            int(),
            Tiling::data_function(int(), Tiling::data_function(int(), Tiling::Scalar(int()))),
        );
        ConverseProducer::new(
            ProducerBase::unowned(ConverseProducer::alloc_id(), &output_tiling),
            Box::new(TestTileProducer::new(tile, tiling)),
            CurryLevel::new(1),
            output_tiling
                .values_at(CurryLevel::new(1))
                .empty_at_no_rows(),
        )
    }

    fn nested_map_domain() -> MapDomainProducer {
        let (tile, tiling) = two_rows();
        MapDomainProducer {
            base: ProducerBase::unowned(MapDomainProducer::alloc_id(), &tiling),
            input: Box::new(TestTileProducer::new(tile, tiling)),
            level: CurryLevel::new(1),
        }
    }

    /// A nested `MapDomain` replaces each row's values with that row's keys, and leaves the
    /// standing level as it was.
    #[test]
    fn a_nested_map_domain_replaces_each_rows_values_by_its_keys() {
        let mut map = nested_map_domain();
        let out = map.get(map.tiling().universal_guard());
        let Tile::DataFunction {
            domain, codomain, ..
        } = &out
        else {
            panic!("expected a collection: {out:?}")
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 2]));
        let Tile::DataFunction {
            row_starts,
            codomain: values,
            ..
        } = codomain.as_ref()
        else {
            panic!("expected a collection of collections: {out:?}")
        };
        assert_eq!(*row_starts, vec![0, 3]);
        assert_eq!(
            **values,
            Tile::Scalar(ColumnValue::Ints(vec![0, 1, 2, 0])),
            "{out:?}"
        );
    }

    /// A nested `MapDomain` keeps its own level's keys as well as the standing one's (two
    /// standing levels, `through_standing_levels`), so a release of inner keys reaches the
    /// input as those keys under every row.
    #[test]
    fn a_nested_map_domain_releases_its_own_keys_to_its_input() {
        let mut map = nested_map_domain();
        map.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::Int(0)))),
        ))));
        let upstream = map.input.obsolete_guard();
        assert!(
            upstream.covers_path(&[Value::Int(1), Value::Int(0)]),
            "{upstream:?}"
        );
        assert!(
            upstream.covers_path(&[Value::Int(2), Value::Int(0)]),
            "{upstream:?}"
        );
        assert!(
            !upstream.covers_path(&[Value::Int(1), Value::Int(1)]),
            "{upstream:?}"
        );
    }

    /// A nested `Converse` keeps only the standing level's keys (one standing level,
    /// `through_standing_levels`): a release of a whole enclosing row reaches the input as
    /// that row.
    #[test]
    fn a_nested_converse_releases_a_whole_enclosing_row_to_its_input() {
        let mut converse = nested_converse();
        converse.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::Int(1)),
        )));
        let upstream = converse.input.obsolete_guard();
        assert!(upstream.covers_path(&[Value::Int(1)]), "{upstream:?}");
        assert!(!upstream.covers_path(&[Value::Int(2)]), "{upstream:?}");
    }

    /// A release beneath a nested `Converse`'s standing level names input rows only through
    /// the groups it rebuilt there, which it cannot release yet, and says so.
    #[test]
    #[should_panic(expected = "a nested Converse cannot yet release part of a row's inversion")]
    fn a_nested_converse_refuses_a_release_beneath_its_standing_level() {
        let mut converse = nested_converse();
        converse.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Domain(Predicate::point(Value::Int(10)))),
        ))));
    }

    /// A converse beneath a standing level inverts each enclosing row's collection on its
    /// own: row `1 = {0→10, 1→10, 2→20}` and row `2 = {0→10}` keep separate groups, though
    /// both hold the value 10. Built through [`Converse::new_at`], so the output tiling is the
    /// one it derives.
    #[test]
    fn a_nested_converse_inverts_each_row_on_its_own() {
        let input_tiling = Tiling::data_function(Extent::Base(BaseType::Int), one_level_tiling());
        let input_tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::Ints(vec![0, 1, 2, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 10, 20, 10]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let mut converse = Converse::new_at(
            Box::new(Constant::collection(input_tile, input_tiling)),
            CurryLevel::new(1),
        );
        let int = || Extent::Base(BaseType::Int);
        assert_eq!(
            *converse.tiling(),
            Tiling::data_function(
                int(),
                Tiling::data_function(int(), Tiling::data_function(int(), Tiling::Scalar(int()))),
            ),
            "the standing level stays, and each row's values become its keys"
        );
        let out_tiling = converse.tiling().clone();
        let mut scheduler = Scheduler::new();
        let mut producer = converse.subscribe(
            out_tiling.universal_guard(),
            Box::new(|| {}),
            &mut scheduler,
        );
        let out = producer.get(out_tiling.universal_guard());
        let groups: Vec<(Value, Value, Value)> = out
            .paths_at(CurryLevel::new(2))
            .into_iter()
            .map(|p| (p[0].clone(), p[1].clone(), p[2].clone()))
            .collect();
        assert_eq!(
            groups,
            vec![
                (Value::Int(1), Value::Int(10), Value::Int(0)),
                (Value::Int(1), Value::Int(10), Value::Int(1)),
                (Value::Int(1), Value::Int(20), Value::Int(2)),
                (Value::Int(2), Value::Int(10), Value::Int(0)),
            ],
            "{out:?}"
        );
    }

    /// Basic converse: `{0→10, 1→20, 2→10}` groups by codomain value.
    /// Expected output: domain1=[10,20], each group lists the domain values that map to it.
    #[test]
    fn converse_producer_basic_grouping() {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 10]))),
            Predicate::True,
            BitSet::new(),
        );
        let result = run_converse(tile, one_level_tiling());
        let Tile::DataFunction {
            domain,
            codomain: groups,
            domain_predicate,
            deleted,
            ..
        } = result
        else {
            panic!("expected a collection");
        };
        // Two distinct codomain values: 10 and 20.
        assert_eq!(domain, ColumnValue::Ints(vec![10, 20]));
        let Tile::DataFunction {
            row_starts,
            domain: inner_keys,
            deleted: inner_deleted,
            ..
        } = groups.as_ref()
        else {
            panic!("expected a collection of collections");
        };
        // Group for 10 starts at 0 (rows 0 and 2 map to 10); group for 20 starts at 2.
        assert_eq!(*row_starts, vec![0, 2]);
        // The inner level is sorted by codomain key: [0, 2] for key 10, then [1] for 20.
        assert_eq!(*inner_keys, ColumnValue::Ints(vec![0, 2, 1]));
        assert_eq!(domain_predicate, Predicate::True);
        assert!(
            deleted.is_empty() && inner_deleted.is_empty(),
            "no deleted entries expected"
        );
    }

    /// Converse with no deleted entries on a single-entry input is a trivial sanity check.
    #[test]
    fn converse_producer_single_entry_no_deleted() {
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![42]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
            Predicate::True,
            BitSet::new(),
        );
        let result = run_converse(tile, one_level_tiling());
        let Tile::DataFunction {
            codomain: groups, ..
        } = result
        else {
            panic!("expected a collection");
        };
        let Tile::DataFunction { deleted, .. } = groups.as_ref() else {
            panic!("expected a collection of collections");
        };
        assert!(deleted.is_empty());
    }

    /// Deleted bit on an input row must appear at the correct remapped position in the output.
    ///
    /// Input: domain=[0,1,2], codomain=[20,10,20], deleted={0}  (row 0 is logically removed).
    /// Sort order by codomain: [1(→10), 0(→20), 2(→20)].
    /// After remapping, input row 0 lands at output position 1, so output deleted={1}.
    #[test]
    fn converse_producer_deleted_remapped_through_sort() {
        let mut input_deleted = BitSet::new();
        input_deleted.insert(0); // row 0 is logically removed
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![20, 10, 20]))),
            Predicate::True,
            input_deleted,
        );
        let result = run_converse(tile, one_level_tiling());
        let Tile::DataFunction {
            codomain: groups, ..
        } = result
        else {
            panic!("expected a collection");
        };
        let Tile::DataFunction {
            domain, deleted, ..
        } = groups.as_ref()
        else {
            panic!("expected a collection of collections");
        };
        // Sorted order: row 1 (key 10) first, then row 0 (key 20), then row 2 (key 20).
        // Output position 1 holds original row 0, which was deleted.
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 0, 2]));
        let mut expected = BitSet::new();
        expected.insert(1);
        assert_eq!(*deleted, expected);
    }

    /// Multiple deleted rows are all remapped correctly.
    ///
    /// Input: domain=[0,1,2,3], codomain=[30,10,20,10], deleted={1,3}.
    /// Sort order by codomain: [1(10), 3(10), 2(20), 0(30)].
    /// Input rows 1 and 3 land at output positions 0 and 1, so output deleted={0,1}.
    #[test]
    fn converse_producer_multiple_deleted_remapped() {
        let mut input_deleted = BitSet::new();
        input_deleted.insert(1);
        input_deleted.insert(3);
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![0, 1, 2, 3]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![30, 10, 20, 10]))),
            Predicate::True,
            input_deleted,
        );
        let result = run_converse(tile, one_level_tiling());
        let Tile::DataFunction {
            codomain: groups, ..
        } = result
        else {
            panic!("expected a collection");
        };
        let Tile::DataFunction { deleted, .. } = groups.as_ref() else {
            panic!("expected a collection of collections");
        };
        let mut expected = BitSet::new();
        expected.insert(0);
        expected.insert(1);
        assert_eq!(*deleted, expected);
    }
    /// [`Product`] takes each row's group from the inner tile, so rows with
    /// **different numbers of keys** pair correctly — which is the case a shared inner
    /// side cannot express, its every group being one domain.
    ///
    /// Rows `100` and `200` hold collections of two and three keys, so the output is
    /// `(100,0) (100,1) ‖ (200,0) (200,1) (200,2)`: five pairs in two groups.
    #[test]
    fn product_per_row_takes_each_row_s_own_domain() {
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 200]))),
            Predicate::True,
            BitSet::new(),
        );
        let outer_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        // Two rows, holding collections of two and three keys.
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::from_uints(vec![0, 1, 0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8, 9, 10, 11]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let out_tiling = outer_tiling.append_level(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::UInt)),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction { codomain, .. } = &out else {
            panic!("Product tiles as a collection of collections, got {out:?}")
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain: pairs,
            ..
        } = codomain.as_ref()
        else {
            panic!("the paired level is a collection")
        };
        assert_eq!(
            row_starts,
            &vec![0, 2],
            "the groups are the rows' own, two keys then three"
        );
        assert_eq!(domain, &ColumnValue::from_uints(vec![0, 1, 0, 1, 2]));
        let Tile::Scalar(ColumnValue::Records(fields)) = pairs.as_ref() else {
            panic!("a pair is a record of the row's value and its key")
        };
        assert_eq!(
            fields[&tuple_field(0)],
            ColumnValue::Ints(vec![100, 100, 200, 200, 200]),
            "each row's value repeats across its own group"
        );
        assert_eq!(
            fields[&tuple_field(1)],
            ColumnValue::from_uints(vec![0, 1, 0, 1, 2])
        );
    }

    /// [`Product::per_row_values_at`] pairs each row with the **values** of its own
    /// collection, keyed by that collection's keys: the rows of
    /// [`product_per_row_takes_each_row_s_own_domain`] give the same five-pair groups, with
    /// the second components `7 8 ‖ 9 10 11` rather than the keys.
    #[test]
    fn product_per_row_values_pairs_each_row_with_its_own_values() {
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 200]))),
            Predicate::True,
            BitSet::new(),
        );
        let outer_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::from_uints(vec![0, 1, 0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8, 9, 10, 11]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let mut product = Product::per_row_values_at(
            Box::new(Constant::collection(outer, outer_tiling)),
            Box::new(Constant::collection(inner, inner_tiling)),
            CurryLevel::new(1),
        );
        let out_tiling = product.tiling().clone();
        let mut scheduler = Scheduler::new();
        let mut producer = product.subscribe(
            out_tiling.universal_guard(),
            Box::new(|| {}),
            &mut scheduler,
        );
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction { codomain, .. } = &out else {
            panic!("Product tiles as a collection of collections, got {out:?}")
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain: pairs,
            ..
        } = codomain.as_ref()
        else {
            panic!("the paired level is a collection")
        };
        assert_eq!(row_starts, &vec![0, 2]);
        assert_eq!(
            domain,
            &ColumnValue::from_uints(vec![0, 1, 0, 1, 2]),
            "the paired level keeps each row's own keys"
        );
        let Tile::Scalar(ColumnValue::Records(fields)) = pairs.as_ref() else {
            panic!("a pair is a record of the row's value and a value of its collection")
        };
        assert_eq!(
            fields[&tuple_field(0)],
            ColumnValue::Ints(vec![100, 100, 200, 200, 200])
        );
        assert_eq!(
            fields[&tuple_field(1)],
            ColumnValue::Ints(vec![7, 8, 9, 10, 11])
        );
    }

    /// A release of some of a row's pairs names keys of that row's inner collection, so it
    /// reaches the inner side, and leaves the outer row standing.
    #[test]
    fn product_per_row_releases_part_of_a_row_to_the_inner_side() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let outer_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100]))),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 8]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let out_tiling = outer_tiling.append_level(
            uint(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), uint()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let _ = producer.get(out_tiling.universal_guard());
        let first_pair = TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Function(FunctionGuard::Domain(Predicate::qualified(
                Predicate::point(Value::UInt(0)),
                Predicate::point(Value::UInt(0)),
            ))),
        )));
        producer.release(first_pair.clone());
        assert_eq!(*producer.inner.obsolete_guard(), first_pair);
        assert!(
            producer.outer.obsolete_guard().is_empty(),
            "the row still has a pair: {:?}",
            producer.outer.obsolete_guard()
        );
    }

    /// Beneath standing levels a path is complete where both sides call it complete, each
    /// counting what the levels above say. The outer side settles the standing key 0 at the
    /// outermost level and states nothing one level down; the inner side settles `[0, 0]` one
    /// level down. Both are complete at `[0, 0]`, so the output says so there.
    #[test]
    fn product_beneath_standing_levels_reads_each_sides_closure() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let single = |codomain: Tile, stated: Predicate| {
            Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(codomain),
                stated,
                BitSet::new(),
            )
        };
        let outer_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
        );
        let outer = single(
            single(
                single(Tile::Scalar(ColumnValue::Ints(vec![100])), Predicate::True),
                Predicate::False,
            ),
            Predicate::True,
        );
        let inner_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
            ),
        );
        let inner = single(
            single(
                single(
                    single(Tile::Scalar(ColumnValue::Ints(vec![7])), Predicate::True),
                    Predicate::True,
                ),
                Predicate::True,
            ),
            Predicate::False,
        );
        let out_tiling = outer_tiling.append_level(
            uint(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), uint()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::new(2),
            empty_level: out_tiling.values_at(CurryLevel::new(2)).empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction {
            domain_predicate, ..
        } = out.values_at(CurryLevel::new(1))
        else {
            panic!("a standing level, got {out:?}")
        };
        assert!(
            domain_predicate.contains_path(&[Value::UInt(0), Value::UInt(0)]),
            "both sides are complete at [0, 0]: {out:?}"
        );
    }

    /// A row whose inner collection is still arriving is paired with what it holds and not
    /// called complete: the outer side calls row 0 complete, but the inner side has delivered
    /// one key of row 0's collection and calls nothing complete, so more of it may follow.
    #[test]
    fn product_per_row_keeps_a_row_open_while_its_inner_collection_grows() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let outer_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100]))),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = outer_tiling.append_level(
            uint(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), uint()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let out = producer.get(out_tiling.universal_guard());
        assert!(
            !out.is_empty(),
            "the key row 0 holds is paired already: {out:?}"
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &out
        else {
            panic!("Product tiles as a collection, got {out:?}")
        };
        assert!(
            !domain_predicate.contains(&Value::UInt(0)),
            "row 0's inner collection is still arriving, so row 0 is not complete: \
             {domain_predicate:?}"
        );
    }

    /// A row is complete only where its inner side calls the row complete, not where it calls
    /// the keys it holds complete: the inner side has settled the one key of row 0's collection
    /// it delivered, and row 0 may still gain another.
    #[test]
    fn product_per_row_keeps_a_row_open_whose_delivered_keys_are_settled() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let outer_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100]))),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
                Predicate::qualified(
                    Predicate::point(Value::UInt(0)),
                    Predicate::point(Value::UInt(0)),
                ),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = outer_tiling.append_level(
            uint(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), uint()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let out = producer.get(out_tiling.universal_guard());
        assert!(
            !out.is_empty(),
            "the key row 0 holds is paired already: {out:?}"
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &out
        else {
            panic!("Product tiles as a collection, got {out:?}")
        };
        assert!(
            !domain_predicate.contains(&Value::UInt(0)),
            "row 0's inner collection is still arriving, so row 0 is not complete: \
             {domain_predicate:?}"
        );
    }
}

/// `Filter` as a comprehension's guard uses it: `[x for x in xs if p(x)]` keeps the rows of the
/// stream whose boolean answer, read from a predicate stream over the same keys, is true. A
/// worker pulls both at one morsel.
#[cfg(test)]
mod filter_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, int_entries, ints_by_position, keys_between,
    };
    use bit_set::BitSet;

    const ROWS: u64 = 8;

    /// `[x for x in xs if x % 2 == 0]` over `xs = [0, 10, 20, …]`, the predicate stream holding
    /// the answer at each position: even positions pass.
    fn keep_even_positions() -> (FilterProducer, GuardLog, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| 10 * i).collect();
        let in_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let answers = Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::Scalar(ColumnValue::Bools(
                (0..ROWS).map(|i| i % 2 == 0).collect(),
            ))),
            Predicate::True,
            BitSet::new(),
        );
        let pred_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Bool)),
        );
        let (input, input_pulled, _) =
            ProjectionSpy::new(ints_by_position(&values, true), in_tiling.clone());
        let (predicate, predicate_pulled, _) = ProjectionSpy::new(answers, pred_tiling);
        (
            FilterProducer {
                base: ProducerBase::unowned(FilterProducer::alloc_id(), &in_tiling),
                input: Box::new(input),
                predicate: Box::new(predicate),
                level: CurryLevel::OUTERMOST,
            },
            input_pulled,
            predicate_pulled,
        )
    }

    #[test]
    fn a_filtered_morsel_keeps_the_passing_rows_and_pulls_both_sides_at_it() {
        let (mut filter, input_pulled, predicate_pulled) = keep_even_positions();
        let morsel = filter.get(keys_between(2, 5));
        assert_eq!(int_entries(&morsel), [(2, 20), (4, 40)]);
        assert_eq!(*input_pulled.borrow(), [keys_between(2, 5)]);
        assert_eq!(*predicate_pulled.borrow(), [keys_between(2, 5)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &morsel
        else {
            panic!("a collection")
        };
        let TileGuard::Function(FunctionGuard::Domain(stated)) = keys_between(2, 5) else {
            unreachable!("a morsel is a domain guard")
        };
        assert_eq!(*domain_predicate, stated, "complete over the morsel");
    }

    #[test]
    fn a_filtered_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 3), keys_between(5, 40)] {
            assert_conforms(|| Box::new(keep_even_positions().0), guard);
        }
    }

    /// A rejected row is in no consumer's tile, so no guard of the consumer's names it. The
    /// tile states the region it decided, rejected rows included, and a consumer releases that
    /// region, so the input and the predicate both release the rejected positions with it.
    #[test]
    fn releasing_the_stated_region_releases_the_rejected_rows() {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| 10 * i).collect();
        let (mut filter, _, _) = keep_even_positions();
        let (input, _, input_released) = ProjectionSpy::new(
            ints_by_position(&values, true),
            filter.input.tiling().clone(),
        );
        let answers = Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::Scalar(ColumnValue::Bools(
                (0..ROWS).map(|i| i % 2 == 0).collect(),
            ))),
            Predicate::True,
            BitSet::new(),
        );
        let (predicate, _, predicate_released) =
            ProjectionSpy::new(answers, filter.predicate.tiling().clone());
        filter.input = Box::new(input);
        filter.predicate = Box::new(predicate);
        let kept = filter.get(keys_between(0, ROWS - 1));
        assert_eq!(int_entries(&kept), [(0, 0), (2, 20), (4, 40), (6, 60)]);
        filter.release(kept.to_guard());
        let everything = || keys_between(0, ROWS - 1);
        assert_eq!(*input_released.borrow(), [everything()]);
        assert_eq!(*predicate_released.borrow(), [everything()]);
    }

    /// `[x for x in (evens ++ odds) if p(x)]` while the odd arm has decided only `0..=3`: the
    /// union's tile holds the even rows and the odd rows so far, and states `0..=3` complete.
    /// The predicate answers every position. The filter answers for the rows held and states
    /// only `0..=3` complete. The consumer releases what it holds, `0..=3` and row 6, and the
    /// rows that arrive afterwards are filtered by the predicate's answers for them.
    #[test]
    fn rows_a_union_delivers_late_are_filtered_and_complete_only_where_the_input_is() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;

        let column = |keys: Vec<u64>, decided: Predicate, value: fn(u64) -> Value| {
            let values = keys.iter().map(|&key| value(key)).collect::<Vec<_>>();
            let codomain = match values.first() {
                Some(Value::Bool(_)) => ColumnValue::Bools(
                    values
                        .iter()
                        .map(|v| matches!(v, Value::Bool(true)))
                        .collect(),
                ),
                _ => ColumnValue::Ints(
                    values
                        .iter()
                        .map(|v| match v {
                            Value::Int(i) => *i,
                            other => panic!("an int or a bool, got {other:?}"),
                        })
                        .collect(),
                ),
            };
            Tile::data_function(
                ColumnValue::from_uints(keys),
                Box::new(Tile::Scalar(codomain)),
                decided,
                BitSet::new(),
            )
        };
        let value = |key: u64| Value::Int(10 * key as i64);
        // Positions 1, 4 and 7 fail.
        let answer = |key: u64| Value::Bool(key % 3 != 1);
        let TileGuard::Function(FunctionGuard::Domain(through_3)) = keys_between(0, 3) else {
            unreachable!("keys_between names a key region")
        };
        let TileGuard::Function(FunctionGuard::Domain(from_4)) = keys_between(4, ROWS - 1) else {
            unreachable!("keys_between names a key region")
        };

        let in_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let pred_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Bool)),
        );
        let (input, input_cell) = ScriptedProducer::new(
            column(vec![0, 1, 2, 3, 4, 6], through_3.clone(), value),
            in_tiling.clone(),
        );
        let (predicate, predicate_cell) = ScriptedProducer::new(
            column((0..ROWS).collect(), Predicate::True, answer),
            pred_tiling,
        );
        let mut filter = FilterProducer {
            base: ProducerBase::unowned(FilterProducer::alloc_id(), &in_tiling),
            input: Box::new(input),
            predicate: Box::new(predicate),
            level: CurryLevel::OUTERMOST,
        };

        let first = filter.get(keys_between(0, ROWS - 1));
        assert_eq!(int_entries(&first), [(0, 0), (2, 20), (3, 30), (6, 60)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &first
        else {
            panic!("a collection, got {first:?}")
        };
        assert_eq!(
            *domain_predicate, through_3,
            "positions 5 and 7 have not arrived, so only the input's decided prefix is complete"
        );

        filter.release(first.to_guard());
        *input_cell.borrow_mut() = column(vec![4, 5, 7], from_4.clone(), value);
        *predicate_cell.borrow_mut() = column(vec![4, 5, 7], Predicate::True, answer);
        let second = filter.get(keys_between(0, ROWS - 1));
        assert_eq!(int_entries(&second), [(5, 50)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &second
        else {
            panic!("a collection, got {second:?}")
        };
        assert_eq!(*domain_predicate, from_4);
    }

    #[test]
    fn nothing_filters_nothing() {
        let (mut filter, input_pulled, predicate_pulled) = keep_even_positions();
        let nothing = filter.tiling().empty_guard();
        assert_eq!(filter.get(nothing), filter.tiling().empty_tile());
        assert!(input_pulled.borrow().is_empty() && predicate_pulled.borrow().is_empty());
    }
}

/// `Restrict` as the head of a filtered iteration uses it: `iterate ▷ (p ▷ restrict)` keeps the
/// positions a predicate stream passes, and a worker pulls the predicate at one morsel.
#[cfg(test)]
mod restrict_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, keys_between,
    };
    use bit_set::BitSet;

    const ROWS: u64 = 8;

    /// The positions whose predicate answer is true: every third position.
    fn every_third() -> (RestrictProducer, GuardLog) {
        let answers = Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::Scalar(ColumnValue::Bools(
                (0..ROWS).map(|i| i % 3 == 0).collect(),
            ))),
            Predicate::True,
            BitSet::new(),
        );
        let pred_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Bool)),
        );
        let out = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::uint_range(ROWS)),
        );
        let (predicate, pulled, _) = ProjectionSpy::new(answers, pred_tiling);
        (
            RestrictProducer {
                base: ProducerBase::unowned(RestrictProducer::alloc_id(), &out),
                predicate: Box::new(predicate),
            },
            pulled,
        )
    }

    /// The keys a consumer sees: those the tile does not mark deleted.
    fn live_keys(tile: &Tile) -> Vec<u64> {
        let Tile::DataFunction {
            domain: ColumnValue::UInts(keys),
            deleted,
            ..
        } = tile
        else {
            panic!("a collection of positions, got {tile:?}")
        };
        keys.iter()
            .enumerate()
            .filter(|(row, _)| !deleted.contains(*row))
            .map(|(_, key)| *key)
            .collect()
    }

    #[test]
    fn a_restricted_morsel_keeps_the_passing_positions_and_pulls_the_predicate_at_it() {
        let (mut restrict, pulled) = every_third();
        let morsel = restrict.get(keys_between(2, 7));
        assert_eq!(live_keys(&morsel), [3, 6]);
        assert_eq!(*pulled.borrow(), [keys_between(2, 7)]);
    }

    #[test]
    fn a_restricted_morsel_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 3), keys_between(4, 30)] {
            assert_conforms(|| Box::new(every_third().0), guard);
        }
    }

    #[test]
    fn nothing_restricts_nothing() {
        let (mut restrict, pulled) = every_third();
        let nothing = restrict.tiling().empty_guard();
        assert_eq!(restrict.get(nothing), restrict.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}

/// `MapDomain` as a loop over a grouping reads it: the values of a collection are replaced by its
/// keys, at the level the loop iterates, while the keys above stand. A worker pulls the groups
/// it owns.
#[cfg(test)]
mod map_domain_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, ints_by_position, keys_between,
    };
    use bit_set::BitSet;

    const ROWS: u64 = 6;

    /// A stream of positions holding `0, 10, 20, …`, whose values are replaced by the positions.
    fn keys_of_a_stream() -> (MapDomainProducer, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| 10 * i).collect();
        let tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let out = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::uint_range(ROWS)),
        );
        let (input, pulled, _) = ProjectionSpy::new(ints_by_position(&values, true), tiling);
        (
            MapDomainProducer {
                base: ProducerBase::unowned(MapDomainProducer::alloc_id(), &out),
                input: Box::new(input),
                level: CurryLevel::OUTERMOST,
            },
            pulled,
        )
    }

    #[test]
    fn a_stream_keeps_its_morsel_and_takes_its_keys_as_values() {
        let (mut keys, pulled) = keys_of_a_stream();
        let morsel = keys.get(keys_between(1, 3));
        let Tile::DataFunction {
            domain, codomain, ..
        } = &morsel
        else {
            panic!("a collection")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![1, 2, 3]));
        assert_eq!(**codomain, Tile::Scalar(ColumnValue::UInts(vec![1, 2, 3])));
        assert_eq!(*pulled.borrow(), [keys_between(1, 3)]);
    }

    /// The groups a `Converse` makes, each member listed by the key it stands at: the outer keys
    /// are the groups, which the projection names, and the inner values become the inner keys.
    fn members_of_groups() -> (MapDomainProducer, GuardLog) {
        let groups = Tile::data_function(
            ColumnValue::Ints(vec![1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 2, 3],
                ColumnValue::UInts(vec![0, 2, 1, 3]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 6, 7, 8]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(4),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let out = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(Extent::uint_range(4), Tiling::Scalar(Extent::uint_range(4))),
        );
        let (input, pulled, _) = ProjectionSpy::new(groups, in_tiling);
        (
            MapDomainProducer {
                base: ProducerBase::unowned(MapDomainProducer::alloc_id(), &out),
                input: Box::new(input),
                level: CurryLevel::new(1),
            },
            pulled,
        )
    }

    fn groups_one_and_three() -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::Int(1)).union(&Predicate::point(Value::Int(3))),
        ))
    }

    #[test]
    fn a_projection_of_groups_reaches_the_groups() {
        let (mut members, pulled) = members_of_groups();
        let answer = members.get(groups_one_and_three());
        let Tile::DataFunction { domain, .. } = &answer else {
            panic!("a collection")
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![1, 3]));
        assert_eq!(*pulled.borrow(), [groups_one_and_three()]);
    }

    #[test]
    fn the_projections_are_the_whole_pull_cut_to_them() {
        assert_conforms(|| Box::new(keys_of_a_stream().0), keys_between(2, 4));
        assert_conforms(|| Box::new(members_of_groups().0), groups_one_and_three());
    }

    #[test]
    fn nothing_maps_nothing() {
        let (mut keys, pulled) = keys_of_a_stream();
        let nothing = keys.tiling().empty_guard();
        assert_eq!(keys.get(nothing), keys.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}

/// `Uncurry` as a join reads a grouping: `K ⤇ (D ⤇ V)` becomes a collection keyed by the pairs
/// `(k, d)`. A worker's morsel names pairs, and the first component of each is a key of the
/// grouping.
#[cfg(test)]
mod uncurry_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms,
    };
    use bit_set::BitSet;

    /// Groups 1, 2 and 3 holding members `{0, 2}`, `{1}` and `{3}` with values 10 to 40.
    fn paired_groups() -> (UncurryProducer, GuardLog) {
        let groups = Tile::data_function(
            ColumnValue::Ints(vec![1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 2, 3],
                ColumnValue::UInts(vec![0, 2, 1, 3]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 30, 20, 40]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(4),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let out = Tiling::data_function(
            Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::Int)),
                    (tuple_field(1), Extent::uint_range(4)),
                ]
                .into_iter()
                .collect(),
            ),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (input, pulled, _) = ProjectionSpy::new(groups, in_tiling);
        (
            UncurryProducer {
                base: ProducerBase::unowned(UncurryProducer::alloc_id(), &out),
                input: Box::new(input),
                level: CurryLevel::OUTERMOST,
                empty_pair: out.empty_at_no_rows(),
            },
            pulled,
        )
    }

    /// The pairs whose first component `first` admits and whose second `second` admits.
    fn pairs(first: Predicate, second: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::Record(
            [(tuple_field(0), first), (tuple_field(1), second)]
                .into_iter()
                .collect(),
        )))
    }

    fn groups_one_and_three() -> Predicate {
        Predicate::point(Value::Int(1)).union(&Predicate::point(Value::Int(3)))
    }

    fn pair_count(tile: &Tile) -> usize {
        let Tile::DataFunction { domain, .. } = tile else {
            panic!("a collection, got {tile:?}")
        };
        domain.len()
    }

    /// A morsel of pairs headed by groups 1 and 3 reads those groups of the grouping alone, and
    /// holds the pairs they head: `(1, 0)`, `(1, 2)` and `(3, 3)`.
    #[test]
    fn a_morsel_of_pairs_reads_the_groups_that_head_them() {
        let (mut uncurry, pulled) = paired_groups();
        let guard = pairs(groups_one_and_three(), Predicate::True);
        let morsel = uncurry.get(guard);
        assert_eq!(pair_count(&morsel), 3);
        assert_eq!(
            *pulled.borrow(),
            [TileGuard::Function(FunctionGuard::Domain(
                groups_one_and_three()
            ))]
        );
    }

    /// A morsel that names the second component only cannot say which groups it needs, so the
    /// grouping is read whole and the pairs are cut after.
    #[test]
    fn a_morsel_of_second_components_reads_the_grouping_whole_and_cuts_the_pairs() {
        let (mut uncurry, pulled) = paired_groups();
        let guard = pairs(Predicate::True, Predicate::point(Value::UInt(1)));
        let morsel = uncurry.get(guard);
        assert_eq!(pair_count(&morsel), 1, "only the pair (2, 1)");
        assert_eq!(*pulled.borrow(), [uncurry.input.tiling().universal_guard()]);
    }

    #[test]
    fn a_morsel_of_pairs_is_the_whole_pull_cut_to_it() {
        for guard in [
            pairs(groups_one_and_three(), Predicate::True),
            pairs(Predicate::True, Predicate::point(Value::UInt(1))),
            pairs(
                Predicate::point(Value::Int(1)),
                Predicate::point(Value::UInt(2)),
            ),
        ] {
            assert_conforms(|| Box::new(paired_groups().0), guard);
        }
    }

    #[test]
    fn nothing_pairs_nothing() {
        let (mut uncurry, pulled) = paired_groups();
        let nothing = uncurry.tiling().empty_guard();
        assert_eq!(uncurry.get(nothing), uncurry.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}

/// `Product` as a correlated inner comprehension uses it: `[(x, y) for x in xs for y in ys_of(x)]`
/// pairs each row of `xs` with the keys of the collection that row holds. A worker owns a range
/// of the rows.
#[cfg(test)]
mod product_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, ints_by_position, keys_between,
    };
    use bit_set::BitSet;

    /// Four rows `100, 200, 300, 400`, row `i` holding a collection over the keys `0..=i`.
    fn rows_and_their_keys() -> (ProductProducer, GuardLog, GuardLog) {
        let outer = ints_by_position(&[100, 200, 300, 400], true);
        let outer_tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let sizes = [1usize, 2, 3, 4];
        let starts: Vec<usize> = sizes
            .iter()
            .scan(0, |at, n| {
                let start = *at;
                *at += n;
                Some(start)
            })
            .collect();
        let keys: Vec<u64> = sizes.iter().flat_map(|n| 0..*n as u64).collect();
        let values: Vec<i64> = (0..keys.len() as i64).collect();
        let inner = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2, 3]),
            Box::new(Tile::grouped(
                starts,
                ColumnValue::UInts(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let inner_tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::data_function(
                Extent::uint_range(4),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let out_tiling = outer_tiling.append_level(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::uint_range(4)),
            ]))),
        );
        let (outer, outer_pulled, _) = ProjectionSpy::new(outer, outer_tiling);
        let (inner, inner_pulled, _) = ProjectionSpy::new(inner, inner_tiling);
        (
            ProductProducer {
                base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
                outer: Box::new(outer),
                inner: Box::new(inner),
                level: CurryLevel::OUTERMOST,
                empty_level: out_tiling.empty_at_no_rows(),
                pair: out_tiling.deepest_values().clone(),
                second: Paired::Key,
            },
            outer_pulled,
            inner_pulled,
        )
    }

    #[test]
    fn a_range_of_rows_pulls_both_sides_at_it() {
        let (mut product, outer_pulled, inner_pulled) = rows_and_their_keys();
        let rows = product.get(keys_between(1, 2));
        let Tile::DataFunction {
            domain, codomain, ..
        } = &rows
        else {
            panic!("a collection of rows")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![1, 2]));
        let Tile::DataFunction { domain: keys, .. } = codomain.as_ref() else {
            panic!("a collection per row")
        };
        assert_eq!(keys.len(), 2 + 3, "rows 1 and 2 hold two and three keys");
        assert_eq!(*outer_pulled.borrow(), [keys_between(1, 2)]);
        assert_eq!(*inner_pulled.borrow(), [keys_between(1, 2)]);
    }

    #[test]
    fn a_range_of_rows_is_the_whole_pull_cut_to_it() {
        for guard in [keys_between(0, 1), keys_between(3, 9)] {
            assert_conforms(|| Box::new(rows_and_their_keys().0), guard);
        }
    }

    /// An outer row whose inner collection has not arrived has no pairs yet and is not in the
    /// output, and the output states complete only the rows both sides settle: the inner side
    /// may still deliver rows 1 and 2, and a statement covering them would have a consumer
    /// release them before they exist.
    #[test]
    fn a_row_with_no_inner_collection_yet_is_not_stated_complete() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let outer_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let outer = ints_by_position(&[100, 200, 300], true);
        let inner_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::exactly(&[Value::UInt(0)]),
            BitSet::new(),
        );
        let out_tiling = outer_tiling.append_level(
            uint(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), uint()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::unowned(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(ProjectionSpy::new(outer, outer_tiling).0),
            inner: Box::new(ProjectionSpy::new(inner, inner_tiling).0),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            second: Paired::Key,
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction {
            domain,
            domain_predicate,
            ..
        } = &out
        else {
            panic!("Product tiles as a collection, got {out:?}")
        };
        assert_eq!(
            *domain,
            ColumnValue::UInts(vec![0]),
            "rows 1 and 2 have no pairs yet"
        );
        for withheld in [1, 2] {
            assert!(
                !domain_predicate.contains(&Value::UInt(withheld)),
                "row {withheld} may still be paired, so it is not complete: {domain_predicate:?}"
            );
        }
    }

    #[test]
    fn nothing_pairs_nothing() {
        let (mut product, outer_pulled, inner_pulled) = rows_and_their_keys();
        let nothing = product.tiling().empty_guard();
        assert_eq!(product.get(nothing), product.tiling().empty_tile());
        assert!(outer_pulled.borrow().is_empty() && inner_pulled.borrow().is_empty());
    }
}

/// `Converse` as the bucketize step of a group-by uses it: the key stream `sales ≫ key` is
/// inverted into the groups `key ⤇ (position ⤇ position)`, and a worker owns a range of groups.
#[cfg(test)]
mod converse_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, ints_by_position, keys_between,
    };
    use bit_set::BitSet;

    const ROWS: u64 = 8;

    /// The group of each position: `1, 2, 1, 3, 2, 1, 3, 2`, so group 1 holds positions
    /// `{0, 2, 5}`, group 2 holds `{1, 4, 7}` and group 3 holds `{3, 6}`.
    const GROUPS: [i64; 8] = [1, 2, 1, 3, 2, 1, 3, 2];

    fn groups_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::uint_range(ROWS)),
            ),
        )
    }

    fn bucketize() -> (ConverseProducer, GuardLog, GuardLog) {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (keys, pulled, released) =
            ProjectionSpy::new(ints_by_position(&GROUPS, true), in_tiling);
        (
            ConverseProducer::new(
                ProducerBase::unowned(ConverseProducer::alloc_id(), &groups_tiling()),
                Box::new(keys),
                CurryLevel::OUTERMOST,
                groups_tiling()
                    .values_at(CurryLevel::OUTERMOST)
                    .empty_at_no_rows(),
            ),
            pulled,
            released,
        )
    }

    fn groups(keys: &[i64]) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(
            keys.iter()
                .map(|k| Predicate::point(Value::Int(*k)))
                .fold(Predicate::False, |all, one| all.union(&one)),
        ))
    }

    /// Each group of `tile` as `(key, members)`, members in position order.
    fn members_by_group(tile: &Tile) -> Vec<(i64, Vec<u64>)> {
        let Tile::DataFunction {
            domain: ColumnValue::Ints(keys),
            codomain,
            ..
        } = tile
        else {
            panic!("groups keyed by integers, got {tile:?}")
        };
        let Tile::DataFunction {
            row_starts,
            domain: ColumnValue::UInts(members),
            ..
        } = codomain.as_ref()
        else {
            panic!("members per group, got {codomain:?}")
        };
        let mut groups: Vec<(i64, Vec<u64>)> = keys
            .iter()
            .enumerate()
            .map(|(group, key)| {
                let end = row_starts.get(group + 1).copied().unwrap_or(members.len());
                let mut held = members[row_starts[group]..end].to_vec();
                held.sort_unstable();
                (*key, held)
            })
            .collect();
        groups.sort();
        groups
    }

    /// A worker's groups: the keys are read from the rows, so the whole key stream is read and
    /// the groups outside the range are cut.
    #[test]
    fn a_range_of_groups_reads_the_whole_key_stream_and_cuts_the_groups() {
        let (mut converse, pulled, _) = bucketize();
        let answer = converse.get(groups(&[1, 3]));
        assert_eq!(
            members_by_group(&answer),
            [(1, vec![0, 2, 5]), (3, vec![3, 6])]
        );
        assert_eq!(
            *pulled.borrow(),
            [converse.input.tiling().universal_guard()]
        );
    }

    /// The consumer releases the groups it took. That frees the rows they hold at the input and
    /// no others, so the next range finds its own rows still there.
    #[test]
    fn releasing_a_range_of_groups_frees_its_rows_and_leaves_the_others() {
        let (mut converse, _, released) = bucketize();
        converse.get(groups(&[1]));
        converse.release(groups(&[1]));
        let freed = released.borrow().clone();
        assert_eq!(freed.len(), 1);
        let TileGuard::Function(FunctionGuard::Domain(rows)) = &freed[0] else {
            panic!("a domain release of the rows, got {freed:?}")
        };
        for row in [0u64, 2, 5] {
            assert!(rows.contains(&Value::UInt(row)), "row {row} is group 1's");
        }
        for row in [1u64, 3, 4, 6, 7] {
            assert!(!rows.contains(&Value::UInt(row)), "row {row} is not");
        }
        let rest = converse.get(groups(&[2, 3]));
        assert_eq!(
            members_by_group(&rest),
            [(2, vec![1, 4, 7]), (3, vec![3, 6])]
        );
    }

    #[test]
    fn a_range_of_groups_is_the_whole_pull_cut_to_it() {
        for guard in [groups(&[1]), groups(&[2, 3]), groups(&[9])] {
            assert_conforms(|| Box::new(bucketize().0), guard);
        }
    }

    /// A group-by whose source varies per enclosing row inverts each row's collection on its
    /// own: the outer keys stand, so the projection of rows reaches the rows.
    #[test]
    fn beneath_a_standing_level_the_projection_reaches_the_enclosing_rows() {
        let rows = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::UInts(vec![0, 1, 2, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![5, 6, 5, 7, 7]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let out = Tiling::data_function(Extent::uint_range(2), groups_tiling());
        let make = || {
            let (input, pulled, _) = ProjectionSpy::new(rows.clone(), in_tiling.clone());
            (
                ConverseProducer::new(
                    ProducerBase::unowned(ConverseProducer::alloc_id(), &out),
                    Box::new(input),
                    CurryLevel::new(1),
                    out.values_at(CurryLevel::new(1)).empty_at_no_rows(),
                ),
                pulled,
            )
        };
        let (mut converse, pulled) = make();
        converse.get(keys_between(1, 1));
        assert_eq!(*pulled.borrow(), [keys_between(1, 1)]);
        assert_conforms(|| Box::new(make().0), keys_between(1, 1));
    }

    #[test]
    fn nothing_inverts_nothing() {
        let (mut converse, pulled, _) = bucketize();
        let nothing = converse.tiling().empty_guard();
        assert_eq!(converse.get(nothing), converse.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}

/// A consuming `Converse` over an input that grows and is released: the rows it holds, what it
/// offers and what reaches the input, against a model of the rows consumed and the groups released.
#[cfg(test)]
mod converse_consuming_tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Rng, Shared, Step, ints, predicate, same_region, source_of,
    };
    use crate::interpreter::tile_operators::test_helpers::{int_entries, keys_between};
    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Notify, Release};

    /// The group a key joins: three groups, so rows share a value.
    fn group_of(key: u64) -> i64 {
        (key % 3) as i64
    }

    fn out_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(KEYS),
                Tiling::Scalar(Extent::uint_range(KEYS)),
            ),
        )
    }

    fn converse_over(source: &Shared) -> ConverseProducer {
        ConverseProducer::new(
            ProducerBase::unowned(ConverseProducer::alloc_id(), &out_tiling()),
            Box::new(Input::over(source)),
            CurryLevel::OUTERMOST,
            out_tiling().empty_at_no_rows(),
        )
    }

    fn rows_source(keys: impl IntoIterator<Item = u64>) -> Shared {
        source_of(keys, group_of)
    }

    /// A source of rows that states complete only the keys it holds until it is closed.
    fn growing_rows_source(keys: impl IntoIterator<Item = u64>) -> Shared {
        let source = rows_source(keys);
        source.borrow_mut().growing = true;
        source
    }

    /// The groups an answer holds: each value with the keys that carry it.
    fn groups(tile: &Tile) -> BTreeMap<i64, BTreeSet<u64>> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection of groups, got {tile:?}")
        };
        let Tile::DataFunction {
            row_starts,
            domain: members,
            ..
        } = &**codomain
        else {
            panic!("a collection per group, got {codomain:?}")
        };
        let mut out = BTreeMap::new();
        for group in 0..domain.len() {
            let Value::Int(value) = domain.index_at(group) else {
                panic!("an integer group, got {:?}", domain.index_at(group))
            };
            let end = row_starts.get(group + 1).copied().unwrap_or(members.len());
            let keys = (row_starts[group]..end)
                .map(|row| {
                    let Value::UInt(key) = members.index_at(row) else {
                        panic!("a key, got {:?}", members.index_at(row))
                    };
                    key
                })
                .collect();
            out.insert(value, keys);
        }
        out
    }

    fn grouped(keys: impl IntoIterator<Item = u64>) -> BTreeMap<i64, BTreeSet<u64>> {
        let mut out: BTreeMap<i64, BTreeSet<u64>> = BTreeMap::new();
        for key in keys {
            out.entry(group_of(key)).or_default().insert(key);
        }
        out
    }

    /// The keys of the universe the input has been released at.
    fn released_keys(source: &Shared) -> BTreeSet<u64> {
        source
            .borrow()
            .released
            .iter()
            .flat_map(|guard| {
                let TileGuard::Function(FunctionGuard::Domain(keys)) = guard else {
                    panic!("a release of keys, got {guard:?}")
                };
                (0..KEYS).filter(|key| keys.contains(&Value::UInt(*key)))
            })
            .collect()
    }

    fn cached(converse: &ConverseProducer) -> Vec<u64> {
        int_entries(&converse.cached)
            .into_iter()
            .map(|(key, _)| key)
            .collect()
    }

    fn universal() -> TileGuard {
        out_tiling().universal_guard()
    }

    /// The guard that names the groups `first` to `last`.
    fn groups_guard(first: i64, last: i64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(first),
                Value::Int(last),
            )),
        )))
    }

    #[test]
    fn a_region_is_merged_pulled_and_released_once() {
        let source = rows_source(0..10);
        let mut converse = converse_over(&source);
        converse.consume_impl(keys_between(2, 5));
        assert_eq!(cached(&converse), vec![2, 3, 4, 5]);
        assert_eq!(source.borrow().pulled, vec![keys_between(2, 5)]);
        assert_eq!(source.borrow().released, vec![keys_between(2, 5)]);
        assert_eq!(groups(&converse.get(universal())), grouped(2..=5));
    }

    #[test]
    fn disjoint_and_overlapping_regions_merge_each_row_once() {
        let source = rows_source(0..10);
        let mut converse = converse_over(&source);
        converse.consume_impl(keys_between(1, 2));
        converse.consume_impl(keys_between(7, 9));
        assert_eq!(cached(&converse), vec![1, 2, 7, 8, 9]);
        converse.consume_impl(keys_between(2, 7));
        assert_eq!(cached(&converse), (1..=9).collect::<Vec<_>>());
        assert_eq!(groups(&converse.get(universal())), grouped(1..=9));
    }

    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = rows_source(0..10);
        let mut converse = converse_over(&source);
        converse.consume_impl(ints().empty_guard());
        assert!(source.borrow().pulled.is_empty());
        assert!(cached(&converse).is_empty());
    }

    /// Everything consumed drains the input, and the offer is what a pull in pull mode answers.
    #[test]
    fn everything_consumed_offers_what_a_lazy_pull_answers() {
        let mut consuming = converse_over(&rows_source(0..10));
        consuming.consume_impl(ints().universal_guard());
        let mut lazy = converse_over(&rows_source(0..10));
        assert_eq!(consuming.get(universal()), lazy.get(universal()));
        // Every group is final once the input has drained, whatever its value.
        assert_eq!(consuming.final_guard(), universal());
    }

    /// A group released drops its rows from what the converse holds and from the input, and
    /// `finalize` leaves the group out.
    #[test]
    fn a_released_group_leaves_the_rows_of_the_group_out() {
        let source = rows_source(0..9);
        let mut converse = converse_over(&source);
        converse.consume_impl(ints().universal_guard());
        converse.release(groups_guard(1, 1));
        assert_eq!(
            groups(&converse.get(universal())),
            grouped((0..9).filter(|k| k % 3 != 1))
        );
        assert_eq!(
            cached(&converse),
            (0..9).filter(|k| k % 3 != 1).collect::<Vec<_>>()
        );
        let TileGuard::Function(FunctionGuard::Domain(kept)) = converse.final_guard() else {
            panic!("a guard of the groups")
        };
        assert!(kept.contains(&Value::Int(0)) && kept.contains(&Value::Int(2)));
        assert!(
            !kept.contains(&Value::Int(1)),
            "the released group is not finalized"
        );
    }

    #[test]
    fn a_consuming_converse_offers_without_pulling() {
        let source = rows_source(0..10);
        let mut converse = converse_over(&source);
        converse.consume_impl(ints().universal_guard());
        let pulls = source.borrow().pulled.len();
        for _ in 0..3 {
            converse.get(universal());
        }
        assert_eq!(source.borrow().pulled.len(), pulls);
    }

    /// A converse beneath a standing level has no consuming mode, and says so.
    #[test]
    #[should_panic(expected = "has no consuming mode")]
    fn a_nested_converse_cannot_consume() {
        let tiling = out_tiling();
        let mut nested = ConverseProducer::new(
            ProducerBase::unowned(ConverseProducer::alloc_id(), &tiling),
            Box::new(Input::over(&rows_source(0..3))),
            CurryLevel::new(1),
            tiling.empty_at_no_rows(),
        );
        nested.consume_impl(ints().universal_guard());
    }

    /// A growing input withholds a key it does not hold yet: the release leaves it, and a row
    /// that arrives there later joins its group at the next consume.
    #[test]
    fn a_key_the_input_withheld_joins_its_group_at_a_later_consume() {
        let source = growing_rows_source([0, 1, 2, 4, 5]);
        let mut converse = converse_over(&source);
        converse.consume_impl(keys_between(0, 5));
        assert!(!released_keys(&source).contains(&3));
        source.borrow_mut().rows.insert(3, group_of(3));
        converse.consume_impl(keys_between(0, 5));
        assert_eq!(cached(&converse), (0..=5).collect::<Vec<_>>());
        assert!(released_keys(&source).contains(&3));
    }

    /// Part of the input consumed states no group complete: a row of any group may still come.
    #[test]
    fn an_offer_after_a_partial_consume_states_no_group_complete() {
        let mut converse = converse_over(&rows_source(0..10));
        converse.consume_impl(keys_between(0, 5));
        let Tile::DataFunction {
            domain_predicate, ..
        } = converse.get(universal())
        else {
            panic!("a collection of groups")
        };
        assert!(domain_predicate.is_false(), "{domain_predicate:?}");
    }

    /// A release named beneath the groups, at input keys, takes those keys out of every group,
    /// and the input drops them when they arrive again.
    #[test]
    fn a_release_beneath_the_groups_takes_its_keys_out_of_every_group() {
        let source = rows_source(0..10);
        let mut converse = converse_over(&source);
        converse.consume_impl(keys_between(0, 3));
        converse.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            keys_between(4, 5),
        ))));
        assert!(
            [4, 5]
                .iter()
                .all(|key| released_keys(&source).contains(key)),
            "the input is released at the keys, whatever group they join"
        );
        source.borrow_mut().rows.insert(4, group_of(4));
        converse.consume_impl(ints().universal_guard());
        let held: BTreeSet<u64> = groups(&converse.get(universal()))
            .into_values()
            .flatten()
            .collect();
        assert_eq!(held, (0..10).filter(|key| ![4, 5].contains(key)).collect());
    }

    /// What such a release leaves has no difference in the guard algebra, so `finalize` names the
    /// gap.
    #[test]
    #[should_panic(expected = "the guard algebra has no difference")]
    fn finalize_after_a_release_beneath_the_groups_names_the_gap() {
        let mut converse = converse_over(&rows_source(0..10));
        converse.consume_impl(ints().universal_guard());
        converse.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            keys_between(4, 5),
        ))));
        converse.final_guard();
    }

    /// A release of every group leaves nothing held.
    #[test]
    fn finalize_after_releasing_everything_holds_nothing() {
        let mut converse = converse_over(&rows_source(0..10));
        converse.consume_impl(ints().universal_guard());
        converse.release(universal());
        assert_eq!(converse.final_guard(), out_tiling().empty_guard());
    }

    /// The model of a run over a growing input: the rows held and the groups released.
    struct Run {
        sut: ConverseProducer,
        sut_source: Shared,
        input: InputModel,
        released_groups: Predicate,
        released_all: bool,
        cache: BTreeSet<u64>,
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let sut_source = growing_rows_source(initial.iter().copied());
            Self {
                sut: converse_over(&sut_source),
                sut_source,
                input: InputModel::new(initial),
                released_groups: Predicate::False,
                released_all: false,
                cache: BTreeSet::new(),
                trace,
            }
        }

        fn group_released(&self, key: u64) -> bool {
            self.released_all || self.released_groups.contains(&Value::Int(group_of(key)))
        }

        /// The groups the rows held fall in, which a release names half the time.
        fn groups_held(&self) -> BTreeSet<u64> {
            self.cache.iter().map(|key| key % 3).collect()
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        self.sut_source.borrow_mut().rows.insert(key, group_of(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.sut_source.borrow_mut().closed = true;
                }
                Notify(_) => unreachable!("a converse listens to no region"),
                Consume(region) => {
                    self.sut.consume_impl(region.guard());
                    let (answered, _) = self.input.pull(region);
                    let kept: Vec<u64> = answered
                        .into_iter()
                        .filter(|key| !self.group_released(*key))
                        .collect();
                    self.cache.extend(kept);
                }
                Release(All) => {
                    self.sut.release(universal());
                    if !self.released_all {
                        self.released_all = true;
                        self.cache.clear();
                        self.input.release(All);
                    }
                }
                Release(Keys(first, last)) => {
                    let named = predicate(&groups_guard(first as i64, last as i64));
                    self.sut.release(groups_guard(first as i64, last as i64));
                    if self.released_all || named.minus(&self.released_groups).is_false() {
                        return;
                    }
                    self.released_groups = self.released_groups.union(&named);
                    let dropped: BTreeSet<u64> = self
                        .cache
                        .iter()
                        .copied()
                        .filter(|key| self.group_released(*key))
                        .collect();
                    self.cache.retain(|key| !dropped.contains(key));
                    self.input.release_keys(&dropped);
                }
            }
        }

        fn check(&mut self) {
            let trace = &self.trace;
            assert_eq!(
                cached(&self.sut),
                self.cache.iter().copied().collect::<Vec<_>>(),
                "{trace}: the rows held"
            );
            if self.sut.consuming {
                assert_eq!(
                    groups(&self.sut.get(universal())),
                    grouped(self.cache.iter().copied()),
                    "{trace}: the groups offered"
                );
            }
            self.input.check(&self.sut_source, trace);
            if self.input.drained() {
                let guard = self.sut.final_guard();
                match self.released_all {
                    true => assert_eq!(guard, out_tiling().empty_guard(), "{trace}: finalize"),
                    false => {
                        let expected = Predicate::True.minus(&self.released_groups);
                        assert!(
                            same_region(&predicate(&guard), &expected),
                            "{trace}: finalize is {guard:?}, not {expected:?}"
                        );
                    }
                }
            }
        }

        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            // A converse in pull mode over exactly the rows held offers what the consuming one
            // does.
            let twin_source = rows_source(self.cache.iter().copied());
            let mut twin = converse_over(&twin_source);
            // Rows keep the order they arrived in, so the answers are compared as groups.
            assert_eq!(
                groups(&self.sut.get(universal())),
                groups(&twin.get(universal())),
                "{}: the answer in pull mode",
                self.trace
            );
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            run.finish();
        }
    }

    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[Consume(Keys(0, 3)), Add(3), Add(8), Consume(Keys(0, 11))],
            &[
                Consume(Keys(0, 3)),
                Release(Keys(1, 1)),
                Add(7),
                Consume(Keys(4, 11)),
            ],
            &[
                Release(Keys(2, 2)),
                Add(5),
                Add(6),
                Close,
                Consume(Keys(4, 8)),
            ],
            &[
                Consume(Keys(0, 5)),
                Consume(Keys(3, 8)),
                Release(Keys(0, 0)),
                Close,
                Consume(All),
            ],
            &[Release(All), Add(3), Consume(All)],
            &[Close, Consume(All), Release(Keys(1, 2))],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0xa54f_f53a_5f1d_36f1;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..12 {
                let step = rng.step_among(&run.groups_held(), false);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}

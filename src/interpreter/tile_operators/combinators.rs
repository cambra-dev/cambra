use bit_set::BitSet;
use bit_vec::BitVec;
use log::trace;
use std::collections::HashMap;
use std::iter::repeat_n;

use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{
        ColumnValue, Consumer, Extent, Scheduler, Value, forwarding_consumer, shared_consumer,
        tuple_field,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Inverts a function operator, producing a lookup-function from codomain to domain.
///
/// For an input `domain → codomain`, `Converse` produces a
/// `DataFunction { domain: codomain, codomain: domain }`.  Each codomain
/// value maps to the list of domain values that produce it.
pub struct Converse {
    /// Output tiling: `DataFunction { domain: input.codomain, codomain: input.domain }`.
    base: OperatorBase,
    /// The function input to invert.
    input: Box<dyn TileOperator>,
}

impl Converse {
    /// Create a `Converse` operator that inverts `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let (domain, codomain) = input
            .tiling()
            .split_function_extent()
            .unwrap_or_else(|| panic!("Converse expected function, got {:?}", input.tiling()));
        let tiling = Tiling::DataFunction {
            domain: codomain,
            codomain: Box::new(Tiling::DataFunction {
                domain: domain.clone(),
                codomain: Box::new(Tiling::Scalar(domain)),
            }),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
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
        Box::new(ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            held: Vec::new(),
        })
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
    /// at is, which takes its value to read.
    held: Vec<(Value, Value)>,
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
            ColumnValue::UInts(group_starts),
            domain2_col.clone(),
            Box::new(Tile::Scalar(domain2_col)),
            domain_predicate,
            output_deleted,
        )),
        outer_predicate,
        BitSet::new(),
    )
}

impl TileProducer for ConverseProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let mut out = match input_tile {
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
                    "converse inverts one mapping, so its input is one collection"
                );
                self.held = match &*codomain {
                    Tile::Scalar(values) => (0..domain.len())
                        .filter(|row| !deleted.contains(*row))
                        .map(|row| (values.index_at(row), domain.index_at(row)))
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
                            ColumnValue::Ints(v) => converse_group_by_key(
                                v,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            ),
                            ColumnValue::UInts(v) => converse_group_by_key(
                                v,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            ),
                            ColumnValue::Strings(v) => converse_group_by_key(
                                v,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            ),
                            ColumnValue::Bools(bv) => {
                                // Materialise as Vec<bool> so the element type is PartialOrd.
                                let v: Vec<bool> = bv.iter().collect();
                                converse_group_by_key(
                                    &v,
                                    &codomain,
                                    &domain,
                                    domain_predicate,
                                    &deleted,
                                )
                            }
                            ColumnValue::Variants(v) => {
                                // Value is PartialOrd; pass the inner vec directly.
                                converse_group_by_key(
                                    v,
                                    &codomain,
                                    &domain,
                                    domain_predicate,
                                    &deleted,
                                )
                            }
                            ColumnValue::Records(_) => {
                                // No native slice to borrow; materialise one Value per row for sorting.
                                // TODO: benchmark this and figure out a way to avoid if needed.
                                let n = codomain.len();
                                let keys: Vec<Value> =
                                    (0..n).map(|i| codomain.index_at(i)).collect();
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
                                let keys: Vec<Value> =
                                    (0..n).map(|i| codomain.index_at(i)).collect();
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
        // A group can be released while the input still grows, since `release_impl` frees
        // only the rows held; a row arriving later with a released value would otherwise
        // put the group back into a region the consumer has let go.
        if !self.base.obsolete_guard.is_empty() {
            out.remove_guarded(self.base.obsolete_guard.clone());
        }
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let released = match obsolete_guard {
            g if g.is_universal() => {
                return self.input.release(self.input.tiling().universal_guard());
            }
            // An input row stands at exactly one output path, under its own value, so it is
            // released where that path is: under a released group, or named beneath one.
            ref g => self
                .held
                .iter()
                .filter(|(value, key)| g.covers_path(&[value.clone(), key.clone()]))
                .map(|(_, key)| key.clone())
                .collect::<Vec<_>>(),
        };
        // A statement beneath the groups that names no group says the same under every one, so it
        // releases the input rows it names whether or not they have arrived.
        fn under_every_group(guard: &TileGuard) -> Predicate {
            match guard {
                TileGuard::Or(arms) => arms
                    .iter()
                    .map(under_every_group)
                    .fold(Predicate::False, |all, one| all.union(&one)),
                TileGuard::Function(FunctionGuard::Codomain(inner)) => match inner.as_ref() {
                    TileGuard::Function(FunctionGuard::Domain(keys)) => match keys {
                        Predicate::Or(arms) => arms
                            .iter()
                            .filter(|arm| !arm.qualifies())
                            .fold(Predicate::False, |all, one| all.union(one)),
                        unqualified if !unqualified.qualifies() => unqualified.clone(),
                        _ => Predicate::False,
                    },
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
        self.input
            .release(TileGuard::Function(FunctionGuard::Domain(rows)));
    }
}

/// Replaces the codomain of a function with the domain values themselves,
/// creating an identity mapping where the codomain is a copy of the domain.
///
/// Takes a `DataFunction(domain → codomain)` and produces `DataFunction(domain → Scalar(domain))`.
/// The output domain is unchanged; the codomain becomes a scalar version of the same domain values.
pub struct MapDomain {
    /// Output tiling: `DataFunction { domain, codomain: Scalar(domain) }`.
    base: OperatorBase,
    /// The function input.
    input: Box<dyn TileOperator>,
}

impl MapDomain {
    /// Create a `MapDomain` operator that replaces the codomain with the domain values.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::DataFunction { domain, .. } = input.tiling() else {
            panic!(
                "MapDomain expected a function tiling, got {:?}",
                input.tiling()
            )
        };
        let domain = domain.clone();
        let tiling = Tiling::data_function(domain.clone(), Tiling::Scalar(domain));
        Self {
            base: OperatorBase::new(tiling),
            input,
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
        Box::new(MapDomainProducer {
            base: ProducerBase::new(MapDomainProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
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
}

impl TileProducer for MapDomainProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::DataFunction {
                row_starts,
                domain,
                domain_predicate,
                deleted,
                ..
            } => {
                let as_data = domain.clone();
                Tile::grouped(
                    row_starts,
                    domain,
                    Box::new(Tile::Scalar(as_data)),
                    domain_predicate,
                    deleted,
                )
            }
            other => panic!("MapDomain expected a collection, got {other:?}"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            g => todo!("Restrict cannot honor the release guard {g:?}"),
        });
    }
}

/// Flattens a collection of collections into one collection keyed by pairs.
///
/// Takes `A ⤇ B ⤇ C` and produces `{_0: A, _1: B} ⤇ C`: the two key extents are packed
/// into a record key, and the values stand as they were.
pub struct Uncurry {
    /// Output tiling: `DataFunction { domain: Record { _0: A, _1: B }, codomain: Scalar(C) }`,
    /// beneath `depth` standing levels.
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
        Box::new(UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
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

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
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
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let input_guard = self.split_pair_guard(obsolete_guard, self.level);
        trace!("{} releasing up with: {input_guard:?}", self.name());
        self.input.release(input_guard);
    }
}

/// Pair a curried collection's two levels into one keyed by `(outer, inner)` pairs.
///
/// The whole of what [`Uncurry`] does, on a tile that is exactly those two levels. An
/// standing `Uncurry` applies it to each enclosing row's group, which is such a tile.
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
    let ColumnValue::UInts(offsets_vec) = &row_starts else {
        panic!("row starts are UInts")
    };

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
    /// and the guard beneath it is split. At the paired level itself, a pair release
    /// reaches the input's outer key only where it covers that key's **whole** inner
    /// collection — a partial group leaves the outer key still live. A pair arm qualified by
    /// the standing rows above it releases its outer keys under those same rows.
    fn split_pair_guard(&self, guard: TileGuard, level: CurryLevel) -> TileGuard {
        match guard {
            g if g.is_empty() => self.input.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            TileGuard::Function(FunctionGuard::Codomain(inner))
                if level != CurryLevel::OUTERMOST =>
            {
                TileGuard::Function(FunctionGuard::Codomain(Box::new(
                    self.split_pair_guard(*inner, level.in_codomain()),
                )))
            }
            g @ TileGuard::Function(FunctionGuard::Domain(_)) if level != CurryLevel::OUTERMOST => {
                g
            }
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
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let pair_fields = HashMap::from([(tuple_field(0), ()), (tuple_field(1), ())]);
                let arms = |p: &Predicate| -> Vec<Predicate> {
                    match p {
                        Predicate::Or(arms) => arms.clone(),
                        one => vec![one.clone()],
                    }
                };
                let mut domain_guard = TileGuard::Function(FunctionGuard::Domain(Predicate::False));
                for arm in arms(&pred) {
                    let (enclosing, pairs) = arm.split_qualification();
                    for pair in arms(pairs) {
                        let mut split_preds = pair.split_record(&pair_fields);
                        let outer_pred = split_preds.remove(&tuple_field(0)).unwrap();
                        let inner_pred = split_preds.remove(&tuple_field(1)).unwrap();
                        if inner_pred.is_true() {
                            domain_guard =
                                domain_guard.union(&TileGuard::Function(FunctionGuard::Domain(
                                    Predicate::qualified(enclosing.clone(), outer_pred),
                                )));
                        }
                    }
                }
                domain_guard
            }
            // Each arm names its own region, so each splits on its own.
            TileGuard::Or(arms) => arms
                .into_iter()
                .fold(self.input.tiling().empty_guard(), |all, arm| {
                    all.union(&self.split_pair_guard(arm, level))
                }),
            g => todo!("Uncurry cannot honor the release guard {g:?}"),
        }
    }
}

/// Filters a function tile by a predicate, keeping only pairs whose domain element
/// maps to `true` under the predicate.
///
/// The `predicate` operator must produce a function from the input's domain type to
/// `bool`. For each domain element in the input tile, the predicate is evaluated;
/// only elements where it returns `true` are retained together with their associated
/// codomain values.
///
/// TODO we should replace this with a Restrict node that filters based on a function of the domain,
/// rather than this which filters based on a function of the codomain.
pub struct Filter {
    /// Output tiling, equal to the input tiling (filtering preserves the type).
    base: OperatorBase,
    /// The function input to filter.
    input: Box<dyn TileOperator>,
    /// The boolean predicate applied to each domain element.
    predicate: Box<dyn TileOperator>,
}

impl Filter {
    /// Create a `Filter` that retains elements of `input` for which `predicate` is `true`.
    pub fn new(input: Box<dyn TileOperator>, predicate: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self {
            base: OperatorBase::new(tiling),
            input,
            predicate,
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
        let shared = shared_consumer(consumer);
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            forwarding_consumer(&shared, &scheduler.wakeup_queue()),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            forwarding_consumer(&shared, &scheduler.wakeup_queue()),
            scheduler,
        );
        Box::new(FilterProducer {
            base: ProducerBase::new(FilterProducer::alloc_id(), self.tiling()),
            input: input_producer,
            predicate: predicate_producer,
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
}

impl TileProducer for FilterProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let i_guard = self.input.tiling().universal_guard();
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
                        .as_bitvec()
                        .unwrap_or_else(|| panic!("Expected boolean mask"));
                    let mut output = input;
                    output.mark_deleted(mask);
                    output
                }
                _ => panic!("Filter predicate is not a function"),
            },
            // Both predicate and input are collections over the same entries: the predicate
            // compiled over the same rows, so its innermost values are one boolean per
            // innermost key, in key order — the mask `retain_keys` takes, which re-offsets
            // the groups a filter shortens.
            (pred @ Tile::DataFunction { .. }, mut input @ Tile::DataFunction { .. }) => {
                let Tile::DataFunction {
                    domain: pred_keys, ..
                } = pred
                    .innermost_level()
                    .unwrap_or_else(|| unreachable!("the arm matched a collection"))
                else {
                    unreachable!("innermost_level answers a collection")
                };
                let Tile::DataFunction { domain: inner, .. } = input
                    .innermost_level()
                    .unwrap_or_else(|| unreachable!("the arm matched a collection"))
                else {
                    unreachable!("innermost_level answers a collection")
                };
                // **The mask is positional**, so it applies only while the two sides are in
                // step. An input with nothing in it is already filtered — the predicate
                // keeps answering for entries whose rows have been handed on.
                if inner.is_empty() {
                    return input;
                }
                // Anything else out of step is a shape this does not serve, and it says so
                // rather than reading a mask across the misalignment (which drops the wrong
                // entries, silently) or answering empty (which waits for an alignment that is
                // not coming). Each side is pulled from its own branch of the pairs, and a
                // source delivering its rows one at a time — a transaction's — lets the
                // predicate reach entries the input has not.
                assert_eq!(
                    pred_keys.len(),
                    inner.len(),
                    "a correlated filter needs its predicate and its rows in step; the \
                     predicate has answered for a different number of entries than the rows \
                     carry. A source that delivers rows one at a time is the case this does \
                     not serve yet.",
                );
                // Equal counts are what a positional mask needs stated on every pull, and
                // equal keys are what makes it the right mask. The second walks both columns,
                // so it is checked where checks cost nothing.
                debug_assert!(
                    pred_keys == inner,
                    "a correlated filter's predicate and rows agree in count but not in keys, \
                     so the mask is positional over two different orders",
                );
                let pred_column = scalar_tile_to_column_value(pred.deepest_values().clone());
                let mask = pred_column
                    .as_bitvec()
                    .unwrap_or_else(|| panic!("Expected bools"));
                // The mask names the innermost keys, so it drops entries from each row's
                // group and leaves every level above standing.
                input
                    .innermost_level_mut()
                    .unwrap_or_else(|| unreachable!("the arm matched a collection"))
                    .retain_keys(mask);
                input
            }
            _ => panic!("Invalid Filter input tiles"),
        }
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

/// Filters the **inner collections** of a collection of collections, one outer key at a
/// time.
///
/// [`Filter`] and [`Restrict`] both narrow a collection's own keys. Neither reaches inside
/// a nested one, where the keys a predicate selects on are the inner collection's — the
/// per-key collection — and the survivors differ from key to key. A per-group filter
/// (`sum([s.amount for s in g if s.qty > 2])` over a `groupby`) is that shape: the
/// refinement rides the inner collection's keys, under the outer key's binder.
///
/// The predicate produces the same nesting over `Bool`, so its innermost values are the
/// mask directly — inner key `i` survives iff the predicate's entry `i` is `true`. Running
/// the keys of every group together is what makes this one masked pass rather than a
/// per-key loop: the outer level is untouched, and [`Tile::retain_keys`] re-cuts the inner
/// runs around the survivors.
pub struct MapFilter {
    /// Output tiling, equal to the input's — filtering removes rows, not structure.
    base: OperatorBase,
    /// The input whose element collections are filtered.
    input: Box<dyn TileOperator>,
    /// A `Bool` per key of each element collection, over the same levels as the input.
    predicate: Box<dyn TileOperator>,
    /// The level the elements stand at: each is a collection whose keys are filtered, and
    /// the levels above stand.
    level: CurryLevel,
}

impl MapFilter {
    /// Retain the keys of each element collection of `input`, the values at `level`, where
    /// `predicate` holds.
    ///
    /// `level` is the iteration the filter sits in, which the caller states from where it is
    /// in the program: an element's own values may be collections too, so the level to
    /// filter is not the innermost one.
    pub fn new_at(
        input: Box<dyn TileOperator>,
        predicate: Box<dyn TileOperator>,
        level: CurryLevel,
    ) -> Self {
        let tiling = input.tiling().clone();
        assert!(
            matches!(tiling.values_at(level), Tiling::DataFunction { .. }),
            "MapFilter filters the collection each element at {level} is, got {tiling:?}"
        );
        assert!(
            matches!(predicate.tiling().values_at(level), Tiling::DataFunction { codomain, .. }
                if !codomain.is_data_function()),
            "MapFilter's predicate answers each key of each element at {level}, got {:?}",
            predicate.tiling()
        );
        Self {
            base: OperatorBase::new(tiling),
            input,
            predicate,
            level,
        }
    }
}

impl TileOperator for MapFilter {
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
        let shared = shared_consumer(consumer);
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            forwarding_consumer(&shared, &scheduler.wakeup_queue()),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            forwarding_consumer(&shared, &scheduler.wakeup_queue()),
            scheduler,
        );
        Box::new(MapFilterProducer {
            base: ProducerBase::new(MapFilterProducer::alloc_id(), self.tiling()),
            input: input_producer,
            predicate: predicate_producer,
            level: self.level,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

struct MapFilterProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    predicate: Box<dyn TileProducer>,
    level: CurryLevel,
}

impl TileProducer for MapFilterProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let input_guard = self.input.tiling().universal_guard();
        let predicate_result = self.predicate.get(pred_guard);
        let mut input_result = self.input.get(input_guard);
        let Tile::DataFunction {
            domain: pred_keys,
            codomain: pred_values,
            ..
        } = predicate_result.values_at(self.level)
        else {
            panic!(
                "MapFilter's predicate is not a collection at {}",
                self.level
            );
        };
        let Tile::DataFunction {
            domain: input_keys, ..
        } = input_result.values_at(self.level)
        else {
            panic!("MapFilter's input is not a collection at {}", self.level);
        };
        // The mask is positional over the keys of every element at once, so the two sides
        // must be the same flattening of the same keys. They share an upstream `FanOut`, so
        // a mismatch is a planning bug rather than a data-dependent case.
        debug_assert_eq!(
            pred_keys, input_keys,
            "MapFilter predicate and input must flatten the same inner domains"
        );
        let pred_column = scalar_tile_to_column_value((**pred_values).clone());
        let mask = pred_column
            .as_bitvec()
            .unwrap_or_else(|| panic!("MapFilter predicate codomain is not boolean"));
        input_result.values_at_mut(self.level).retain_keys(mask);
        input_result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Both sides read the same upstream collection, so they release together —
        // releasing one leaves the other's `FanOut` guard stale, which re-delivers
        // consumed rows on the next `get`. Same coupling as [`Filter`].
        self.predicate.release(obsolete_guard.clone());
        self.input.release(obsolete_guard);
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
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            consumer,
            scheduler,
        );
        Box::new(RestrictProducer {
            base: ProducerBase::new(RestrictProducer::alloc_id(), self.tiling()),
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

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let pred_result = self.predicate.get(pred_guard);
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
                    .as_bitvec()
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
/// carry.
///
/// Both sides are pulled from their own branch and need not have reached the same rows, so
/// only the rows *both* have carry a group. A row the inner side has not delivered has no
/// domain yet. A row whose collection is still arriving is paired with the keys it holds so
/// far and left open, so a later tile adds to its group
/// ([`Tile::append_open_level_beneath`]).
fn pair_one_level(outer: &Tile, inner: &Tile, pair: &Tiling) -> Tile {
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
        domain: group_keys, ..
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
    let mut kept = BitVec::from_elem(outer_keys.len(), false);
    for r in &paired {
        kept.set(*r, true);
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
        let keys = group_keys.select_indices(key_indices.into_iter(), total);
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
            ColumnValue::UInts(starts),
            keys.clone(),
            Box::new(pair_tile(outer_values, keys, pair)),
            Predicate::False,
            BitSet::new(),
        )
    })
}

/// The pair `{_0: element, _1: key}` in the representation `pair` names.
///
/// One rule, stated in [`Product`]'s constructor and read here: a materialized record column
/// unless the element carries a level, which a column has nowhere to put.
fn pair_tile(element: Tile, keys: ColumnValue, pair: &Tiling) -> Tile {
    match pair {
        Tiling::Record(_) => Tile::tuple(vec![element, Tile::Scalar(keys)]),
        _ => Tile::Scalar(ColumnValue::Records(HashMap::from([
            (tuple_field(0), scalar_tile_to_column_value(element)),
            (tuple_field(1), keys),
        ]))),
    }
}

/// Each row of one stream paired with every key of its group in another: the product that
/// makes a correlated inner comprehension and a nested loop compilable.
///
/// **A per-row inner side** ([`Product::per_row_at`]) gives each row a group of its own. A
/// **nested loop**, and a comprehension whose inner source is the row itself, has a domain
/// that belongs to the row:
/// `for xs in rows: for x in xs` gives each row its own collection, and a source whose
/// elements are lists gives them differing lengths with no witness and no `box` involved.
/// There is then no extent to enumerate — the element extent's domain is unbounded — so the
/// keys come from the tile.
///
/// The output tiling is the outer's levels with the inner domain put beneath the rows, over
/// `{_0: outer value, _1: inner key}`. A row is complete as soon as both sides call it
/// complete, and a row whose group is still arriving is paired with what it holds and left
/// open.
///
/// **A shared inner side** ([`Product::shared_at`]) is the case where every row's
/// collection is the same one: a correlated inner comprehension whose inner source is closed
/// over the outer binder. `lambda_elim` turns `[… f(r, v) … for v in xs]` written inside a
/// `for r in …` into a curried morphism over the outer collection, taking the pair `(r, v)`,
/// and the pairs are each row with every element `xs` holds. That side is a stream rather than
/// an extent: a list literal's domain is an `IterateExtent` over its index range, and a map's
/// is `MapDomain` of the collection, since `extent_of` strips its present-key refinement to
/// the unbounded key type. Both carry that domain in their codomain, which is what is paired.
/// Every row reads the whole of it, so it is released only when everything is.
pub struct Product {
    /// Output tiling: the outer's levels down to its rows, the inner domain beneath them,
    /// then the pairs.
    base: OperatorBase,
    /// The level the pairing adds ([`Product::per_row_at`]).
    paired: CurryLevel,
    /// The outer collection, one row per group.
    outer: Box<dyn TileOperator>,
    /// The per-row collections, aligned with `outer` row for row — or, where `shared`, the
    /// one collection every row pairs with, whose values are the keys paired.
    inner: Box<dyn TileOperator>,
    shared: bool,
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
        assert!(
            inner.tiling().levels() > paired.index(),
            "Product's inner side holds one collection per row of the outer at {paired}, \
             got {:?} — a shared inner domain is [`Product::shared_at`]",
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
        let row_domain = row_domain.clone();
        Self::build(outer, inner, paired, row_domain, false)
    }

    /// Pair every row of `outer` at `paired`'s enclosing level with every element of the one
    /// collection `inner`: the elements are its values, which is where a list's index range
    /// and a map's domain both carry the domain iterated.
    pub fn shared_at(
        outer: Box<dyn TileOperator>,
        inner: Box<dyn TileOperator>,
        paired: CurryLevel,
    ) -> Self {
        let Tiling::DataFunction {
            codomain: elements, ..
        } = inner.tiling()
        else {
            panic!(
                "Product reads a shared inner domain off a collection's values, got {:?}",
                inner.tiling()
            )
        };
        let row_domain = elements.extent();
        Self::build(outer, inner, paired, row_domain, true)
    }

    fn build(
        outer: Box<dyn TileOperator>,
        inner: Box<dyn TileOperator>,
        paired: CurryLevel,
        row_domain: Extent,
        shared: bool,
    ) -> Self {
        let outer_tiling = outer.tiling();
        assert!(
            outer_tiling.is_data_function() && paired.index() >= 1,
            "Product pairs the rows of a collection, got {outer_tiling:?} at {paired}"
        );
        let element = outer_tiling.values_at(paired).clone();
        // The pair rides materialized in one column unless the element carries a level, which a
        // column has nowhere to put: a nest whose elements are collections pairs each of
        // them against its own keys, so the pair is a struct of arrays there.
        let pair = if element.holds_a_level() {
            Tiling::tuple(&[element, Tiling::Scalar(row_domain.clone())])
        } else {
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), element.extent()),
                (tuple_field(1), row_domain.clone()),
            ])))
        };
        let tiling = level_beneath(outer_tiling, paired.index() - 1, row_domain, pair);
        Self {
            base: OperatorBase::new(tiling),
            outer,
            inner,
            paired,
            shared,
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
        let shared = shared_consumer(consumer);
        let level = self
            .paired
            .enclosing()
            .unwrap_or_else(|| unreachable!("the paired level is beneath a row"));
        let empty_level = self.tiling().values_at(level).empty_at_no_rows();
        Box::new(ProductProducer {
            base: ProducerBase::new(ProductProducer::alloc_id(), self.tiling()),
            outer: self.outer.subscribe(
                self.outer.tiling().universal_guard(),
                forwarding_consumer(&shared, &scheduler.wakeup_queue()),
                scheduler,
            ),
            inner: self.inner.subscribe(
                self.inner.tiling().universal_guard(),
                forwarding_consumer(&shared, &scheduler.wakeup_queue()),
                scheduler,
            ),
            level,
            empty_level,
            pair: self.tiling().deepest_values().clone(),
            shared: self.shared.then_some(SharedInner {
                elements: None,
                complete: false,
            }),
        })
    }
}

/// A shared inner side as last read, and whether it has closed: once it has, it is not read
/// again.
struct SharedInner {
    elements: Option<ColumnValue>,
    complete: bool,
}

/// Producer for [`Product`].
struct ProductProducer {
    base: ProducerBase,
    outer: Box<dyn TileProducer>,
    inner: Box<dyn TileProducer>,
    /// The levels both sides carry above the one being paired. The pair is formed at the
    /// level the inner side *adds*, which is the outer's deepest — so a carrier inside a
    /// deeper nest pairs beneath the levels it leaves standing rather than at the top,
    /// where a key value repeats across enclosing rows and names no single row.
    level: CurryLevel,
    /// The paired level, empty — what an enclosing row that neither side has reached
    /// contributes to the regrouped result.
    empty_level: Tile,
    /// The pair's own tiling, which says whether it rides materialized in one column.
    pair: Tiling,
    /// Where the inner side is one collection every row pairs with ([`Product::shared_at`]).
    shared: Option<SharedInner>,
}

impl ProductProducer {
    /// The rows of `outer_tile` each paired with every element the shared side holds so far.
    ///
    /// Until that side closes, every row's group can still gain an element, so no row is
    /// complete, nor any standing row above one: the pairs are appended open
    /// ([`pair_one_level`]), as a row whose own collection is still arriving is.
    fn pair_shared(&mut self, outer_tile: Tile) -> Tile {
        let shared = self.shared.as_mut().expect("a shared inner side");
        if !shared.complete {
            let mut tile = self.inner.get(self.inner.tiling().universal_guard());
            tile.compact();
            shared.complete = tile.is_terminal();
            let Tile::DataFunction { codomain, .. } = tile else {
                panic!("Product's shared inner side is a collection, got {tile:?}")
            };
            shared.elements = Some(scalar_tile_to_column_value(*codomain));
        }
        let (elements, complete) = (
            shared.elements.clone().expect("read above"),
            shared.complete,
        );
        let mut tile =
            outer_tile.regroup_beneath(self.level, self.empty_level.clone(), &mut |row| {
                let Some(outer) = outer_tile.group_at(self.level, row) else {
                    return self.empty_level.clone();
                };
                let inner = every_row_holding(&outer, &elements, complete);
                pair_one_level(&outer, &inner, &self.pair)
            });
        if !complete {
            for depth in (0..self.level.index()).map(CurryLevel::new) {
                let Tile::DataFunction {
                    domain_predicate, ..
                } = tile.values_at_mut(depth)
                else {
                    unreachable!("the levels above the pair are collections")
                };
                *domain_predicate = Predicate::False;
            }
        }
        tile.remove_guarded(self.obsolete_guard().clone());
        tile
    }
}

/// The inner side [`pair_one_level`] reads for a shared one: `outer`'s rows, each holding
/// `elements` as its keys, complete where the shared side is.
fn every_row_holding(outer: &Tile, elements: &ColumnValue, complete: bool) -> Tile {
    let Tile::DataFunction { domain: rows, .. } = outer else {
        unreachable!("Product pairs the rows of a collection, got {outer:?}")
    };
    let (count, width) = (rows.len(), elements.len());
    let total = count * width;
    let keys = elements.select_indices((0..total).map(|i| i % width), total);
    let stated = match complete {
        true => Predicate::True,
        false => Predicate::False,
    };
    Tile::data_function(
        rows.clone(),
        Box::new(Tile::grouped(
            ColumnValue::UInts((0..count).map(|r| r * width).collect()),
            keys.clone(),
            Box::new(Tile::Scalar(keys)),
            stated.clone(),
            BitSet::new(),
        )),
        stated,
        BitSet::new(),
    )
}

impl TileProducer for ProductProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("outer", self.outer.inspect(opts))
            .child("inner", self.inner.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut outer_tile = self.outer.get(self.outer.tiling().universal_guard());
        outer_tile.compact();
        if self.shared.is_some() {
            return self.pair_shared(outer_tile);
        }
        let mut inner_tile = self.inner.get(self.inner.tiling().universal_guard());
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
                pair_one_level(&outer, &inner, &self.pair)
            });
        // Beneath a standing level both sides fill the row, so a row there is complete
        // where both call it complete; the outer side's statement alone is about half of it.
        for depth in (0..self.level.index()).map(CurryLevel::new) {
            let (
                Tile::DataFunction {
                    domain_predicate: inner_complete,
                    ..
                },
                Tile::DataFunction {
                    domain_predicate, ..
                },
            ) = (inner_tile.values_at(depth), tile.values_at_mut(depth))
            else {
                unreachable!("the levels above the pair are collections on both sides")
            };
            *domain_predicate = domain_predicate.intersect(inner_complete);
        }
        tile.remove_guarded(self.obsolete_guard().clone());
        tile
    }

    /// A row releases to both sides: each holds that row's own contribution, unlike a
    /// shared inner side, which no single row is done with.
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
            // Every row reads the whole shared side, so nothing short of everything frees
            // any of it; a row goes to the outer side as it would here.
            g if self.shared.is_some() => {
                let shared = self.level.index() + 1;
                self.outer
                    .release(crate::interpreter::tiling::through_shared_levels(
                        g,
                        shared,
                        self.outer.tiling(),
                    ));
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
    /// pair arm qualified by its standing row releases outer keys under that row only, and
    /// only those whose inner collection it covers whole.
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
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
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
        let expected = domain(Predicate::below(Value::UInt(1))).union(&TileGuard::Function(
            FunctionGuard::Codomain(Box::new(domain(Predicate::qualified(
                Predicate::point(Value::UInt(1)),
                Predicate::below(Value::UInt(2)),
            )))),
        ));
        assert_eq!(
            uncurry.split_pair_guard(released, CurryLevel::new(1)),
            expected
        );
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
                ColumnValue::UInts(vec![0, 2]),
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
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
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
                ColumnValue::UInts(vec![0, 1, 2]),
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
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
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
        //
        // Previously, Predicate::True was preserved directly.
        // Now, it should be transformed into a Record predicate with both
        // fields (_0 and _1) set to Predicate::True.

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 2, 3]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0, 1, 2]),
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
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
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
        //
        // Previously, Predicate::False was preserved directly.
        // Now, it should be transformed into a Record predicate with both
        // fields (_0 and _1) set to Predicate::False.

        let two_level_tile = Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0, 1]),
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
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
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
        let mut producer = ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            held: Vec::new(),
        };
        producer.get(producer.tiling().universal_guard())
    }

    fn one_level_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// A released group stays released: a row the input delivers later with that group's
    /// value does not put the group back.
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
        let mut producer = ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), &output_tiling),
            input: Box::new(input),
            held: Vec::new(),
        };
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
        assert_eq!(*row_starts, ColumnValue::UInts(vec![0, 2]));
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
                ColumnValue::from_uints(vec![0, 2]),
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
            base: ProducerBase::new(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            shared: None,
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
            &ColumnValue::from_uints(vec![0, 2]),
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

    /// A shared inner side pairs every live outer row with each of its elements, and a
    /// removed outer row pairs with none.
    #[test]
    fn product_pairs_every_live_row_with_a_shared_inner_side() {
        let stream = |values: Vec<i64>, deleted: BitSet| {
            Tile::data_function(
                ColumnValue::from_uints((0..values.len()).collect()),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::True,
                deleted,
            )
        };
        let stream_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let mut deleted = BitSet::new();
        deleted.insert(0);
        let out_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Record(HashMap::from([
                    (tuple_field(0), Extent::Base(BaseType::Int)),
                    (tuple_field(1), Extent::Base(BaseType::Int)),
                ]))),
            ),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::new(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(
                stream(vec![100, 200], deleted),
                stream_tiling.clone(),
            )),
            inner: Box::new(TestTileProducer::new(
                stream(vec![7, 8], BitSet::new()),
                stream_tiling,
            )),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            shared: Some(SharedInner {
                elements: None,
                complete: false,
            }),
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction {
            domain: rows,
            codomain,
            domain_predicate,
            ..
        } = &out
        else {
            panic!("Product tiles as a collection of collections")
        };
        assert_eq!(*rows, ColumnValue::from_uints(vec![1]), "row 0 was removed");
        assert!(domain_predicate.is_true(), "both sides are complete");
        let Tile::DataFunction {
            domain, codomain, ..
        } = codomain.as_ref()
        else {
            panic!("the paired level is a collection")
        };
        assert_eq!(*domain, ColumnValue::Ints(vec![7, 8]));
        let Tile::Scalar(ColumnValue::Records(fields)) = codomain.as_ref() else {
            panic!("a pair is a record of the row's value and the element")
        };
        assert_eq!(fields[&tuple_field(0)], ColumnValue::Ints(vec![200, 200]));
    }

    /// While the shared side is still arriving, every row pairs with what it holds so far
    /// and none is complete, since each can still gain the next element.
    #[test]
    fn product_pairs_rows_with_a_shared_side_still_arriving() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let stream_tiling = Tiling::data_function(uint(), Tiling::Scalar(int()));
        let outer = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 200]))),
            Predicate::True,
            BitSet::new(),
        );
        let inner = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
            Predicate::False,
            BitSet::new(),
        );
        let out_tiling = stream_tiling.append_level(
            int(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), int()),
                (tuple_field(1), int()),
            ]))),
        );
        let mut producer = ProductProducer {
            base: ProducerBase::new(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, stream_tiling.clone())),
            inner: Box::new(TestTileProducer::new(inner, stream_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            shared: Some(SharedInner {
                elements: None,
                complete: false,
            }),
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction {
            codomain,
            domain_predicate,
            ..
        } = &out
        else {
            panic!("Product tiles as a collection of collections")
        };
        assert!(
            domain_predicate.is_false(),
            "no row is complete while the shared side may grow: {domain_predicate:?}"
        );
        let Tile::DataFunction {
            row_starts, domain, ..
        } = codomain.as_ref()
        else {
            panic!("the paired level is a collection")
        };
        assert_eq!(*row_starts, ColumnValue::from_uints(vec![0, 1]));
        assert_eq!(*domain, ColumnValue::Ints(vec![7, 7]));
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
                ColumnValue::from_uints(vec![0]),
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
            base: ProducerBase::new(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            shared: None,
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
                ColumnValue::from_uints(vec![0]),
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
            base: ProducerBase::new(ProductProducer::alloc_id(), &out_tiling),
            outer: Box::new(TestTileProducer::new(outer, outer_tiling)),
            inner: Box::new(TestTileProducer::new(inner, inner_tiling)),
            level: CurryLevel::OUTERMOST,
            empty_level: out_tiling.empty_at_no_rows(),
            pair: out_tiling.deepest_values().clone(),
            shared: None,
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

use bit_set::BitSet;
use log::trace;
use std::{collections::HashMap, iter};

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

/// Inverts a sealed-function operator, producing a lookup-function from codomain to domain.
///
/// For an input `domain → codomain`, `Converse` produces a
/// `CurriedFunction { domain: codomain, codomain: domain }`.  Each codomain
/// value maps to the list of domain values that produce it.
pub struct Converse {
    /// Output tiling: `CurriedFunction { domain: input.codomain, codomain: input.domain }`.
    base: OperatorBase,
    /// The sealed-function input to invert.
    input: Box<dyn TileOperator>,
}

impl Converse {
    /// Create a `Converse` operator that inverts `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let (domain, codomain) = input
            .tiling()
            .split_function_extent()
            .unwrap_or_else(|| panic!("Converse expected function, got {:?}", input.tiling()));
        let tiling = Tiling::CurriedFunction {
            domain1: codomain,
            domain2: domain.clone(),
            codomain: domain,
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

    fn subscribe_impl(
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
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(vec![TilePathStep::Codomain])
    }
}

/// Producer for [`Converse`]: inverts a sealed-function tile into a lookup-function tile.
struct ConverseProducer {
    base: ProducerBase,
    /// The upstream producer whose output is inverted.
    input: Box<dyn TileProducer>,
}

/// Sort row indices by typed key, detect group boundaries, and assemble the
/// curried-function tile for [`ConverseProducer`].
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
    // domain1: one codomain value per group (the key for the outer lookup).
    let domain1_col = codomain.select_indices(group_starts.iter().map(|&s| order[s]), num_groups);
    // Remap deleted bits: output position j corresponds to input row order[j].
    let output_deleted: BitSet = order
        .iter()
        .enumerate()
        .filter(|(_, src)| input_deleted.contains(**src))
        .map(|(j, _)| j)
        .collect();
    // domain2/codomain_out: original domain values reordered to match sorted groups.
    let domain2_col = domain.select_indices(order.into_iter(), n);
    Tile::curried_function(
        domain1_col,
        ColumnValue::UInts(group_starts),
        domain2_col.clone(),
        domain2_col,
        if domain_predicate.as_bool().unwrap_or(false) {
            Predicate::True
        } else {
            Predicate::False
        },
        output_deleted,
    )
}

impl TileProducer for ConverseProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => match *codomain {
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
            },
            _ => panic!("Can only converse functions"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_universal() => self.input.release(self.input.tiling().universal_guard()),
            TileGuard::Function(FunctionGuard::Codomain(g)) => {
                if let TileGuard::Function(FunctionGuard::Domain(p)) = g.as_ref() {
                    self.input
                        .release(TileGuard::Function(FunctionGuard::Domain(p.clone())))
                }
            }
            g => panic!("Converse cannot honor the release guard {g:?}"),
        }
    }
}

/// Replaces the codomain of a sealed function with the domain values themselves,
/// creating an identity mapping where the codomain is a copy of the domain.
///
/// Takes a `SealedFunction(domain → codomain)` and produces `SealedFunction(domain → Scalar(domain))`.
/// The output domain is unchanged; the codomain becomes a scalar version of the same domain values.
pub struct MapDomain {
    /// Output tiling: `SealedFunction { domain, codomain: Scalar(domain) }`.
    base: OperatorBase,
    /// The sealed-function input.
    input: Box<dyn TileOperator>,
}

impl MapDomain {
    /// Create a `MapDomain` operator that replaces the codomain with the domain values.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::SealedFunction { domain, .. } = input.tiling() else {
            panic!(
                "MapDomain expected SealedFunction, got {:?}",
                input.tiling()
            )
        };
        let tiling = Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(domain.clone())),
        };
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

    fn subscribe_impl(
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

/// Producer for [`MapDomain`]: replaces a sealed-function's codomain with its domain.
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
            Tile::SealedFunction {
                domain,
                domain_predicate,
                deleted,
                ..
            } => Tile::SealedFunction {
                codomain: Box::new(Tile::Scalar(domain.clone())),
                domain,
                domain_predicate,
                deleted,
            },
            _ => panic!("MapDomain expected SealedFunction tile"),
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

/// Flattens a curried function into a sealed function with a pair domain.
///
/// Takes a `CurriedFunction(A → B → C)` and produces `SealedFunction(Record(A, B) → Scalar(C))`.
/// The two domain extents are packed into a record domain with fields `_0` (outer domain) and `_1` (inner domain),
/// while the codomain becomes a scalar version of the original codomain.
pub struct Uncurry {
    /// Output tiling: `SealedFunction { domain: Record { _0: A, _1: B }, codomain: Scalar(C) }`.
    base: OperatorBase,
    /// The curried-function input.
    input: Box<dyn TileOperator>,
}

impl Uncurry {
    /// Create an `Uncurry` operator that flattens a curried function into a sealed function.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain,
        } = input.tiling()
        else {
            panic!("Uncurry expected CurriedFunction, got {:?}", input.tiling())
        };
        let pair_extent = Extent::Record(HashMap::from([
            (tuple_field(0), domain1.clone()),
            (tuple_field(1), domain2.clone()),
        ]));
        let tiling = Tiling::SealedFunction {
            domain: pair_extent,
            codomain: Box::new(Tiling::Scalar(codomain.clone())),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for Uncurry {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe_impl(
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
        })
    }
}

/// Producer for [`Uncurry`]: flattens a curried-function tile into a sealed-function tile with pair domain.
struct UncurryProducer {
    base: ProducerBase,
    /// The upstream producer whose curried function is flattened.
    input: Box<dyn TileProducer>,
}

impl TileProducer for UncurryProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::CurriedFunction {
                domain1,
                offsets,
                domain2,
                codomain,
                domain_predicate,
                ..
            } => {
                // Extract offsets as a vec of usize.
                let ColumnValue::UInts(offsets_vec) = offsets else {
                    panic!("CurriedFunction offsets must be ColumnValue::UInts");
                };

                // Build an expansion index iterator: for each group i,
                // emit i repeated (group_end - group_start) times.
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
                let expanded_domain1 =
                    domain1.select_indices(expansion_indices.into_iter(), total_rows);

                // Build the pair domain column as Record with fields _0 and _1.
                let pair_domain = ColumnValue::Records(HashMap::from([
                    (tuple_field(0), expanded_domain1),
                    (tuple_field(1), domain2),
                ]));

                let inner_pred = if domain_predicate.as_bool().unwrap_or(true) {
                    Predicate::True
                } else {
                    Predicate::False
                };
                let mut result = Tile::SealedFunction {
                    domain: pair_domain,
                    codomain: Box::new(Tile::Scalar(codomain)),
                    domain_predicate: Predicate::Record(HashMap::from([
                        (tuple_field(0), domain_predicate),
                        (tuple_field(1), inner_pred),
                    ])),
                    deleted: BitSet::new(),
                };
                result.remove_guarded(self.base().obsolete_guard.clone());
                result
            }
            _ => panic!("Uncurry expected CurriedFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let input_guard = match &obsolete_guard {
            // Pass through empty and universal guards unchanged.
            g if g.is_empty() => self.input.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            // Split domain guards on the pair domain (_0, _1) into record predicates.
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let pair_fields = HashMap::from([(tuple_field(0), ()), (tuple_field(1), ())]);

                let preds: Box<dyn Iterator<Item = &Predicate>> = match pred {
                    Predicate::Or(preds) => Box::new(preds.iter()),
                    _ => Box::new(iter::once(pred)),
                };

                let mut domain_guard = TileGuard::Function(FunctionGuard::Domain(Predicate::False));
                for pred in preds {
                    let mut split_preds = pred.split_record(&pair_fields);
                    let outer_pred = split_preds.remove(&tuple_field(0)).unwrap();
                    let inner_pred = split_preds.remove(&tuple_field(1)).unwrap();
                    if inner_pred.as_bool().is_some_and(|x| x) {
                        domain_guard = domain_guard
                            .union(&TileGuard::Function(FunctionGuard::Domain(outer_pred)));
                    }
                }
                domain_guard
            }
            g => panic!("Filter cannot honor the release guard {g:?}"),
        };
        trace!("{} releasing up with: {input_guard:?}", self.name());
        self.input.release(input_guard);
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
    /// The sealed-function input to filter.
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

    fn subscribe_impl(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            forwarding_consumer(&shared),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            forwarding_consumer(&shared),
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
            // Scalar predicate applied element-wise to a function tile's domain.
            (
                Tile::Scalar(pred),
                Tile::SealedFunction {
                    domain,
                    codomain,
                    domain_predicate,
                    deleted,
                },
            ) => match pred.as_single() {
                Some(Value::ComputableFunction(f)) => {
                    let func_result = f.apply(domain.clone());
                    let mask = func_result
                        .as_bitvec()
                        .unwrap_or_else(|| panic!("Expected boolean mask"));
                    let mut output = Tile::SealedFunction {
                        domain,
                        codomain,
                        domain_predicate,
                        deleted,
                    };
                    output.mark_deleted(mask);
                    output
                }
                _ => panic!("Filter predicate is not a function"),
            },
            // Both predicate and input are function tiles sharing the same domain.
            (
                Tile::SealedFunction {
                    domain: pred_inputs,
                    codomain: pred_outputs,
                    ..
                },
                Tile::SealedFunction {
                    domain: i_inputs,
                    codomain: i_outputs,
                    domain_predicate,
                    deleted,
                },
            ) => {
                // We rely on having the predicate and input sharing exactly the same domain
                // so that we can cheaply extract the bitmask from the predicate codomain.
                // This check is expensive, so only run it in debug builds.
                debug_assert_eq!(pred_inputs, i_inputs);
                let pred_outputs = scalar_tile_to_column_value(*pred_outputs);
                // Build a domain-value → bool map from the predicate tile.
                let mask = pred_outputs
                    .as_bitvec()
                    .unwrap_or_else(|| panic!("Expected bools"));
                let mut output = Tile::SealedFunction {
                    domain: i_inputs,
                    codomain: i_outputs,
                    domain_predicate,
                    deleted,
                };
                output.retain(mask);
                output
            }
            _ => panic!("Invalid Filter input tiles"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if matches!(self.predicate.tiling(), Tiling::SealedFunction { .. }) {
            // Both predicate and input share the same underlying domain source, so both
            // must be released together; releasing only one leaves the other's upstream
            // FanOutProducer release-guard stale, causing it to re-deliver already-consumed
            // data while the other side returns nothing on the next get().
            self.predicate.release(obsolete_guard.clone());
        }
        self.input.release(obsolete_guard);
    }
}

/// Filters the **inner collections** of a curried function, one outer key at a time.
///
/// [`Filter`] and [`Restrict`] both narrow a [`Tiling::SealedFunction`]'s single
/// domain. Neither reaches inside a [`Tiling::CurriedFunction`], where the domain
/// that a predicate selects on is `domain2` — the per-key collection — and the
/// surviving rows differ from key to key. A per-group filter (`sum([s.amount for s
/// in g if s.qty > 2])` over a `groupby`) is that shape: the refinement rides the
/// inner collection's domain, under the outer key's binder.
///
/// The predicate produces a `CurriedFunction` of `Bool` over the same keys and
/// inner domain as the input, so its flattened codomain is the mask directly —
/// row `i` of `domain2` survives iff the predicate's row `i` is `true`. The CSR
/// layout is what makes this one masked pass rather than a per-key loop: `offsets`
/// and `domain1` are untouched, and [`Tile::retain`] rebuilds `offsets` for the
/// surviving rows.
pub struct MapFilter {
    /// Output tiling, equal to the input's — filtering removes rows, not structure.
    base: OperatorBase,
    /// The curried-function input whose inner collections are filtered.
    input: Box<dyn TileOperator>,
    /// A `Bool`-codomain curried function over the input's keys and inner domain.
    predicate: Box<dyn TileOperator>,
}

impl MapFilter {
    /// Create a `MapFilter` retaining the inner-collection rows where `predicate` holds.
    ///
    /// Panics unless both operands are curried functions: the whole point of this
    /// operator is the inner domain, and a `SealedFunction` has no inner domain to
    /// filter (use [`Filter`] or [`Restrict`]).
    pub fn new(input: Box<dyn TileOperator>, predicate: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        assert!(
            matches!(tiling, Tiling::CurriedFunction { .. }),
            "MapFilter expects a CurriedFunction input, got {tiling:?}"
        );
        assert!(
            matches!(predicate.tiling(), Tiling::CurriedFunction { .. }),
            "MapFilter expects a CurriedFunction predicate, got {:?}",
            predicate.tiling()
        );
        Self {
            base: OperatorBase::new(tiling),
            input,
            predicate,
        }
    }
}

impl TileOperator for MapFilter {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
        visit(value("predicate", &*self.predicate));
    }

    fn subscribe_impl(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            forwarding_consumer(&shared),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            forwarding_consumer(&shared),
            scheduler,
        );
        Box::new(MapFilterProducer {
            base: ProducerBase::new(MapFilterProducer::alloc_id(), self.tiling()),
            input: input_producer,
            predicate: predicate_producer,
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

        let Tile::CurriedFunction {
            codomain: pred_rows,
            domain2: pred_domain2,
            ..
        } = predicate_result
        else {
            panic!("MapFilter predicate produced {predicate_result:?}, expected a CurriedFunction");
        };
        let Tile::CurriedFunction {
            domain2: input_domain2,
            ..
        } = &input_result
        else {
            panic!("MapFilter input produced {input_result:?}, expected a CurriedFunction");
        };
        // The mask is positional over the flattened rows, so the two sides must be
        // the same flattening of the same keys. They share an upstream `FanOut`, so
        // a mismatch is a planning bug rather than a data-dependent case.
        debug_assert_eq!(
            &pred_domain2, input_domain2,
            "MapFilter predicate and input must flatten the same inner domains"
        );
        let mask = pred_rows
            .as_bitvec()
            .unwrap_or_else(|| panic!("MapFilter predicate codomain is not boolean"));
        input_result.retain(mask);
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
/// The predicate operator must produce a `SealedFunction { domain: D, codomain: Bool }`.
/// `Restrict` returns `SealedFunction { domain: D', codomain: D' }` where D' ⊆ D is the
/// subset of domain elements for which the predicate is `true`.
pub struct Restrict {
    /// Output tiling — `SealedFunction(D, D)` mirroring an [`IterateExtent`] over D.
    base: OperatorBase,
    /// The boolean predicate over the domain to restrict.
    predicate: Box<dyn TileOperator>,
}

impl Restrict {
    /// Create a `Restrict` from a predicate operator.
    ///
    /// Panics if `predicate` does not have a `SealedFunction` tiling.
    pub fn new(predicate: Box<dyn TileOperator>) -> Self {
        let domain_extent = match predicate.tiling() {
            Tiling::SealedFunction { domain, .. } => domain.clone(),
            other => panic!("Restrict expects SealedFunction predicate tiling, got {other:?}"),
        };
        let tiling = Tiling::SealedFunction {
            domain: domain_extent.clone(),
            codomain: Box::new(Tiling::Scalar(domain_extent)),
        };
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

    fn subscribe_impl(
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
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                let pred_bools = scalar_tile_to_column_value(*codomain);
                let mask = pred_bools
                    .as_bitvec()
                    .unwrap_or_else(|| panic!("Restrict: expected boolean predicate codomain"));
                // Build identity: each surviving domain element maps to itself.
                let mut output = Tile::SealedFunction {
                    codomain: Box::new(Tile::Scalar(domain.clone())),
                    domain,
                    domain_predicate,
                    deleted,
                };
                output.mark_deleted(mask);
                output
            }
            _ => panic!("Restrict: predicate must produce a SealedFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.predicate.release(obsolete_guard);
    }
}

/// A column of **materialized** collection values, read as a collection per row.
///
/// A collection reaches an operator in one of two shapes, and the runtime already names
/// both: a **streamed** one carries its keys in a domain column, and a **materialized** one
/// is a single map value — `Value::Function`, a binding list carrying its own keys — which
/// is how a transactional collection's store key holds it ([`Lookup`]). Lookup reads either;
/// every consumer that wants to *iterate* a collection reads the streamed shape only. This
/// is the adapter between them: `SealedFunction { domain: 𝐷, codomain: Scalar(𝐾 ⇒ 𝑉) }`
/// becomes `CurriedFunction { domain1: 𝐷, domain2: 𝐾, codomain: 𝑉 }`, each row's bindings
/// becoming that row's group.
///
/// **A row whose collection is empty contributes no group**, because a curried-function
/// tile cannot hold one: its offsets are strictly ascending, so every group has at least
/// one entry (`validate_tile`). A consumer therefore sees that row as absent rather than as
/// an empty collection, which for an aggregate is the difference between no answer and the
/// identity.
pub struct StreamMaterialized {
    /// Output tiling: `CurriedFunction { domain1: input.domain, domain2: 𝐾, codomain: 𝑉 }`.
    base: OperatorBase,
    /// The column of collection values.
    input: Box<dyn TileOperator>,
}

impl StreamMaterialized {
    /// Whether `tiling` is a column of materialized collection values — the one shape this
    /// operator adapts, and the question a consumer asks before inserting one.
    pub fn adapts(tiling: &Tiling) -> bool {
        matches!(
            tiling,
            Tiling::SealedFunction { codomain, .. }
                if matches!(codomain.as_ref(), Tiling::Scalar(Extent::Function { .. }))
        )
    }

    /// Create a `StreamMaterialized` over a column of collection values.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::SealedFunction { domain, codomain } = input.tiling() else {
            panic!(
                "StreamMaterialized expected SealedFunction, got {:?}",
                input.tiling()
            )
        };
        let Tiling::Scalar(Extent::Function {
            domain: key,
            codomain: value,
        }) = codomain.as_ref()
        else {
            panic!(
                "StreamMaterialized expected a column of collection values, got {:?}",
                codomain
            )
        };
        let tiling = Tiling::CurriedFunction {
            domain1: domain.clone(),
            domain2: (**key).clone(),
            codomain: (**value).clone(),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for StreamMaterialized {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe_impl(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (key, value) = match self.tiling() {
            Tiling::CurriedFunction {
                domain2, codomain, ..
            } => (domain2.clone(), codomain.clone()),
            other => unreachable!("StreamMaterialized tiles as a curried function, got {other:?}"),
        };
        Box::new(StreamMaterializedProducer {
            base: ProducerBase::new(StreamMaterializedProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            key,
            value,
        })
    }
}

/// Producer for [`StreamMaterialized`].
struct StreamMaterializedProducer {
    base: ProducerBase,
    /// The upstream producer of collection values.
    input: Box<dyn TileProducer>,
    /// The key extent, for building each group's domain column.
    key: Extent,
    /// The value extent, for building each group's codomain column.
    value: Extent,
}

impl TileProducer for StreamMaterializedProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } = input_tile
        else {
            panic!("StreamMaterialized expected a SealedFunction tile, got {input_tile:?}")
        };
        let Tile::Scalar(values) = *codomain else {
            panic!("StreamMaterialized expected a scalar codomain column")
        };
        // One group per row whose collection has an entry, in row order. A row is kept by
        // index so `domain1` and the offsets stay parallel after the empty ones drop.
        let mut kept: Vec<usize> = Vec::new();
        let mut offsets: Vec<usize> = Vec::new();
        let mut keys: Vec<Value> = Vec::new();
        let mut outputs: Vec<Value> = Vec::new();
        for row in 0..values.len() {
            let Value::Function(bindings) = values.index_at(row) else {
                panic!("StreamMaterialized: a collection value is a binding list")
            };
            if bindings.is_empty() {
                continue;
            }
            kept.push(row);
            offsets.push(keys.len());
            for b in bindings {
                keys.push(b.input);
                outputs.push(b.output);
            }
        }
        let deleted = kept
            .iter()
            .enumerate()
            .filter(|(_, row)| deleted.contains(**row))
            .map(|(group, _)| group)
            .collect();
        let group_count = kept.len();
        let domain1 = domain.select_indices(kept.into_iter(), group_count);
        // **Every row delivered here is final**, which is what this operator knows and its
        // input does not. A `domain_predicate` names the region of `domain1` that will see
        // no new elements, *together with its whole list* — and a materialized map value
        // carries its own keys, so it is complete wherever it is present ([`Lookup`]). The
        // input's own region is unioned in rather than replaced: whether further rows
        // arrive is its claim, not this one's, and without the union an aggregate over a
        // live store would never reach a terminal answer for the rows it already has.
        let domain_predicate = domain_predicate.union(&Predicate::from_column_value(&domain1));
        let mut tile = Tile::curried_function(
            domain1,
            ColumnValue::UInts(offsets),
            ColumnValue::from_values(keys, &self.key),
            ColumnValue::from_values(outputs, &self.value),
            domain_predicate,
            deleted,
        );
        // **What this producer released, it drops here**, because it cannot drop it
        // upstream: a released key is one binding of a materialized map, and the map is a
        // single cell the input keeps whole. Rebuilding from that cell would hand the
        // consumer the binding a second time, which an accumulating consumer adds twice.
        tile.remove_guarded(self.obsolete_guard().clone());
        tile
    }

    /// A row releases upstream; a **key within a row** releases nothing.
    ///
    /// The output's outer domain is the input's, so a guard on it passes through. Its inner
    /// domain is the key set of one materialized map, and that map is a single cell of the
    /// input — nothing upstream holds a binding of it separately, so there is nothing to
    /// release. The row's own release is what frees it.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_universal() => self.input.release(self.input.tiling().universal_guard()),
            g if g.is_empty() => self.input.release(self.input.tiling().empty_guard()),
            TileGuard::Function(FunctionGuard::Domain(p)) => self
                .input
                .release(TileGuard::Function(FunctionGuard::Domain(p))),
            TileGuard::Function(FunctionGuard::Codomain(_)) => {}
            // A consumer that has taken a whole row names both halves — the keys it
            // folded and the row they came from — so the arms are applied in turn and the
            // row half is the one that reaches the input.
            TileGuard::Or(arms) => {
                for arm in arms {
                    self.release_impl(arm);
                }
            }
            g => todo!("StreamMaterialized cannot honor the release guard {g:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
    use crate::interpreter::{BaseType, ColumnValue, Extent};

    #[test]
    fn uncurry_producer_basic() {
        // Test UncurryProducer.get_impl with a simple CurriedFunction
        //
        // Creates a CurriedFunction with:
        // - domain1: [1, 2] (two keys)
        // - offsets: [0, 2] (key 1 has 2 items, key 2 has 1 item [implicit end at domain2.len()])
        // - domain2: [10, 20, 30] (flattened second-level domain)
        // - codomain: [100, 200, 300] (flattened codomain)
        //
        // Expected expansion_indices: [0, 0, 1] (key 0 repeated 2 times, key 1 repeated 1 time)
        // Expected expanded_domain1: [1, 1, 2]
        // Expected pair domain: Record with _0=[1,1,2] and _1=[10,20,30]

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2]),
            offsets: ColumnValue::UInts(vec![0, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![100, 200, 300]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling.clone());

        // Create UncurryProducer with the test producer as input
        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        // Get the result from UncurryProducer
        let result = uncurry.get(uncurry.tiling().universal_guard());

        // Verify the result is a SealedFunction
        match result {
            Tile::SealedFunction {
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
            _ => panic!("Expected SealedFunction result"),
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

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![100, 200, 300]),
            offsets: ColumnValue::UInts(vec![0, 1, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![1, 2, 3]),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
                domain,
                codomain: _,
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

                // Verify domain_predicate is transformed appropriately
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::False),
                        (tuple_field(1), Predicate::False),
                    ])),
                    "domain_predicate should be preserved"
                );
            }
            _ => panic!("Expected SealedFunction result"),
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

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2, 3]),
            offsets: ColumnValue::UInts(vec![0, 1, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![100, 200, 300]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
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
            _ => panic!("Expected SealedFunction result"),
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

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2]),
            offsets: ColumnValue::UInts(vec![0, 1]),
            domain2: ColumnValue::UInts(vec![10, 20]),
            codomain: ColumnValue::UInts(vec![100, 200]),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
                domain_predicate, ..
            } => {
                // Verify domain_predicate is transformed into a Record with both fields False
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::False),
                        (tuple_field(1), Predicate::False),
                    ])),
                    "domain_predicate should be transformed into Record(_0: False, _1: False)"
                );
            }
            _ => panic!("Expected SealedFunction result"),
        }
    }

    /// Build a `ConverseProducer` wrapping the given input tile and call `get`.
    fn run_converse(input_tile: Tile, input_tiling: Tiling) -> Tile {
        let output_tiling = {
            let (domain, codomain) = input_tiling.split_function_extent().unwrap();
            Tiling::CurriedFunction {
                domain1: codomain,
                domain2: domain.clone(),
                codomain: domain,
            }
        };
        let mut producer = ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
        };
        producer.get(producer.tiling().universal_guard())
    }

    fn sealed_fn_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: Extent::Base(BaseType::Int),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// Basic converse: `{0→10, 1→20, 2→10}` groups by codomain value.
    /// Expected output: domain1=[10,20], each group lists the domain values that map to it.
    #[test]
    fn converse_producer_basic_grouping() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 10]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            domain_predicate,
            deleted,
            ..
        } = result
        else {
            panic!("expected CurriedFunction");
        };
        // Two distinct codomain values: 10 and 20.
        assert_eq!(domain1, ColumnValue::Ints(vec![10, 20]));
        // Group for 10 starts at 0 (rows 0 and 2 map to 10); group for 20 starts at 2.
        assert_eq!(offsets, ColumnValue::UInts(vec![0, 2]));
        // domain2 is sorted by codomain key: [0, 2] for key 10, then [1] for key 20.
        assert_eq!(domain2, ColumnValue::Ints(vec![0, 2, 1]));
        assert_eq!(domain_predicate, Predicate::True);
        assert!(deleted.is_empty(), "no deleted entries expected");
    }

    /// Converse with no deleted entries on a single-entry input is a trivial sanity check.
    #[test]
    fn converse_producer_single_entry_no_deleted() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![42]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction { deleted, .. } = result else {
            panic!("expected CurriedFunction");
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
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![20, 10, 20]))),
            domain_predicate: Predicate::True,
            deleted: input_deleted,
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction {
            deleted, domain2, ..
        } = result
        else {
            panic!("expected CurriedFunction");
        };
        // Sorted order: row 1 (key 10) first, then row 0 (key 20), then row 2 (key 20).
        // Output position 1 holds original row 0, which was deleted.
        assert_eq!(domain2, ColumnValue::Ints(vec![1, 0, 2]));
        let mut expected = BitSet::new();
        expected.insert(1);
        assert_eq!(deleted, expected);
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
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![30, 10, 20, 10]))),
            domain_predicate: Predicate::True,
            deleted: input_deleted,
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction { deleted, .. } = result else {
            panic!("expected CurriedFunction");
        };
        let mut expected = BitSet::new();
        expected.insert(0);
        expected.insert(1);
        assert_eq!(deleted, expected);
    }
}

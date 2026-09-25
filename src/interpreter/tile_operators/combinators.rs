use bit_set::BitSet;
use bit_vec::BitVec;
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
    /// Output tiling: `DataFunction { domain: Record { _0: A, _1: B }, codomain: Scalar(C) }`.
    base: OperatorBase,
    /// The two-level input.
    input: Box<dyn TileOperator>,
}

impl Uncurry {
    /// Create an `Uncurry` operator that flattens two collection levels into one.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        // Flattening pairs a collection with the one inside it, so it takes exactly that:
        // a collection whose values are a collection. A deeper one flattens a level at a
        // time.
        let Tiling::DataFunction {
            domain: outer,
            codomain: inner,
        } = input.tiling()
        else {
            panic!("Uncurry expected a collection, got {:?}", input.tiling())
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
        let tiling = Tiling::DataFunction {
            domain: pair_extent,
            codomain: codomain.clone(),
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
        })
    }
}

/// Producer for [`Uncurry`]: flattens a two-level tile into a one-level tile with pair domain.
struct UncurryProducer {
    base: ProducerBase,
    /// The upstream producer whose two levels are flattened.
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
            Tile::DataFunction {
                domain: domain1,
                codomain: inner,
                domain_predicate,
                ..
            } => {
                let Tile::DataFunction {
                    row_starts,
                    domain: domain2,
                    codomain,
                    ..
                } = *inner
                else {
                    panic!("Uncurry flattens two collections")
                };
                let domain2 = &domain2;
                let codomain = scalar_tile_to_column_value(*codomain);
                let ColumnValue::UInts(offsets_vec) = &row_starts else {
                    panic!("row starts are UInts");
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
                    (tuple_field(1), domain2.clone()),
                ]));

                let inner_pred = if domain_predicate.as_bool().unwrap_or(true) {
                    Predicate::True
                } else {
                    Predicate::False
                };
                let mut result = Tile::data_function(
                    pair_domain,
                    Box::new(Tile::Scalar(codomain)),
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), domain_predicate),
                        (tuple_field(1), inner_pred),
                    ])),
                    BitSet::new(),
                );
                result.remove_guarded(self.base().obsolete_guard.clone());
                result
            }
            _ => panic!("Uncurry expected DataFunction tile"),
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
    /// The two-level input whose inner collections are filtered.
    input: Box<dyn TileOperator>,
    /// A `Bool`-codomain two-level function over the input's keys and inner domain.
    predicate: Box<dyn TileOperator>,
}

impl MapFilter {
    /// Create a `MapFilter` retaining the inner-collection rows where `predicate` holds.
    ///
    /// Panics unless both operands hold two levels: the whole point of this
    /// operator is the inner domain, and a one-level collection has no inner domain to
    /// filter (use [`Filter`] or [`Restrict`]).
    pub fn new(input: Box<dyn TileOperator>, predicate: Box<dyn TileOperator>) -> Self {
        let two_levels = |tiling: &Tiling| {
            matches!(tiling, Tiling::DataFunction { codomain, .. }
                if matches!(codomain.as_ref(), Tiling::DataFunction { codomain: inner, .. }
                    if !inner.holds_a_level()))
        };
        let tiling = input.tiling().clone();
        assert!(
            two_levels(&tiling),
            "MapFilter expects a two-level DataFunction input, got {tiling:?}"
        );
        assert!(
            two_levels(predicate.tiling()),
            "MapFilter expects a two-level DataFunction predicate, got {:?}",
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

    fn subscribe(
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

        let Tile::DataFunction {
            codomain: pred_inner_tile,
            ..
        } = predicate_result
        else {
            panic!("MapFilter predicate produced a non-collection");
        };
        let Tile::DataFunction {
            domain: pred_inner,
            codomain: pred_rows,
            ..
        } = *pred_inner_tile
        else {
            panic!("MapFilter predicate is not a collection of collections");
        };
        let Tile::DataFunction {
            codomain: inner, ..
        } = &input_result
        else {
            panic!("MapFilter input produced {input_result:?}, expected a collection");
        };
        let Tile::DataFunction {
            domain: input_inner,
            ..
        } = inner.as_ref()
        else {
            panic!("MapFilter input is not a collection of collections");
        };
        let pred_inner = &pred_inner;
        // The mask is positional over the flattened rows, so the two sides must be
        // the same flattening of the same keys. They share an upstream `FanOut`, so
        // a mismatch is a planning bug rather than a data-dependent case.
        debug_assert_eq!(
            pred_inner, input_inner,
            "MapFilter predicate and input must flatten the same inner domains"
        );
        let pred_column = scalar_tile_to_column_value(*pred_rows);
        let mask = pred_column
            .as_bitvec()
            .unwrap_or_else(|| panic!("MapFilter predicate codomain is not boolean"));
        let Tile::DataFunction {
            codomain: inner, ..
        } = &mut input_result
        else {
            unreachable!("the shape was matched above")
        };
        inner.retain_keys(mask);
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

/// Each row of one stream paired with every element of another's domain — the cartesian
/// product that makes a correlated inner comprehension compilable.
///
/// `lambda_elim` turns `[… f(r, v) … for v in xs]` written inside a `for r in …` into a
/// curried morphism over the outer collection, taking the pair `(r, v)`. Compiling that means
/// running the morphism once per pair and grouping the results by the outer row, which is a
/// [`Tiling::DataFunction`] under another — a collection per row. This builds the pairs; the morphism
/// then compiles over them like any other morphism over a stream, and the grouping is
/// already there because this operator emits it.
///
/// **The inner side is a stream, not an extent**, and that is what lets one builder serve
/// both sources a comprehension can have. A list literal's domain is an index range, so the
/// inner collection is an `IterateExtent` over it. A map's is its present-key refinement,
/// which `extent_of` strips to answer the unbounded key type, so the inner collection is
/// `MapDomain` of the collection instead. Both carry that domain in their codomain, which
/// is all this reads.
///
/// The codomain is the pair the morphism reads: `_0` the row's value, `_1` the element.
pub struct Product {
    /// Output tiling: the outer's levels with the inner domain appended, over the codomain
    /// `{_0: outer codomain, _1: inner inner_domain}`.
    base: OperatorBase,
    /// The outer collection, one group per row.
    outer: Box<dyn TileOperator>,
    /// The inner collection, whose codomain is the domain every group holds.
    inner: Box<dyn TileOperator>,
}

impl Product {
    /// Pair every row of `outer` with every element of the domain `inner` carries.
    pub fn new(outer: Box<dyn TileOperator>, inner: Box<dyn TileOperator>) -> Self {
        // The outer collection is either one level of rows or already grouped
        // by earlier pairings. Pairing appends a level either way, which is what makes
        // correlated nesting unbounded in depth ([`Tiling::append_level`]).
        let outer_tiling = outer.tiling();
        assert!(
            outer_tiling.is_data_function(),
            "Product expected a collection as its outer operand, got {outer_tiling:?}"
        );
        let outer_codomain = outer_tiling.deepest_values().extent();
        let Tiling::DataFunction {
            codomain: inner_domain,
            ..
        } = inner.tiling()
        else {
            panic!(
                "Product reads the inner domain off a collection's values, got {:?}",
                inner.tiling()
            )
        };
        let inner_domain = inner_domain.extent();
        // The row's value as one extent, however many columns carry it: a product row
        // spreads over a column per field, and the pair this builds holds it whole.
        let tiling = outer_tiling.append_level(
            inner_domain.clone(),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), outer_codomain),
                (tuple_field(1), inner_domain),
            ]))),
        );
        Self {
            base: OperatorBase::new(tiling),
            outer,
            inner,
        }
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
        Box::new(ProductProducer {
            base: ProducerBase::new(ProductProducer::alloc_id(), self.tiling()),
            outer: self.outer.subscribe(
                self.outer.tiling().universal_guard(),
                forwarding_consumer(&shared),
                scheduler,
            ),
            inner: self.inner.subscribe(
                self.inner.tiling().universal_guard(),
                forwarding_consumer(&shared),
                scheduler,
            ),
            inner_domain: None,
        })
    }
}

/// `outer`'s rows paired against an inner side that has not delivered its domain yet: no
/// groups at all.
///
/// A group is the whole inner domain, so one built before the inner side is terminal could
/// still gain elements — and a group that can grow is what the layout cannot hold
/// ([`Tile::append_level`]). Emitting no rows claims nothing about them, which is why the
/// region is `False` rather than whatever `outer` has decided.
///
/// An inner side that is terminal and empty is a different fact: every row is present and
/// pairs with nothing.
fn unpaired_rows(outer: &Tile) -> Tile {
    let Tile::DataFunction { domain, .. } = outer else {
        panic!("Product expected a collection as its outer tile, got {outer:?}")
    };
    // Dropping every key empties the levels beneath it too, so what is left is the outer's
    // shape holding nothing — which is what the appended level then sits over.
    let mut emptied = outer.clone();
    emptied.retain_keys(&BitVec::from_elem(domain.len(), false));
    let mut tile = emptied.append_level(|values| {
        let outer = scalar_tile_to_column_value(values);
        let inner = ColumnValue::UInts(Vec::new());
        Tile::grouped(
            ColumnValue::UInts(Vec::new()),
            inner.clone(),
            Box::new(Tile::Scalar(ColumnValue::Records(HashMap::from([
                (tuple_field(0), outer),
                (tuple_field(1), inner),
            ])))),
            Predicate::False,
            BitSet::new(),
        )
    });
    let Tile::DataFunction {
        domain_predicate, ..
    } = &mut tile
    else {
        unreachable!("append_level leaves a collection")
    };
    *domain_predicate = Predicate::False;
    tile
}

/// Producer for [`Product`].
struct ProductProducer {
    base: ProducerBase,
    /// The outer collection.
    outer: Box<dyn TileProducer>,
    /// The inner collection, read once for its inner_domain.
    inner: Box<dyn TileProducer>,
    /// The inner_domain, kept after the inner collection has delivered all of them.
    ///
    /// **Every group holds the whole domain**, so a row cannot be emitted until the inner
    /// side is complete — a group built from a prefix would claim a row finished with
    /// elements still to come. The inner side of a correlated comprehension is closed over
    /// the outer binder, so it is the same stream for every row and reading it once is all
    /// this needs.
    inner_domain: Option<ColumnValue>,
}

impl TileProducer for ProductProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("outer", self.outer.inspect(opts))
            .child("inner", self.inner.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        if self.inner_domain.is_none() {
            let inner_tile = self.inner.get(self.inner.tiling().universal_guard());
            if inner_tile.is_terminal() {
                let Tile::DataFunction { codomain, .. } = inner_tile else {
                    panic!("Product expected a collection as its inner tile")
                };
                self.inner_domain = Some(scalar_tile_to_column_value(*codomain));
            }
        }
        let outer_tile = self.outer.get(self.outer.tiling().universal_guard());
        let Some(inner_domain) = self.inner_domain.clone() else {
            return unpaired_rows(&outer_tile);
        };
        let width = inner_domain.len();
        // Every group is the whole inner domain, so a row is complete as soon as it
        // arrives — the group [`Tile::append_level`] needs whole. An inner domain that is
        // terminal and empty pairs every row with nothing, which equal starts carry.
        let mut tile = outer_tile.append_level(|codomain| {
            let outer = scalar_tile_to_column_value(codomain);
            let rows = outer.len();
            let total = rows * width;
            // Row-major: row `r` occupies `r * width .. (r + 1) * width`, so the row's
            // value repeats across its own group and the inner domain repeats across rows.
            let keys = inner_domain.select_indices((0..total).map(|i| i % width), total);
            Tile::grouped(
                ColumnValue::UInts((0..rows).map(|r| r * width).collect()),
                keys.clone(),
                Box::new(Tile::Scalar(ColumnValue::Records(HashMap::from([
                    (
                        tuple_field(0),
                        outer.select_indices((0..total).map(|i| i / width), total),
                    ),
                    (tuple_field(1), keys),
                ])))),
                Predicate::False,
                BitSet::new(),
            )
        });
        tile.remove_guarded(self.obsolete_guard().clone());
        tile
    }

    /// A row releases to the **outer** stream; an element within a row releases nothing.
    ///
    /// The domain is the inner collection's whole content, held here because every group
    /// holds all of them, so one group being done says nothing about them. The inner side
    /// is released when everything is.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_universal() => {
                self.outer.release(self.outer.tiling().universal_guard());
                self.inner.release(self.inner.tiling().universal_guard());
            }
            g if g.is_empty() => self.outer.release(self.outer.tiling().empty_guard()),
            TileGuard::Function(FunctionGuard::Domain(p)) => self
                .outer
                .release(TileGuard::Function(FunctionGuard::Domain(p))),
            TileGuard::Function(FunctionGuard::Codomain(_)) => {}
            TileGuard::Or(arms) => {
                for arm in arms {
                    self.release_impl(arm);
                }
            }
            g => todo!("Product cannot honor the release guard {g:?}"),
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
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::DataFunction {
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
    /// Pairing appends a level, so the outer's levels are the output's level for level and
    /// a removed outer row stays marked where it already was. `compact` takes the group of
    /// pairs it opened.
    #[test]
    fn product_removes_an_outer_row_at_its_own_level() {
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
            inner_domain: None,
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction {
            codomain, deleted, ..
        } = &out
        else {
            panic!("Product tiles as a collection of collections")
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            deleted: pairs_deleted,
            ..
        } = codomain.as_ref()
        else {
            panic!("the paired level is a collection")
        };
        assert_eq!(
            *row_starts,
            ColumnValue::from_uints(vec![0, 2]),
            "each row pairs with both inner elements"
        );
        assert_eq!(domain.len(), 4, "four flat pairs");
        let mut expected = BitSet::new();
        expected.insert(0);
        assert_eq!(*deleted, expected, "outer row 0 is marked, as a row");
        assert!(
            pairs_deleted.is_empty(),
            "the pairs it opened are not; `compact` takes them with it"
        );
    }
}

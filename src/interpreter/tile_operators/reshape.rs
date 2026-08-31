use std::collections::HashMap;

use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Extent, Scheduler, tuple_field},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// An operator that permutes the fields of the domain of a `SealedFunction`, according
/// to a specified permutation of field indices.
///
/// For now, this only supports record types that represent tuples, but can
/// be extended if needed.
pub struct PermuteRecordDomain {
    input: Box<dyn TileOperator>,
    /// Identity and the output tiling: the input's `SealedFunction` with its
    /// `Record` domain permuted.
    base: OperatorBase,
    permutation: Vec<usize>,
}

fn permute_record<T>(mut input: HashMap<String, T>, permutation: &[usize]) -> HashMap<String, T> {
    HashMap::from_iter(permutation.iter().enumerate().map(|(idx, target)| {
        (
            tuple_field(idx),
            input
                .remove(&tuple_field(*target))
                .unwrap_or_else(|| panic!("Input record missing {target}")),
        )
    }))
}

impl PermuteRecordDomain {
    pub fn new(input: Box<dyn TileOperator>, permutation: Vec<usize>) -> Self {
        let Tiling::SealedFunction { domain, codomain } = input.tiling() else {
            panic!(
                "PermuteRecordDomain requires SealedFunction input, got {}",
                input.tiling()
            );
        };
        let Extent::Record(input_fields) = domain else {
            panic!(
                "PermuteRecordDomain requires input with Record domain, got {}",
                input.tiling()
            );
        };
        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(permute_record(input_fields.clone(), &permutation)),
            codomain: codomain.clone(),
        };
        Self {
            input,
            base: OperatorBase::new(tiling),
            permutation,
        }
    }
}

impl TileOperator for PermuteRecordDomain {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(PermuteRecordDomainProducer {
            base: ProducerBase::new(PermuteRecordDomainProducer::alloc_id(), &self.base.tiling),
            input: self.input.subscribe(intent_guard, consumer, scheduler),
            permutation: self.permutation.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        permute_result_correlation(self.input.result_correlation()?, &self.permutation)
    }
}

/// Translates a `result_correlation` path through a `PermuteRecordDomain` operation.
///
/// The first `Record` step in `corr` names a field in the INPUT domain; after permutation,
/// that field is at the inverse-permuted index in the output domain. An empty path (domain
/// identity) cannot be preserved because the domain is renamed while the codomain is not.
fn permute_result_correlation(
    mut corr: Vec<TilePathStep>,
    permutation: &[usize],
) -> Option<Vec<TilePathStep>> {
    let Some(TilePathStep::Record(f)) = corr.first_mut() else {
        // Empty path means domain == codomain; permuting domain breaks that identity.
        // Non-Record first steps (e.g. Codomain) are unaffected by domain renaming.
        return if corr.is_empty() { None } else { Some(corr) };
    };

    // Build inverse permutation: inv_perm[j] = i where permutation[i] = j.
    // Input field _j is now at output field _inv_perm[j].
    let mut inv_perm = vec![0usize; permutation.len()];
    for (i, &target) in permutation.iter().enumerate() {
        inv_perm[target] = i;
    }
    let j = tuple_field_index(f);
    *f = tuple_field(inv_perm[j]);
    Some(corr)
}

struct PermuteRecordDomainProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    // TODO support non-tuple records
    permutation: Vec<usize>,
}

impl TileProducer for PermuteRecordDomainProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } = input_tile
        else {
            unreachable!();
        };
        let ColumnValue::Records(input_fields) = domain else {
            unreachable!();
        };
        let output_domain = ColumnValue::Records(permute_record(input_fields, &self.permutation));
        let output_domain_pred = match domain_predicate {
            g @ Predicate::True | g @ Predicate::False => g,
            Predicate::Record(fields) => {
                Predicate::Record(permute_record(fields, &self.permutation))
            }
            _ => unreachable!(),
        };
        Tile::SealedFunction {
            domain: output_domain,
            codomain,
            domain_predicate: output_domain_pred,
            deleted,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let upstream_guard = match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(Predicate::Record(fields))) => {
                TileGuard::Function(FunctionGuard::Domain(Predicate::Record(permute_record(
                    fields,
                    &self.permutation,
                ))))
            }
            g => unreachable!("PermuteRecordDomain cannot honor the release guard {g:?}"),
        };
        self.input.release(upstream_guard);
    }
}

/// Parses the numeric index from a tuple field name like `"_3"`.
fn tuple_field_index(field: &str) -> usize {
    field
        .strip_prefix('_')
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| panic!("non-tuple field name: {field}"))
}

/// Converts a `Predicate` written over a nested-record domain into one over the flat
/// positional-tuple domain produced by `FlattenTupleDomain`.
///
/// `field_map[i]` describes where flat field `_i` came from in the nested record:
/// - `(outer_key, None)` — `_i` is the outer field `outer_key` passed through unchanged.
/// - `(outer_key, Some(inner_key))` — `_i` was flattened out of the sub-record at `outer_key`,
///   specifically its field `inner_key`.
///
/// Example: nested type `{a: {x: T, y: T}, b: T}` flattens to `(_0, _1, _2)` with
/// `field_map = [("a", Some("x")), ("a", Some("y")), ("b", None)]`.
/// A predicate `{a: {x: P1, y: P2}, b: P3}` on the nested domain becomes
/// `{_0: P1, _1: P2, _2: P3}` on the flat domain.
fn flatten_predicate(pred: &Predicate, field_map: &[(String, Option<String>)]) -> Predicate {
    match pred {
        Predicate::True | Predicate::False => pred.clone(),
        Predicate::Record(outer_preds) => Predicate::Record(
            field_map
                .iter()
                .enumerate()
                .map(|(out_idx, (outer_k, inner_k_opt))| {
                    let outer_pred = outer_preds
                        .get(outer_k)
                        .unwrap_or_else(|| panic!("missing outer field {outer_k} in predicate"));
                    let out_pred = match inner_k_opt {
                        None => outer_pred.clone(),
                        Some(inner_k) => match outer_pred {
                            Predicate::True => Predicate::True,
                            Predicate::False => Predicate::False,
                            Predicate::Record(inner_preds) => {
                                inner_preds.get(inner_k).cloned().unwrap_or_else(|| {
                                    panic!("missing inner field {inner_k} in sub-predicate")
                                })
                            }
                            p => panic!("unexpected predicate for outer field {outer_k}: {p:?}"),
                        },
                    };
                    (tuple_field(out_idx), out_pred)
                })
                .collect(),
        ),
        p => panic!("FlattenTupleDomain: unsupported domain predicate: {p:?}"),
    }
}

/// Converts a flat-domain `Predicate` back into a nested-tuple `Predicate`.
///
/// Inverse of [`flatten_predicate`]; used when propagating release guards upstream.
fn unflatten_predicate(pred: &Predicate, field_map: &[(String, Option<String>)]) -> Predicate {
    match pred {
        Predicate::True | Predicate::False => pred.clone(),
        Predicate::Record(flat_preds) => {
            let mut outer_groups: HashMap<String, HashMap<String, Predicate>> = HashMap::new();
            let mut pass_through: HashMap<String, Predicate> = HashMap::new();
            for (out_idx, (outer_k, inner_k_opt)) in field_map.iter().enumerate() {
                let flat_pred = flat_preds
                    .get(&tuple_field(out_idx))
                    .unwrap_or_else(|| panic!("missing flat field _{out_idx} in predicate"))
                    .clone();
                match inner_k_opt {
                    None => {
                        pass_through.insert(outer_k.clone(), flat_pred);
                    }
                    Some(inner_k) => {
                        outer_groups
                            .entry(outer_k.clone())
                            .or_default()
                            .insert(inner_k.clone(), flat_pred);
                    }
                }
            }
            let mut result: HashMap<String, Predicate> = pass_through;
            for (outer_k, inner_preds) in outer_groups {
                result.insert(outer_k, Predicate::Record(inner_preds));
            }
            Predicate::Record(result)
        }
        Predicate::Or(preds) => Predicate::Or(
            preds
                .iter()
                .map(|p| unflatten_predicate(p, field_map))
                .collect(),
        ),
        p => panic!("FlattenTupleDomain: unsupported flat predicate: {p:?}"),
    }
}

/// Translates a `result_correlation` path through a [`FlattenTupleDomain`] operation.
///
/// `field_map[i] = (outer_key, inner_key_opt)` describes how the input's nested domain maps to
/// the flat output domain. A two-step `[Record(outer), Record(inner), ...]` path collapses to
/// `[Record(flat_i), ...]` where `flat_i` is the index in `field_map` matching `(outer, Some(inner))`.
/// A single `[Record(outer)]` step is preserved only when `outer` is a pass-through field
/// (`inner_key_opt = None`); flattened outer fields expand to multiple flat fields and cannot
/// be expressed as a single path step, so `None` is returned. An empty path (domain == codomain
/// identity) is also not preservable after flattening and returns `None`.
fn flatten_result_correlation(
    corr: Vec<TilePathStep>,
    field_map: &[(String, Option<String>)],
) -> Option<Vec<TilePathStep>> {
    let Some(first) = corr.first() else {
        return None; // empty path: flat domain ≠ nested codomain
    };
    match first {
        TilePathStep::Codomain => Some(corr), // codomain steps are unaffected by domain renaming
        TilePathStep::Record(outer_key) => {
            let outer_key = outer_key.clone();
            match corr.get(1) {
                Some(TilePathStep::Record(inner_key)) => {
                    // Two-level path: collapse [Record(outer), Record(inner)] to [Record(flat_i)].
                    let inner_key = inner_key.clone();
                    let flat_idx = field_map.iter().position(|(ok, ik)| {
                        ok == &outer_key && ik.as_deref() == Some(inner_key.as_str())
                    })?;
                    let mut result = vec![TilePathStep::Record(tuple_field(flat_idx))];
                    result.extend_from_slice(&corr[2..]);
                    Some(result)
                }
                _ => {
                    // Single Record step: valid only for pass-through (non-flattened) outer fields.
                    let flat_idx = field_map
                        .iter()
                        .position(|(ok, ik)| ok == &outer_key && ik.is_none())?;
                    let mut result = vec![TilePathStep::Record(tuple_field(flat_idx))];
                    result.extend_from_slice(&corr[1..]);
                    Some(result)
                }
            }
        }
    }
}

/// Flattens selected fields of a `SealedFunction` whose domain is a tuple into a single-level tuple domain.
///
/// Only outer fields whose indices appear in `indices_to_flatten` are expanded; all other outer
/// fields are passed through unchanged. For flattened fields, the inner `Record` fields are
/// spliced in sequence. Only one level is flattened; inner fields that are themselves records
/// are preserved unchanged.
///
/// For example, with domain `(_0: (_0: A, (_0: B, _1: C)), _1: (_0: D), _2: E)` and `indices_to_flatten = [0, 1]`,
/// the output domain is `(_0: A, _1: (_0: B, _1: C), _2: D, _3: E)`.
pub struct FlattenTupleDomain {
    /// Identity and the output tiling: `SealedFunction` with a single-level
    /// `Record` domain.
    base: OperatorBase,
    /// Input operator whose domain is a `Record`.
    input: Box<dyn TileOperator>,
    /// Maps output field index `i` to `(outer_field_key, inner_field_key_opt)`.
    ///
    /// `inner_field_key_opt = Some(k)` for flattened fields; `None` for pass-through fields.
    field_map: Vec<(String, Option<String>)>,
}

impl FlattenTupleDomain {
    /// Create a `FlattenTupleDomain` operator.
    ///
    /// Outer fields whose tuple index is in `indices_to_flatten` must be `Record`-typed and will
    /// be expanded; all other outer fields are passed through as-is. Panics if the input tiling
    /// is not a `SealedFunction` with a `Record` domain, or if a field marked for flattening is
    /// not a `Record`.
    pub fn new(input: Box<dyn TileOperator>, indices_to_flatten: Vec<usize>) -> Self {
        let Tiling::SealedFunction { domain, codomain } = input.tiling() else {
            panic!(
                "FlattenTupleDomain requires SealedFunction input, got {}",
                input.tiling()
            )
        };
        let Extent::Record(outer_fields) = domain else {
            panic!(
                "FlattenTupleDomain requires a Record domain, got {}",
                input.tiling()
            )
        };

        let mut sorted_outer: Vec<(&String, &Extent)> = outer_fields.iter().collect();
        sorted_outer.sort_by_key(|(k, _)| tuple_field_index(k));

        let mut field_map: Vec<(String, Option<String>)> = Vec::new();
        let mut flat_extent: HashMap<String, Extent> = HashMap::new();
        let mut out_idx = 0usize;

        for (outer_key, outer_extent) in sorted_outer {
            let outer_idx = tuple_field_index(outer_key);
            if indices_to_flatten.contains(&outer_idx) {
                let Extent::Record(inner_fields) = outer_extent else {
                    panic!(
                        "FlattenTupleDomain: outer field {outer_key} marked for flattening is not a Record, got {outer_extent}"
                    )
                };
                let mut sorted_inner: Vec<(&String, &Extent)> = inner_fields.iter().collect();
                sorted_inner.sort_by_key(|(k, _)| tuple_field_index(k));
                for (inner_key, inner_extent) in sorted_inner {
                    field_map.push((outer_key.clone(), Some(inner_key.clone())));
                    flat_extent.insert(tuple_field(out_idx), inner_extent.clone());
                    out_idx += 1;
                }
            } else {
                field_map.push((outer_key.clone(), None));
                flat_extent.insert(tuple_field(out_idx), outer_extent.clone());
                out_idx += 1;
            }
        }

        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(flat_extent),
            codomain: codomain.clone(),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
            field_map,
        }
    }
}

impl TileOperator for FlattenTupleDomain {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &self.base.tiling),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            field_map: self.field_map.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        flatten_result_correlation(self.input.result_correlation()?, &self.field_map)
    }
}

/// Producer for [`FlattenTupleDomain`]: rewrites a nested-tuple domain tile to a flat one.
struct FlattenTupleDomainProducer {
    base: ProducerBase,
    /// Upstream producer whose domain is a tuple of tuples.
    input: Box<dyn TileProducer>,
    /// Maps output field index `i` to `(outer_field_key, inner_field_key_opt)`.
    ///
    /// `inner_field_key_opt = Some(k)` for flattened fields; `None` for pass-through fields.
    field_map: Vec<(String, Option<String>)>,
}

impl TileProducer for FlattenTupleDomainProducer {
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
            panic!("FlattenTupleDomain expected SealedFunction tile");
        };
        let ColumnValue::Records(outer_cols) = domain else {
            panic!("FlattenTupleDomain expected Records domain column");
        };

        let flat_domain = ColumnValue::Records(
            self.field_map
                .iter()
                .enumerate()
                .map(|(out_idx, (outer_k, inner_k_opt))| {
                    let col = match inner_k_opt {
                        None => outer_cols
                            .get(outer_k)
                            .cloned()
                            .unwrap_or_else(|| panic!("missing outer column {outer_k}")),
                        Some(inner_k) => match outer_cols.get(outer_k) {
                            Some(ColumnValue::Records(inner_map)) => inner_map
                                .get(inner_k)
                                .cloned()
                                .unwrap_or_else(|| panic!("missing inner column {inner_k}")),
                            _ => panic!("outer column {outer_k} is not a Records ColumnValue"),
                        },
                    };
                    (tuple_field(out_idx), col)
                })
                .collect(),
        );

        let flat_pred = flatten_predicate(&domain_predicate, &self.field_map);

        Tile::SealedFunction {
            domain: flat_domain,
            codomain,
            domain_predicate: flat_pred,
            deleted,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let upstream_guard = match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(pred)) => TileGuard::Function(
                FunctionGuard::Domain(unflatten_predicate(&pred, &self.field_map)),
            ),
            g => panic!("FlattenTupleDomain: unsupported obsolete guard: {g:?}"),
        };
        self.input.release(upstream_guard);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::TestTileProducer;
    use crate::interpreter::{BaseType, ColumnValue, Extent};
    use bit_set::BitSet;

    // ── FlattenTupleDomain helpers ────────────────────────────────────────────

    /// Build the nested outer `Extent` used by the `FlattenTupleDomain` tests:
    /// `(_0: (Int, Int), _1: (Int,))`.
    fn nested_outer_extent() -> Extent {
        let inner0 = Extent::Record(HashMap::from([
            (tuple_field(0), Extent::Base(BaseType::Int)),
            (tuple_field(1), Extent::Base(BaseType::Int)),
        ]));
        let inner1 = Extent::Record(HashMap::from([(
            tuple_field(0),
            Extent::Base(BaseType::Int),
        )]));
        Extent::Record(HashMap::from([
            (tuple_field(0), inner0),
            (tuple_field(1), inner1),
        ]))
    }

    /// `FlattenTupleDomain::new` produces the correct flat domain tiling.
    ///
    /// Input domain: `(_0: (Int, Int), _1: (Int,))`
    /// Expected output domain: `(_0: Int, _1: Int, _2: Int)`
    #[test]
    fn flatten_tuple_domain_tiling_is_correct() {
        // IterateExtent produces SealedFunction(outer → outer); the codomain is
        // irrelevant here — FlattenTupleDomain only inspects the domain.
        let input = Box::new(IterateExtent::new(nested_outer_extent()));
        let op = FlattenTupleDomain::new(input, vec![0, 1]);
        let Tiling::SealedFunction { domain, .. } = op.tiling() else {
            panic!("expected SealedFunction tiling");
        };
        let Extent::Record(fields) = domain else {
            panic!("expected Record domain");
        };
        assert_eq!(fields.len(), 3);
        assert!(matches!(
            fields.get("_0"),
            Some(Extent::Base(BaseType::Int))
        ));
        assert!(matches!(
            fields.get("_1"),
            Some(Extent::Base(BaseType::Int))
        ));
        assert!(matches!(
            fields.get("_2"),
            Some(Extent::Base(BaseType::Int))
        ));
    }

    /// `flatten_predicate` with `Predicate::True` is a no-op (passes through).
    ///
    /// Input domain: `{ _0: { _0: [10, 20], _1: [30, 40] }, _1: { _0: [50, 60] } }`
    /// Expected output columns after flattening: `{ _0: [10,20], _1: [30,40], _2: [50,60] }`.
    #[test]
    fn flatten_tuple_domain_get_flattens_columns() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let outer_cols = HashMap::from([
            (
                tuple_field(0),
                ColumnValue::Records(HashMap::from([
                    (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                    (tuple_field(1), ColumnValue::Ints(vec![30, 40])),
                ])),
            ),
            (
                tuple_field(1),
                ColumnValue::Records(HashMap::from([(
                    tuple_field(0),
                    ColumnValue::Ints(vec![50, 60]),
                )])),
            ),
        ]);

        let flat_domain: HashMap<String, ColumnValue> = field_map
            .iter()
            .enumerate()
            .map(|(out_idx, (outer_k, inner_k))| {
                let inner_col = match outer_cols.get(outer_k) {
                    Some(ColumnValue::Records(inner_map)) => {
                        inner_map[inner_k.as_ref().unwrap()].clone()
                    }
                    _ => panic!("expected Records for outer field {outer_k}"),
                };
                (tuple_field(out_idx), inner_col)
            })
            .collect();
        assert_eq!(
            flat_domain[&tuple_field(0)],
            ColumnValue::Ints(vec![10, 20])
        );
        assert_eq!(
            flat_domain[&tuple_field(1)],
            ColumnValue::Ints(vec![30, 40])
        );
        assert_eq!(
            flat_domain[&tuple_field(2)],
            ColumnValue::Ints(vec![50, 60])
        );

        assert_eq!(
            flatten_predicate(&Predicate::True, &field_map),
            Predicate::True
        );
    }

    /// `flatten_predicate` expands `Predicate::Record { _0: Record { _0: pA, _1: pB }, _1: Record { _0: pC } }`.
    #[test]
    fn flatten_predicate_expands_nested_record_predicate() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let pred = Predicate::Record(HashMap::from([
            (
                tuple_field(0),
                Predicate::Record(HashMap::from([
                    (tuple_field(0), Predicate::True),
                    (tuple_field(1), Predicate::False),
                ])),
            ),
            (tuple_field(1), Predicate::True),
        ]));
        let flat = flatten_predicate(&pred, &field_map);
        let Predicate::Record(fields) = flat else {
            panic!("expected Record predicate");
        };
        assert_eq!(fields[&tuple_field(0)], Predicate::True);
        assert_eq!(fields[&tuple_field(1)], Predicate::False);
        assert_eq!(fields[&tuple_field(2)], Predicate::True);
    }

    /// `unflatten_predicate` is the inverse of `flatten_predicate` for Record predicates.
    #[test]
    fn unflatten_predicate_is_inverse_of_flatten() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let flat = Predicate::Record(HashMap::from([
            (tuple_field(0), Predicate::True),
            (tuple_field(1), Predicate::False),
            (tuple_field(2), Predicate::True),
        ]));
        let nested = unflatten_predicate(&flat, &field_map);
        let Predicate::Record(outer) = nested else {
            panic!("expected Record predicate");
        };
        let Predicate::Record(inner0) = &outer[&tuple_field(0)] else {
            panic!("expected inner Record for _0");
        };
        assert_eq!(inner0[&tuple_field(0)], Predicate::True);
        assert_eq!(inner0[&tuple_field(1)], Predicate::False);
        let Predicate::Record(inner1) = &outer[&tuple_field(1)] else {
            panic!("expected inner Record for _1");
        };
        assert_eq!(inner1[&tuple_field(0)], Predicate::True);
    }

    // ── permute_record ────────────────────────────────────────────────────────

    /// `permute_record` with `[2, 0, 1]`: out_0 ← in_2, out_1 ← in_0, out_2 ← in_1.
    #[test]
    fn permute_record_reorders_fields() {
        let input = HashMap::from([
            (tuple_field(0), 10u32),
            (tuple_field(1), 20u32),
            (tuple_field(2), 30u32),
        ]);
        let result = permute_record(input, &[2, 0, 1]);
        assert_eq!(result[&tuple_field(0)], 30);
        assert_eq!(result[&tuple_field(1)], 10);
        assert_eq!(result[&tuple_field(2)], 20);
    }

    /// Identity permutation leaves every field in place.
    #[test]
    fn permute_record_identity_is_noop() {
        let input = HashMap::from([(tuple_field(0), 10u32), (tuple_field(1), 20u32)]);
        let result = permute_record(input, &[0, 1]);
        assert_eq!(result[&tuple_field(0)], 10);
        assert_eq!(result[&tuple_field(1)], 20);
    }

    // ── FlattenTupleDomainProducer ────────────────────────────────────────────

    /// Returns a nested outer `Tiling` matching `nested_outer_extent()`.
    fn nested_outer_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: nested_outer_extent(),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// Returns a flat three-field `Tiling` with all-`Int` domain.
    fn flat_three_int_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
                (tuple_field(2), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// `FlattenTupleDomainProducer::get_impl` flattens a nested `Records` domain column.
    ///
    /// Input: `{ _0: { _0: [10,20], _1: [30,40] }, _1: { _0: [50,60] } }`
    /// Expected: `{ _0: [10,20], _1: [30,40], _2: [50,60] }`, predicate unchanged (`True`).
    #[test]
    fn flatten_producer_get_flattens_nested_domain() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let input_tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (
                    tuple_field(0),
                    ColumnValue::Records(HashMap::from([
                        (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                        (tuple_field(1), ColumnValue::Ints(vec![30, 40])),
                    ])),
                ),
                (
                    tuple_field(1),
                    ColumnValue::Records(HashMap::from([(
                        tuple_field(0),
                        ColumnValue::Ints(vec![50, 60]),
                    )])),
                ),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let flat_tiling = flat_three_int_tiling();
        let mut producer = FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &flat_tiling),
            input: Box::new(TestTileProducer::new(input_tile, nested_outer_tiling())),
            field_map,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            domain_predicate,
            ..
        } = result
        else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![10, 20]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![30, 40]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![50, 60]));
        assert_eq!(domain_predicate, Predicate::True);
    }

    /// `FlattenTupleDomainProducer::get_impl` passes through non-flattened outer fields unchanged.
    ///
    /// Input: `{ _0: { _0: [10,20] }, _1: [99, 88] }` with field_map `[("_0", Some("_0")), ("_1", None)]`.
    /// Expected: `{ _0: [10,20], _1: [99, 88] }`.
    #[test]
    fn flatten_producer_get_passes_through_non_flattened_field() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(1), None),
        ];
        let pass_through_tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (
                    tuple_field(0),
                    Extent::Record(HashMap::from([(
                        tuple_field(0),
                        Extent::Base(BaseType::Int),
                    )])),
                ),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let input_tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (
                    tuple_field(0),
                    ColumnValue::Records(HashMap::from([(
                        tuple_field(0),
                        ColumnValue::Ints(vec![10, 20]),
                    )])),
                ),
                (tuple_field(1), ColumnValue::Ints(vec![99, 88])),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let out_tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &out_tiling),
            input: Box::new(TestTileProducer::new(input_tile, pass_through_tiling)),
            field_map,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![10, 20]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![99, 88]));
    }

    // ── PermuteRecordDomainProducer ───────────────────────────────────────────

    /// Helper: build a three-field `SealedFunction` tile and tiling with all-`Int` `Records` domain.
    fn make_three_field_records_tile_and_tiling() -> (Tile, Tiling) {
        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
                (tuple_field(2), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (tuple_field(0), ColumnValue::Ints(vec![1, 2])),
                (tuple_field(1), ColumnValue::Ints(vec![3, 4])),
                (tuple_field(2), ColumnValue::Ints(vec![5, 6])),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        (tile, tiling)
    }

    /// `PermuteRecordDomainProducer::get_impl` reorders domain columns by permutation.
    ///
    /// Permutation `[2, 0, 1]`: out_0 ← in_2, out_1 ← in_0, out_2 ← in_1.
    #[test]
    fn permute_producer_get_permutes_domain_fields() {
        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let permutation = vec![2usize, 0, 1];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![5, 6]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![3, 4]));
    }

    /// `PermuteRecordDomainProducer::get_impl` with identity permutation leaves domain unchanged.
    #[test]
    fn permute_producer_get_identity_permutation_is_noop() {
        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let permutation = vec![0usize, 1, 2];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![3, 4]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![5, 6]));
    }

    /// `PermuteRecordDomainProducer::get_impl` permutes a `Record` domain predicate.
    ///
    /// Permutation `[2, 0, 1]` on predicate `{_0: True, _1: False, _2: True}` →
    /// `{_0: True, _1: True, _2: False}` (out_0 ← in_2 = True, out_1 ← in_0 = True, out_2 ← in_1 = False).
    #[test]
    fn permute_producer_get_permutes_record_predicate() {
        let (mut input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        // Override the predicate on the input tile.
        if let Tile::SealedFunction {
            ref mut domain_predicate,
            ..
        } = input_tile
        {
            *domain_predicate = Predicate::Record(HashMap::from([
                (tuple_field(0), Predicate::True),
                (tuple_field(1), Predicate::False),
                (tuple_field(2), Predicate::True),
            ]));
        }
        let permutation = vec![2usize, 0, 1];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction {
            domain_predicate, ..
        } = result
        else {
            panic!("expected SealedFunction");
        };
        let Predicate::Record(fields) = domain_predicate else {
            panic!("expected Record predicate");
        };
        assert_eq!(fields[&tuple_field(0)], Predicate::True); // in_2 = True
        assert_eq!(fields[&tuple_field(1)], Predicate::True); // in_0 = True
        assert_eq!(fields[&tuple_field(2)], Predicate::False); // in_1 = False
    }

    /// `PermuteRecordDomainProducer::release_impl` applies the permutation to a `Record` guard.
    ///
    /// Release guard `{_0: True, _1: False, _2: True}` with permutation `[2, 0, 1]`.
    /// Upstream receives `{_0: True, _1: True, _2: False}`.
    #[test]
    fn permute_producer_release_record_guard_is_permuted() {
        use std::sync::mpsc;
        let (tx, rx) = mpsc::channel::<TileGuard>();

        struct SenderProducer {
            base: ProducerBase,
            tile: Tile,
            tx: mpsc::Sender<TileGuard>,
        }
        impl TileProducer for SenderProducer {
            impl_producer_base!();
            fn add_inspect_children(&self, node: InspectNode, _: &VizOptions) -> InspectNode {
                node
            }
            fn get_impl(&mut self, _: TileGuard) -> Tile {
                self.tile.clone()
            }
            fn release_impl(&mut self, guard: TileGuard) {
                let _ = self.tx.send(guard);
            }
        }

        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let sender = SenderProducer {
            base: ProducerBase::new(SenderProducer::alloc_id(), &input_tiling),
            tile: input_tile,
            tx,
        };
        let out_tiling = flat_three_int_tiling();
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(PermuteRecordDomainProducer::alloc_id(), &out_tiling),
            input: Box::new(sender),
            permutation: vec![2usize, 0, 1],
        };
        let obsolete =
            TileGuard::Function(FunctionGuard::Domain(Predicate::Record(HashMap::from([
                (tuple_field(0), Predicate::True),
                (tuple_field(1), Predicate::False),
                (tuple_field(2), Predicate::True),
            ]))));
        producer.release(obsolete);
        let upstream = rx.recv().expect("release_impl did not send upstream guard");
        let TileGuard::Function(FunctionGuard::Domain(Predicate::Record(fields))) = upstream else {
            panic!("expected Function/Domain/Record guard, got {upstream:?}");
        };
        // permutation [2,0,1]: upstream field `target` receives the downstream field at that index.
        // `release_impl` calls permute_record(fields, permutation):
        //   upstream._0 ← downstream._2 = True
        //   upstream._1 ← downstream._0 = True
        //   upstream._2 ← downstream._1 = False
        assert_eq!(fields[&tuple_field(0)], Predicate::True);
        assert_eq!(fields[&tuple_field(1)], Predicate::True);
        assert_eq!(fields[&tuple_field(2)], Predicate::False);
    }

    // ── permute_result_correlation ────────────────────────────────────────────

    fn tuple_step(idx: usize) -> TilePathStep {
        TilePathStep::Record(tuple_field(idx))
    }

    /// `(A, B) -> A`: correlation `[_0]` with permutation `[1, 0]` → `[_1]`.
    #[test]
    fn permute_result_correlation_swaps_two_fields() {
        let result = permute_result_correlation(vec![tuple_step(0)], &[1, 0]);
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// Permutation `[2, 0, 1]` with correlation `[_0]`: inv_perm[0] = 1 → `[_1]`.
    #[test]
    fn permute_result_correlation_three_arm() {
        let result = permute_result_correlation(vec![tuple_step(0)], &[2, 0, 1]);
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// Permutation `[2, 0, 1]` with correlation `[_2]`: inv_perm[2] = 0 → `[_0]`.
    #[test]
    fn permute_result_correlation_three_arm_field_two() {
        let result = permute_result_correlation(vec![tuple_step(2)], &[2, 0, 1]);
        assert_eq!(result, Some(vec![tuple_step(0)]));
    }

    /// Extra path steps after the Record step are passed through unchanged.
    #[test]
    fn permute_result_correlation_preserves_tail() {
        let result =
            permute_result_correlation(vec![tuple_step(0), TilePathStep::Codomain], &[1, 0]);
        assert_eq!(result, Some(vec![tuple_step(1), TilePathStep::Codomain]));
    }

    /// Empty correlation (identity) returns `None` — domain renamed but codomain unchanged.
    #[test]
    fn permute_result_correlation_empty_returns_none() {
        assert_eq!(permute_result_correlation(vec![], &[1, 0]), None);
    }

    /// Non-Record first step passes through unchanged.
    #[test]
    fn permute_result_correlation_codomain_first_step_passes_through() {
        let corr = vec![TilePathStep::Codomain, tuple_step(0)];
        assert_eq!(
            permute_result_correlation(corr.clone(), &[1, 0]),
            Some(corr)
        );
    }

    // ── flatten_result_correlation ────────────────────────────────────────────

    /// field_map for `{ _0: A, _1: (B, C) }` with both flattened:
    /// flat._0 = outer._0 (pass-through), flat._1 = outer._1._0 (B), flat._2 = outer._1._1 (C).
    fn nested_field_map() -> Vec<(String, Option<String>)> {
        vec![
            (tuple_field(0), None),
            (tuple_field(1), Some(tuple_field(0))),
            (tuple_field(1), Some(tuple_field(1))),
        ]
    }

    /// `(A, (B, C)) -> B`: `[_1, _0]` → `[_1]` (outer._1, inner._0 = B is at flat._1).
    #[test]
    fn flatten_result_correlation_two_level_collapses_to_flat_index() {
        let result =
            flatten_result_correlation(vec![tuple_step(1), tuple_step(0)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// `(A, (B, C)) -> C`: `[_1, _1]` → `[_2]` (outer._1, inner._1 = C is at flat._2).
    #[test]
    fn flatten_result_correlation_two_level_inner_field_one() {
        let result =
            flatten_result_correlation(vec![tuple_step(1), tuple_step(1)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(2)]));
    }

    /// Pass-through outer field: `[_0]` → `[_0]` (outer._0 = A is at flat._0).
    #[test]
    fn flatten_result_correlation_passthrough_field_maps_to_flat_index() {
        let result = flatten_result_correlation(vec![tuple_step(0)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(0)]));
    }

    /// Flattened outer field with single step (no inner step): returns `None`.
    #[test]
    fn flatten_result_correlation_flattened_outer_single_step_returns_none() {
        // outer._1 is flattened; there is no single flat field for the whole of _1.
        let result = flatten_result_correlation(vec![tuple_step(1)], &nested_field_map());
        assert_eq!(result, None);
    }

    /// Empty correlation returns `None`.
    #[test]
    fn flatten_result_correlation_empty_returns_none() {
        assert_eq!(
            flatten_result_correlation(vec![], &nested_field_map()),
            None
        );
    }

    /// `Codomain` first step passes through unchanged.
    #[test]
    fn flatten_result_correlation_codomain_first_step_passes_through() {
        let corr = vec![TilePathStep::Codomain, tuple_step(0)];
        assert_eq!(
            flatten_result_correlation(corr.clone(), &nested_field_map()),
            Some(corr)
        );
    }

    /// Extra path steps after the collapsed pair are preserved.
    #[test]
    fn flatten_result_correlation_preserves_tail_after_two_level() {
        let result = flatten_result_correlation(
            vec![tuple_step(1), tuple_step(0), TilePathStep::Codomain],
            &nested_field_map(),
        );
        assert_eq!(result, Some(vec![tuple_step(1), TilePathStep::Codomain]));
    }
}

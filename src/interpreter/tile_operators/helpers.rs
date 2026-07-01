//! Cross-cluster free functions shared by the tile operator submodules.
//!
//! These are the tile-shape transformations (column ↔ tile conversions,
//! function-tile application, codomain rewriting) that several operator
//! clusters reuse.  They carry the `pub(crate)` visibility needed to reach
//! across submodule boundaries; `scalar_tile_to_column_value` is `pub`
//! because it is part of the crate-public surface re-exported from
//! `tile_operators`.

use std::{collections::HashMap, hash::Hash};

use super::{Predicate, Tile, TilePathStep, Tiling};
use crate::interpreter::{ColumnValue, Extent, Value, bindings_are_list, transform_hashmap_values};

/// Repeat a scalar or record-of-scalars tile `len` times along the domain axis.
///
/// Used by [`MapToConstProducer`] to broadcast a constant value across all
/// domain elements: `Tile::Scalar(cv)` → `Tile::Scalar(cv.repeat(len))`;
/// `Tile::Record(m)` → `Tile::Record(m.map(t → repeat_tile(t, len)))`.
pub(crate) fn repeat_tile(tile: Tile, len: usize) -> Tile {
    match tile {
        Tile::Scalar(cv) => Tile::Scalar(cv.repeat(len)),
        Tile::Record(m) => Tile::Record(
            m.into_iter()
                .map(|(k, t)| (k, repeat_tile(t, len)))
                .collect(),
        ),
        other => panic!("repeat_tile: unsupported tile shape {other:?}"),
    }
}

/// Converts a Scalar tile or Record of Scalars to its underlying [`ColumnValue`].
pub fn scalar_tile_to_column_value(tile: Tile) -> ColumnValue {
    match tile {
        Tile::Scalar(cv) => cv,
        Tile::Record(m) => {
            ColumnValue::Records(extract_hashmap_values(m, scalar_tile_to_column_value))
        }
        _ => panic!("Not scalar"),
    }
}

/// Apply a function tile over a column of input values, producing a column of outputs.
///
/// Handles all four function tile representations:
/// - [`Tile::Scalar`] wrapping a [`Value::ComputableFunction`]: calls `f.apply` directly.
/// - [`Tile::Scalar`] wrapping a [`Value::Function`] (bindings table): maps each element
///   through the table.
/// - [`Tile::SealedFunction`]: treated as a point-lookup table keyed by domain value.
/// - [`Tile::CurriedFunction`]: each input value maps to a [`Value::Function`] bag of the
///   matching codomain group.
///
/// `output_extent` types the output column for the bindings-table and `SealedFunction`
/// cases; it is unused for `ComputableFunction` (which determines its own output type)
/// and `CurriedFunction` (which always produces [`ColumnValue::Variants`]).
pub(crate) fn apply_function_tile(
    function_tile: Tile,
    mut input: ColumnValue,
    input_extent: &Extent,
    output_extent: &Extent,
) -> ColumnValue {
    match function_tile {
        Tile::Scalar(func) => match func.as_single() {
            Some(Value::ComputableFunction(f)) => f.apply(input),
            Some(Value::Function(bindings)) => {
                if bindings_are_list(&bindings) {
                    // Inputs are sequential u0, u1, … so input holds raw indices.
                    let table = ColumnValue::from_values(
                        bindings.into_iter().map(|b| b.output).collect(),
                        output_extent,
                    );
                    input.transform_by_list(table)
                } else {
                    let (keys, values) = bindings.into_iter().map(|b| (b.input, b.output)).unzip();
                    let keys = ColumnValue::from_values(keys, input_extent);
                    let values = ColumnValue::from_values(values, output_extent);
                    input.transform_by_map(keys, values)
                }
            }
            None => ColumnValue::from_values(Vec::new(), output_extent),
            _ => panic!("apply_function_tile: Scalar tile is not a function value"),
        },
        Tile::SealedFunction {
            domain, codomain, ..
        } => input.transform_by_map(domain, scalar_tile_to_column_value(*codomain)),
        tile => panic!("apply_function_tile: not a function tile: {tile:?}"),
    }
}
/// Inverse of [`scalar_tile_to_column_value`]: reconstructs a [`Tile`] from a
/// [`ColumnValue`] using the given [`Tiling`] to determine the output shape.
///
/// - `Tiling::Scalar` → `Tile::Scalar(cv)`
/// - `Tiling::Record` → `Tile::Record(fields)` where each field is rebuilt recursively
fn column_value_to_tile(cv: ColumnValue, tiling: &Tiling) -> Tile {
    match tiling {
        Tiling::Scalar(_) => Tile::Scalar(cv),
        Tiling::Record(fields) => {
            let ColumnValue::Records(mut cv_fields) = cv else {
                panic!(
                    "column_value_to_tile: expected Records ColumnValue for Record tiling, got {cv:?}"
                );
            };
            Tile::Record(
                fields
                    .iter()
                    .map(|(k, t)| {
                        let field_cv = cv_fields
                            .remove(k)
                            .unwrap_or_else(|| panic!("column_value_to_tile: missing field {k}"));
                        (k.clone(), column_value_to_tile(field_cv, t))
                    })
                    .collect(),
            )
        }
        other => panic!("column_value_to_tile: unsupported tiling {other:?}"),
    }
}

/// Creates a new tiling based on the input tiling and a transformation of the deepest codomain
/// of the input (i.e. the "result" of the tiling).
pub(crate) fn change_tiling_result(
    input_tiling: &Tiling,
    transformation: impl FnOnce(&Extent) -> Tiling,
) -> Tiling {
    match input_tiling {
        Tiling::Scalar(e) => transformation(e),
        Tiling::Record(fields) => {
            transformation(&Extent::Record(transform_hashmap_values(fields, |t| {
                t.extent()
            })))
        }
        Tiling::SealedFunction { domain, codomain } => Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(change_tiling_result(codomain, transformation)),
        },
        Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain,
        } => Tiling::CurriedFunction {
            domain1: domain1.clone(),
            domain2: domain2.clone(),
            codomain: transformation(codomain).extent(),
        },
        _ => panic!("Cannot apply Map to {input_tiling}"),
    }
}

/// Apply the given transformation to the ColumnValue that is the deepest codomain of the
/// provided nested function tile (i.e. the "result" of the tile).
pub(crate) fn process_tile_result(
    input_tiling: &Tiling,
    input_tile: Tile,
    transformation: impl FnOnce(ColumnValue) -> ColumnValue,
) -> Tile {
    match input_tile {
        Tile::Scalar(t) => column_value_to_tile(transformation(t), input_tiling),
        Tile::Record(fields) => column_value_to_tile(
            transformation(scalar_tile_to_column_value(Tile::Record(fields))),
            input_tiling,
        ),
        Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::SealedFunction {
            domain,
            domain_predicate,
            deleted,
            codomain: Box::new(process_tile_result(
                &input_tiling.codomain().unwrap_or_else(|| unreachable!()),
                *codomain,
                transformation,
            )),
        },
        Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain: transformation(codomain),
            domain_predicate,
            deleted,
        },
        _ => panic!("Cannot apply Map to {input_tile:?}"),
    }
}
pub(crate) fn extract_predicate(pred: &Predicate, path: &[TilePathStep]) -> Predicate {
    if path.is_empty() || pred.as_bool().is_some() {
        return pred.clone();
    };

    if let Predicate::Or(arms) = pred {
        return Predicate::flatten_or(
            arms.iter()
                .map(|arm| extract_predicate(arm, path))
                .collect(),
        );
    }

    match &path[0] {
        TilePathStep::Record(f) => {
            if let Predicate::Record(fields) = pred {
                // If we see a Record predicate with our field where all other fields are false, then
                // return our field.  Correlated predicates don't give us any information about the
                // requested field in isolation, so return false.
                if fields.iter().all(|(field, p)| field == f || p.is_true()) {
                    extract_predicate(&fields[f], &path[1..])
                } else {
                    Predicate::False
                }
            } else {
                panic!("Expected record predicate, got {pred:?}");
            }
        }
        _ => todo!("We don't support correlated function preds yet"),
    }
}
fn extract_hashmap_values<K: Clone + Eq + Hash, InputV, V, F: Fn(InputV) -> V>(
    source: HashMap<K, InputV>,
    f: F,
) -> HashMap<K, V> {
    source.into_iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

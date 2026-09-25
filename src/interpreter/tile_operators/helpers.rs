//! Cross-cluster free functions shared by the tile operator submodules.
//!
//! These are the tile-shape transformations (column ↔ tile conversions,
//! function-tile application, codomain rewriting) that several operator
//! clusters reuse.  They carry the `pub(crate)` visibility needed to reach
//! across submodule boundaries; `scalar_tile_to_column_value` is `pub`
//! because it is part of the crate-public surface re-exported from
//! `tile_operators`.

use std::collections::HashMap;

use super::{Predicate, Tile, TilePathStep, Tiling};
use crate::interpreter::{
    ColumnValue, Extent, FuncBinding, Value, bindings_are_list, transform_hashmap_values,
};

/// A column of map values, one per row, as the tile those collections form
/// (`src/interpreter/design-operators.md`, "A collection inside a value stays a tile").
///
/// A store holds one value per key per tick, so a collection-valued variable is read out of
/// it as a column of maps.
///
/// Keys are sorted within each row, which is the invariant
/// [`Tile::DataFunction`](crate::interpreter::Tile::DataFunction) states of its `keys`.
pub(crate) fn open_row_collections(
    cells: &ColumnValue,
    key_extent: &Extent,
    value_extent: &Extent,
) -> Tile {
    let mut starts = Vec::with_capacity(cells.len());
    let mut keys: Vec<Value> = Vec::new();
    let mut values: Vec<Value> = Vec::new();
    for row in 0..cells.len() {
        starts.push(keys.len());
        let cell = cells.index_at(row);
        let Value::Function(mut bindings) = cell else {
            panic!("a collection-valued cell holds a map, got {cell:?}")
        };
        bindings.sort_by(|a, b| {
            a.input
                .partial_cmp(&b.input)
                .expect("a collection's keys are one extent's values, so they compare")
        });
        for binding in bindings {
            keys.push(binding.input);
            values.push(binding.output);
        }
    }
    Tile::grouped(
        ColumnValue::UInts(starts),
        ColumnValue::from_values(keys, key_extent),
        Box::new(Tile::Scalar(ColumnValue::from_values(values, value_extent))),
        // The row's whole map arrives at once, so nothing more is coming under these keys.
        Predicate::True,
        bit_set::BitSet::new(),
    )
}

/// Repeat a whole value's tile `len` times along the domain axis.
///
/// Used by [`MapResultToConstProducer`] to broadcast a constant value across all
/// domain elements: `Tile::Scalar(cv)` → `Tile::Scalar(cv.repeat(len))`;
/// `Tile::Record(m)` → `Tile::Record(m.map(t → repeat_tile(t, len)))`; a collection, one row
/// holding its keys, → one group per element, each a copy of that row's.
pub(crate) fn repeat_tile(tile: Tile, len: usize) -> Tile {
    match tile {
        Tile::Scalar(cv) => Tile::Scalar(cv.repeat(len)),
        Tile::Record(m) => Tile::Record(
            m.into_iter()
                .map(|(k, t)| (k, repeat_tile(t, len)))
                .collect(),
        ),
        collection @ Tile::DataFunction { .. } => {
            assert_eq!(
                collection.rows(),
                1,
                "a broadcast collection is one whole value, its one row's group"
            );
            collection.select_rows(&vec![0; len])
        }
        other => panic!("repeat_tile: unsupported tile shape {other:?}"),
    }
}

/// Converts a Scalar tile or Record of Scalars to its underlying [`ColumnValue`].
pub fn scalar_tile_to_column_value(tile: Tile) -> ColumnValue {
    try_scalar_tile_to_column_value(tile).expect("Not scalar")
}

/// The same conversion, answering `None` for a shape that is not a scalar or a record
/// of them.
///
/// For a caller holding a tile whose shape is **data** rather than a compiler
/// invariant — a seed drained from a producer, where a record with a collection-valued
/// field is a program the store cannot seed. Such a caller reports it; only a caller
/// whose tile shape is an invariant may take the panicking form.
pub fn try_scalar_tile_to_column_value(tile: Tile) -> Option<ColumnValue> {
    match tile {
        Tile::Scalar(cv) => Some(cv),
        Tile::Record(m) => {
            let mut fields = HashMap::with_capacity(m.len());
            for (name, field) in m {
                fields.insert(name, try_scalar_tile_to_column_value(field)?);
            }
            Some(ColumnValue::Records(fields))
        }
        _ => None,
    }
}

/// Apply a function tile over a column of input values, producing a column of outputs.
///
/// Handles three function tile representations:
/// - [`Tile::Scalar`] wrapping a [`Value::ComputableFunction`]: calls `f.apply` directly.
/// - [`Tile::Scalar`] wrapping a [`Value::Function`] (bindings table): maps each element
///   through the table.
/// - A one-level [`Tile::DataFunction`]: a point-lookup table keyed by domain value.
///
/// `output_extent` types the output column for the bindings-table case and for an empty
/// scalar; it is unused for `ComputableFunction`, which determines its own output type, and
/// for a collection, whose values carry their own.
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
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            ..
        } => {
            assert_eq!(
                row_starts.len(),
                1,
                "apply_function_tile pairs one collection's keys with its values"
            );
            input.transform_by_map(domain, scalar_tile_to_column_value(*codomain))
        }
        tile => panic!("apply_function_tile: not a function tile: {tile:?}"),
    }
}
/// A tile as a column, turning each collection it holds into one map value per row, for the
/// places one value is required: a variant's payload rides its arm as one, and a store write
/// is one value per key. The inverse of [`open_row_collections`].
///
/// Distinct from [`scalar_tile_to_column_value`], which refuses a collection held as a tile:
/// boxing one is a defect wherever the tile was the point, so the two are separate functions
/// rather than one that always obliges.
pub(crate) fn materialize_collections(tile: Tile) -> ColumnValue {
    match tile {
        Tile::Scalar(cv) => cv,
        Tile::Record(m) => ColumnValue::Records(
            m.into_iter()
                .map(|(name, field)| (name, materialize_collections(field)))
                .collect(),
        ),
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            deleted,
            ..
        } => {
            let inner = materialize_collections(*codomain);
            let starts: Vec<usize> = (0..row_starts.len())
                .map(|r| match row_starts.index_at(r) {
                    Value::UInt(u) => u,
                    other => panic!("a collection's row starts are UInts, got {other:?}"),
                })
                .collect();
            ColumnValue::Variants(
                (0..starts.len())
                    .map(|r| {
                        let from = starts[r];
                        let to = starts.get(r + 1).copied().unwrap_or(domain.len());
                        Value::Function(
                            (from..to)
                                .filter(|i| !deleted.contains(*i))
                                .map(|i| FuncBinding {
                                    input: domain.index_at(i),
                                    output: inner.index_at(i),
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }
        other => panic!("materialize_collections: not a value-shaped tile: {other:?}"),
    }
}

/// Replace the tile sitting under every level of `input_tile` with what `transformation`
/// makes of it — the tile-level [`process_tile_result`].
///
/// Used where the result carries levels, which a column has nowhere to put, and where the
/// values are read as a tile rather than as a column of elements. It needs no tiling: what
/// it replaces is chosen by the tile's own shape, and the transformation states the rest.
pub(crate) fn map_tile_result(
    mut input_tile: Tile,
    transformation: impl FnOnce(Tile) -> Tile,
) -> Tile {
    let values = input_tile.deepest_values_mut();
    let taken = std::mem::replace(values, Tile::Scalar(ColumnValue::Units(0)));
    *values = transformation(taken);
    input_tile
}

/// Inverse of [`scalar_tile_to_column_value`]: reconstructs a [`Tile`] from a
/// [`ColumnValue`] using the given [`Tiling`] to determine the output shape.
///
/// - `Tiling::Scalar` → `Tile::Scalar(cv)`
/// - `Tiling::Record` → `Tile::Record(fields)` where each field is rebuilt recursively
pub(crate) fn column_value_to_tile(cv: ColumnValue, tiling: &Tiling) -> Tile {
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
        Tiling::DataFunction { domain, codomain } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(change_tiling_result(codomain, transformation)),
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
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::DataFunction {
            row_starts,
            domain,
            codomain: Box::new(process_tile_result(
                &input_tiling.codomain().unwrap_or_else(|| unreachable!()),
                *codomain,
                transformation,
            )),
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

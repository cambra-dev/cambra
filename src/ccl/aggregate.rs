//! Aggregation kinds and their interpreter-facing fold semantics.

use smol_str::SmolStr;

use crate::ccl::BaseType;
use crate::interpreter::{ColumnValue, Extent};

/// Types of aggregations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AggregateKind {
    Sum,
    Max,
    /// The terminal aggregate: consume a collection of any element type and
    /// yield the single `unit` value. Its accumulator is `unit` (identity
    /// `unit`, merge `unit ⊕ unit = unit`), so it collapses a group of any
    /// multiplicity to one `unit`. The `set` constructor uses it to reduce each
    /// key's group — which holds ≥ 1 duplicate elements — to the single `unit`
    /// payload of `Set(K) = Map(K, unit)`, deduplicating in the process.
    /// Consuming the group is *also* what abstracts its key-dependence — the sum is
    /// consumed there (design/collections.md).
    Drain,
    /// The singleton aggregate: a group's one element, a group holding more
    /// rejected. The accumulator law is `Option(𝐴)`'s — identity `none`, and
    /// merging two `some` values faults, two elements under one key being the
    /// duplicate a map literal forbids (`src/ccl/design/collections.md`,
    /// "`sole` is an `Option`-accumulator aggregate").
    ///
    /// Presence is out-of-band: `none` is the empty accumulator column and
    /// `some` a column of length one. Any element is a valid value, so there is
    /// no in-band identity to seed with as `Sum` seeds with `0` and `Max` with
    /// `MIN`, and column length is what makes a duplicate detectable.
    Sole,
}

impl AggregateKind {
    pub fn output_extent(&self, input_extent: &Extent) -> Option<Extent> {
        match (self, input_extent) {
            (AggregateKind::Sum, Extent::Base(BaseType::Int)) => Some(Extent::Base(BaseType::Int)),
            (AggregateKind::Max, Extent::Base(b)) => Some(Extent::Base(b.clone())),
            // `Drain` folds any element type to `unit`.
            (AggregateKind::Drain, _) => Some(Extent::Base(BaseType::Unit)),
            // `Sole` yields an element of the group, so the extent is unchanged.
            (AggregateKind::Sole, e) => Some(e.clone()),
            _ => None,
        }
    }

    /// Returns the identity element for this aggregation over the given accumulator extent.
    ///
    /// Used to seed the [`Tile::Aggregation`](crate::interpreter::tiling::Tile::Aggregation)
    /// accumulator before the first batch of values arrives.
    pub fn initial_accumulator(&self, accumulator_extent: &Extent) -> ColumnValue {
        match (self, accumulator_extent) {
            (AggregateKind::Sum, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![0]),
            (AggregateKind::Max, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![i64::MIN]),
            (AggregateKind::Max, Extent::Base(BaseType::UInt)) => ColumnValue::UInts(vec![0]),
            (AggregateKind::Max, Extent::Base(BaseType::String)) => {
                ColumnValue::Strings(vec![SmolStr::default()])
            }
            // The single `unit` a drained group collapses to; further elements
            // fold in as no-ops (see `accumulate`).
            (AggregateKind::Drain, Extent::Base(BaseType::Unit)) => ColumnValue::Units(1),
            // `Sole`'s identity is `none`, and `none` is an empty column: the
            // accumulator's length is what carries presence, so the seed cannot be a
            // value of the element type.
            (AggregateKind::Sole, e) => ColumnValue::from_values(Vec::new(), e),
            _ => panic!("No identity for {self:?} over {accumulator_extent:?}"),
        }
    }

    /// Fold `values[start..end]` into `accumulator` in place.
    ///
    /// `accumulator` holds the running state (a single-element `ColumnValue`);
    /// `values` is the source column and `start..end` is the slice of elements
    /// to incorporate.  Passing `0..values.len()` incorporates the whole column.
    pub fn accumulate(
        &self,
        accumulator: &mut ColumnValue,
        values: &ColumnValue,
        start: usize,
        end: usize,
    ) {
        match (self, accumulator, values) {
            (AggregateKind::Sum, ColumnValue::Ints(acc), ColumnValue::Ints(vs)) => {
                acc[0] += vs[start..end].iter().sum::<i64>()
            }
            (AggregateKind::Max, ColumnValue::Ints(acc), ColumnValue::Ints(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            (AggregateKind::Max, ColumnValue::UInts(acc), ColumnValue::UInts(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            (AggregateKind::Max, ColumnValue::Strings(acc), ColumnValue::Strings(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            // `Drain`: the accumulator already holds the single `unit` the group
            // collapses to; folding in more elements is a no-op (any positive
            // multiplicity yields one `unit`). The values column is ignored.
            (AggregateKind::Drain, ColumnValue::Units(_), _) => {}
            // `Sole`: at most one element survives, so the fold is an append under a
            // length bound. Exceeding it means two elements share one key, which is
            // the duplicate a map literal forbids — enforced here rather than at
            // compile time because only the key *values* decide it
            // (`src/ccl/design/collections.md`, "Constructor lowering: runtime
            // `groupby` now, constant-folding later"). `select_indices` and `append`
            // recurse through a record column, so a group whose elements are pairs
            // folds by the same two calls as a scalar one.
            (AggregateKind::Sole, acc, vs) => {
                let incoming = end - start;
                assert!(
                    acc.len() + incoming <= 1,
                    "sole: {} elements under one key; a map literal's keys are distinct",
                    acc.len() + incoming
                );
                if incoming > 0 {
                    acc.append(vs.select_indices(start..end, incoming));
                }
            }
            _ => panic!("Invalid accumulate"),
        };
    }

    /// Convert accumulator state into output state.
    /// Currently, we only have aggregates where the extracted state is equal to the accumulators.
    pub fn extract(&self, accumulator: ColumnValue) -> ColumnValue {
        match (self, &accumulator) {
            (AggregateKind::Sum, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::UInts(_))
            | (AggregateKind::Max, ColumnValue::Strings(_))
            | (AggregateKind::Drain, ColumnValue::Units(_)) => accumulator,
            // Extraction is per *column*, and under `MapAggregate` that column holds
            // one accumulated value per key — so its length is the key count, not a
            // group's size. `Sole`'s bound is therefore checked in `accumulate`, where
            // the slice arriving is one group's.
            (AggregateKind::Sole, _) => accumulator,
            _ => panic!("Invalid accumulate"),
        }
    }
}

fn accumulate_max<T: Ord + Clone>(acc: &mut [T], values: &[T]) {
    let max = values.iter().max().cloned();
    if let Some(max) = max
        && max > acc[0]
    {
        acc[0] = max;
    }
}

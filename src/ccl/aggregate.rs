//! Aggregation kinds and their interpreter-facing fold semantics.

use smol_str::SmolStr;

use crate::ccl::BaseType;
use crate::interpreter::{ColumnValue, Extent, Tile, Tiling};

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
    /// duplicate a map literal forbids.
    ///
    /// Presence is out-of-band: `none` is the empty accumulator column and
    /// `some` a column of length one. Any element is a valid value, so there is
    /// no in-band identity to seed with as `Sum` seeds with `0` and `Max` with
    /// `MIN`, and column length is what makes a duplicate detectable.
    Sole,
}

impl AggregateKind {
    /// Whether folding a group can **fault** — the accumulator's merge is partial.
    ///
    /// Every other law here is per-variant and read off a `match` arm; this one was
    /// implicit in [`accumulate`](Self::accumulate)'s `Sole` arm, where a consumer asking
    /// "can this aggregate fail on user data" had nothing to read. It decides the presence
    /// convention as well: a total fold seeds an in-band identity of the element type, and
    /// a partial one has none, so its accumulator carries presence in its length
    /// ([`initial_accumulator`](Self::initial_accumulator) asserts the two agree).
    ///
    /// A fault today stops the process, which is a gap in the engine rather than in this
    /// law (`src/ccl/design/collections.md`, "A duplicate key is a process fault today").
    pub fn is_partial(&self) -> bool {
        match self {
            AggregateKind::Sum | AggregateKind::Max | AggregateKind::Drain => false,
            // `Option(𝐴)`'s partial monoid: merging two `some` values has no result.
            AggregateKind::Sole => true,
        }
    }

    /// The shape a fold leaves where the values it folded stood.
    ///
    /// `Sole` yields **an element of the group**, so a collection-valued element keeps its
    /// levels rather than collapsing to a boxed cell. Every other fold reduces to a value,
    /// so it leaves a scalar.
    pub fn output_tiling(&self, input: &Tiling) -> Option<Tiling> {
        match self {
            AggregateKind::Sole => Some(input.clone()),
            _ => self.output_extent(&input.extent()).map(Tiling::Scalar),
        }
    }

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
    pub fn initial_accumulator(&self, accumulator: &Tiling) -> Tile {
        let seed = self.seed(accumulator);
        // **Presence is in-band exactly when the fold is total.** A total aggregate has an
        // identity of the element type to seed with, so its accumulator is a column of one;
        // a partial one has none, and its length is what carries presence. The two halves
        // are written in different arms, so a new partial aggregate seeding a value —
        // making its own empty group indistinguishable from a group of one — is caught here.
        assert_eq!(
            seed.is_empty(),
            self.is_partial(),
            "an accumulator seed is empty exactly for a partial aggregate: {self:?}"
        );
        seed
    }

    fn seed(&self, accumulator: &Tiling) -> Tile {
        // A partial fold seeds no value, so its accumulator is that shape at no rows —
        // whatever the shape is. A total one seeds one value of the element type, which is
        // always a column.
        if self.is_partial() {
            return accumulator.empty_at_no_rows();
        }
        Tile::Scalar(self.scalar_seed(&accumulator.extent()))
    }

    fn scalar_seed(&self, accumulator_extent: &Extent) -> ColumnValue {
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
            _ => panic!("No identity for {self:?} over {accumulator_extent:?}"),
        }
    }

    /// Fold rows `start..end` of `values` into `accumulator` in place.
    ///
    /// Both are tiles because a fold may yield an element rather than reduce to a value:
    /// `Sole`'s accumulator carries whatever shape the element has, levels included.
    pub fn accumulate(&self, accumulator: &mut Tile, values: &Tile, start: usize, end: usize) {
        // `Sole` selects rather than reduces, so it is stated over tiles; every other fold
        // reduces a column and is stated over columns.
        if let AggregateKind::Sole = self {
            let incoming = end - start;
            // At most one element survives. Exceeding that means two elements share one
            // key, which is the duplicate a map literal forbids — enforced here rather than
            // at compile time because only the key *values* decide it
            // (`src/ccl/design/collections.md`, "Constructor lowering: runtime `groupby`
            // now, constant-folding later").
            let held = accumulator.rows();
            assert!(
                held + incoming <= 1,
                "sole: {} elements under one key; a map literal's keys are distinct",
                held + incoming
            );
            if incoming > 0 {
                accumulator.merge_rows(values.select_rows(&(start..end).collect::<Vec<_>>()));
            }
            return;
        }
        let (Tile::Scalar(accumulator), Tile::Scalar(values)) = (accumulator, values) else {
            panic!("{self:?} reduces a column, so its accumulator and values are columns");
        };
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
            _ => panic!("Invalid accumulate"),
        };
    }

    /// Convert accumulator state into output state.
    /// Currently, we only have aggregates where the extracted state is equal to the accumulators.
    pub fn extract(&self, accumulator: Tile) -> Tile {
        // `Sole` yields the element it held, whatever shape that is.
        if let AggregateKind::Sole = self {
            return accumulator;
        }
        let Tile::Scalar(column) = &accumulator else {
            panic!("{self:?} reduces a column, so its accumulator is a column");
        };
        match (self, column) {
            (AggregateKind::Sum, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::UInts(_))
            | (AggregateKind::Max, ColumnValue::Strings(_))
            | (AggregateKind::Drain, ColumnValue::Units(_)) => accumulator,
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

//! Aggregation kinds and their interpreter-facing fold semantics.

use crate::ccl::BaseType;
use crate::interpreter::{ColumnValue, Extent, Tile, Tiling};

mod aggregation;

pub use aggregation::{Accumulator, Aggregation, Element, StateTile};
use aggregation::{Drain, FromTile, Instantiate, SoleAccum, instantiate};

/// Types of aggregations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AggregateKind {
    Sum,
    Max,
    Min,
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
            (AggregateKind::Min, Extent::Base(b)) => Some(Extent::Base(b.clone())),
            // `Drain` folds any element type to `unit`.
            (AggregateKind::Drain, _) => Some(Extent::Base(BaseType::Unit)),
            // `Sole` yields an element of the group, so the extent is unchanged.
            (AggregateKind::Sole, e) => Some(e.clone()),
            _ => None,
        }
    }

    /// An accumulator for this aggregate over the partial aggregations in `state`, one row each.
    ///
    /// `Drain` and `Sole` hold elements of any shape. Every other aggregate reduces a column and
    /// is selected by the column's type.
    pub fn accumulator_of(&self, state: Tile) -> Box<dyn Accumulator> {
        match self {
            AggregateKind::Drain => return FromTile(state).with(Drain),
            AggregateKind::Sole => return Box::new(SoleAccum::new(state)),
            AggregateKind::Sum | AggregateKind::Max | AggregateKind::Min => {}
        }
        let Tile::Scalar(column) = &state else {
            panic!("{self:?} reduces a column, so its accumulator is a column, got {state:?}");
        };
        let base = match column {
            ColumnValue::Ints(_) => BaseType::Int,
            ColumnValue::UInts(_) => BaseType::UInt,
            ColumnValue::Strings(_) => BaseType::String,
            ColumnValue::Bools(_) => BaseType::Bool,
            other => panic!("No aggregation of {self:?} over {other:?}"),
        };
        instantiate(*self, &base, FromTile(state))
            .unwrap_or_else(|| panic!("No aggregation of {self:?} over {base:?}"))
    }

    /// An accumulator for this aggregate that has seen no group, whose state has the tiling
    /// `accumulator`.
    pub fn accumulator(&self, accumulator: &Tiling) -> Box<dyn Accumulator> {
        self.accumulator_of(accumulator.empty_at_no_rows())
    }
}

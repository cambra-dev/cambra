//! Aggregation kinds and their interpreter-facing fold semantics.

use smol_str::SmolStr;

use crate::ccl::BaseType;
use crate::interpreter::{ColumnValue, Extent, Tile, Tiling};

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
            AggregateKind::Sum | AggregateKind::Max | AggregateKind::Min | AggregateKind::Drain => {
                false
            }
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
            (AggregateKind::Min, Extent::Base(b)) => Some(Extent::Base(b.clone())),
            // A nominal value's extreme, in the order its declaration writes, which its tag
            // names (`crate::ccl::nominal::payload_order`).
            (AggregateKind::Max | AggregateKind::Min, e @ Extent::Union(_)) => Some(e.clone()),
            // A tuple's extreme is lexicographic, seeded by each position's.
            (AggregateKind::Max | AggregateKind::Min, e @ Extent::Record(fields))
                if fields
                    .values()
                    .all(|f| self.output_extent(f).as_ref() == Some(f)) =>
            {
                Some(e.clone())
            }
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
        // **Presence is in-band exactly when the fold has an identity at the element type.**
        // Such an aggregate seeds it, so its accumulator is a column of one; a partial one has
        // none by its law, and its length carries presence. A partial aggregate seeding a
        // value, which makes its own empty group indistinguishable from a group of one, is
        // caught here. `Max` and `Min` at a type with no least or greatest value have no
        // identity either. Until they return `Option(T)` (`docs/chl-spec.md`, "7.1
        // Aggregates"), their first element seeds them, and their extreme of an empty
        // collection is not defined.
        assert!(
            !(self.is_partial() && !seed.is_empty()),
            "a partial aggregate seeds no value: {self:?}"
        );
        assert!(
            !seed.is_empty() || self.is_partial() || self.identity(&accumulator.extent()).is_none(),
            "an aggregate with an identity seeds it: {self:?}"
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
        let extent = accumulator.extent();
        // Interim, until `max` and `min` return `Option(T)` (`docs/chl-spec.md`, "7.1
        // Aggregates"): an extreme with no identity at the element type starts from no
        // value, and its first element seeds it ([`accumulate`](Self::accumulate)).
        Tile::Scalar(
            self.identity(&extent)
                .unwrap_or_else(|| ColumnValue::from_values(Vec::new(), &extent)),
        )
    }

    /// The identity of this fold at `accumulator_extent`, the value its accumulator starts
    /// from, where there is one. `Min` over `String` has none, since no string is greatest, and
    /// neither has an extreme over a tuple holding one. Until `max` and `min` return
    /// `Option(T)` (`docs/chl-spec.md`, "7.1 Aggregates"), such an extreme is seeded by its
    /// first element instead.
    fn identity(&self, accumulator_extent: &Extent) -> Option<ColumnValue> {
        Some(match (self, accumulator_extent) {
            (AggregateKind::Sum, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![0]),
            (AggregateKind::Max, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![i64::MIN]),
            (AggregateKind::Min, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![i64::MAX]),
            (AggregateKind::Max, Extent::Base(BaseType::UInt)) => ColumnValue::UInts(vec![0]),
            (AggregateKind::Min, Extent::Base(BaseType::UInt)) => {
                ColumnValue::UInts(vec![u64::MAX])
            }
            (AggregateKind::Max, Extent::Base(BaseType::String)) => {
                ColumnValue::Strings(vec![SmolStr::default()])
            }
            (AggregateKind::Max, Extent::Base(BaseType::Bool)) => {
                ColumnValue::Bools(vec![false; 1])
            }
            (AggregateKind::Min, Extent::Base(BaseType::Bool)) => ColumnValue::Bools(vec![true; 1]),
            // A tuple's identity is each position's, lexicographically least for `Max` and
            // greatest for `Min`.
            (AggregateKind::Max | AggregateKind::Min, Extent::Record(fields)) => {
                ColumnValue::Records(
                    fields
                        .iter()
                        .map(|(name, f)| Some((name.clone(), self.identity(f)?)))
                        .collect::<Option<_>>()?,
                )
            }
            // The single `unit` a drained group collapses to; further elements
            // fold in as no-ops (see `accumulate`).
            (AggregateKind::Drain, Extent::Base(BaseType::Unit)) => ColumnValue::Units(1),
            (AggregateKind::Min, Extent::Base(BaseType::String)) => return None,
            // A nominal value's extreme has none either: its declaration bounds nothing.
            (AggregateKind::Max | AggregateKind::Min, Extent::Union(_)) => return None,
            _ => panic!("No identity for {self:?} over {accumulator_extent:?}"),
        })
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
        // A fold over no rows leaves the accumulator as it is, held value or none.
        if start == end {
            return;
        }
        let values = as_column(values).unwrap_or_else(|| {
            panic!("{self:?} reduces a column, so its values are a column, got {values:?}")
        });
        let Tile::Scalar(accumulator) = accumulator else {
            panic!("{self:?} reduces a column, so its accumulator is a column");
        };
        let mut start = start;
        // Interim, until `max` and `min` return `Option(T)`: an extreme with no identity
        // starts from no value, and the first element is the one held.
        if accumulator.is_empty() {
            *accumulator = values.select_indices(std::iter::once(start), 1);
            start += 1;
        }
        let values = &values;
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
            // `False < True`, so the maximum is whether any element is `True`.
            (AggregateKind::Max, ColumnValue::Bools(acc), ColumnValue::Bools(vs)) => {
                if (start..end).any(|i| vs[i]) {
                    acc[0] = true;
                }
            }
            (AggregateKind::Min, ColumnValue::Ints(acc), ColumnValue::Ints(vs)) => {
                accumulate_min(acc, &vs[start..end]);
            }
            (AggregateKind::Min, ColumnValue::UInts(acc), ColumnValue::UInts(vs)) => {
                accumulate_min(acc, &vs[start..end]);
            }
            (AggregateKind::Min, ColumnValue::Strings(acc), ColumnValue::Strings(vs)) => {
                accumulate_min(acc, &vs[start..end]);
            }
            // `False < True`, so the minimum is whether every element is `True`.
            (AggregateKind::Min, ColumnValue::Bools(acc), ColumnValue::Bools(vs)) => {
                if (start..end).any(|i| !vs[i]) {
                    acc[0] = false;
                }
            }
            // A tuple's extreme, lexicographically, and a nominal value's, in its declaration's
            // order: the row the batch holds beyond the one held, if any, by the values' own
            // comparison.
            (
                kind @ (AggregateKind::Max | AggregateKind::Min),
                acc @ (ColumnValue::Records(_) | ColumnValue::Union(_)),
                vs @ (ColumnValue::Records(_) | ColumnValue::Union(_)),
            ) => {
                let beyond = if *kind == AggregateKind::Max {
                    std::cmp::Ordering::Greater
                } else {
                    std::cmp::Ordering::Less
                };
                let mut held = acc.index_at(0);
                let mut chosen = None;
                for i in start..end {
                    let v = vs.index_at(i);
                    if v.partial_cmp(&held) == Some(beyond) {
                        held = v;
                        chosen = Some(i);
                    }
                }
                if let Some(i) = chosen {
                    *acc = vs.select_indices(std::iter::once(i), 1);
                }
            }
            // `Drain`: the accumulator already holds the single `unit` the group
            // collapses to; folding in more elements is a no-op (any positive
            // multiplicity yields one `unit`). The values column is ignored.
            (AggregateKind::Drain, ColumnValue::Units(_), _) => {}
            _ => panic!("Invalid accumulate"),
        };
    }

    /// Whether `accumulator` holds no value yet, which is how an extreme with no identity
    /// stands before its first element. Interim, until `max` and `min` return `Option(T)`
    /// (`docs/chl-spec.md`, "7.1 Aggregates"). A partial fold's empty accumulator is a value,
    /// its identity.
    pub fn awaits_first_element(&self, accumulator: &Tile) -> bool {
        !self.is_partial() && accumulator.rows() == 0
    }

    /// Stop at the extreme of a complete, empty collection, which has no value. Interim, as
    /// `//` by zero stops: `max` and `min` are to return `Option::none` there
    /// (`docs/chl-spec.md`, "7.1 Aggregates").
    pub fn no_extreme_of_nothing(&self) -> ! {
        let name = match self {
            AggregateKind::Max => "max",
            AggregateKind::Min => "min",
            other => unreachable!("{other:?} has an identity, so it has a value at no elements"),
        };
        panic!("`{name}` of an empty collection has no value")
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
            | (AggregateKind::Max, ColumnValue::Bools(_))
            | (AggregateKind::Min, ColumnValue::Ints(_))
            | (AggregateKind::Min, ColumnValue::UInts(_))
            | (AggregateKind::Min, ColumnValue::Strings(_))
            | (AggregateKind::Min, ColumnValue::Bools(_))
            | (AggregateKind::Max | AggregateKind::Min, ColumnValue::Records(_))
            | (AggregateKind::Max | AggregateKind::Min, ColumnValue::Union(_))
            | (AggregateKind::Drain, ColumnValue::Units(_)) => accumulator,
            _ => panic!("Invalid accumulate"),
        }
    }
}

/// The column `tile` is: a scalar's, or the column of records a record of scalar fields holding
/// a cell at every row is. A tuple element reaches a fold as either.
fn as_column(tile: &Tile) -> Option<ColumnValue> {
    match tile {
        Tile::Scalar(column) => Some(column.clone()),
        Tile::Record { fields, absent } if absent.values().all(|a| a.is_empty()) => {
            Some(ColumnValue::Records(
                fields
                    .iter()
                    .map(|(name, field)| Some((name.clone(), as_column(field)?)))
                    .collect::<Option<_>>()?,
            ))
        }
        _ => None,
    }
}

fn accumulate_max<T: Ord + Clone>(acc: &mut [T], values: &[T]) {
    if let Some(max) = values.iter().max()
        && max > &acc[0]
    {
        acc[0].clone_from(max);
    }
}

fn accumulate_min<T: Ord + Clone>(acc: &mut [T], values: &[T]) {
    if let Some(min) = values.iter().min()
        && min < &acc[0]
    {
        acc[0].clone_from(min);
    }
}

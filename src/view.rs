//! A borrowed region of a column: stored values, one value repeated, or stored values at a list
//! of positions.
//!
//! Shared by `crate::scalar_ops` and the interpreter; both import `View` from this module.

use crate::interpreter::RowIndex;
use std::ops::Range;

/// A borrowed region of a column: stored values, one value repeated `len` times, or the stored
/// values at `positions`, in that order.
#[derive(Debug)]
pub enum View<'a, T> {
    Slice(&'a [T]),
    Constant {
        value: &'a T,
        len: usize,
    },
    Selected {
        values: &'a [T],
        positions: &'a [RowIndex],
    },
}

impl<T> Clone for View<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for View<'_, T> {}

impl<'a, T> View<'a, T> {
    /// Borrow `value` as a sequence of length `len`, without allocating copies.
    pub fn repeated(value: &'a T, len: usize) -> Self {
        View::Constant { value, len }
    }

    /// The number of values.
    pub fn len(&self) -> usize {
        match *self {
            View::Slice(values) => values.len(),
            View::Constant { len, .. } => len,
            View::Selected { positions, .. } => positions.len(),
        }
    }

    /// Whether there are no values.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The value at `i`.
    pub fn get(&self, i: usize) -> &'a T {
        match *self {
            View::Slice(values) => &values[i],
            View::Constant { value, len } => {
                assert!(i < len, "index {i} out of a view of {len}");
                value
            }
            View::Selected { values, positions } => &values[positions[i]],
        }
    }

    /// The values in `range`.
    pub fn range(self, range: Range<usize>) -> Self {
        match self {
            View::Slice(values) => View::Slice(&values[range]),
            View::Constant { value, len } => {
                assert!(range.end <= len, "range {range:?} out of a view of {len}");
                View::Constant {
                    value,
                    len: range.len(),
                }
            }
            View::Selected { values, positions } => View::Selected {
                values,
                positions: &positions[range],
            },
        }
    }

    /// The values at `positions`, in that order, without copying them, or `None` for a view that
    /// is already a selection: composing two selections would build a new list of positions.
    pub fn select(self, positions: &'a [RowIndex]) -> Option<Self> {
        match self {
            View::Slice(values) => Some(View::Selected { values, positions }),
            View::Constant { value, len } => {
                debug_assert!(positions.iter().all(|&p| p < len));
                Some(View::Constant {
                    value,
                    len: positions.len(),
                })
            }
            View::Selected { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn values<T: Clone>(view: View<'_, T>) -> Vec<T> {
        match view {
            View::Slice(values) => values.to_vec(),
            View::Constant { value, len } => vec![value.clone(); len],
            View::Selected { values, positions } => {
                positions.iter().map(|&p| values[p].clone()).collect()
            }
        }
    }

    /// A stored column and a repeated value read as the same sequence.
    #[test]
    fn a_slice_and_a_repeated_value_read_as_the_same_values() {
        let stored = vec![7, 7, 7];
        let seven = 7;
        let repeated = View::repeated(&seven, 3);
        assert_eq!(values(View::Slice(&stored)), vec![7; 3]);
        assert_eq!(values(repeated), vec![7; 3]);
        assert_eq!(View::Slice(&stored).len(), repeated.len());
    }

    #[test]
    fn a_range_of_a_view_is_a_view_of_the_same_values() {
        let stored = vec![1, 2, 3, 4];
        assert_eq!(values(View::Slice(&stored).range(1..3)), vec![2, 3]);
        let nine = 9;
        let part = View::repeated(&nine, 5).range(2..4);
        assert_eq!(part.len(), 2);
        assert_eq!(values(part), vec![9, 9]);
    }

    /// A selection reads a slice's values at its positions, in their order, and a range of it
    /// is a range of those positions. A repeated value selects a shorter repeat, and a selection
    /// of a selection is refused rather than built.
    #[test]
    fn a_selection_reads_the_values_at_its_positions() {
        let stored = vec![10, 11, 12, 13, 14];
        let positions = [4, 0, 2];
        let selected = View::Slice(&stored)
            .select(&positions)
            .expect("a slice selects");
        assert_eq!(selected.len(), 3);
        assert_eq!(*selected.get(0), 14);
        assert_eq!(values(selected), vec![14, 10, 12]);
        assert_eq!(values(selected.range(1..3)), vec![10, 12]);
        let five = 5;
        let repeat = View::repeated(&five, 9)
            .select(&positions)
            .expect("a repeat selects");
        assert!(matches!(repeat, View::Constant { len: 3, .. }));
        assert!(selected.select(&[0]).is_none());
    }

    #[test]
    #[should_panic(expected = "out of a view of 3")]
    fn a_range_past_the_end_of_a_repeated_value_is_refused() {
        let one = 1;
        View::repeated(&one, 3).range(0..4);
    }
}

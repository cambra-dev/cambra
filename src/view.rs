//! A borrowed region of a column: stored values, or one value repeated.
//!
//! The kernels in `crate::scalar_ops` take their operands as views, so one kernel serves a stored
//! column, a region of one, and a literal. A region of the input is read without a copy, and a
//! repeated operand is read as one value, not as a column of copies.
//!
//! Its own module, like `crate::scalar_ops`, because the layering forbids `ccl` from depending
//! upward on `interpreter`, and `ccl::planning::const_fold` calls the kernels.

use std::iter::repeat_n;
use std::ops::Range;

/// A borrowed region of a column: stored values, or one value repeated `len` times.
#[derive(Debug)]
pub enum View<'a, T> {
    Slice(&'a [T]),
    Constant { value: &'a T, len: usize },
}

impl<T> Clone for View<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for View<'_, T> {}

impl<'a, T> View<'a, T> {
    /// A region of `len` copies of `value`.
    pub fn repeated(value: &'a T, len: usize) -> Self {
        View::Constant { value, len }
    }

    /// The number of values.
    pub fn len(&self) -> usize {
        match *self {
            View::Slice(values) => values.len(),
            View::Constant { len, .. } => len,
        }
    }

    /// Whether there are no values.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The first `rows` values.
    pub fn prefix(self, rows: usize) -> Self {
        self.range(0..rows)
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
        }
    }
}

impl<T: Clone> View<'_, T> {
    /// Append every value to `out`.
    pub fn extend_into(self, out: &mut Vec<T>) {
        match self {
            View::Slice(values) => out.extend_from_slice(values),
            View::Constant { value, len } => out.extend(repeat_n(value.clone(), len)),
        }
    }
}

/// Two views are equal when they read as the same values in the same order, however stored.
impl<T: PartialEq> PartialEq for View<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        match (*self, *other) {
            (View::Slice(a), View::Slice(b)) => a == b,
            (View::Constant { value: a, len: n }, View::Constant { value: b, len: m }) => {
                n == m && (n == 0 || a == b)
            }
            (View::Slice(values), View::Constant { value, len })
            | (View::Constant { value, len }, View::Slice(values)) => {
                values.len() == len && values.iter().all(|v| v == value)
            }
        }
    }
}

impl<T: Eq> Eq for View<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;

    fn values<T: Clone>(view: View<'_, T>) -> Vec<T> {
        let mut out = Vec::new();
        view.extend_into(&mut out);
        out
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
        assert_eq!(values(part.prefix(1)), vec![9]);
    }

    /// Views compare by the values they read, not by how they are stored.
    #[test]
    fn views_compare_by_their_values() {
        let (stored, seven) = (vec![7, 7], 7);
        assert_eq!(View::Slice(&stored), View::repeated(&seven, 2));
        assert_ne!(View::Slice(&stored), View::repeated(&seven, 3));
        assert_ne!(View::Slice(&[7, 8]), View::repeated(&seven, 2));
        assert_eq!(View::repeated(&seven, 0), View::Slice(&Vec::<i32>::new()));
    }

    #[test]
    #[should_panic(expected = "out of a view of 3")]
    fn a_range_past_the_end_of_a_repeated_value_is_refused() {
        let one = 1;
        View::repeated(&one, 3).range(0..4);
    }
}

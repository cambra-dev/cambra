//! The storage behind one column of values of a single element type.
//!
//! A [`Storage`] is either a `Vec` of the values or a [`Constant`]: one value and a length. A
//! value repeated `n` times costs one entry, so a broadcast value (`ColumnValue::repeat`) takes no
//! memory per row.
//!
//! Code that wants a `Vec` or a slice reads a constant through `Deref`, which expands it once and
//! keeps the expansion. `len`, `iter`, `get` and indexing by position read a constant without
//! expanding it.
//!
//! Its own module, like `crate::scalar_ops`, because the layering forbids `ccl` from depending
//! upward on `interpreter`.

use std::iter::repeat_n;
use std::ops::{
    Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};
use std::sync::OnceLock;

/// One value repeated `len` times, stored once.
#[derive(Debug, Clone)]
pub struct Constant<T> {
    value: T,
    len: usize,
}

impl<T> Constant<T> {
    pub fn new(value: T, len: usize) -> Self {
        Constant { value, len }
    }

    pub fn value(&self) -> &T {
        &self.value
    }
}

/// An owned column's values: stored one by one, or one value repeated and stored once.
pub enum Storage<T> {
    Vec(Vec<T>),
    Constant {
        constant: Constant<T>,
        /// The values as a `Vec`, built the first time something reads them as one.
        expanded: OnceLock<Vec<T>>,
    },
}

impl<T> Storage<T> {
    /// `value` repeated `len` times, stored once.
    pub fn constant(value: T, len: usize) -> Self {
        Storage::Constant {
            constant: Constant::new(value, len),
            expanded: OnceLock::new(),
        }
    }

    /// Whether the values are one repeated value.
    pub fn is_constant(&self) -> bool {
        matches!(self, Storage::Constant { .. })
    }

    /// The number of values.
    pub fn len(&self) -> usize {
        match self {
            Storage::Vec(v) => v.len(),
            Storage::Constant { constant, .. } => constant.len,
        }
    }

    /// Whether there are no values.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The `i`th value.
    pub fn get(&self, i: usize) -> Option<&T> {
        match self {
            Storage::Vec(v) => v.get(i),
            Storage::Constant { constant, .. } => (i < constant.len).then_some(&constant.value),
        }
    }

    /// The values in order.
    pub fn iter(&self) -> Iter<'_, T> {
        match self {
            Storage::Vec(v) => Iter::Slice(v.iter()),
            Storage::Constant { constant, .. } => {
                Iter::Repeat(repeat_n(&constant.value, constant.len))
            }
        }
    }
}

impl<T: Clone> Storage<T> {
    /// The values as a `Vec`, expanding a constant.
    pub fn into_vec(self) -> Vec<T> {
        match self {
            Storage::Vec(v) => v,
            Storage::Constant { constant, expanded } => expanded
                .into_inner()
                .unwrap_or_else(|| repeat_n(constant.value, constant.len).collect()),
        }
    }

    /// The values as a `Vec` that can change, expanding a constant in place.
    pub fn to_mut(&mut self) -> &mut Vec<T> {
        if self.is_constant() {
            *self = Storage::Vec(std::mem::take(self).into_vec());
        }
        let Storage::Vec(v) = self else {
            unreachable!("a constant was expanded above")
        };
        v
    }
}

impl<T: Clone> Deref for Storage<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Vec<T> {
        match self {
            Storage::Vec(v) => v,
            Storage::Constant { constant, expanded } => {
                expanded.get_or_init(|| repeat_n(constant.value.clone(), constant.len).collect())
            }
        }
    }
}

impl<T: Clone> DerefMut for Storage<T> {
    fn deref_mut(&mut self) -> &mut Vec<T> {
        self.to_mut()
    }
}

impl<T> Default for Storage<T> {
    fn default() -> Self {
        Storage::Vec(Vec::new())
    }
}

impl<T: Clone> Clone for Storage<T> {
    fn clone(&self) -> Self {
        match self {
            Storage::Vec(v) => Storage::Vec(v.clone()),
            Storage::Constant { constant, .. } => Storage::Constant {
                constant: constant.clone(),
                expanded: OnceLock::new(),
            },
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Storage<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Storage::Vec(v) => v.fmt(f),
            // A constant prints as one value and its length, not as `len` copies.
            Storage::Constant { constant, .. } => {
                write!(f, "[{:?}; {}]", constant.value, constant.len)
            }
        }
    }
}

impl<T: PartialEq> Storage<T> {
    /// Whether the values equal `other`, in order, however they are stored.
    fn eq_slice(&self, other: &[T]) -> bool {
        match self {
            Storage::Vec(v) => v.as_slice() == other,
            Storage::Constant { constant, .. } => {
                constant.len == other.len() && other.iter().all(|x| x == &constant.value)
            }
        }
    }
}

/// Two storages are equal when they hold the same values in the same order, however stored.
impl<T: PartialEq> PartialEq for Storage<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Storage::Vec(_), Storage::Vec(v)) => self.eq_slice(v),
            (Storage::Vec(v), Storage::Constant { .. }) => other.eq_slice(v),
            (Storage::Constant { .. }, Storage::Vec(v)) => self.eq_slice(v),
            (Storage::Constant { constant: a, .. }, Storage::Constant { constant: b, .. }) => {
                a.len == b.len && (a.len == 0 || a.value == b.value)
            }
        }
    }
}

impl<T: Eq> Eq for Storage<T> {}

impl<T: PartialEq> PartialEq<Vec<T>> for Storage<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.eq_slice(other)
    }
}

impl<T: PartialEq> PartialEq<Storage<T>> for Vec<T> {
    fn eq(&self, other: &Storage<T>) -> bool {
        other.eq_slice(self)
    }
}

impl<T: PartialEq, const N: usize> PartialEq<[T; N]> for Storage<T> {
    fn eq(&self, other: &[T; N]) -> bool {
        self.eq_slice(other)
    }
}

impl<T: PartialEq> PartialEq<&[T]> for Storage<T> {
    fn eq(&self, other: &&[T]) -> bool {
        self.eq_slice(other)
    }
}

impl<T> From<Vec<T>> for Storage<T> {
    fn from(values: Vec<T>) -> Self {
        Storage::Vec(values)
    }
}

impl<T> FromIterator<T> for Storage<T> {
    fn from_iter<I: IntoIterator<Item = T>>(values: I) -> Self {
        Storage::Vec(values.into_iter().collect())
    }
}

impl<T: Clone> IntoIterator for Storage<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Storage<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T> Index<usize> for Storage<T> {
    type Output = T;

    fn index(&self, i: usize) -> &T {
        self.get(i)
            .unwrap_or_else(|| panic!("index {i} out of a column of {}", self.len()))
    }
}

impl<T: Clone> IndexMut<usize> for Storage<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        &mut self.to_mut()[i]
    }
}

/// Indexing by a range reads the expansion, as slicing a `Vec` would.
macro_rules! index_by_range {
    ($($range:ty),*) => {$(
        impl<T: Clone> Index<$range> for Storage<T> {
            type Output = [T];

            fn index(&self, range: $range) -> &[T] {
                &(**self)[range]
            }
        }

        impl<T: Clone> IndexMut<$range> for Storage<T> {
            fn index_mut(&mut self, range: $range) -> &mut [T] {
                &mut self.to_mut()[range]
            }
        }
    )*};
}

index_by_range!(
    Range<usize>,
    RangeFrom<usize>,
    RangeTo<usize>,
    RangeFull,
    RangeInclusive<usize>,
    RangeToInclusive<usize>
);

/// The values of a [`Storage`], in order.
pub enum Iter<'a, T> {
    Slice(std::slice::Iter<'a, T>),
    Repeat(std::iter::RepeatN<&'a T>),
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match self {
            Iter::Slice(it) => it.next(),
            Iter::Repeat(it) => it.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Iter::Slice(it) => it.size_hint(),
            Iter::Repeat(it) => it.size_hint(),
        }
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        match self {
            Iter::Slice(it) => it.next_back(),
            Iter::Repeat(it) => it.next_back(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stored column and a constant read as the same values.
    #[test]
    fn a_constant_reads_as_the_column_of_copies() {
        let stored: Storage<i64> = vec![7, 7, 7].into();
        let constant = Storage::constant(7, 3);
        assert_eq!(stored, constant);
        assert_eq!(constant, vec![7, 7, 7]);
        assert_eq!(vec![7, 7, 7], constant);
        assert_eq!(constant, [7, 7, 7]);
        assert_ne!(constant, Storage::constant(7, 4));
        assert_ne!(constant, vec![7, 8, 7]);
        assert_eq!(Storage::<i64>::constant(1, 0), Storage::from(Vec::new()));
    }

    /// Reading by length, position and iteration does not expand a constant; reading as a
    /// `Vec` does, once.
    #[test]
    fn only_a_read_as_a_vec_expands_a_constant() {
        let constant = Storage::constant(5, 1_000_000);
        assert_eq!(constant.len(), 1_000_000);
        assert_eq!(constant[999_999], 5);
        assert_eq!(constant.get(1_000_000), None);
        assert_eq!(constant.iter().len(), 1_000_000);
        assert_eq!(constant.iter().rev().take(2).count(), 2);
        let Storage::Constant { expanded, .. } = &constant else {
            unreachable!()
        };
        assert!(expanded.get().is_none(), "nothing expanded it yet");
        assert_eq!(constant.as_slice().len(), 1_000_000);
        let Storage::Constant { expanded, .. } = &constant else {
            unreachable!()
        };
        assert!(expanded.get().is_some());
    }

    #[test]
    fn mutating_a_constant_replaces_it_with_its_expansion() {
        let mut storage = Storage::constant(2, 3);
        storage.push(9);
        assert!(!storage.is_constant());
        assert_eq!(storage, vec![2, 2, 2, 9]);
        let mut storage = Storage::constant(1, 2);
        storage[1] = 4;
        assert_eq!(storage, vec![1, 4]);
    }
}

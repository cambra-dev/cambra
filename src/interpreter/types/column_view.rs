//! A borrowed column: the values of one column of a base type as a [`View`] of its element type.

use smol_str::SmolStr;

use crate::view::View;

use super::{ColumnValue, RowIndex};

/// A column of `Int`, `UInt`, `String` or `Bool` values, borrowed from a [`ColumnValue`] or
/// built from a literal.
///
/// Kernel dispatch and allocation rules are in `src/interpreter/design-operators.md`,
/// "Column views".
#[derive(Debug, Clone, Copy)]
pub enum ColumnView<'a> {
    Ints(View<'a, i64>),
    UInts(View<'a, u64>),
    Strings(View<'a, SmolStr>),
    Bools(View<'a, bool>),
}

impl<'a> ColumnView<'a> {
    /// The number of values.
    pub fn len(&self) -> usize {
        match self {
            ColumnView::Ints(v) => v.len(),
            ColumnView::UInts(v) => v.len(),
            ColumnView::Strings(v) => v.len(),
            ColumnView::Bools(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The empty column of this view's element type.
    pub fn empty_like(&self) -> ColumnValue {
        match self {
            ColumnView::Ints(_) => ColumnValue::Ints(Vec::new()),
            ColumnView::UInts(_) => ColumnValue::UInts(Vec::new()),
            ColumnView::Strings(_) => ColumnValue::Strings(Vec::new()),
            ColumnView::Bools(_) => ColumnValue::Bools(Vec::new()),
        }
    }

    /// The values at `positions`, in that order, as a column.
    pub(crate) fn gather(&self, positions: &[RowIndex]) -> ColumnValue {
        fn pick<T: Clone>(view: &View<'_, T>, positions: &[RowIndex]) -> Vec<T> {
            positions.iter().map(|&p| view.get(p).clone()).collect()
        }
        match self {
            ColumnView::Ints(v) => ColumnValue::Ints(pick(v, positions)),
            ColumnView::UInts(v) => ColumnValue::UInts(pick(v, positions)),
            ColumnView::Strings(v) => ColumnValue::Strings(pick(v, positions)),
            ColumnView::Bools(v) => ColumnValue::Bools(pick(v, positions)),
        }
    }

    /// Append `len` values to `out`, a column of this view's type: the value at position `p` is the
    /// next value of the one part whose positions hold `p`. The parts' positions are ascending and
    /// together hold each of `0..len` once, and each part has one value per position it holds.
    pub(crate) fn scatter_into(
        parts: &[(ColumnView<'_>, &[RowIndex])],
        len: usize,
        out: &mut ColumnValue,
    ) {
        fn place<'v, T: Clone + 'v>(
            parts: impl Iterator<Item = (View<'v, T>, &'v [RowIndex])>,
            len: usize,
            out: &mut Vec<T>,
        ) {
            let mut placed: Vec<Option<T>> = vec![None; len];
            for (view, positions) in parts {
                debug_assert_eq!(view.len(), positions.len(), "one value per position");
                for (i, &p) in positions.iter().enumerate() {
                    let slot = &mut placed[p];
                    debug_assert!(slot.is_none(), "position {p} is held by two parts");
                    *slot = Some(view.get(i).clone());
                }
            }
            out.extend(
                placed
                    .into_iter()
                    .map(|value| value.expect("every position is held by a part")),
            );
        }
        macro_rules! scatter {
            ($variant:ident, $out:expr) => {
                place(
                    parts.iter().map(|(view, positions)| match view {
                        ColumnView::$variant(v) => (*v, *positions),
                        other => panic!("parts of one type, got {other:?}"),
                    }),
                    len,
                    $out,
                )
            };
        }
        match out {
            ColumnValue::Ints(out) => scatter!(Ints, out),
            ColumnValue::UInts(out) => scatter!(UInts, out),
            ColumnValue::Strings(out) => scatter!(Strings, out),
            ColumnValue::Bools(out) => scatter!(Bools, out),
            other => panic!("a scatter writes a column with a view, got {other:?}"),
        }
    }

    /// The first `rows` values.
    pub fn prefix(self, rows: usize) -> Self {
        self.range(0..rows)
    }

    /// The values in `range`.
    pub fn range(self, range: std::ops::Range<usize>) -> Self {
        match self {
            ColumnView::Ints(v) => ColumnView::Ints(v.range(range)),
            ColumnView::UInts(v) => ColumnView::UInts(v.range(range)),
            ColumnView::Strings(v) => ColumnView::Strings(v.range(range)),
            ColumnView::Bools(v) => ColumnView::Bools(v.range(range)),
        }
    }
}

impl ColumnValue {
    /// Borrow an `Int`, `UInt`, `String`, or `Bool` column. Other variants, including `Units`,
    /// return `None`.
    pub fn view(&self) -> Option<ColumnView<'_>> {
        match self {
            ColumnValue::Ints(v) => Some(ColumnView::Ints(View::Slice(v))),
            ColumnValue::UInts(v) => Some(ColumnView::UInts(View::Slice(v))),
            ColumnValue::Strings(v) => Some(ColumnView::Strings(View::Slice(v))),
            ColumnValue::Bools(v) => Some(ColumnView::Bools(View::Slice(v))),
            _ => None,
        }
    }

    /// Append the values of `view`, a view of this column's element type.
    pub fn extend_from_view(&mut self, view: ColumnView<'_>) {
        match (self, view) {
            (ColumnValue::Ints(out), ColumnView::Ints(v)) => extend(out, v),
            (ColumnValue::UInts(out), ColumnView::UInts(v)) => extend(out, v),
            (ColumnValue::Strings(out), ColumnView::Strings(v)) => extend(out, v),
            (ColumnValue::Bools(out), ColumnView::Bools(v)) => extend(out, v),
            (out, view) => panic!("cannot append a view of {view:?} to {out:?}"),
        }
    }
}

fn extend<T: Clone>(out: &mut Vec<T>, view: View<'_, T>) {
    match view {
        View::Slice(values) => out.extend_from_slice(values),
        View::Constant { value, len } => out.extend(std::iter::repeat_n(value, len).cloned()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A slice and a repeated value append their values, for every element type.
    #[test]
    fn a_view_appends_its_values() {
        let mut ints = ColumnValue::Ints(vec![1]);
        ints.extend_from_view(ColumnView::Ints(View::Slice(&[2, 3])));
        ints.extend_from_view(ColumnView::Ints(View::repeated(&4, 2)));
        assert_eq!(ints, ColumnValue::Ints(vec![1, 2, 3, 4, 4]));
        let mut uints = ColumnValue::UInts(Vec::new());
        uints.extend_from_view(ColumnView::UInts(View::repeated(&7, 3)));
        assert_eq!(uints, ColumnValue::UInts(vec![7; 3]));
        let s = SmolStr::from("s");
        let mut strings = ColumnValue::Strings(vec!["a".into()]);
        strings.extend_from_view(ColumnView::Strings(View::repeated(&s, 2)));
        assert_eq!(
            strings,
            ColumnValue::Strings(vec!["a".into(), s.clone(), s])
        );
        let mut bools = ColumnValue::Bools(Vec::new());
        bools.extend_from_view(ColumnView::Bools(View::Slice(&[true, false])));
        assert_eq!(bools, ColumnValue::Bools(vec![true, false]));
    }

    #[test]
    #[should_panic(expected = "cannot append a view")]
    fn a_view_of_another_type_is_refused() {
        let one = ColumnView::Bools(View::repeated(&true, 1));
        ColumnValue::Ints(Vec::new()).extend_from_view(one);
    }
}

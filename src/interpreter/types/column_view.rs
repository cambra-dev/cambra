//! A borrowed column: the values of one column of a base type as a [`View`] of its element type.

use smol_str::SmolStr;

use crate::view::View;

use super::ColumnValue;
use super::RowIndex;

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

    /// Append the values at `positions`, in that order, to `out`, a column of this view's type.
    pub(crate) fn gather_into(&self, positions: &[RowIndex], out: &mut ColumnValue) {
        fn pick<T: Clone>(view: View<'_, T>, positions: &[RowIndex], out: &mut Vec<T>) {
            match view {
                View::Slice(values) => out.extend(positions.iter().map(|&p| values[p].clone())),
                View::Constant { value, len } => {
                    debug_assert!(positions.iter().all(|&p| p < len));
                    out.extend(std::iter::repeat_n(value, positions.len()).cloned())
                }
                View::Selected {
                    values,
                    positions: selected,
                } => out.extend(positions.iter().map(|&p| values[selected[p]].clone())),
            }
        }
        match (self, out) {
            (ColumnView::Ints(v), ColumnValue::Ints(out)) => pick(*v, positions, out),
            (ColumnView::UInts(v), ColumnValue::UInts(out)) => pick(*v, positions, out),
            (ColumnView::Strings(v), ColumnValue::Strings(out)) => pick(*v, positions, out),
            (ColumnView::Bools(v), ColumnValue::Bools(out)) => pick(*v, positions, out),
            (view, out) => panic!("cannot gather a view of {view:?} into {out:?}"),
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
        debug_assert_eq!(
            parts
                .iter()
                .map(|(_, positions)| positions.len())
                .sum::<usize>(),
            len,
            "the parts hold len positions in all"
        );
        // Disjointness is the caller's invariant: a `CaseFn`'s arms take disjoint rows.
        debug_assert!(
            parts.iter().all(|(_, positions)| {
                positions.windows(2).all(|pair| pair[0] < pair[1])
                    && positions.last().is_none_or(|&p| p < len)
            }),
            "each part's positions ascend and lie below len"
        );
        // The new rows are first filled with one part's first value, then each is overwritten
        // by the value of the part holding its position.
        fn place<'v, T: Clone + 'v>(
            parts: impl Iterator<Item = (View<'v, T>, &'v [RowIndex])> + Clone,
            len: usize,
            out: &mut Vec<T>,
        ) {
            let Some(fill) = parts
                .clone()
                .find(|(view, _)| !view.is_empty())
                .map(|(view, _)| view.get(0).clone())
            else {
                return;
            };
            let base = out.len();
            out.resize(base + len, fill);
            let placed = &mut out[base..];
            for (view, positions) in parts {
                debug_assert_eq!(view.len(), positions.len(), "one value per position");
                match view {
                    View::Slice(values) => {
                        for (value, &p) in values.iter().zip(positions) {
                            placed[p] = value.clone();
                        }
                    }
                    View::Constant { value, .. } => {
                        for &p in positions {
                            placed[p] = value.clone();
                        }
                    }
                    View::Selected {
                        values,
                        positions: selected,
                    } => {
                        for (&s, &p) in selected.iter().zip(positions) {
                            placed[p] = values[s].clone();
                        }
                    }
                }
            }
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

    /// The values at `positions` without copying them, or `None` for a view that is already a
    /// selection ([`View::select`]).
    pub(crate) fn select(self, positions: &'a [RowIndex]) -> Option<Self> {
        Some(match self {
            ColumnView::Ints(v) => ColumnView::Ints(v.select(positions)?),
            ColumnView::UInts(v) => ColumnView::UInts(v.select(positions)?),
            ColumnView::Strings(v) => ColumnView::Strings(v.select(positions)?),
            ColumnView::Bools(v) => ColumnView::Bools(v.select(positions)?),
        })
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
        View::Selected { values, positions } => {
            out.extend(positions.iter().map(|&p| values[p].clone()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A selection appends, gathers and scatters the values at its positions.
    #[test]
    fn a_selection_appends_gathers_and_scatters_its_values() {
        let stored = [10_i64, 11, 12, 13];
        let positions = [3, 1];
        let selected = ColumnView::Ints(View::Selected {
            values: &stored,
            positions: &positions,
        });
        let mut appended = ColumnValue::Ints(Vec::new());
        appended.extend_from_view(selected);
        assert_eq!(appended, ColumnValue::Ints(vec![13, 11]));
        let mut gathered = ColumnValue::Ints(Vec::new());
        selected.gather_into(&[1, 0, 1], &mut gathered);
        assert_eq!(gathered, ColumnValue::Ints(vec![11, 13, 11]));
        let others = [7_i64];
        let mut scattered = ColumnValue::Ints(vec![0]);
        ColumnView::scatter_into(
            &[
                (selected, &[0, 2]),
                (ColumnView::Ints(View::Slice(&others)), &[1]),
            ],
            3,
            &mut scattered,
        );
        assert_eq!(scattered, ColumnValue::Ints(vec![0, 13, 7, 11]));
        let mut with_repeat = ColumnValue::Ints(Vec::new());
        ColumnView::scatter_into(
            &[
                (ColumnView::Ints(View::repeated(&5, 2)), &[0, 2]),
                (selected, &[1, 3]),
            ],
            4,
            &mut with_repeat,
        );
        assert_eq!(with_repeat, ColumnValue::Ints(vec![5, 13, 5, 11]));
    }

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

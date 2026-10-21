//! A borrowed column: the values of one flat column as a [`View`] of its element type.

use smol_str::SmolStr;

use crate::view::View;

use super::ColumnValue;

/// A column of `Int`, `UInt`, `String` or `Bool` values, borrowed from a [`ColumnValue`] or
/// built from a literal.
///
/// The element-wise operations read their operands as column views, so an operand that is a
/// region of the input, or one literal repeated, is read in place and never copied into a column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// This column as a view, or `None` for a column that is not flat (a record, a union, or
    /// another composite).
    pub fn view(&self) -> Option<ColumnView<'_>> {
        match self {
            ColumnValue::Ints(v) => Some(ColumnView::Ints(View::Slice(v))),
            ColumnValue::UInts(v) => Some(ColumnView::UInts(View::Slice(v))),
            ColumnValue::Strings(v) => Some(ColumnView::Strings(View::Slice(v))),
            ColumnValue::Bools(v) => Some(ColumnView::Bools(View::Slice(v))),
            _ => None,
        }
    }

    /// Append every value of `view`, a view of the same element type.
    pub fn extend_from_view(&mut self, view: ColumnView<'_>) {
        match (self, view) {
            (ColumnValue::Ints(o), ColumnView::Ints(v)) => v.extend_into(o),
            (ColumnValue::UInts(o), ColumnView::UInts(v)) => v.extend_into(o),
            (ColumnValue::Strings(o), ColumnView::Strings(v)) => v.extend_into(o),
            (ColumnValue::Bools(o), ColumnView::Bools(v)) => v.extend_into(o),
            (out, view) => panic!("cannot append {view:?} to {out:?}"),
        }
    }
}

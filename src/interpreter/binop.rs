//! BinOp operator: the column dispatch over the scalar kernel in
//! [`crate::scalar_ops`], which owns the operator enums and the element-wise semantics.

use smol_str::SmolStr;
use std::collections::HashMap;

pub use crate::scalar_ops::{ArithmeticKind, BinOpKind, CompareKind, LogicKind};
use crate::scalar_ops::{
    zip_arithmetic, zip_bool_compare, zip_bool_logic, zip_compare, zip_concat,
};

use super::{BaseType, ColumnValue, ColumnView, Extent};

/// Output [`Extent`] for a [`BinOpKind`].
pub fn binop_output_extent(op: &BinOpKind) -> Extent {
    match op {
        BinOpKind::Arithmetic(_) => Extent::Base(BaseType::Int),
        BinOpKind::Compare(_) | BinOpKind::BoolLogic(_) => Extent::Base(BaseType::Bool),
        BinOpKind::Concat => Extent::Base(BaseType::String),
    }
}

/// The empty column that holds the result of `op` over operands shaped like `left`.
pub fn binop_result_column(op: BinOpKind, left: &ColumnView) -> ColumnValue {
    match op {
        BinOpKind::Arithmetic(_) => left.empty_like(),
        BinOpKind::Concat => ColumnValue::Strings(Vec::new()),
        BinOpKind::BoolLogic(_) | BinOpKind::Compare(_) => ColumnValue::Bools(Vec::new()),
    }
}

/// The empty column that holds the result of `op` over operands shaped like `left`, a column of a
/// base type or a record column.
fn binop_result_column_of(op: BinOpKind, left: &ColumnValue) -> ColumnValue {
    match left.view() {
        Some(view) => binop_result_column(op, &view),
        // Only the comparison of two products reads a column that is not of a base type.
        None => ColumnValue::Bools(Vec::new()),
    }
}

/// Apply a binary operation element-wise on two column views, appending the result to `out`.
///
/// `out` is a column of the result's variant (see [`binop_result_column`]). One row is appended
/// per position of the operands' common prefix. The caller owns the rest of the column's state:
/// it clears the rows it does not keep and reserves room for the new ones, and the kernel
/// writes each result once into that room.
///
/// Only co-present positions combine. A longer operand would otherwise keep its surplus tail in
/// the result, which fabricates values for positions the other operand has not reached. That
/// misfires when the shorter operand has not yet converged (a sibling induction loop's
/// still-empty final read): the result would read as terminal instead of waiting. The sibling
/// half of this invariant is that `MapResultToConstProducer` emits an empty non-terminal tile
/// rather than broadcasting an absent constant.
pub fn apply_binop_views(
    op: BinOpKind,
    left: &ColumnView,
    right: &ColumnView,
    out: &mut ColumnValue,
) {
    let rows = left.len().min(right.len());
    let (left, right) = (left.prefix(rows), right.prefix(rows));
    match (op, left, right, out) {
        (
            BinOpKind::Arithmetic(op),
            ColumnView::Ints(l),
            ColumnView::Ints(r),
            ColumnValue::Ints(o),
        ) => zip_arithmetic(op, l, r, o),
        (
            BinOpKind::Arithmetic(op),
            ColumnView::UInts(l),
            ColumnView::UInts(r),
            ColumnValue::UInts(o),
        ) => zip_arithmetic(op, l, r, o),
        (
            BinOpKind::BoolLogic(op),
            ColumnView::Bools(l),
            ColumnView::Bools(r),
            ColumnValue::Bools(o),
        ) => zip_bool_logic(op, l, r, o),
        (
            BinOpKind::Concat,
            ColumnView::Strings(l),
            ColumnView::Strings(r),
            ColumnValue::Strings(o),
        ) => zip_concat(l, r, o),
        (
            BinOpKind::Compare(op),
            ColumnView::Strings(l),
            ColumnView::Strings(r),
            ColumnValue::Bools(o),
        ) => zip_compare(op, l, r, o),
        (
            BinOpKind::Compare(op),
            ColumnView::Ints(l),
            ColumnView::Ints(r),
            ColumnValue::Bools(o),
        ) => zip_compare(op, l, r, o),
        (
            BinOpKind::Compare(op),
            ColumnView::UInts(l),
            ColumnView::UInts(r),
            ColumnValue::Bools(o),
        ) => zip_compare(op, l, r, o),
        (
            BinOpKind::Compare(op),
            ColumnView::Bools(l),
            ColumnView::Bools(r),
            ColumnValue::Bools(o),
        ) => zip_bool_compare(op, l, r, o),
        (op, left, right, out) => {
            panic!("Unsupported binop: {op:?} on {left:?}, {right:?}, into a column {out:?}")
        }
    }
}

/// Apply a binary operation element-wise on two `ColumnValue`s, appending the result to `out`,
/// as [`apply_binop_views`] does for columns of a base type.
fn apply_binop_into(op: BinOpKind, left: &ColumnValue, right: &ColumnValue, out: &mut ColumnValue) {
    match (op, left, right, &mut *out) {
        // A product compares **componentwise**, which is the whole of what makes one
        // equatable (`src/ccl/design/type-inference.md`, "What the tables hold").
        (
            BinOpKind::Compare(op @ (CompareKind::Equals | CompareKind::NotEquals)),
            ColumnValue::Records(l),
            ColumnValue::Records(r),
            ColumnValue::Bools(o),
        ) => o.extend(compare_records(op, l, r)),
        // A tuple orders lexicographically by position (`docs/chl-spec.md`, "3.4
        // Comparisons"), and a nominal value by its fields in the order its declaration writes
        // them, which its tag names: both are the values' own comparison.
        (
            BinOpKind::Compare(
                op @ (CompareKind::Less
                | CompareKind::LessOrEq
                | CompareKind::Greater
                | CompareKind::GreaterOrEq),
            ),
            l @ (ColumnValue::Records(_) | ColumnValue::Union(_)),
            r @ (ColumnValue::Records(_) | ColumnValue::Union(_)),
            ColumnValue::Bools(o),
        ) => o.extend(order_rows(op, l, r)),
        // A nominal value compares by value: constructor, then argument.
        (
            BinOpKind::Compare(op @ (CompareKind::Equals | CompareKind::NotEquals)),
            l @ (ColumnValue::Union(_) | ColumnValue::Variants(_)),
            r @ (ColumnValue::Union(_) | ColumnValue::Variants(_)),
            ColumnValue::Bools(o),
        ) => o.extend(equal_rows(op, l, r)),
        _ => match (left.view(), right.view()) {
            (Some(l), Some(r)) => apply_binop_views(op, &l, &r, out),
            _ => panic!("Unsupported binop: {op:?} on {left:?}, {right:?}, into a column {out:?}"),
        },
    }
}

/// Compare two tagged columns row by row under `==` or `!=`, by value: a value's tag, then its
/// payload.
fn equal_rows(op: CompareKind, left: &ColumnValue, right: &ColumnValue) -> Vec<bool> {
    let rows = left.len().min(right.len());
    (0..rows)
        .map(|i| (left.index_at(i) == right.index_at(i)) == (op == CompareKind::Equals))
        .collect()
}

/// Order two columns of tuples or nominal values row by row, by the values' own comparison,
/// under an ordering comparator.
fn order_rows(op: CompareKind, left: &ColumnValue, right: &ColumnValue) -> Vec<bool> {
    let rows = left.len().min(right.len());
    (0..rows)
        .map(|i| {
            let (l, r) = (left.index_at(i), right.index_at(i));
            let ord = l.partial_cmp(&r).unwrap_or_else(|| {
                panic!("{l:?} and {r:?} have no order; typing admits an ordered pair")
            });
            order_holds(op, ord)
        })
        .collect()
}

/// Whether the ordering comparison `op` holds of two values that compare as `ord`.
pub fn order_holds(op: CompareKind, ord: std::cmp::Ordering) -> bool {
    match op {
        CompareKind::Less => ord.is_lt(),
        CompareKind::LessOrEq => ord.is_le(),
        CompareKind::Greater => ord.is_gt(),
        CompareKind::GreaterOrEq => ord.is_ge(),
        CompareKind::Equals | CompareKind::NotEquals => {
            unreachable!("equality is compared by value, not by an order")
        }
    }
}

/// Apply a binary operation element-wise on two `ColumnValue`s, into a newly allocated column.
///
/// Neither operand's buffer is reused.
pub fn apply_binop_column(op: BinOpKind, left: &ColumnValue, right: &ColumnValue) -> ColumnValue {
    let mut out = binop_result_column_of(op, left);
    apply_binop_into(op, left, right, &mut out);
    out
}

/// The fields a comparison of two products compares, each with the two sides' values: the fields
/// both sides carry, in no particular order.
///
/// **The fields both sides carry are the product the type names.** Typing rejects a comparison
/// between two different products, so the two field sets differ only where width subtyping let a
/// wider value reach a narrower position and the tiling kept the surplus column. A field the
/// position's type does not name is not part of the value there, and the intersection reads the
/// value at its type whichever operand carries it.
///
/// A value carrying exactly the fields its type names would retire the intersection. What
/// keeps the surplus is inlining dropping the parameter's annotation — see the vault issue
/// `type-checker-inlining-drops-a-narrowing-annotation`.
pub(crate) fn compared_fields<'a, L, R>(
    left: &'a HashMap<SmolStr, L>,
    right: &'a HashMap<SmolStr, R>,
) -> impl Iterator<Item = (&'a SmolStr, &'a L, &'a R)> + Clone {
    left.iter()
        .filter_map(|(name, l)| Some((name, l, right.get(name)?)))
}

/// Compare two record columns field by field, `Equals` conjoining the results and
/// `NotEquals` disjoining them, over the fields [`compared_fields`] names.
///
/// The length is the shortest column those fields read, a column still filling being one whose
/// later positions have not been decided. A surplus column is excluded from that minimum for the
/// same reason it is excluded from the answer: its extent belongs to the wider value, and a short
/// one would truncate a result the named fields already decided.
fn compare_records(
    op: CompareKind,
    left: &HashMap<SmolStr, ColumnValue>,
    right: &HashMap<SmolStr, ColumnValue>,
) -> Vec<bool> {
    let fields = compared_fields(left, right);
    let rows = fields
        .clone()
        .flat_map(|(_, l, r)| [l.len(), r.len()])
        .min()
        .unwrap_or(0);
    let mut acc = vec![op == CompareKind::Equals; rows];
    for (_, l, r) in fields {
        let mut field_eq = ColumnValue::Bools(Vec::new());
        apply_binop_into(BinOpKind::Compare(op), l, r, &mut field_eq);
        let ColumnValue::Bools(field_eq) = field_eq else {
            unreachable!("a comparison yields a Bool column")
        };
        // A nested product reports the length of one of its own fields, so a recursive
        // comparison can answer for fewer positions than `rows`. `acc` shrinks to what
        // arrived: zipping `acc` with a shorter `field_eq` leaves the tail of `acc` unchanged
        // rather than dropping it, and padding would invent positions.
        if field_eq.len() < acc.len() {
            acc.truncate(field_eq.len());
        }
        match op {
            CompareKind::Equals => acc.iter_mut().zip(&field_eq).for_each(|(a, &b)| *a &= b),
            CompareKind::NotEquals => acc.iter_mut().zip(&field_eq).for_each(|(a, &b)| *a |= b),
            _ => unreachable!("guarded by the caller's match"),
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use std::hint::black_box;
    use std::time::Duration;

    use super::apply_binop_into;
    use crate::interpreter::*;
    use test_log::test;

    /// Verify all six CompareKind operations on every pair of bool values.
    #[test]
    fn test_zip_bool_compare_all_ops() {
        // Compare single bool values via the public apply_binop_column API.
        let cmp = |op: CompareKind, l: bool, r: bool| -> bool {
            let result = apply_binop_column(
                BinOpKind::Compare(op),
                &ColumnValue::Bools(vec![l; 1]),
                &ColumnValue::Bools(vec![r; 1]),
            );
            match result {
                ColumnValue::Bools(v) => v[0],
                other => panic!("expected Bools, got {other:?}"),
            }
        };

        // false < true (0 < 1) — verify all four input pairs for each op.
        assert!(!cmp(CompareKind::Less, false, false));
        assert!(cmp(CompareKind::Less, false, true));
        assert!(!cmp(CompareKind::Less, true, false));
        assert!(!cmp(CompareKind::Less, true, true));

        assert!(cmp(CompareKind::LessOrEq, false, false));
        assert!(cmp(CompareKind::LessOrEq, false, true));
        assert!(!cmp(CompareKind::LessOrEq, true, false));
        assert!(cmp(CompareKind::LessOrEq, true, true));

        assert!(!cmp(CompareKind::Greater, false, false));
        assert!(!cmp(CompareKind::Greater, false, true));
        assert!(cmp(CompareKind::Greater, true, false));
        assert!(!cmp(CompareKind::Greater, true, true));

        assert!(cmp(CompareKind::GreaterOrEq, false, false));
        assert!(!cmp(CompareKind::GreaterOrEq, false, true));
        assert!(cmp(CompareKind::GreaterOrEq, true, false));
        assert!(cmp(CompareKind::GreaterOrEq, true, true));

        // Sanity-check Equals/NotEquals while we're here.
        assert!(cmp(CompareKind::Equals, false, false));
        assert!(!cmp(CompareKind::Equals, false, true));
        assert!(!cmp(CompareKind::NotEquals, true, true));
        assert!(cmp(CompareKind::NotEquals, false, true));
    }

    /// Operands of unequal length (one side still converging) combine only over
    /// their common prefix — the surplus tail is dropped, never fabricated.
    /// Regression for the string-concat co-presence bug (`zip_concat` returned
    /// the longer operand's tail verbatim) and the bool-op equal-length panic.
    #[test]
    fn binop_unequal_lengths_combine_common_prefix_only() {
        // String concat: `l` longer than `r` → result is the 2-element prefix.
        let l = ColumnValue::Strings(
            ["a", "b", "c"]
                .into_iter()
                .map(SmolStr::new)
                .collect::<Vec<_>>(),
        );
        let r = ColumnValue::Strings(["1", "2"].into_iter().map(SmolStr::new).collect::<Vec<_>>());
        match apply_binop_column(BinOpKind::Concat, &l, &r) {
            ColumnValue::Strings(v) => {
                assert_eq!(v, vec![SmolStr::new("a1"), SmolStr::new("b2")]);
            }
            other => panic!("expected Strings, got {other:?}"),
        }

        // Arithmetic: `r` longer than `l` → result is the 1-element prefix.
        match apply_binop_column(
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            &ColumnValue::Ints(vec![10]),
            &ColumnValue::Ints(vec![1, 2, 3]),
        ) {
            ColumnValue::Ints(v) => assert_eq!(v, vec![11]),
            other => panic!("expected Ints, got {other:?}"),
        }

        // Bool ops must not panic on unequal lengths; the kernels combine the
        // common prefix and drop the rest.
        match apply_binop_column(
            BinOpKind::Compare(CompareKind::Less),
            &ColumnValue::Bools(vec![false; 3]),
            &ColumnValue::Bools(vec![true; 1]),
        ) {
            ColumnValue::Bools(v) => {
                assert_eq!(v.len(), 1);
                assert!(v[0]); // false < true
            }
            other => panic!("expected Bools, got {other:?}"),
        }
        match apply_binop_column(
            BinOpKind::BoolLogic(LogicKind::And),
            &ColumnValue::Bools(vec![true; 1]),
            &ColumnValue::Bools(vec![true; 4]),
        ) {
            ColumnValue::Bools(v) => {
                assert_eq!(v.len(), 1);
                assert!(v[0]);
            }
            other => panic!("expected Bools, got {other:?}"),
        }
    }

    #[test]
    #[ignore]
    fn binop_benchmarks() {
        let len: usize = 1000000;
        let lv: Vec<i64> = (0..(len as i64)).collect();
        let rv: Vec<i64> = (0..(len as i64)).collect();
        let l = ColumnValue::Ints(lv.clone());
        let r = ColumnValue::Ints(rv.clone());

        let options = microbench::Options::default().time(Duration::new(1, 0));
        microbench::bench(&options, "native_iter", || {
            let _result: Vec<i64> =
                black_box(lv.iter().zip(rv.iter()).map(|(a, b)| a + b).collect());
        });
        microbench::bench_setup(
            &options,
            "native_iter_consume",
            || lv.clone(),
            |mut lv| {
                lv.iter_mut().zip(rv.iter()).for_each(|(a, b)| *a += b);
            },
        );
        microbench::bench(&options, "native_for1", || {
            let mut result: Vec<i64> = Vec::with_capacity(len);
            for i in 0..lv.len() {
                result.push(lv[i] + rv[i]);
            }
        });
        microbench::bench(&options, "native_for2", || {
            let mut result: Vec<i64> = vec![0; len];
            for i in 0..lv.len() {
                result[i] = lv[i] + rv[i];
            }
        });
        microbench::bench_setup(
            &options,
            "ColumnData",
            || l.clone(),
            |l| {
                let _result =
                    apply_binop_column(BinOpKind::Arithmetic(ArithmeticKind::Add), &l, &r);
            },
        );
    }

    #[test]
    #[ignore]
    fn string_benchmarks() {
        let len: usize = 1000000;
        let l: Vec<String> = (0..len).map(|i| i.to_string()).collect();
        let r: Vec<String> = (0..len).map(|i| i.to_string()).collect();

        let options = microbench::Options::default().time(Duration::new(1, 0));
        microbench::bench(&options, "format", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| format!("{a}{b}"))
                    .collect(),
            );
        });
        microbench::bench(&options, "push_str", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| {
                        let mut out = a.clone();
                        out.push_str(b);
                        out
                    })
                    .collect(),
            );
        });
        microbench::bench(&options, "plus", || {
            let _result: Vec<String> = black_box(
                l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| {
                        let mut out = a.clone();
                        out += b;
                        out
                    })
                    .collect(),
            );
        });
        microbench::bench_setup(
            &options,
            "plus_consume",
            || l.clone(),
            |mut l| {
                l.iter_mut().zip(r.iter()).for_each(|(a, b)| {
                    *a += b;
                });
            },
        );
    }

    /// The caller clears a recycled `out`; the call appends the common prefix to what is left.
    #[test]
    fn a_result_is_appended_to_the_callers_column() {
        let add = BinOpKind::Arithmetic(ArithmeticKind::Add);
        let mut out = ColumnValue::Ints(vec![99; 8]);
        out.clear();
        apply_binop_into(
            add,
            &ColumnValue::Ints(vec![1, 2, 3]),
            &ColumnValue::Ints(vec![10, 20]),
            &mut out,
        );
        assert_eq!(out, ColumnValue::Ints(vec![11, 22]));
        apply_binop_into(
            add,
            &ColumnValue::Ints(vec![1]),
            &ColumnValue::Ints(vec![10]),
            &mut out,
        );
        assert_eq!(out, ColumnValue::Ints(vec![11, 22, 11]));
    }

    /// A comparison reads integers and writes a `Bool` column.
    #[test]
    fn a_comparison_writes_a_bool_column() {
        let mut out = ColumnValue::Bools(Vec::new());
        apply_binop_into(
            BinOpKind::Compare(CompareKind::Greater),
            &ColumnValue::Ints(vec![1, 5, 9]),
            &ColumnValue::Ints(vec![4, 4, 4]),
            &mut out,
        );
        assert_eq!(out, ColumnValue::Bools(vec![false, true, true]));
    }

    /// A constant operand is read as one value: it combines with a slice from either side, and
    /// with another constant, as a column of repeats would.
    #[test]
    fn a_constant_operand_combines_without_a_column_of_repeats() {
        use crate::view::View;
        let sub = BinOpKind::Arithmetic(ArithmeticKind::Sub);
        let column = ColumnValue::Ints(vec![10, 20, 30]);
        let five = 5;
        let constant = ColumnView::Ints(View::repeated(&five, 3));
        let slice = column.view().unwrap();
        let apply = |l: ColumnView, r: ColumnView| {
            let mut out = binop_result_column(sub, &l);
            apply_binop_views(sub, &l, &r, &mut out);
            out
        };
        assert_eq!(apply(slice, constant), ColumnValue::Ints(vec![5, 15, 25]));
        assert_eq!(
            apply(constant, slice),
            ColumnValue::Ints(vec![-5, -15, -25])
        );
        assert_eq!(apply(constant, constant), ColumnValue::Ints(vec![0, 0, 0]));
        // The common prefix applies to a constant as to a slice.
        let long = ColumnView::Ints(View::repeated(&five, 10));
        assert_eq!(apply(slice, long), ColumnValue::Ints(vec![5, 15, 25]));
    }

    /// Two constants over no rows combine nothing: a division by a constant zero, and the
    /// negation of the smallest integer, do not fault, as they do not over an empty column.
    #[test]
    fn two_constants_over_no_rows_apply_nothing() {
        use crate::view::View;
        let (one, zero) = (1, 0);
        let floor_div = BinOpKind::Arithmetic(ArithmeticKind::FloorDiv);
        let (l, r) = (
            ColumnView::Ints(View::repeated(&one, 0)),
            ColumnView::Ints(View::repeated(&zero, 0)),
        );
        let mut out = binop_result_column(floor_div, &l);
        apply_binop_views(floor_div, &l, &r, &mut out);
        assert_eq!(out, ColumnValue::Ints(Vec::new()));
        let smallest = i64::MIN;
        let mut out = ColumnValue::Ints(Vec::new());
        apply_unaryop_views(
            UnaryOpKind::Neg,
            &ColumnView::Ints(View::repeated(&smallest, 0)),
            &mut out,
        );
        assert_eq!(out, ColumnValue::Ints(Vec::new()));
    }
}

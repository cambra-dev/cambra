//! BinOp operator: the column dispatch over the scalar kernel in
//! [`crate::scalar_ops`], which owns the operator enums and the element-wise semantics.

use smol_str::SmolStr;
use std::collections::HashMap;

pub use crate::scalar_ops::{ArithmeticKind, BinOpKind, CompareKind, LogicKind};
use crate::scalar_ops::{
    zip_arithmetic, zip_bool_compare, zip_bool_logic, zip_compare, zip_concat,
};

use super::ColumnValue;

/// The empty column that holds the result of `op` over operands shaped like `left`.
fn result_column(op: BinOpKind, left: &ColumnValue) -> ColumnValue {
    match op {
        BinOpKind::Arithmetic(_) => left.empty_like(),
        BinOpKind::Concat => ColumnValue::Strings(Vec::new()),
        BinOpKind::BoolLogic(_) | BinOpKind::Compare(_) => ColumnValue::Bools(Vec::new()),
    }
}

/// The operands cut to their common prefix, `min(l.len(), r.len())`.
///
/// Only co-present positions combine. A longer `l` would otherwise keep its surplus tail in
/// the result, which fabricates values for positions the other operand has not reached. That
/// misfires when `r` has not yet converged (a sibling induction loop's still-empty final
/// read): the result would read as terminal instead of waiting. The sibling half of this
/// invariant is that `MapResultToConstProducer` emits an empty non-terminal tile rather than
/// broadcasting an absent constant.
fn co_present<'a, T>(l: &'a [T], r: &'a [T]) -> (&'a [T], &'a [T]) {
    let rows = l.len().min(r.len());
    (&l[..rows], &r[..rows])
}

/// Apply a binary operation element-wise on two `ColumnValue`s, appending the result to `out`.
///
/// `out` is a column of the result's variant (see [`apply_binop_column`] for a fresh one). One
/// row is appended per position of the operands' common prefix. The caller owns the rest of
/// the column's state: it clears the rows it does not keep and reserves room for the new ones,
/// and the kernel writes each result once into that room.
pub fn apply_binop_into(
    op: BinOpKind,
    left: &ColumnValue,
    right: &ColumnValue,
    out: &mut ColumnValue,
) {
    match (op, left, right, out) {
        (
            BinOpKind::Arithmetic(op),
            ColumnValue::Ints(l),
            ColumnValue::Ints(r),
            ColumnValue::Ints(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_arithmetic(op, l, r, o);
        }
        (
            BinOpKind::Arithmetic(op),
            ColumnValue::UInts(l),
            ColumnValue::UInts(r),
            ColumnValue::UInts(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_arithmetic(op, l, r, o);
        }
        (
            BinOpKind::BoolLogic(op),
            ColumnValue::Bools(l),
            ColumnValue::Bools(r),
            ColumnValue::Bools(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_bool_logic(op, l, r, o);
        }
        (
            BinOpKind::Concat,
            ColumnValue::Strings(l),
            ColumnValue::Strings(r),
            ColumnValue::Strings(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_concat(l, r, o);
        }
        (
            BinOpKind::Compare(op),
            ColumnValue::Strings(l),
            ColumnValue::Strings(r),
            ColumnValue::Bools(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_compare(op, l, r, o);
        }
        (
            BinOpKind::Compare(op),
            ColumnValue::Ints(l),
            ColumnValue::Ints(r),
            ColumnValue::Bools(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_compare(op, l, r, o);
        }
        (
            BinOpKind::Compare(op),
            ColumnValue::UInts(l),
            ColumnValue::UInts(r),
            ColumnValue::Bools(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_compare(op, l, r, o);
        }
        (
            BinOpKind::Compare(op),
            ColumnValue::Bools(l),
            ColumnValue::Bools(r),
            ColumnValue::Bools(o),
        ) => {
            let (l, r) = co_present(l, r);
            zip_bool_compare(op, l, r, o);
        }
        // A product compares **componentwise**, which is the whole of what makes one
        // equatable (`src/ccl/design/type-inference.md`, "What the tables hold").
        (
            BinOpKind::Compare(op @ (CompareKind::Equals | CompareKind::NotEquals)),
            ColumnValue::Records(l),
            ColumnValue::Records(r),
            ColumnValue::Bools(o),
        ) => o.extend(compare_records(op, l, r)),
        (op, left, right, out) => {
            panic!("Unsupported binop: {op:?} on {left:?}, {right:?}, into a column {out:?}")
        }
    }
}

/// Apply a binary operation element-wise on two `ColumnValue`s, into a newly allocated column.
///
/// Neither operand's buffer is reused.
pub fn apply_binop_column(op: BinOpKind, left: &ColumnValue, right: &ColumnValue) -> ColumnValue {
    let mut out = result_column(op, left);
    apply_binop_into(op, left, right, &mut out);
    out
}

/// Compare two record columns field by field, `Equals` conjoining the results and
/// `NotEquals` disjoining them.
///
/// **The fields both columns carry are the product the type names.** Typing rejects a
/// comparison between two different products, so the two field sets differ only where
/// width subtyping let a wider value reach a narrower position and the tiling kept the
/// surplus column. A column the position's type does not name is not part of the value
/// there, and the intersection reads the value at its type whichever operand carries it.
///
/// The length is the shortest column the intersection reads, a column still filling being
/// one whose later positions have not been decided. A surplus column is excluded from that
/// minimum for the same reason it is excluded from the answer: its extent belongs to the
/// wider value, and a short one would truncate a result the named fields already decided.
///
/// A value carrying exactly the fields its type names would retire the intersection. What
/// keeps the surplus is inlining dropping the parameter's annotation — see the vault issue
/// `type-checker-inlining-drops-a-narrowing-annotation`.
fn compare_records(
    op: CompareKind,
    left: &HashMap<SmolStr, ColumnValue>,
    right: &HashMap<SmolStr, ColumnValue>,
) -> Vec<bool> {
    let rows = left
        .iter()
        .filter(|(field, _)| right.contains_key(*field))
        .flat_map(|(field, l)| [l.len(), right[field].len()])
        .min()
        .unwrap_or(0);
    let mut acc = vec![op == CompareKind::Equals; rows];
    for (field, l) in left {
        // A column only one side carries is the surplus of a wider value, not a field of
        // the product being compared.
        let Some(r) = right.get(field) else {
            continue;
        };
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
}

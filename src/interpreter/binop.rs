//! BinOp operator: binary arithmetic operations on dataflow values.

use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

use bit_vec::BitVec;
use smol_str::{SmolStr, SmolStrBuilder};

use super::ColumnValue;

/// Kinds of binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    Arithmetic(ArithmeticKind),
    BoolLogic(LogicKind),
    Concat,
    Compare(CompareKind),
    // Other binary operators are either less useful at the
    // moment (e.g. bitwise ops) or require non-Int extents
    // to be implmented first (e.g. float division).
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithmeticKind {
    Add,
    Sub,
    Mul,
    FloorDiv,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareKind {
    Equals,
    NotEquals,
    Less,
    LessOrEq,
    Greater,
    GreaterOrEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicKind {
    And,
    Nand,
    Or,
    Nor,
    Xor,
    Xnor,
}

// Performance note: trying to factor this futher to avoid repeating the zip/iter logic
// slows it down by ~15%
fn zip_arithmetic<T: Copy + AddAssign<T> + SubAssign<T> + MulAssign<T> + DivAssign<T>>(
    op: ArithmeticKind,
    mut l: Vec<T>,
    r: &[T],
) -> Vec<T> {
    match op {
        ArithmeticKind::Add => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a += *b),
        ArithmeticKind::Sub => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a -= *b),
        ArithmeticKind::Mul => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a *= *b),
        ArithmeticKind::FloorDiv => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a /= *b),
    };
    l
}

fn zip_concat(mut l: Vec<SmolStr>, r: &[SmolStr]) -> Vec<SmolStr> {
    l.iter_mut().zip(r.iter()).for_each(|(a, b)| {
        *a = {
            let mut builder = SmolStrBuilder::new();
            builder.push_str(a);
            builder.push_str(b);
            builder.finish()
        }
    });
    l
}

fn zip_compare<T: PartialEq + PartialOrd>(op: CompareKind, l: Vec<T>, r: &[T]) -> BitVec {
    match op {
        CompareKind::Equals => l.iter().zip(r.iter()).map(|(a, b)| a == b).collect(),
        CompareKind::NotEquals => l.iter().zip(r.iter()).map(|(a, b)| a != b).collect(),
        CompareKind::Less => l.iter().zip(r.iter()).map(|(a, b)| a < b).collect(),
        CompareKind::LessOrEq => l.iter().zip(r.iter()).map(|(a, b)| a <= b).collect(),
        CompareKind::Greater => l.iter().zip(r.iter()).map(|(a, b)| a > b).collect(),
        CompareKind::GreaterOrEq => l.iter().zip(r.iter()).map(|(a, b)| a >= b).collect(),
    }
}

fn zip_bool_compare(op: CompareKind, mut l: BitVec, r: &BitVec) -> BitVec {
    // Boolean ordering: false < true (0 < 1).
    match op {
        CompareKind::Equals => l.xnor(r),
        CompareKind::NotEquals => l.xor(r),
        CompareKind::Less => {
            // a < b  ≡  !a & b
            l.negate();
            l.and(r)
        }
        CompareKind::LessOrEq => {
            // a <= b  ≡  !a | b
            l.negate();
            l.or(r)
        }
        CompareKind::Greater => {
            // a > b  ≡  a & !b
            let mut not_r = r.clone();
            not_r.negate();
            l.and(&not_r)
        }
        CompareKind::GreaterOrEq => {
            // a >= b  ≡  a | !b
            let mut not_r = r.clone();
            not_r.negate();
            l.or(&not_r)
        }
    };
    l
}

fn zip_bool_logic(op: LogicKind, mut l: BitVec, r: &BitVec) -> BitVec {
    match op {
        LogicKind::And => l.and(r),
        LogicKind::Nand => l.nand(r),
        LogicKind::Or => l.or(r),
        LogicKind::Nor => l.nor(r),
        LogicKind::Xor => l.xor(r),
        LogicKind::Xnor => l.xnor(r),
    };
    l
}

/// Apply a binary operation element-wise on two `ColumnValue`s.
pub fn apply_binop_column(op: BinOpKind, left: ColumnValue, right: &ColumnValue) -> ColumnValue {
    match (op, left, right) {
        (BinOpKind::Arithmetic(op), ColumnValue::Ints(l), ColumnValue::Ints(r)) => {
            ColumnValue::Ints(zip_arithmetic(op, l, r))
        }
        (BinOpKind::Arithmetic(op), ColumnValue::UInts(l), ColumnValue::UInts(r)) => {
            ColumnValue::UInts(zip_arithmetic(op, l, r))
        }
        (BinOpKind::BoolLogic(op), ColumnValue::Bools(l), ColumnValue::Bools(r)) => {
            ColumnValue::Bools(zip_bool_logic(op, l, r))
        }
        (BinOpKind::Concat, ColumnValue::Strings(l), ColumnValue::Strings(r)) => {
            ColumnValue::Strings(zip_concat(l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Strings(l), ColumnValue::Strings(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Ints(l), ColumnValue::Ints(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::UInts(l), ColumnValue::UInts(r)) => {
            ColumnValue::Bools(zip_compare(op, l, r))
        }
        (BinOpKind::Compare(op), ColumnValue::Bools(l), ColumnValue::Bools(r)) => {
            ColumnValue::Bools(zip_bool_compare(op, l, r))
        }
        (op, left, right) => panic!("Unsupported binop: {:?} on {:?}, {:?}", op, left, right),
    }
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
        use bit_vec::BitVec;

        // Compare single bool values via the public apply_binop_column API.
        let cmp = |op: CompareKind, l: bool, r: bool| -> bool {
            let result = apply_binop_column(
                BinOpKind::Compare(op),
                ColumnValue::Bools(BitVec::from_elem(1, l)),
                &ColumnValue::Bools(BitVec::from_elem(1, r)),
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
                let _result = apply_binop_column(BinOpKind::Arithmetic(ArithmeticKind::Add), l, &r);
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
}

//! The scalar semantics of CHL's binary operators, as a column kernel.
//!
//! `crate::interpreter::binop` applies these kernels to a `ColumnValue`.
//! `crate::ccl::planning::const_fold` calls the same kernels on one-element columns.
//!
//! The vectorized form is the primitive and the single-element call wraps it, rather than
//! the other way round: a per-element closure over the column costs about 15% (measured;
//! the note on [`zip_arithmetic`]), and folding one pair is not on any hot path.
//!
//! Its own module because the layering forbids `ccl` from depending upward on
//! `interpreter`, so a kernel both import lives below both. That is also why the operator
//! enums live here, with `crate::ccl::BinOpKind` converting into [`BinOpKind`]
//! (`impl From`, in `src/ccl/ops.rs`) — the one place the two spellings meet.

use std::ops::{AddAssign, MulAssign, SubAssign};

use bit_vec::BitVec;
use smol_str::{SmolStr, SmolStrBuilder};

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
    Pow,
}

/// Integer division rounding toward negative infinity.
pub(crate) trait IntFloorDiv: Copy {
    fn floor_div(self, divisor: Self) -> Self;
}

impl IntFloorDiv for i64 {
    fn floor_div(self, divisor: Self) -> Self {
        let quotient = self / divisor;
        if self % divisor != 0 && (self < 0) != (divisor < 0) {
            // A nonzero remainder excludes an exact MIN quotient, so subtraction cannot overflow.
            quotient - 1
        } else {
            quotient
        }
    }
}

impl IntFloorDiv for u64 {
    fn floor_div(self, divisor: Self) -> Self {
        self / divisor
    }
}

/// Integer exponentiation, the scalar behind [`ArithmeticKind::Pow`].
///
/// A separate trait because `**` has no `*Assign` operator to bound
/// [`zip_arithmetic`]'s element type by. The exponent is non-negative by typing, so the
/// two element types differ only in whether that has to be stated: `u64` has no negative
/// value to exclude.
pub(crate) trait IntPow: Copy {
    /// The multiplicative identity, which seeds [`Self::raised`] and is what
    /// `a ** 0` yields for every `a`.
    const ONE: Self;

    fn mul_wrapping(self, rhs: Self) -> Self;

    /// `self` raised to a non-negative `exponent`, by squaring, so the cost is
    /// logarithmic in `exponent`.
    ///
    /// Wrapping, so both profiles answer the same. The release profile sets no
    /// `overflow-checks`, and a plain `*` therefore panics on `2 ** 64` in debug and
    /// answers `0` in release. `zip_arithmetic`'s `+`, `-`, and `*` still use plain
    /// operators and retain that profile-dependent overflow behavior, tracked in the vault
    /// issue `interpreter-integer-arithmetic-divergences`. Integer division
    /// panics on zero divisors and on `i64::MIN // -1` in both profiles.
    fn raised(mut self, mut exponent: u64) -> Self {
        let mut acc = Self::ONE;
        while exponent > 0 {
            if exponent & 1 == 1 {
                acc = acc.mul_wrapping(self);
            }
            exponent >>= 1;
            if exponent > 0 {
                self = self.mul_wrapping(self);
            }
        }
        acc
    }

    fn int_pow(self, exponent: Self) -> Self;
}

impl IntPow for i64 {
    const ONE: Self = 1;

    fn mul_wrapping(self, rhs: Self) -> Self {
        i64::wrapping_mul(self, rhs)
    }

    fn int_pow(self, exponent: Self) -> Self {
        // The exponent is non-negative: `**` states `{Int | __elem >= 0}` of it
        // (`src/ccl/lower/exprs.rs`'s `pow_with_checked_exponent`), so a negative one is a
        // type error and never arrives. Asserted in every profile rather than in debug
        // alone: `unsigned_abs` would turn a negative exponent into a large positive one
        // and answer, so proceeding past this is a wrong number rather than a crash.
        assert!(exponent >= 0, "`**` states a non-negative exponent");
        self.raised(exponent.unsigned_abs())
    }
}

impl IntPow for u64 {
    const ONE: Self = 1;

    fn mul_wrapping(self, rhs: Self) -> Self {
        u64::wrapping_mul(self, rhs)
    }

    fn int_pow(self, exponent: Self) -> Self {
        self.raised(exponent)
    }
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
pub(crate) fn zip_arithmetic<
    T: IntPow + IntFloorDiv + AddAssign<T> + SubAssign<T> + MulAssign<T>,
>(
    op: ArithmeticKind,
    mut l: Vec<T>,
    r: &[T],
) -> Vec<T> {
    // Combine only co-present positions — element-wise over the common
    // prefix, `min(l.len(), r.len())`. `zip` already stops at the shorter
    // side, but it leaves a *longer* `l`'s tail untouched and returns it, so
    // without this truncate `l op r` with `r` shorter would emit `l`'s surplus
    // verbatim. That misfires when `r` is a value that has not yet converged
    // (e.g. a sibling induction loop's still-empty final read): the result
    // would fabricate `l`'s tail and read as terminal instead of waiting.
    // (Sibling half of this invariant: `MapResultToConstProducer` emits an
    // empty non-terminal tile rather than broadcasting an absent constant.)
    l.truncate(r.len());
    match op {
        ArithmeticKind::Add => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a += *b),
        ArithmeticKind::Sub => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a -= *b),
        ArithmeticKind::Mul => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a *= *b),
        ArithmeticKind::FloorDiv => l
            .iter_mut()
            .zip(r.iter())
            .for_each(|(a, b)| *a = a.floor_div(*b)),
        ArithmeticKind::Pow => l
            .iter_mut()
            .zip(r.iter())
            .for_each(|(a, b)| *a = a.int_pow(*b)),
    };
    l
}

pub(crate) fn zip_concat(mut l: Vec<SmolStr>, r: &[SmolStr]) -> Vec<SmolStr> {
    // Combine only co-present positions — see `zip_arithmetic`. Without this,
    // `l ++ r` with `r` shorter would return `l`'s surplus tail verbatim,
    // fabricating values for positions the other operand has not yet reached
    // (e.g. a still-converging sibling read) and reading terminal too early.
    l.truncate(r.len());
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

pub(crate) fn zip_compare<T: PartialEq + PartialOrd>(
    op: CompareKind,
    l: Vec<T>,
    r: &[T],
) -> BitVec {
    match op {
        CompareKind::Equals => l.iter().zip(r.iter()).map(|(a, b)| a == b).collect(),
        CompareKind::NotEquals => l.iter().zip(r.iter()).map(|(a, b)| a != b).collect(),
        CompareKind::Less => l.iter().zip(r.iter()).map(|(a, b)| a < b).collect(),
        CompareKind::LessOrEq => l.iter().zip(r.iter()).map(|(a, b)| a <= b).collect(),
        CompareKind::Greater => l.iter().zip(r.iter()).map(|(a, b)| a > b).collect(),
        CompareKind::GreaterOrEq => l.iter().zip(r.iter()).map(|(a, b)| a >= b).collect(),
    }
}

/// Align two bit-vectors to their common-prefix length. `BitVec`'s in-place set
/// ops (`and`/`or`/`xor`/…) assert *equal* length, so a still-converging operand
/// (one side ahead of the other — the co-presence case `zip_arithmetic` handles
/// by truncation) would panic without this. `l` is truncated in place; `r` is
/// returned truncated, cloned into `scratch` only when it is the longer side.
fn align_common<'a>(l: &mut BitVec, r: &'a BitVec, scratch: &'a mut Option<BitVec>) -> &'a BitVec {
    let n = l.len().min(r.len());
    l.truncate(n);
    if r.len() == n {
        r
    } else {
        let mut c = r.clone();
        c.truncate(n);
        &*scratch.insert(c)
    }
}

pub(crate) fn zip_bool_compare(op: CompareKind, mut l: BitVec, r: &BitVec) -> BitVec {
    // Boolean ordering: false < true (0 < 1).
    let mut scratch = None;
    let r = align_common(&mut l, r, &mut scratch);
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

pub(crate) fn zip_bool_logic(op: LogicKind, mut l: BitVec, r: &BitVec) -> BitVec {
    let mut scratch = None;
    let r = align_common(&mut l, r, &mut scratch);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_division_signed_boundaries() {
        let cases = [
            (7, 2, 3),
            (-7, 2, -4),
            (7, -2, -4),
            (-7, -2, 3),
            (6, -2, -3),
            (-6, 2, -3),
            (-6, -2, 3),
            (0, 2, 0),
            (0, -2, 0),
            (i64::MIN, 1, i64::MIN),
            (i64::MIN, 3, -3_074_457_345_618_258_603),
            (i64::MIN, i64::MIN, 1),
            (i64::MIN, i64::MAX, -2),
            (i64::MAX, i64::MIN, -1),
            (i64::MAX, -1, -i64::MAX),
            (1, i64::MIN, -1),
            (-1, i64::MIN, 0),
        ];
        let left = cases.iter().map(|&(a, _, _)| a).collect();
        let right: Vec<_> = cases.iter().map(|&(_, b, _)| b).collect();
        let expected: Vec<_> = cases.iter().map(|&(_, _, q)| q).collect();
        assert_eq!(
            zip_arithmetic(ArithmeticKind::FloorDiv, left, &right),
            expected
        );
    }

    #[test]
    fn floor_division_satisfies_floor_bounds() {
        for a in -128_i64..=127 {
            for b in -128_i64..=127 {
                if b == 0 {
                    continue;
                }
                let q = i128::from(a.floor_div(b));
                let (a, b) = (i128::from(a), i128::from(b));
                if b > 0 {
                    assert!(q * b <= a && a < (q + 1) * b, "{a} // {b} = {q}");
                } else {
                    assert!(q * b >= a && a > (q + 1) * b, "{a} // {b} = {q}");
                }
            }
        }
    }

    #[test]
    fn floor_division_unsigned() {
        assert_eq!(
            zip_arithmetic(
                ArithmeticKind::FloorDiv,
                vec![0_u64, 7, u64::MAX],
                &[2, 2, 1]
            ),
            vec![0, 3, u64::MAX]
        );
    }

    #[test]
    #[should_panic(expected = "divide by zero")]
    fn floor_division_zero_divisor_panics() {
        zip_arithmetic(ArithmeticKind::FloorDiv, vec![1_i64], &[0]);
    }

    #[test]
    #[should_panic(expected = "divide by zero")]
    fn floor_division_unsigned_zero_divisor_panics() {
        zip_arithmetic(ArithmeticKind::FloorDiv, vec![1_u64], &[0]);
    }

    #[test]
    #[should_panic(expected = "divide with overflow")]
    fn floor_division_unrepresentable_quotient_panics() {
        zip_arithmetic(ArithmeticKind::FloorDiv, vec![i64::MIN], &[-1]);
    }
}

//! The scalar semantics of CHL's binary operators, as a column kernel.
//!
//! **One implementation, two callers.** `crate::interpreter::binop` maps these over a
//! `ColumnValue`, and `crate::ccl::planning::const_fold` calls them on a one-element column
//! to fold a closed computation. A second implementation for the second caller is what put
//! the `//` disagreement in two places, and agreement between a compile-time answer and a
//! run-time one is not a property a test can establish once.
//!
//! The vectorized form is the primitive and the single-element call wraps it, rather than
//! the other way round: a per-element closure over the column costs about 15% (measured;
//! the note on [`zip_arithmetic`]), and folding one pair is not on any hot path.
//!
//! Its own module because the layering forbids `ccl` from depending upward on
//! `interpreter`, so a kernel both import lives below both. That is also why the operator
//! enums live here, with `crate::ccl::BinOpKind` converting into [`BinOpKind`]
//! (`impl From`, in `src/ccl/ops.rs`) — the one place the two spellings meet.

use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

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

/// Integer exponentiation, the scalar behind [`ArithmeticKind::Pow`].
///
/// A separate trait because `**` has no `*Assign` operator to bound
/// [`zip_arithmetic`]'s element type by. The exponent is non-negative by typing, so the
/// two element types differ only in whether that has to be stated: `usize` has no negative
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
    /// answers `0` in release. `zip_arithmetic`'s `+ - * //` are still the plain
    /// operators and still diverge that way — the vault issue
    /// `interpreter-integer-arithmetic-divergences` carries the class.
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

impl IntPow for usize {
    const ONE: Self = 1;

    fn mul_wrapping(self, rhs: Self) -> Self {
        usize::wrapping_mul(self, rhs)
    }

    fn int_pow(self, exponent: Self) -> Self {
        self.raised(exponent as u64)
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
    T: IntPow + AddAssign<T> + SubAssign<T> + MulAssign<T> + DivAssign<T>,
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
        ArithmeticKind::FloorDiv => l.iter_mut().zip(r.iter()).for_each(|(a, b)| *a /= *b),
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

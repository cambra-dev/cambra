//! Semantic refinement subtyping, discharged to an SMT solver.
//!
//! Refinement subtyping in [`super::constrain`] matches refinements by structural
//! predicate equality, which is sound and incomplete: `{Int | __elem == 1 ^+ 3 ^+ 2}`
//! and `{Int | __elem == 1 ^+ 5}` denote one set and compare unequal. This module
//! decides the leftover cases by asking whether the lhs predicates entail the rhs
//! ones.
//!
//! The encoded fragment is linear integer arithmetic over `Int` and `Bool` bases.
//! Anything outside it — a `String` base, floor division, a product of two
//! unknowns, a predicate mentioning an application or a projection — yields
//! `false`, and the caller reports the structural mismatch it would have reported
//! without this module. So does a solver that will not start: `smt_sub` only ever
//! turns a rejection into an acceptance, never the reverse.

use std::collections::HashMap;
use std::io;

use easy_smt::{Context, ContextBuilder, Response, SExpr};

use crate::ccl::{
    ArithmeticKind, BaseType, BinOpKind, CompareKind, Lit, LogicKind, Name, Refinement, Type,
    TypedExpr, TypedExprNode, UnaryOpKind,
};

/// Whether every value of `base` satisfying all of `lhs` satisfies all of `rhs`.
///
/// [`REFINEMENT_BINDER`] is declared once at `base`'s sort and shared by both
/// sides, so the query is `∀ __elem. ⋀lhs ⇒ ⋀rhs`, decided by checking
/// `⋀lhs ∧ ¬⋀rhs` unsatisfiable. Every other free name is declared at the sort of
/// the node referencing it and is therefore universally quantified too; the
/// refinements its own type carries are dropped, which only weakens the
/// antecedent.
///
/// Both sides' predicates must already be transported into one frame — this
/// compares terms, so a name meaning two different things across the two sides
/// makes the answer meaningless.
///
/// [`REFINEMENT_BINDER`]: crate::ccl::REFINEMENT_BINDER
pub fn smt_sub(base: &Type, lhs: &[Refinement], rhs: &[Refinement]) -> bool {
    if rhs.is_empty() {
        return true;
    }
    with_solver(|ctx| check(ctx, base, lhs, rhs)).unwrap_or(false)
}

/// One query: build it, then run it inside a `push`/`pop` scope so the constants
/// it declares and the formula it asserts leave no trace for the next query.
fn check(
    ctx: &mut Context,
    base: &Type,
    lhs: &[Refinement],
    rhs: &[Refinement],
) -> io::Result<bool> {
    // Encoding is pure and can bail; bailing before the `push` leaves no scope to
    // unwind.
    let mut enc = Encode::new(ctx);
    let Some(formula) = enc.query(base, lhs, rhs) else {
        return Ok(false);
    };
    let decls = enc.decls;

    ctx.push()?;
    // A failed exchange poisons the slot and drops the context, so the `pop`
    // balancing this `push` only has to happen on the success path.
    let unsat = run(ctx, decls, formula)?;
    ctx.pop()?;
    Ok(unsat)
}

fn run(ctx: &mut Context, decls: Vec<(String, SExpr)>, formula: SExpr) -> io::Result<bool> {
    for (sym, sort) in decls {
        ctx.declare_const(sym, sort)?;
    }
    ctx.assert(formula)?;
    // `Unknown` is not an entailment proof, so it joins `Sat` in rejecting.
    Ok(matches!(ctx.check()?, Response::Unsat))
}

/// Translation from a refinement predicate to an s-expression, plus the constant
/// declarations the result depends on.
///
/// `Context` is borrowed immutably: building s-expressions is pure, and deferring
/// the `declare-const` commands to [`run`] keeps a translation that bails from
/// having sent anything.
struct Encode<'a> {
    ctx: &'a Context,
    /// Free names encoded so far, keyed by [`Name`] identity so that one name is
    /// one SMT constant across both sides of the query.
    vars: HashMap<Name, SExpr>,
    /// `(symbol, sort)` per entry of `vars`, in declaration order.
    decls: Vec<(String, SExpr)>,
}

impl<'a> Encode<'a> {
    fn new(ctx: &'a Context) -> Self {
        Encode {
            ctx,
            vars: HashMap::new(),
            decls: Vec::new(),
        }
    }

    /// `⋀lhs ∧ ¬⋀rhs` — unsatisfiable exactly when the entailment holds.
    fn query(&mut self, base: &Type, lhs: &[Refinement], rhs: &[Refinement]) -> Option<SExpr> {
        // `__elem`'s sort comes from the refined base rather than from whatever a
        // predicate's occurrence of it happens to be typed at, and declaring it
        // ahead of both sides is what makes them share the constant.
        let elem_sort = self.sort(base)?;
        self.declare(Name::elem(), elem_sort);

        let mut conjuncts: Vec<SExpr> = lhs
            .iter()
            .map(|r| self.expr(&r.predicate))
            .collect::<Option<_>>()?;
        let goals: Vec<SExpr> = rhs
            .iter()
            .map(|r| self.expr(&r.predicate))
            .collect::<Option<_>>()?;
        conjuncts.push(self.ctx.not(self.ctx.and_many(goals)));
        Some(self.ctx.and_many(conjuncts))
    }

    /// The SMT sort a Cambra type is encoded at, or `None` outside the fragment.
    ///
    /// `UInt` encodes as `Int` without its non-negativity, on the same footing as
    /// a free variable's dropped refinements: an assumption left out weakens the
    /// antecedent and cannot make an invalid entailment provable.
    fn sort(&self, ty: &Type) -> Option<SExpr> {
        match ty.peel_refinements() {
            Type::Base(BaseType::Int | BaseType::UInt) => Some(self.ctx.int_sort()),
            Type::Base(BaseType::Bool) => Some(self.ctx.bool_sort()),
            _ => None,
        }
    }

    fn expr(&mut self, e: &TypedExpr) -> Option<SExpr> {
        match &e.node {
            TypedExprNode::Lit(Lit::Int(n)) => Some(self.numeral(*n)),
            TypedExprNode::Lit(Lit::Bool(b)) => Some(if *b {
                self.ctx.true_()
            } else {
                self.ctx.false_()
            }),
            TypedExprNode::Var(name) => self.var(name, &e.ty),
            TypedExprNode::UnaryOp(op, operand) => {
                let operand = self.expr(operand)?;
                Some(match op {
                    UnaryOpKind::Neg => self.ctx.negate(operand),
                    UnaryOpKind::Not => self.ctx.not(operand),
                })
            }
            TypedExprNode::BinOp { left, op, right } => {
                let (l, r) = (self.expr(left)?, self.expr(right)?);
                self.binop(*op, left, right, l, r)
            }
            _ => None,
        }
    }

    fn binop(
        &self,
        op: BinOpKind,
        left: &TypedExpr,
        right: &TypedExpr,
        l: SExpr,
        r: SExpr,
    ) -> Option<SExpr> {
        let c = self.ctx;
        Some(match op {
            // `^+` computes what `+` computes and differs only in the trait it
            // states (`src/ccl/ops.rs`), so both are SMT's `+`.
            BinOpKind::Arithmetic(ArithmeticKind::Add | ArithmeticKind::AddRefined) => c.plus(l, r),
            BinOpKind::Arithmetic(ArithmeticKind::Sub) => c.sub(l, r),
            // A product stays linear when one factor is a constant.
            BinOpKind::Arithmetic(ArithmeticKind::Mul)
                if is_int_literal(left) || is_int_literal(right) =>
            {
                c.times(l, r)
            }
            BinOpKind::Compare(CompareKind::Equals) => c.eq(l, r),
            BinOpKind::Compare(CompareKind::NotEquals) => c.not(c.eq(l, r)),
            BinOpKind::Compare(CompareKind::Less) => c.lt(l, r),
            BinOpKind::Compare(CompareKind::LessOrEq) => c.lte(l, r),
            BinOpKind::Compare(CompareKind::Greater) => c.gt(l, r),
            BinOpKind::Compare(CompareKind::GreaterOrEq) => c.gte(l, r),
            BinOpKind::BoolLogic(LogicKind::And) => c.and(l, r),
            BinOpKind::BoolLogic(LogicKind::Or) => c.or(l, r),
            BinOpKind::BoolLogic(LogicKind::Xor) => c.xor(l, r),
            BinOpKind::BoolLogic(LogicKind::Nand) => c.not(c.and(l, r)),
            BinOpKind::BoolLogic(LogicKind::Nor) => c.not(c.or(l, r)),
            BinOpKind::BoolLogic(LogicKind::Xnor) => c.eq(l, r),
            // Outside the fragment: a product of two unknowns is nonlinear, and
            // SMT-LIB's `div` is Euclidean rather than floor division, so `//`
            // would encode as something else at a negative divisor. `++` is on
            // strings, which have no sort here.
            BinOpKind::Arithmetic(ArithmeticKind::Mul | ArithmeticKind::FloorDiv)
            | BinOpKind::Concat => return None,
        })
    }

    /// SMT-LIB numerals are non-negative, so a negative literal encodes as a
    /// negation applied to its magnitude.
    fn numeral(&self, n: i64) -> SExpr {
        let magnitude = self.ctx.numeral(n.unsigned_abs());
        if n < 0 {
            self.ctx.negate(magnitude)
        } else {
            magnitude
        }
    }

    fn var(&mut self, name: &Name, ty: &Type) -> Option<SExpr> {
        if let Some(e) = self.vars.get(name) {
            return Some(*e);
        }
        let sort = self.sort(ty)?;
        Some(self.declare(name.clone(), sort))
    }

    /// Assign `name` a fresh constant at `sort`.
    ///
    /// The symbol is positional rather than the name's spelling: a [`Name`]'s
    /// identity is not its spelling (two `Unique`s share a `base`), and a spelling
    /// need not be a legal SMT-LIB symbol.
    fn declare(&mut self, name: Name, sort: SExpr) -> SExpr {
        let sym = format!("v!{}", self.decls.len());
        let e = self.ctx.atom(sym.as_str());
        self.decls.push((sym, sort));
        self.vars.insert(name, e);
        e
    }
}

fn is_int_literal(e: &TypedExpr) -> bool {
    match &e.node {
        TypedExprNode::Lit(Lit::Int(_)) => true,
        TypedExprNode::UnaryOp(UnaryOpKind::Neg, operand) => is_int_literal(operand),
        _ => false,
    }
}

/// The per-thread solver subprocess.
enum Slot {
    /// No query has run on this thread yet.
    Unstarted,
    /// Boxed because a `Context` is ~1KB and the other two variants are empty.
    Ready(Box<Context>),
    /// The subprocess would not start, or an exchange with it failed. Poisoning is
    /// permanent: a solver that broke mid-query has an assertion stack nothing
    /// here can account for, and starting a replacement would hide a
    /// misencoding behind a retry.
    Poisoned,
}

thread_local! {
    static SOLVER: std::cell::RefCell<Slot> = const { std::cell::RefCell::new(Slot::Unstarted) };
}

/// Run `f` against this thread's solver, starting it on first use.
///
/// `None` when the solver is unavailable or `f`'s exchange with it fails, which
/// callers read as "no proof".
fn with_solver<T>(f: impl FnOnce(&mut Context) -> io::Result<T>) -> Option<T> {
    SOLVER.with_borrow_mut(|slot| {
        if matches!(slot, Slot::Unstarted) {
            *slot = match ContextBuilder::new().with_z3_defaults().build() {
                Ok(ctx) => Slot::Ready(Box::new(ctx)),
                Err(_) => Slot::Poisoned,
            };
        }
        let Slot::Ready(ctx) = slot else {
            return None;
        };
        match f(ctx) {
            Ok(value) => Some(value),
            Err(_) => {
                *slot = Slot::Poisoned;
                None
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, TypedExpr};
    use std::rc::Rc;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `__elem <op> rhs` as a refinement over `Int`.
    fn elem_cmp(op: CompareKind, rhs: TypedExpr) -> Refinement {
        Refinement::born(Rc::new(
            TypedExpr::binop(
                TypedExpr::var(Name::elem()).with_ty(int()),
                BinOpKind::Compare(op),
                rhs,
            )
            .with_ty(Type::Base(BaseType::Bool)),
        ))
    }

    fn lit(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n)).with_ty(int())
    }

    fn add(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::AddRefined), r).with_ty(int())
    }

    /// The case `constrain`'s structural matching cannot decide: two sums that
    /// compare unequal as terms and denote one value.
    #[test]
    fn equal_sums_entail_each_other() {
        let lhs = [elem_cmp(
            CompareKind::Equals,
            add(add(lit(1), lit(3)), lit(2)),
        )];
        let rhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(5)))];
        assert!(smt_sub(&int(), &lhs, &rhs));
        assert!(smt_sub(&int(), &rhs, &lhs));
    }

    #[test]
    fn unequal_sums_entail_neither_way() {
        let lhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(3)))];
        let rhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(5)))];
        assert!(!smt_sub(&int(), &lhs, &rhs));
        assert!(!smt_sub(&int(), &rhs, &lhs));
    }

    /// A singleton entails every bound it satisfies, and no bound it violates.
    #[test]
    fn a_singleton_entails_the_bounds_it_satisfies() {
        let five = [elem_cmp(CompareKind::Equals, lit(5))];
        assert!(smt_sub(
            &int(),
            &five,
            &[elem_cmp(CompareKind::GreaterOrEq, lit(1))]
        ));
        assert!(smt_sub(
            &int(),
            &five,
            &[elem_cmp(CompareKind::NotEquals, lit(0))]
        ));
        assert!(!smt_sub(
            &int(),
            &five,
            &[elem_cmp(CompareKind::Less, lit(1))]
        ));
    }

    /// Entailment is over the whole set on each side, conjunctively.
    #[test]
    fn both_sides_are_conjunctions() {
        let bounded = [
            elem_cmp(CompareKind::GreaterOrEq, lit(3)),
            elem_cmp(CompareKind::LessOrEq, lit(4)),
        ];
        let weaker = [
            elem_cmp(CompareKind::NotEquals, lit(0)),
            elem_cmp(CompareKind::Less, lit(10)),
        ];
        assert!(smt_sub(&int(), &bounded, &weaker));
        assert!(!smt_sub(&int(), &weaker, &bounded));
    }

    /// A free name is universally quantified, so a claim that holds only for some
    /// of its values is not an entailment.
    #[test]
    fn a_free_name_is_universally_quantified() {
        let t = TypedExpr::var(Name::raw("t")).with_ty(int());
        let lhs = [elem_cmp(CompareKind::Equals, add(t.clone(), lit(3)))];
        // `__elem == t + 3` gives `__elem > t`, and gives nothing about `__elem`
        // against a constant.
        assert!(smt_sub(&int(), &lhs, &[elem_cmp(CompareKind::Greater, t)]));
        assert!(!smt_sub(
            &int(),
            &lhs,
            &[elem_cmp(CompareKind::Greater, lit(3))]
        ));
    }

    /// Outside the encoded fragment the answer is `false` rather than a guess: a
    /// `String` base has no sort, so even a predicate pair that matches
    /// structurally is left to the caller's own comparison.
    #[test]
    fn an_unencodable_base_is_no_proof() {
        let refs = [elem_cmp(CompareKind::Equals, lit(5))];
        assert!(!smt_sub(&Type::Base(BaseType::String), &refs, &refs));
    }

    /// A term the encoding does not cover bails the whole query, including the
    /// conjuncts around it that would have sufficed on their own.
    #[test]
    fn an_unencodable_term_is_no_proof() {
        let opaque = TypedExpr::lit(Lit::String("s".into())).with_ty(Type::Base(BaseType::String));
        let lhs = [
            elem_cmp(CompareKind::Equals, lit(5)),
            elem_cmp(CompareKind::Equals, opaque),
        ];
        assert!(!smt_sub(
            &int(),
            &lhs,
            &[elem_cmp(CompareKind::GreaterOrEq, lit(1))]
        ));
    }

    /// Nothing demanded is nothing to prove.
    #[test]
    fn an_empty_demand_holds() {
        assert!(smt_sub(&int(), &[], &[]));
    }
}

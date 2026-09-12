//! Constant folding: a closed scalar computation becomes the literal it computes.
//!
//! Op conversion builds a collection literal's binding table out of its elements
//! (`compile_list_fn` in `src/interpreter/operator_conversion.rs`), so an element that is
//! still an application has no value to put there. A scaled constant is that element:
//! `500 * one_dollar` names two values the compiler holds and one it does not.
//!
//! # What folds
//!
//! Planning runs after lambda elimination, so every operator in the term is already
//! point-free and the fold recognizes three shapes:
//!
//! - `Var(𝑥)` where an enclosing `Let` binds 𝑥 to a literal.
//! - `(𝑎, 𝑏) ▷ binop` where 𝑎 and 𝑏 are literals.
//! - `𝑎 ▷ neg` and `𝑎 ▷ not_fn` where 𝑎 is a literal.
//!
//! The walk is bottom-up and each shape reads its operands one level deep, so a chain
//! (`a = 2; b = a * 3; c = b + 1`) folds in one pass without the fold evaluating
//! anything recursively.
//!
//! # What does not fold
//!
//! **Anything whose value the compiler does not have**: a source, a mutable variable's
//! history, a comprehension binder, an aggregate, a collection, a lambda, a `Case`. A
//! binder that is not a `Let` of a literal shadows an outer binding of the same name
//! rather than exposing it, so no substitution crosses into a scope that rebinds the
//! name.
//!
//! **A compound constant**, including a `Let` of a tuple, a record or a variant.
//! Substituting one copies nodes, and a copy needs minted [`NodeId`]s and a recording
//! (`src/ccl/design/provenance.md`, "Where to open a recording"). Replacing `expr.node`
//! with a `Lit` mints nothing and duplicates no id, which is why this pass opens no
//! recording.
//!
//! **A `//` whose two definitions disagree.** `docs/chl-spec.md`, "3.3 Arithmetic and
//! logical operators" calls it floor division, and the runtime truncates toward zero. The
//! two coincide for a non-negative dividend and a positive divisor, and the fold fires
//! only there, so it holds whichever way the disagreement is settled.
//!
//! **An operation with no result**: integer overflow, and division by zero. Every
//! arithmetic case goes through a guard or a `checked_*`, and declining leaves the
//! application in place for the runtime to evaluate as it would have.
//!
//! **Types.** A refinement predicate is a shared `Rc` whose structural identity is what
//! matches a producer's contract against its consumer's
//! (`src/ccl/design/type-inference.md`, "Sharing is an invariant, not an optimization
//! detail"), so folding one occurrence of a predicate and not another would break the
//! match. The folded node keeps its recorded type.
//!
//! **A definition the body's type discharges.** The post-planning wall compares recorded
//! and reconstructed types with their refinements, not by base, and a `Let` whose binder is
//! free in its body's type has that binder discharged into the recorded type
//! (`close_let_type` in `src/ccl/infer/check.rs`). The wall re-runs the discharge over
//! whatever `bound_expr` holds by then, so folding the definition puts `{Int | __elem == 4}`
//! against `{Int | __elem == 1 ^+ 3}` — one value, two spellings, compared structurally.
//! Such a definition is left alone and its binder exposes no literal. A definition no type
//! records still folds, which is every case this pass exists for.
//!
//! # Agreement with the runtime
//!
//! Every folded operation must compute what
//! [`apply_binop_column`](crate::interpreter::apply_binop_column) computes for the same
//! operands. There are two implementations because `ccl` may not depend upward on
//! `interpreter`, a rule stated at `builtin_to_binop` in
//! `src/interpreter/operator_conversion.rs`. The exclusions above are the operations where
//! agreement is not available.

use std::cmp::Ordering;

use super::*;
use crate::ccl::ArithmeticKind;
use crate::ccl::scope::{ScopedItemMut, for_each_scoped_item_mut};

/// Replace every closed scalar computation in `expr` with its value.
pub(super) fn fold_constants(expr: &mut Expr) {
    fold(expr, &mut Consts::default());
}

/// The literals in scope, innermost last.
///
/// Every binder pushes its name, with `None` when it binds no literal. An entry is what
/// shadows an outer binding, so a lambda parameter spelled like an enclosing constant
/// hides it rather than taking its value.
#[derive(Default)]
struct Consts(Vec<(Name, Option<Lit>)>);

impl Consts {
    fn get(&self, name: &Name) -> Option<&Lit> {
        self.0.iter().rev().find(|(n, _)| n == name)?.1.as_ref()
    }

    fn push(&mut self, name: Name, lit: Option<Lit>) {
        self.0.push((name, lit));
    }
}

fn fold(expr: &mut Expr, consts: &mut Consts) {
    let base = consts.0.len();
    if matches!(expr.node, TypedExprNode::Let { .. }) {
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = &mut expr.node
        else {
            unreachable!("matched a Let above")
        };
        // CCL's `let` is non-recursive: the binding scopes over `body` and not over
        // `bound_expr` (`scope::for_each_scoped_item` states every such rule). The bound
        // expression therefore folds in the enclosing environment.
        // **A definition the body's type discharges does not fold.** Where the binder is
        // free in the body's type, the recorded type of this `Let` was closed over the
        // definition as it stands (`close_let_type` in `src/ccl/infer/check.rs`), and the
        // post-planning wall re-runs that discharge over whatever `bound_expr` is by
        // then. Folding it would put two spellings of one value either side of a
        // structural comparison.
        let discharged = crate::ccl::subst::type_free_vars(&body.ty).contains(&binding.name);
        let lit = if discharged {
            None
        } else {
            fold(bound_expr, consts);
            match &bound_expr.node {
                TypedExprNode::Lit(lit) => Some(lit.clone()),
                _ => None,
            }
        };
        consts.push(binding.name.clone(), lit);
        fold(body, consts);
    } else {
        // A scope's children are consecutive and a scope is entered once, an invariant
        // `for_each_scoped_item_mut` documents, so each `Scope` item rebuilds the frame
        // from `base` rather than unwinding one binder at a time.
        for_each_scoped_item_mut(expr, &mut |item| match item {
            ScopedItemMut::Scope(names) => {
                consts.0.truncate(base);
                for name in names {
                    consts.push(name.clone(), None);
                }
            }
            ScopedItemMut::Child(child) => fold(child, consts),
            ScopedItemMut::VarRef(_) | ScopedItemMut::KeyRef(_) => {}
        });
    }
    consts.0.truncate(base);
    if let Some(lit) = value_of(expr, consts) {
        expr.node = TypedExprNode::Lit(lit);
    }
}

/// The value `expr` computes, when its children are already folded and it is one of the
/// three shapes this pass recognizes.
fn value_of(expr: &Expr, consts: &Consts) -> Option<Lit> {
    match &expr.node {
        TypedExprNode::Var(name) => consts.get(name).cloned(),
        TypedExprNode::Apply { function, argument } => {
            let TypedExprNode::Builtin(builtin) = &function.node else {
                return None;
            };
            match builtin {
                Builtin::BinOp(op) => {
                    let TypedExprNode::Tuple(operands) = &argument.node else {
                        return None;
                    };
                    let [left, right] = operands.as_slice() else {
                        return None;
                    };
                    let (TypedExprNode::Lit(left), TypedExprNode::Lit(right)) =
                        (&left.node, &right.node)
                    else {
                        return None;
                    };
                    eval_binop(*op, left, right)
                }
                Builtin::Neg => match &argument.node {
                    TypedExprNode::Lit(Lit::Int(n)) => n.checked_neg().map(Lit::Int),
                    _ => None,
                },
                Builtin::NotFn => match &argument.node {
                    TypedExprNode::Lit(Lit::Bool(b)) => Some(Lit::Bool(!b)),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn eval_binop(op: BinOpKind, left: &Lit, right: &Lit) -> Option<Lit> {
    match (op, left, right) {
        // `^+` computes the sum `+` computes; they differ in the type the result takes,
        // and the node keeps its recorded type through the fold.
        (BinOpKind::Arithmetic(op), Lit::Int(l), Lit::Int(r)) => Some(Lit::Int(match op {
            ArithmeticKind::Add | ArithmeticKind::AddRefined => l.checked_add(*r)?,
            ArithmeticKind::Sub => l.checked_sub(*r)?,
            ArithmeticKind::Mul => l.checked_mul(*r)?,
            // Only where floor division and truncation coincide — see the module
            // docs. The bound also excludes a zero divisor.
            ArithmeticKind::FloorDiv if *l >= 0 && *r > 0 => l / r,
            ArithmeticKind::FloorDiv => return None,
            // The runtime raises by squaring through the same `*` that `Mul` uses
            // (`IntPow::raised`), so folding an exponentiation that overflows would
            // answer where the runtime does not. A negative exponent is the reciprocal
            // `1 // (a ** n)`, undefined at `a == 0` exactly where division is, and is
            // left to the runtime for the reason `FloorDiv` is.
            ArithmeticKind::Pow => l.checked_pow(u32::try_from(*r).ok()?)?,
        })),
        (BinOpKind::Concat, Lit::String(l), Lit::String(r)) => Some(Lit::String(format!("{l}{r}"))),
        (BinOpKind::Compare(op), _, _) => eval_compare(op, left, right).map(Lit::Bool),
        (BinOpKind::BoolLogic(op), Lit::Bool(l), Lit::Bool(r)) => {
            Some(Lit::Bool(eval_logic(op, *l, *r)))
        }
        _ => None,
    }
}

/// Comparison over two literals of the same base.
///
/// `unit` is excluded: the runtime has no comparison for it and panics, so folding one
/// would answer a program the runtime refuses.
fn eval_compare(op: CompareKind, left: &Lit, right: &Lit) -> Option<bool> {
    let ordering = match (left, right) {
        (Lit::Int(l), Lit::Int(r)) => l.cmp(r),
        (Lit::String(l), Lit::String(r)) => l.cmp(r),
        // Boolean ordering is false < true, matching `zip_bool_compare`.
        (Lit::Bool(l), Lit::Bool(r)) => l.cmp(r),
        _ => return None,
    };
    Some(match op {
        CompareKind::Equals => ordering == Ordering::Equal,
        CompareKind::NotEquals => ordering != Ordering::Equal,
        CompareKind::Less => ordering == Ordering::Less,
        CompareKind::LessOrEq => ordering != Ordering::Greater,
        CompareKind::Greater => ordering == Ordering::Greater,
        CompareKind::GreaterOrEq => ordering != Ordering::Less,
    })
}

fn eval_logic(op: LogicKind, left: bool, right: bool) -> bool {
    match op {
        LogicKind::And => left && right,
        LogicKind::Nand => !(left && right),
        LogicKind::Or => left || right,
        LogicKind::Nor => !(left || right),
        LogicKind::Xor => left ^ right,
        LogicKind::Xnor => left == right,
    }
}

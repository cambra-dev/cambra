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
//! with a `Lit` mints nothing and duplicates no id, so the term walk opens no recording of
//! its own. The predicate rebuild below does — [`PredMemo`] opens one per predicate it
//! copies — which is why it is entered only for a type that has something to fold.
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
//! # Predicates fold too, and that is a patch over a deeper problem
//!
//! A refinement built by `^+` **embeds a copy of its operand's term**, so rewriting the
//! term and not the copy leaves two spellings of one fact. The post-planning wall compares
//! them structurally — a point-free predicate is outside the SMT encoding's fragment
//! (`refinements_that_survive_to_post_planning_check_are_rejected` pins that deficit) — so
//! the disagreement is reported as a type mismatch on a well-typed program.
//!
//! So this pass folds the predicates its type slots carry, through a pass-scoped
//! [`PredMemo`] that keeps every occurrence of one predicate pointing at one term
//! (`src/ccl/design/type-inference.md`, "Sharing is an invariant, not an optimization
//! detail"). A predicate folds with an **empty** environment: only the shapes that depend
//! on nothing outside the term itself, so one predicate has one answer wherever it is
//! shared, and no substitution crosses a scope the predicate is not in.
//!
//! **The head application does not fold.** Everything below it is a term the tree also
//! holds, and the wall rebuilds the head fresh from the node's own operator — so folding it
//! would answer a question the wall asks differently. That rule is about the wall rather
//! than about terms, which is the tell: the real fix is for a refinement to compose over its
//! operand's *type* instead of copying its term, and then nothing downstream has to know
//! which terms predicates hold. This pass keeps the two spellings in step until that lands.
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
use crate::ccl::ccl_utils::{PredMemo, walk_refined_predicates, walk_refined_predicates_mut};
use crate::ccl::scope::{ScopedItemMut, for_each_scoped_item_mut};

/// Replace every closed scalar computation in `expr` with its value.
pub(super) fn fold_constants(expr: &mut Expr) {
    let predicates = crate::ccl::ccl_utils::PredMemo::default();
    fold(expr, &mut Consts::default(), Some(&predicates));
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

/// Fold `expr`, reporting whether anything changed.
///
/// `predicates` is `Some` for the term walk and `None` inside a predicate: a predicate's
/// own type slots are not a second place for the tree's terms to live, and re-entering
/// would fold a predicate under the memo that is rebuilding it.
fn fold(expr: &mut Expr, consts: &mut Consts, predicates: Option<&PredMemo<()>>) -> bool {
    let base = consts.0.len();
    let mut changed = false;
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
        changed |= fold(bound_expr, consts, predicates);
        let lit = match &bound_expr.node {
            TypedExprNode::Lit(lit) => Some(lit.clone()),
            _ => None,
        };
        consts.push(binding.name.clone(), lit);
        changed |= fold(body, consts, predicates);
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
            ScopedItemMut::Child(child) => changed |= fold(child, consts, predicates),
            ScopedItemMut::VarRef(_) | ScopedItemMut::KeyRef(_) => {}
        });
    }
    consts.0.truncate(base);
    if let Some(memo) = predicates {
        changed |= fold_predicates(expr, memo);
    }
    if let Some(lit) = value_of(expr, consts) {
        expr.node = TypedExprNode::Lit(lit);
        changed = true;
    }
    changed
}

/// Fold the terms the predicates on `expr`'s type slots embed.
///
/// The **operands** of each predicate's head application, never the head: see the module
/// docs, "Predicates fold too, and that is a patch over a deeper problem".
fn fold_predicates(expr: &mut Expr, memo: &PredMemo<()>) -> bool {
    let mut changed = false;
    expr.walk_type_slots_mut(|ty| {
        // **Scanned before the rebuild walk is entered, not inside it.**
        // [`PredMemo::rebuild`] clones a predicate before its callback can report that
        // there was nothing to do, and a clone advances the process-global
        // [`NodeId`](crate::ccl::provenance::NodeId) mint — which renumbers every later id
        // in the program and rewrites the whole golden corpus (`web/CLAUDE.md`, "The
        // golden fixtures"). A type carrying no foldable predicate is left untouched, so a
        // program with no constant inside a refinement keeps its ids exactly.
        if !has_foldable_predicate(ty) {
            return;
        }
        changed |= walk_refined_predicates_mut(ty, memo, &(), &mut |pred, _| fold_operands(pred));
    });
    changed
}

/// Whether any predicate in `ty` has an operand the fold would rewrite.
fn has_foldable_predicate(ty: &Type) -> bool {
    let mut found = false;
    let mut visited = std::collections::HashSet::new();
    walk_refined_predicates(ty, &mut visited, &mut |pred, _| {
        found |= folds_anything(pred);
    });
    found
}

/// Whether folding `pred`'s operands would change anything — a read-only scan.
fn folds_anything(pred: &Expr) -> bool {
    fn go(e: &Expr) -> bool {
        // An empty environment, matching the fold itself: only the shapes that depend on
        // nothing outside the term. One foldable subterm is enough to enter — the fold is
        // bottom-up from there and may reach more.
        if value_of(e, &Consts::default()).is_some() {
            return true;
        }
        let mut any = false;
        e.walk_children(|c| any |= go(c));
        any
    }
    let mut any = false;
    pred.walk_children(|c| any |= go(c));
    any
}

/// Fold every proper subterm of `pred`, leaving `pred`'s own root alone.
fn fold_operands(pred: &mut Expr) -> bool {
    let mut changed = false;
    for_each_scoped_item_mut(pred, &mut |item| {
        if let ScopedItemMut::Child(child) = item {
            // An empty environment: a predicate folds only by the shapes that depend on
            // nothing outside it, so one predicate has one answer wherever it is shared.
            changed |= fold(child, &mut Consts::default(), None);
        }
    });
    changed
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
        // A refining operator computes what its plain counterpart computes; the two differ
        // in the type the result takes, and the node keeps its recorded type through the
        // fold.
        (BinOpKind::Arithmetic(op), Lit::Int(l), Lit::Int(r)) => Some(Lit::Int(match op {
            ArithmeticKind::Add | ArithmeticKind::AddRefined => l.checked_add(*r)?,
            ArithmeticKind::Sub | ArithmeticKind::SubRefined => l.checked_sub(*r)?,
            ArithmeticKind::Mul | ArithmeticKind::MulRefined => l.checked_mul(*r)?,
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

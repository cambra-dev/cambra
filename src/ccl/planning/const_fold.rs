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
//! **Anything inside a definition the body's type discharges.** The post-planning wall
//! compares recorded and reconstructed types with their refinements rather than by base, and
//! a `Let` whose binder is free in its body's type has that binder discharged into the
//! recorded type (`close_let_type` in `src/ccl/infer/check.rs`). The wall re-runs the
//! discharge over whatever `bound_expr` holds by then, so folding the definition puts
//! `{Int | __elem == 4}` against `{Int | __elem == 1 ^+ 3}` — one value, two spellings,
//! compared structurally (`a_discharged_definition_survives_planning`). A definition no type
//! records still folds, which is every case this pass exists for.
//!
//! The whole subtree is skipped and not just the definition's own node, so a collection
//! literal under such a definition keeps its unevaluated elements — and a downstream `^+`,
//! which is what makes a binder discharged, can therefore stop a literal compiling that
//! compiled under `+` (`a_downstream_refined_sum_stops_an_element_folding`).
//!
//! **A string longer than [`MAX_FOLDED_STRING`].** Concatenation is the one fold whose
//! result can be much larger than its operands, and a doubling chain is exponential in the
//! source's length; above the cap the runtime builds the value once instead.
//!
//! **A compound constant**, including a `Let` of a tuple, a record or a variant.
//! Substituting one copies nodes, and a copy needs minted [`NodeId`]s and a recording
//! (`src/ccl/design/provenance.md`, "Where to open a recording"). Replacing `expr.node`
//! with a `Lit` mints nothing and duplicates no id, which is why this pass opens no
//! recording.
//!
//! **A `//` whose two definitions disagree.** `docs/chl-spec.md`, "3.3 Arithmetic and
//! logical operators" calls it floor division, and the runtime truncates toward zero, so
//! `(0 - 7) // 2` answers -3 where the spec says -4. The two coincide for a non-negative
//! dividend and a positive divisor, and the fold fires only there, so it holds whichever way
//! the disagreement is settled. The disagreement itself is the vault issue
//! `interpreter-integer-arithmetic-divergences`; settling it in the runtime's favour would
//! retire this exclusion.
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
//! # Agreement with the runtime
//!
//! By construction: `eval_binop` calls the kernel in [`crate::scalar_ops`] on a one-element
//! column, and that is the kernel the `BinOp` operator runs. There is one implementation,
//! so there is nothing for a compile-time answer and a run-time one to disagree about, and
//! the exclusions above are the whole of what this pass decides.

use super::*;
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

/// The longest string concatenation this pass will build.
///
/// Folding trades compile-time memory for run-time work, and concatenation is where that
/// trade turns over: the result is as large as both operands together, it is stored in
/// `Consts`, and it is cloned at every occurrence the substitution reaches.
const MAX_FOLDED_STRING: usize = 64 * 1024;

/// Fold one closed application, or decline.
///
/// **The runtime computes the value; this decides whether to ask.** The kernel
/// [`crate::scalar_ops`] holds is the same one the `BinOp` operator will run, called here
/// on a one-element column, so agreement is by construction rather than by two
/// implementations being kept in step. What belongs to the fold is the exclusion list, and
/// that is what [`runtime_answers`] is.
fn eval_binop(op: BinOpKind, left: &Lit, right: &Lit) -> Option<Lit> {
    let rt = crate::scalar_ops::BinOpKind::from(op);
    if !runtime_answers(rt, left, right) {
        return None;
    }
    apply_one(rt, left, right)
}

/// Whether the runtime answers this application at all.
///
/// Each arm is one of the module doc's exclusions. Declining leaves the application in
/// place, and the operator evaluates it as it would have.
fn runtime_answers(op: crate::scalar_ops::BinOpKind, left: &Lit, right: &Lit) -> bool {
    use crate::scalar_ops::{ArithmeticKind as A, BinOpKind as B};
    match (op, left, right) {
        (B::Arithmetic(a), Lit::Int(l), Lit::Int(r)) => match a {
            A::Add => l.checked_add(*r).is_some(),
            A::Sub => l.checked_sub(*r).is_some(),
            A::Mul => l.checked_mul(*r).is_some(),
            // Only where floor division and truncation coincide — see the module docs. The
            // bound also excludes a zero divisor.
            A::FloorDiv => *l >= 0 && *r > 0,
            // Exponentiation has no no-result case: the runtime raises by squaring through
            // `wrapping_mul`, so a result past `i64` is a wrapped value and the fold
            // answers the same one. A negative exponent cannot arrive — `**` states
            // `{Int | __elem >= 0}` of it (`src/ccl/lower/exprs.rs`) — and is excluded here
            // because the kernel asserts on one rather than declining.
            A::Pow => *r >= 0,
        },
        // Bounded, because a chain of doublings is linear in the source and exponential in
        // the result: thirty `s = s + s` lines reach a gigabyte, and the value is then
        // copied into `Consts` and again at every occurrence it is read at. Above the cap
        // the runtime builds it once, lazily, as it did before this pass.
        (B::Concat, Lit::String(l), Lit::String(r)) => l.len() + r.len() <= MAX_FOLDED_STRING,
        // `unit` is excluded: the runtime has no comparison for it and panics, so folding
        // one would answer a program the runtime refuses.
        (B::Compare(_), Lit::Int(_), Lit::Int(_))
        | (B::Compare(_), Lit::String(_), Lit::String(_))
        | (B::Compare(_), Lit::Bool(_), Lit::Bool(_))
        | (B::BoolLogic(_), Lit::Bool(_), Lit::Bool(_)) => true,
        _ => false,
    }
}

/// The kernel's answer for one pair, as a literal.
///
/// A one-element column in and the single position out. `None` is a pairing the kernel has
/// no arm for, which [`runtime_answers`] has already excluded — kept as a `None` rather
/// than an `unreachable!` because the two enumerations are separate matches.
fn apply_one(op: crate::scalar_ops::BinOpKind, left: &Lit, right: &Lit) -> Option<Lit> {
    use crate::scalar_ops as rt;
    match (op, left, right) {
        (rt::BinOpKind::Arithmetic(a), Lit::Int(l), Lit::Int(r)) => {
            Some(Lit::Int(rt::zip_arithmetic(a, vec![*l], &[*r]).pop()?))
        }
        (rt::BinOpKind::Concat, Lit::String(l), Lit::String(r)) => Some(Lit::String(
            rt::zip_concat(vec![l.as_str().into()], &[r.as_str().into()])
                .pop()?
                .to_string(),
        )),
        (rt::BinOpKind::Compare(c), Lit::Int(l), Lit::Int(r)) => {
            Some(Lit::Bool(rt::zip_compare(c, vec![*l], &[*r]).get(0)?))
        }
        (rt::BinOpKind::Compare(c), Lit::String(l), Lit::String(r)) => Some(Lit::Bool(
            rt::zip_compare(c, vec![l.as_str()], &[r.as_str()]).get(0)?,
        )),
        (rt::BinOpKind::Compare(c), Lit::Bool(l), Lit::Bool(r)) => Some(Lit::Bool(
            rt::zip_bool_compare(c, bits(*l), &bits(*r)).get(0)?,
        )),
        (rt::BinOpKind::BoolLogic(g), Lit::Bool(l), Lit::Bool(r)) => Some(Lit::Bool(
            rt::zip_bool_logic(g, bits(*l), &bits(*r)).get(0)?,
        )),
        _ => None,
    }
}

/// A one-position `BitVec`, the column shape the boolean kernels take.
fn bits(b: bool) -> bit_vec::BitVec {
    bit_vec::BitVec::from_elem(1, b)
}

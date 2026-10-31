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
//! A gate that folded to a literal then decides the filter it gates, and the fold applies these
//! rewrites to the terms lambda elimination builds for a value-`Case`:
//!
//! - `filter_values(true ▷ const)` becomes `id`: every position passes.
//! - A [`TypedExprNode::DisjointJoin`] loses each arm headed by `filter_values(false ▷ const)`,
//!   which holds no position, and one arm left is the join. A writer decision that commits
//!   unconditionally is ``Case[true → `commit(…); true → `abort]``, so it plans to its commit
//!   arm alone.
//! - A boolean gate `(𝑙 ▷ const, 𝑝) ▷ zip ≫ and` is 𝑝 where 𝑙 is `true` and `𝑙 ▷ const` where 𝑙 is
//!   `false`. `≫ or` is 𝑝 where 𝑙 is `false` and `𝑙 ▷ const` where 𝑙 is `true`, and either operand
//!   may be the literal. The gate may sit anywhere in a composition, and a composition folds every
//!   gate it holds. The first-match gate of a later `Case` arm is `true and ¬𝑞` when the first
//!   guard is the literal `true`.
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
//! **Anything inside a definition the body's type reads.** The post-planning wall relates a
//! node's refinements to its neighbours' assuming each binder equal to its definition
//! (`src/ccl/design/type-inference.md`, "The scope a query runs in"). A type reading `y`
//! whose definition is `x + 1` meets a type reading `x + 1` through that assumption, and
//! folding the definitions to literals leaves predicates the structural comparison does not
//! relate (`a_binder_is_assumed_equal_to_its_definition`). A definition no type reads still
//! folds, which is every case this pass exists for.
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
//! **An operation with no result**: integer overflow, and division by zero. Every
//! arithmetic case goes through a guard or a `checked_*`, and declining leaves the
//! application in place for the runtime to evaluate as it would have.
//!
//! **Types.** A refinement predicate is a shared `Rc` whose structural identity is what
//! matches a producer's contract against its consumer's
//! (`src/ccl/design/type-inference.md`, "Sharing is an invariant, not an optimization
//! detail"), so folding one occurrence of a predicate and not another would break the
//! match. The folded node keeps its recorded type, except that a gate replaced by its literal
//! operand takes the type of the gate it replaces.
//!
//! # Agreement with the runtime
//!
//! By construction: `eval_binop` calls the kernel in [`crate::scalar_ops`] on a one-element
//! column, and that is the kernel the `BinOp` operator runs. There is one implementation,
//! so there is nothing for a compile-time answer and a run-time one to disagree about, and
//! the exclusions above are the whole of what this pass decides, with one exception: a gate
//! that drops its operand (`false and 𝑝`) also drops whatever failure evaluating 𝑝 would have
//! raised, and a join that drops an empty arm does the same. The operators are columnar and do
//! not short-circuit, so the unfolded term would have evaluated 𝑝 on every position.

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
        // **A definition the body's type reads does not fold.** The post-planning wall
        // relates the types reading the binder through the definition as it stands, and a
        // folded definition no longer relates them (see the module docs).
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
    while let Some(reduction) = reduce(expr, consts) {
        reduction.apply(expr);
    }
}

/// Where a boolean gate sits in a composition and which of its two operands replaces it.
struct GateOperand {
    /// Index of the `(𝑎, 𝑏) ▷ zip` element; the `and`/`or` element follows it.
    at: usize,
    /// Index into the zipped pair of the operand that replaces the gate.
    operand: usize,
    /// The type of the gate's `zip ≫ and`: its own function kind, its domain, and the codomain of
    /// the `and`. A gate that is the whole composition has the composition's recorded type.
    ty: Type,
}

/// What a node reduces to, decided from the node and its already folded children.
///
/// Each variant is applied in place by [`Reduction::apply`]: a literal replaces the node, `id`
/// takes the node's own recorded type, and a promoted arm keeps its id, so nothing is minted.
enum Reduction {
    /// The node computes this value.
    Lit(Lit),
    /// A filter every position passes: `filter_values(true ▷ const)`, typed `𝐴 ⇒ 𝐴`.
    Id,
    /// A [`TypedExprNode::DisjointJoin`] loses its empty arms, and at least one arm is not empty.
    Arms,
    /// A boolean gate `(𝑎, 𝑏) ▷ zip ≫ and` (or `or`) is its operand with this index.
    Operand(GateOperand),
}

impl Reduction {
    fn apply(self, expr: &mut Expr) {
        match self {
            Reduction::Lit(lit) => expr.node = TypedExprNode::Lit(lit),
            Reduction::Id => expr.node = TypedExprNode::Builtin(Builtin::Id),
            Reduction::Arms => {
                let TypedExprNode::DisjointJoin(arms) = &mut expr.node else {
                    unreachable!("an arm reduction names the arms of a disjoint join")
                };
                arms.retain(|arm| !is_empty_arm(arm));
                // One arm left is the join, when it has the join's own type, as the arms of a
                // value-`Case` do.
                if arms.len() == 1 && arms[0].ty == expr.ty {
                    *expr = arms.pop().expect("one arm remains");
                }
            }
            Reduction::Operand(GateOperand {
                at,
                operand: index,
                ty,
            }) => {
                let TypedExprNode::Compose(elts) = &mut expr.node else {
                    unreachable!("an operand reduction names a gate composition")
                };
                let TypedExprNode::Apply { argument, .. } = &mut elts[at].node else {
                    unreachable!("a gate composition holds `(𝑎, 𝑏) ▷ zip` at `at`")
                };
                let TypedExprNode::Tuple(operands) = &mut argument.node else {
                    unreachable!("a gate zips a pair")
                };
                let mut operand = operands.swap_remove(index);
                operand.ty = ty;
                if elts.len() == 2 {
                    *expr = operand;
                } else {
                    let head = match operand.node {
                        TypedExprNode::Compose(inner) => inner,
                        _ => vec![operand],
                    };
                    elts.splice(at..at + 2, head);
                }
            }
        }
    }
}

/// The literal under a constant function: `𝑙` of `𝑙 ▷ const`.
///
/// The term is a function and not the literal, typed `𝐴 ⇒ 𝐵` where the literal is a `𝐵`, so
/// it is recognized here and never replaced by it.
fn const_literal(expr: &Expr) -> Option<&Lit> {
    let TypedExprNode::Apply { argument, function } = &expr.node else {
        return None;
    };
    match (&function.node, &argument.node) {
        (TypedExprNode::Builtin(Builtin::Const), TypedExprNode::Lit(lit)) => Some(lit),
        _ => None,
    }
}

/// The predicate of `𝑝 ▷ filter_values`, when `expr` is one.
fn filter_values_predicate(expr: &Expr) -> Option<&Expr> {
    match &expr.node {
        TypedExprNode::Apply { argument, function }
            if matches!(function.node, TypedExprNode::Builtin(Builtin::FilterValues)) =>
        {
            Some(argument)
        }
        _ => None,
    }
}

/// Whether `arm` of a join is empty: a filter by the constant `false`, alone or heading a
/// composition.
fn is_empty_arm(arm: &Expr) -> bool {
    let head = match &arm.node {
        TypedExprNode::Compose(elts) => elts.first(),
        _ => Some(arm),
    };
    head.and_then(filter_values_predicate)
        .and_then(const_literal)
        .is_some_and(|lit| matches!(lit, Lit::Bool(false)))
}

/// The operand a boolean gate `(𝑎, 𝑏) ▷ zip ≫ and` or `≫ or` reduces to, when one operand is a
/// constant function of a literal.
///
/// `true and 𝑝` and `false or 𝑝` are 𝑝; `false and 𝑝` and `true or 𝑝` are the literal operand
/// and drop 𝑝. The operand replaces the gate only where it has the gate's own type, so a
/// refinement on either side is not lost; a literal operand is re-stamped with it. The gate is the
/// pair `zip ≫ and` at any position of a composition, and the elements around it stay. The first
/// such pair is reported and [`fold`] asks again until none is left.
fn gate_operand(expr: &Expr) -> Option<GateOperand> {
    let TypedExprNode::Compose(elts) = &expr.node else {
        return None;
    };
    let whole = (elts.len() == 2).then_some(&expr.ty);
    (0..elts.len().saturating_sub(1))
        .find_map(|at| gate_operand_at(&elts[at], &elts[at + 1], at, whole))
}

/// [`gate_operand`] for the adjacent pair `zipped ≫ logic` at position `at`.
fn gate_operand_at(
    zipped: &Expr,
    logic: &Expr,
    at: usize,
    whole: Option<&Type>,
) -> Option<GateOperand> {
    use crate::ccl::ops::{BinOpKind, LogicKind};
    let TypedExprNode::Builtin(Builtin::BinOp(BinOpKind::BoolLogic(kind))) = &logic.node else {
        return None;
    };
    let TypedExprNode::Apply { argument, function } = &zipped.node else {
        return None;
    };
    if !matches!(function.node, TypedExprNode::Builtin(Builtin::Zip)) {
        return None;
    }
    let TypedExprNode::Tuple(operands) = &argument.node else {
        return None;
    };
    if operands.len() != 2 {
        return None;
    }
    let absorbing = match kind {
        LogicKind::And => false,
        LogicKind::Or => true,
        _ => return None,
    };
    for (literal, other) in [(0, 1), (1, 0)] {
        let Some(Lit::Bool(b)) = const_literal(&operands[literal]) else {
            continue;
        };
        let keep = if *b == absorbing { literal } else { other };
        let Type::Fun {
            fun_kind, domain, ..
        } = &zipped.ty
        else {
            return None;
        };
        let ty = match whole {
            Some(whole) => whole.clone(),
            None => Type::Fun {
                name: None,
                fun_kind: fun_kind.clone(),
                domain: domain.clone(),
                codomain: Box::new(logic.ty.codomain()?),
            },
        };
        // A kept literal is typed by its own refinement (`Bool@false`) and is re-stamped with
        // the gate's type; a kept predicate must already have it.
        return (keep == literal || operands[keep].ty == ty).then_some(GateOperand {
            at,
            operand: keep,
            ty,
        });
    }
    None
}

/// What `expr` reduces to, when its children are already folded and it is one of the shapes
/// this pass recognizes: those that compute a value, and those a folded gate decides.
fn reduce(expr: &Expr, consts: &Consts) -> Option<Reduction> {
    let lit = match &expr.node {
        TypedExprNode::Var(name) => consts.get(name).cloned(),
        TypedExprNode::DisjointJoin(arms) => {
            // A join whose arms are all empty is left as it is, so it never has no operand.
            let empty = arms.iter().filter(|arm| is_empty_arm(arm)).count();
            return (0 < empty && empty < arms.len()).then_some(Reduction::Arms);
        }
        TypedExprNode::Compose(_) => return gate_operand(expr).map(Reduction::Operand),
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
                // Every position passes, so the filter is the identity. Only where it is typed
                // `𝐴 ⇒ 𝐴`, as the value-`Case` arm types it: a filter that narrows its domain
                // by a refinement keeps it.
                Builtin::FilterValues => {
                    let passes =
                        const_literal(argument).is_some_and(|lit| matches!(lit, Lit::Bool(true)));
                    let (domain, codomain) = (expr.ty.domain(), expr.ty.codomain());
                    return (passes && domain.is_some() && domain == codomain)
                        .then_some(Reduction::Id);
                }
                _ => None,
            }
        }
        _ => None,
    };
    lit.map(Reduction::Lit)
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
pub(crate) fn eval_binop(op: BinOpKind, left: &Lit, right: &Lit) -> Option<Lit> {
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
            A::FloorDiv => l.checked_div(*r).is_some(),
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
    use crate::view::View;
    /// One position per operand: a value repeated once.
    fn one<T>(value: &T) -> View<'_, T> {
        View::repeated(value, 1)
    }
    match (op, left, right) {
        (rt::BinOpKind::Arithmetic(a), Lit::Int(l), Lit::Int(r)) => {
            let mut out = Vec::new();
            rt::zip_arithmetic(a, one(l), one(r), &mut out);
            Some(Lit::Int(out.pop()?))
        }
        (rt::BinOpKind::Concat, Lit::String(l), Lit::String(r)) => {
            let mut out = Vec::new();
            rt::zip_concat(one(l), one(r), &mut out);
            Some(Lit::String(out.pop()?))
        }
        (rt::BinOpKind::Compare(c), Lit::Int(l), Lit::Int(r)) => {
            let mut out = Vec::new();
            rt::zip_compare(c, one(l), one(r), &mut out);
            Some(Lit::Bool(out.pop()?))
        }
        (rt::BinOpKind::Compare(c), Lit::String(l), Lit::String(r)) => {
            let mut out = Vec::new();
            rt::zip_compare(c, one(&l.as_str()), one(&r.as_str()), &mut out);
            Some(Lit::Bool(out.pop()?))
        }
        (rt::BinOpKind::Compare(c), Lit::Bool(l), Lit::Bool(r)) => {
            let mut out = Vec::new();
            rt::zip_bool_compare(c, one(l), one(r), &mut out);
            Some(Lit::Bool(out.pop()?))
        }
        (rt::BinOpKind::BoolLogic(g), Lit::Bool(l), Lit::Bool(r)) => {
            let mut out = Vec::new();
            rt::zip_bool_logic(g, one(l), one(r), &mut out);
            Some(Lit::Bool(out.pop()?))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ops::{BinOpKind, LogicKind};

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    fn boolean() -> Type {
        Type::Base(BaseType::Bool)
    }

    fn var(name: &str, ty: Type) -> Expr {
        Expr::new(TypedExprNode::Var(Name::from(name))).with_ty(ty)
    }

    fn builtin(builtin: Builtin, ty: Type) -> Expr {
        Expr::new(TypedExprNode::Builtin(builtin)).with_ty(ty)
    }

    /// `𝑏 ▷ const`, typed `Int ⇒ Bool@𝑏` as lowering types a constant guard.
    fn const_bool(b: bool) -> Expr {
        let literal = Expr::new(TypedExprNode::Lit(Lit::Bool(b))).with_ty(boolean());
        let ty = Type::fun(int(), boolean());
        Expr::apply(literal, builtin(Builtin::Const, ty.clone())).with_ty(ty)
    }

    /// The elements `(𝑎, 𝑏) ▷ zip` and `and`/`or` of a gate, typed with `fun`: `Type::fun` or
    /// `Type::data_fun`.
    fn gate(a: Expr, b: Expr, kind: LogicKind, fun: fn(Type, Type) -> Type) -> (Expr, Expr) {
        let pair = Type::tuple(vec![boolean(), boolean()]);
        let tuple = Expr::new(TypedExprNode::Tuple(vec![a, b])).with_ty(pair.clone());
        let zip_ty = fun(int(), pair.clone());
        let zipped = Expr::apply(tuple, builtin(Builtin::Zip, zip_ty.clone())).with_ty(zip_ty);
        let logic = builtin(
            Builtin::BinOp(BinOpKind::BoolLogic(kind)),
            fun(pair, boolean()),
        );
        (zipped, logic)
    }

    fn compose(elts: Vec<Expr>) -> Expr {
        let ty = Type::fun(int(), boolean());
        Expr::new(TypedExprNode::Compose(elts)).with_ty(ty)
    }

    fn elements(expr: &Expr) -> &[Expr] {
        match &expr.node {
            TypedExprNode::Compose(elts) => elts,
            _ => panic!("expected a composition"),
        }
    }

    fn predicate() -> Expr {
        var("p", Type::fun(int(), boolean()))
    }

    fn is_const_bool(expr: &Expr, b: bool) -> bool {
        const_literal(expr).is_some_and(|lit| *lit == Lit::Bool(b))
    }

    /// `true and 𝑝` is 𝑝 wherever the gate sits in its composition, and the elements around
    /// it stay.
    #[test]
    fn a_gate_in_the_middle_of_a_composition_folds_to_its_operand() {
        let before = var("f", Type::fun(int(), int()));
        let after = builtin(Builtin::NotFn, Type::fun(boolean(), boolean()));
        let (zipped, logic) = gate(const_bool(true), predicate(), LogicKind::And, Type::fun);
        let mut expr = compose(vec![before, zipped, logic, after]);
        fold_constants(&mut expr);
        let elts = elements(&expr);
        assert_eq!(elts.len(), 3, "the gate's two elements become its operand");
        assert!(matches!(&elts[1].node, TypedExprNode::Var(n) if *n == Name::from("p")));
        assert!(matches!(
            &elts[2].node,
            TypedExprNode::Builtin(Builtin::NotFn)
        ));
    }

    /// `false or 𝑝` keeps 𝑝 and, with the literal on the right, `𝑝 and true` does too.
    #[test]
    fn a_neutral_literal_on_either_side_leaves_the_other_operand() {
        for (a, b, logic, neutral) in [
            (const_bool(false), predicate(), LogicKind::Or, false),
            (predicate(), const_bool(true), LogicKind::And, true),
        ] {
            let (zipped, logic) = gate(a, b, logic, Type::fun);
            let mut expr = compose(vec![zipped, logic]);
            fold_constants(&mut expr);
            assert!(
                matches!(&expr.node, TypedExprNode::Var(n) if *n == Name::from("p")),
                "a gate with the neutral literal {neutral} is its other operand"
            );
        }
    }

    /// `false and 𝑝` and `true or 𝑝` are the literal's `const`, stamped with the gate's own type.
    #[test]
    fn an_absorbing_literal_replaces_the_gate_by_its_constant() {
        for (literal, logic) in [(false, LogicKind::And), (true, LogicKind::Or)] {
            let (zipped, logic) = gate(const_bool(literal), predicate(), logic, Type::fun);
            let mut expr = compose(vec![zipped, logic]);
            fold_constants(&mut expr);
            assert!(is_const_bool(&expr, literal));
            assert_eq!(expr.ty, Type::fun(int(), boolean()));
        }
    }

    /// A data-function gate keeps its `⤇`: the kept operand is stamped with the gate's kind.
    #[test]
    fn a_data_function_gate_keeps_its_function_kind() {
        let (zipped, logic) = gate(
            const_bool(false),
            predicate(),
            LogicKind::And,
            Type::data_fun,
        );
        let mut expr = compose(vec![zipped, logic]).with_ty(Type::data_fun(int(), boolean()));
        fold_constants(&mut expr);
        assert!(is_const_bool(&expr, false));
        assert_eq!(expr.ty, Type::data_fun(int(), boolean()));
    }

    /// A predicate that is a composition is spliced into the elements around the gate, and a
    /// composition holding two gates folds both.
    #[test]
    fn a_composite_operand_is_spliced_and_every_gate_folds() {
        let g = || var("g", Type::fun(int(), boolean()));
        let h = || var("h", Type::fun(int(), boolean()));
        let inner = compose(vec![g(), h()]);
        let (z1, l1) = gate(const_bool(true), inner, LogicKind::And, Type::fun);
        let (z2, l2) = gate(predicate(), const_bool(false), LogicKind::Or, Type::fun);
        let mut expr = compose(vec![
            var("f", Type::fun(int(), int())),
            z1,
            l1,
            z2,
            l2,
            builtin(Builtin::NotFn, Type::fun(boolean(), boolean())),
        ]);
        fold_constants(&mut expr);
        let names: Vec<_> = elements(&expr)
            .iter()
            .map(|e| match &e.node {
                TypedExprNode::Var(n) => n.clone(),
                TypedExprNode::Builtin(Builtin::NotFn) => Name::from("not_fn"),
                other => panic!("unexpected element {other:?}"),
            })
            .collect();
        let expected: Vec<_> = ["f", "g", "h", "p", "not_fn"].map(Name::from).into();
        assert_eq!(names, expected);
    }

    /// A gate that is a whole composition keeps that composition's recorded type, and a
    /// predicate typed otherwise does not replace it.
    #[test]
    fn a_whole_gate_composition_keeps_its_recorded_type() {
        let refined = Type::fun(Type::UIntRange(3), boolean());
        let (zipped, logic) = gate(const_bool(false), predicate(), LogicKind::And, Type::fun);
        let mut expr = compose(vec![zipped, logic]).with_ty(refined.clone());
        fold_constants(&mut expr);
        assert!(is_const_bool(&expr, false));
        assert_eq!(expr.ty, refined);

        let (zipped, logic) = gate(const_bool(true), predicate(), LogicKind::And, Type::fun);
        let mut expr = compose(vec![zipped, logic]).with_ty(refined);
        fold_constants(&mut expr);
        assert_eq!(elements(&expr).len(), 2, "the predicate is typed otherwise");
    }

    /// A predicate of another type than the gate is not substituted for it.
    #[test]
    fn a_predicate_of_another_type_than_the_gate_stays() {
        let narrower = var("p", Type::fun(Type::UIntRange(2), boolean()));
        let (zipped, logic) = gate(const_bool(true), narrower, LogicKind::And, Type::fun);
        let mut expr = compose(vec![zipped, logic]);
        fold_constants(&mut expr);
        assert_eq!(elements(&expr).len(), 2);
    }

    /// `nand`, `nor` and `xor` are not folded: only `and` and `or` have an absorbing element.
    #[test]
    fn other_logic_kinds_are_not_folded() {
        for kind in [LogicKind::Nand, LogicKind::Nor, LogicKind::Xor] {
            let (zipped, logic) = gate(const_bool(true), predicate(), kind, Type::fun);
            let mut expr = compose(vec![zipped, logic]);
            fold_constants(&mut expr);
            assert_eq!(elements(&expr).len(), 2);
        }
    }
}

//! Exception elimination: every `raise` and `try` becomes the sums and matches the rest of
//! the pipeline compiles (`src/ccl/design/ir.md`, "Exceptions").
//!
//! It runs once, right after inlining. Inlining leaves no function to raise through, so each
//! `raise` stands in the tree it escapes through, and inference has refused one that escapes
//! the program, so a `try` catches each.
//!
//! An expression that may raise becomes its **outcome**: a value of the sum
//! ``{`__ok{𝑇} | `__raise𝑖{𝐸𝑖} …}``, `𝑇` its own type and one arm per exception type that can
//! reach the `try` around it, each type one tag throughout the program. What reads its value
//! matches on it: the `ok` arm continues, and every other arm passes the exception on. So a
//! statement after one that raised, and an operand written after one, run only where it did
//! not raise. A `try` matches its body's outcome, running the clause that catches each
//! exception, and passes the rest on to the `try` around it.

use std::collections::HashSet;

use crate::ccl::ccl_utils::{
    PredMemo, projected_element, projected_element_ref, walk_refined_predicates_mut,
};
use crate::ccl::expr::Handler;
use crate::ccl::mut_elim::{binding, tvar};
use crate::ccl::ty::Openness;
use crate::ccl::{
    BaseType, BinOpKind, BindingTransparency, Branch, Builtin, Expr, FieldKey, Label, Lit,
    LogicKind, Name, Pattern, PatternHead, Type, TypedBinding, TypedExprNode, provenance,
};

/// Replace every `raise` and `try` in `expr`.
pub fn eliminate(expr: Expr) -> Expr {
    if !holds_raise(&expr) {
        return expr;
    }
    let mut cx = Cx::default();
    let mut expr = match cx.elim(expr, &[]) {
        Elim::Pure(e) => e,
        Elim::Raising(_) => {
            unreachable!("inference refuses an exception escaping the program")
        }
    };
    for lifted in std::mem::take(&mut cx.lifted) {
        expr = cx.place_filter(expr, lifted);
    }
    // A comprehension's filter rides the types of whatever its value reaches, and each copy
    // a filter's placement left takes the pure form.
    cx.purify_tree(&mut expr);
    expr
}

/// `ty` with each refinement predicate structurally equal to `from` replaced by `to`, one
/// rewrite per predicate term however many slots share it ([`PredMemo`]).
fn replace_filter(ty: &mut Type, memo: &PredMemo<()>, from: &Expr, to: &Expr) {
    walk_refined_predicates_mut(ty, memo, &(), &mut |predicate, _| {
        if !crate::ccl::ty::eq_term_modulo_ty_slots(predicate, from) {
            return false;
        }
        *predicate = to.clone();
        true
    });
}

/// [`replace_filter`] at every type slot in `e`.
fn replace_filter_in(e: &mut Expr, memo: &PredMemo<()>, from: &Expr, to: &Expr) {
    e.walk_type_slots_mut(|t| replace_filter(t, memo, from, to));
    e.walk_children_mut(|c| replace_filter_in(c, memo, from, to));
}

/// A `let` [`take_let`] removed: its node, binding and definition.
struct Taken {
    id: provenance::NodeId,
    binding: TypedBinding,
    value: Expr,
}

/// Remove the `let` binding `name` from `e`, leaving its body where it stood.
fn take_let(e: &mut Expr, name: &Name) -> Option<Taken> {
    if let TypedExprNode::Let { binding, .. } = &e.node
        && &binding.name == name
    {
        let id = e.node_id();
        let TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } = std::mem::take(e).node
        else {
            unreachable!("matched a `Let` above")
        };
        *e = *body;
        return Some(Taken {
            id,
            binding,
            value: *bound_expr,
        });
    }
    let mut found = None;
    e.walk_children_mut(|c| {
        if found.is_none() {
            found = take_let(c, name);
        }
    });
    found
}

/// Put `taken` back around the outermost position in `e` that holds every occurrence of its
/// name and lies inside the scope of each name in `pending`, the definition's free names not
/// yet bound above `e`. False where no such position exists: the occurrences part before
/// every free name is bound, or `e` names the binding in a type of its own.
fn insert_let(e: &mut Expr, taken: &mut Option<Taken>, pending: &mut HashSet<Name>) -> bool {
    let name = &taken
        .as_ref()
        .expect("a binding is placed once")
        .binding
        .name;
    if pending.is_empty() {
        let Taken { id, binding, value } = taken.take().expect("a binding is placed once");
        let body = std::mem::take(e);
        let ty = body.ty.clone();
        *e = Expr::let_in_preserving(id, binding, value, body).with_ty(ty);
        return true;
    }
    let mut named_here = false;
    e.walk_type_slots(|t| {
        named_here |= crate::ccl::subst::type_free_vars(t).contains(name);
    });
    if named_here {
        return false;
    }
    // The children holding an occurrence, each with the names its scope binds.
    let mut holding: Vec<(usize, Vec<Name>)> = Vec::new();
    let mut index = 0;
    crate::ccl::scope::for_each_scoped_item(e, &mut |item| {
        if let crate::ccl::scope::ScopedItem::Child { expr, binders } = item {
            if crate::ccl::ccl_utils::count_free(name, expr) > 0 {
                holding.push((index, binders.iter().map(|b| b.name.clone()).collect()));
            }
            index += 1;
        }
    });
    let [(at, binds)] = holding.as_slice() else {
        return false;
    };
    for name in binds {
        pending.remove(name);
    }
    let mut placed = false;
    let mut i = 0;
    e.walk_children_mut(|c| {
        if i == *at {
            placed = insert_let(c, taken, pending);
        }
        i += 1;
    });
    placed
}

/// `e` with `f` applied to the value it ends in: a statement sequence keeps its statements,
/// and a write or a feed that ends one stays a statement, its value `unit`.
fn at_terminal(e: Expr, f: impl FnOnce(Expr) -> Expr) -> Expr {
    let id = e.node_id();
    match e.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let body = at_terminal(*body, f);
            let ty = body.ty.clone();
            Expr::preserve(
                id,
                TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(body),
                },
            )
            .with_ty(ty)
        }
        TypedExprNode::ExprStmt { expr, body } => {
            let body = at_terminal(*body, f);
            let ty = body.ty.clone();
            Expr::expr_stmt_preserving(id, *expr, body).with_ty(ty)
        }
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => {
            let body = at_terminal(*body, f);
            let ty = body.ty.clone();
            Expr::preserve(
                id,
                TypedExprNode::MutDecl {
                    binding,
                    init,
                    body: Box::new(body),
                },
            )
            .with_ty(ty)
        }
        node @ (TypedExprNode::MutWrite { .. }
        | TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }) => {
            let statement = Expr::preserve(id, node).with_ty(e.ty.clone());
            let unit = Expr::lit(Lit::Unit).with_ty(Type::Base(BaseType::Unit));
            let value = f(unit);
            let ty = value.ty.clone();
            Expr::expr_stmt(statement, value).with_ty(ty)
        }
        node => f(Expr::preserve(id, node).with_ty(e.ty)),
    }
}

/// The type of the value a mutable variable declared as `b` starts at: its history's value.
fn init_value_type(b: &TypedBinding) -> Type {
    b.ty.mut_value_type()
        .cloned()
        .unwrap_or_else(|| b.ty.clone())
}

/// The type of the exception `raise value` raises: `value`'s, through a read of a mutable
/// variable, whose node keeps the variable's `Mut` type.
fn raised_type(value: &Expr) -> Type {
    let mut ty = &value.ty;
    while let Some(read) = ty.mut_value_type() {
        ty = read;
    }
    ty.clone()
}

/// Whether a composition's elements are a loop that only feeds, `𝑠 ≫ (λ 𝑥 → body)` with a
/// `Unit` body, whose body may raise.
fn is_feeding_loop(elts: &[Expr]) -> bool {
    let [_, .., last] = elts else {
        return false;
    };
    matches!(&last.node, TypedExprNode::Lambda { body, .. }
        if matches!(body.ty, Type::Base(BaseType::Unit)) && holds_raise(body))
}

/// Whether `e` holds a `raise` or a `try` anywhere, a comprehension's filter included: a
/// filter is the predicate of a `cast`'s target type.
fn holds_raise(e: &Expr) -> bool {
    match &e.node {
        TypedExprNode::Raise { .. } | TypedExprNode::Try { .. } => true,
        TypedExprNode::Cast { target, .. } if filter_raises(target) => true,
        _ => e.any_child(holds_raise),
    }
}

/// Whether a refinement predicate in `ty` holds a `raise` or a `try`.
fn filter_raises(ty: &Type) -> bool {
    let mut raises = false;
    crate::ccl::ccl_utils::walk_refined_predicates(ty, &mut HashSet::new(), &mut |predicate, _| {
        raises |= holds_raise(predicate)
    });
    raises
}

/// An expression with every `raise` and `try` in it replaced.
enum Elim {
    /// It raises nothing: its value, at its own type.
    Pure(Expr),
    /// It may raise: its outcome.
    Raising(Expr),
}

/// The exceptions an outcome carries: each one's tag and type.
type Arms = [(Label, Type)];

/// Whether an exception of type `raised` is caught by a clause catching `catches`, decided as
/// inference decides it (`InferCtx::settle_catches`).
fn caught(raised: &Type, catches: &Type) -> bool {
    crate::ccl::infer::solver::constrain::constrain_subtype_in(
        raised,
        catches,
        &mut crate::ccl::infer::solver::constrain::ConstrainCache::new().without_effects(),
        &crate::ccl::infer::solver::smt::NoScope,
    )
    .is_ok()
}

fn bool_true() -> Expr {
    Expr::lit(Lit::Bool(true)).with_ty(Type::Base(BaseType::Bool))
}

/// A `match` on the sum bound as `o`, one arm per `(tag, binder, body)`, typed `result`.
fn value_match(o: &TypedBinding, arms: Vec<(Label, TypedBinding, Expr)>, result: &Type) -> Expr {
    Expr::new(TypedExprNode::Case {
        scrutinee: Some(Box::new(tvar(&o.name, o.ty.clone()))),
        branches: arms
            .into_iter()
            .map(|(tag, binder, body)| Branch {
                pattern: Some(Pattern {
                    head: PatternHead::Tag(tag),
                    binding: binder,
                    empty_payload: false,
                }),
                guard: bool_true(),
                body,
            })
            .collect(),
    })
    .with_ty(result.clone())
}

/// `let 𝑜 = scrutinee in match 𝑜 { `𝑡₁(𝑏₁) → body₁; … }`: the body of the arm whose tag the
/// sum `scrutinee` carries, with its payload bound, one arm per `(tag, binder, body)`, typed
/// `result`.
///
/// The scrutinee's statements stand on the statement spine, before the binding of the value it
/// ends in: they are the statements before the one that raised, and a write advances its
/// variable only on the spine. The binders are unique by this phase, so the statements' own
/// bindings capture nothing in the arms they now scope over.
///
/// A scrutinee that ends in a constructor selects its arm here, which binds the payload. One
/// that ends in a `match` or an `if` whose branches each end in a different constructor has
/// the dispatch moved into its branches, where each selects its own arm: no arm is copied,
/// and no value passes through the sum. One that ends in `𝑎 ▷ (λ 𝑥 → 𝑏)`, which binds `𝑥` as
/// `let` does, has it moved into `𝑏`.
fn dispatch(scrutinee: Expr, mut arms: Vec<(Label, TypedBinding, Expr)>, result: &Type) -> Expr {
    let result = result.clone();
    at_terminal(scrutinee, |value| {
        if let TypedExprNode::VariantCtor { tag, payload } = value.node {
            let at = arms
                .iter()
                .position(|(t, ..)| *t == tag)
                .expect("an arm for every tag the outcome carries");
            let (_, binder, body) = arms.swap_remove(at);
            return Expr::let_in(binder, *payload, body).with_ty(result);
        }
        if let Some(tags) = branch_constructors(&value) {
            let id = value.node_id();
            let TypedExprNode::Case {
                scrutinee,
                branches,
            } = value.node
            else {
                unreachable!("`branch_constructors` answers only for a `Case`")
            };
            let branches = branches
                .into_iter()
                .zip(tags)
                .map(|(b, tag)| {
                    let at = arms
                        .iter()
                        .position(|(t, ..)| *t == tag)
                        .expect("an arm for every tag the outcome carries");
                    let arm = arms.swap_remove(at);
                    Branch {
                        body: dispatch(b.body, vec![arm], &result),
                        ..b
                    }
                })
                .collect();
            return Expr::preserve(
                id,
                TypedExprNode::Case {
                    scrutinee,
                    branches,
                },
            )
            .with_ty(result);
        }
        // `𝑎 ▷ (λ 𝑥 → 𝑏)` binds `𝑥` as `let` does, so the dispatch moves into `𝑏`.
        if let TypedExprNode::Apply { function, .. } = &value.node
            && matches!(function.node, TypedExprNode::Lambda { .. })
            && !function.ty.is_collection()
        {
            let id = value.node_id();
            let TypedExprNode::Apply { argument, function } = value.node else {
                unreachable!("matched as an `Apply`")
            };
            let function_id = function.node_id();
            let function_ty = with_codomain(&function.ty, &result);
            let TypedExprNode::Lambda { param, body } = function.node else {
                unreachable!("matched as a `Lambda`")
            };
            let function = Expr::preserve(
                function_id,
                TypedExprNode::Lambda {
                    param,
                    body: Box::new(dispatch(*body, arms, &result)),
                },
            )
            .with_ty(function_ty);
            return Expr::preserve(
                id,
                TypedExprNode::Apply {
                    argument,
                    function: Box::new(function),
                },
            )
            .with_ty(result);
        }
        let o = binding(Name::fresh("__outcome"), value.ty.clone());
        let case = value_match(&o, arms, &result);
        Expr::let_in(o, value, case).with_ty(result)
    })
}

/// The function type `ty` with `codomain` for its codomain, a type its parameter `param` may
/// read by name, as a lambda's body type does: a codomain that reads it names it as the
/// function's binder.
fn with_codomain_over(ty: &Type, param: &Name, codomain: &Type) -> Type {
    let mut fun = with_codomain(ty, codomain);
    if let Type::Fun { name, .. } = &mut fun
        && crate::ccl::subst::type_free_vars(codomain).contains(param)
    {
        *name = Some(param.clone());
    }
    fun
}

/// The function type `ty` with `codomain` for its codomain.
fn with_codomain(ty: &Type, codomain: &Type) -> Type {
    match ty.peel_refinements() {
        Type::Fun {
            name,
            fun_kind,
            domain,
            effects,
            ..
        } => Type::Fun {
            name: name.clone(),
            fun_kind: fun_kind.clone(),
            domain: domain.clone(),
            codomain: Box::new(codomain.clone()),
            effects: effects.clone(),
        },
        other => unreachable!("a collection has a function type, not {other}"),
    }
}

/// The tag each branch of the `Case` `e` ends in, where every branch ends in a constructor and
/// no two in the same one.
fn branch_constructors(e: &Expr) -> Option<Vec<Label>> {
    fn terminal(e: &Expr) -> Option<&Label> {
        match &e.node {
            TypedExprNode::Let { body, .. }
            | TypedExprNode::ExprStmt { body, .. }
            | TypedExprNode::MutDecl { body, .. } => terminal(body),
            TypedExprNode::VariantCtor { tag, .. } => Some(tag),
            _ => None,
        }
    }
    let TypedExprNode::Case { branches, .. } = &e.node else {
        return None;
    };
    let mut tags: Vec<Label> = Vec::with_capacity(branches.len());
    for b in branches {
        let tag = terminal(&b.body)?;
        if tags.contains(tag) {
            return None;
        }
        tags.push(tag.clone());
    }
    Some(tags)
}

/// A loop body in the statement form lowering gives one (`lower_loop_body_chain`), which the
/// loop phases read: each `match` a statement before the rest of the chain, the chain ending
/// in `unit`.
///
/// Elimination ends a dispatch in its `match`, and a `try` statement's value arm in its
/// `Unit` payload. A `Unit`-valued term that is not a statement is dropped for `unit`: it has
/// one value, and it holds no write, feed or loop.
fn statement_form(e: Expr) -> Expr {
    let id = e.node_id();
    let ty = e.ty.clone();
    let unit = || Expr::lit(Lit::Unit).with_ty(Type::Base(BaseType::Unit));
    match e.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => Expr::preserve(
            id,
            TypedExprNode::Let {
                binding,
                bound_expr,
                body: Box::new(statement_form(*body)),
            },
        )
        .with_ty(ty),
        TypedExprNode::MutDecl {
            binding,
            init,
            body,
        } => Expr::preserve(
            id,
            TypedExprNode::MutDecl {
                binding,
                init,
                body: Box::new(statement_form(*body)),
            },
        )
        .with_ty(ty),
        TypedExprNode::ExprStmt { expr, body } => {
            Expr::expr_stmt_preserving(id, statement(*expr), statement_form(*body)).with_ty(ty)
        }
        TypedExprNode::Lit(Lit::Unit) => {
            Expr::preserve(id, TypedExprNode::Lit(Lit::Unit)).with_ty(ty)
        }
        node @ (TypedExprNode::Case { .. }
        | TypedExprNode::MutWrite { .. }
        | TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::For { .. }
        | TypedExprNode::Begin { .. }) => {
            let s = statement(Expr::preserve(id, node).with_ty(ty));
            Expr::expr_stmt(s, unit()).with_ty(Type::Base(BaseType::Unit))
        }
        node => {
            let dropped = Expr::preserve(id, node).with_ty(ty);
            assert!(
                !holds_statement(&dropped),
                "a `Unit` value dropped from a loop body holds a statement: {}",
                crate::ccl::symbolic::symbolic(&dropped)
            );
            unit()
        }
    }
}

/// A statement of a loop body in [`statement_form`]: a `match`'s arms are chains themselves.
fn statement(e: Expr) -> Expr {
    let id = e.node_id();
    let ty = e.ty.clone();
    match e.node {
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => Expr::preserve(
            id,
            TypedExprNode::Case {
                scrutinee,
                branches: branches
                    .into_iter()
                    .map(|b| Branch {
                        body: statement_form(b.body),
                        ..b
                    })
                    .collect(),
            },
        )
        .with_ty(ty),
        node => Expr::preserve(id, node).with_ty(ty),
    }
}

/// Whether `e` writes, feeds, loops or opens a transaction anywhere.
fn holds_statement(e: &Expr) -> bool {
    matches!(
        e.node,
        TypedExprNode::MutWrite { .. }
            | TypedExprNode::Feed { .. }
            | TypedExprNode::Define { .. }
            | TypedExprNode::For { .. }
            | TypedExprNode::Begin { .. }
    ) || e.any_child(holds_statement)
}

#[derive(Default)]
struct Cx {
    /// The tag of each exception type met so far, by its canonical form.
    tags: Vec<(Type, Label)>,
    /// One pure form per filter that may raise, however many types carry it.
    filters: PredMemo<()>,
    /// The filters [`Cx::elim_raising_filter`] read through a `__filter` binding, for
    /// [`Cx::place_filter`] to place once the whole program is eliminated.
    lifted: Vec<LiftedFilter>,
}

/// A comprehension's filter that may raise, `raising`, which its domain states as `held`:
/// where the `name` binding's outcome holds.
struct LiftedFilter {
    /// The comprehension's `cast`, which the copies of `held` in types are made for.
    at: provenance::NodeId,
    name: Name,
    raising: Expr,
    held: Expr,
}

impl Cx {
    fn ok() -> Label {
        Label::new("__ok")
    }

    fn tag(&mut self, ty: &Type) -> Label {
        let canonical = ty.canonical();
        if let Some((_, tag)) = self.tags.iter().find(|(t, _)| *t == canonical) {
            return tag.clone();
        }
        let tag = Label::new(format!("__raise{}", self.tags.len()));
        self.tags.push((canonical, tag.clone()));
        tag
    }

    /// The arms of the outcome of a `try` body raising `raised`.
    fn arms(&mut self, raised: &[Type]) -> Vec<(Label, Type)> {
        let mut arms: Vec<(Label, Type)> = Vec::new();
        for ty in raised {
            let tag = self.tag(ty);
            if !arms.iter().any(|(t, _)| *t == tag) {
                arms.push((tag, ty.clone()));
            }
        }
        arms
    }

    /// The type of an outcome whose value is a `value`.
    fn outcome(value: &Type, arms: &Arms) -> Type {
        let mut tags = vec![(FieldKey::Name(Self::ok()), value.clone())];
        tags.extend(
            arms.iter()
                .map(|(tag, ty)| (FieldKey::Name(tag.clone()), ty.clone())),
        );
        Type::Variant(tags, Openness::Closed)
    }

    /// `e` as an outcome at `arms`: as it is if it may raise, otherwise its value under
    /// `` `__ok ``.
    fn lift(e: Elim, value: &Type, arms: &Arms) -> Expr {
        match e {
            Elim::Raising(x) => x,
            Elim::Pure(v) => {
                let outcome = Self::outcome(value, arms);
                at_terminal(v, |v| Expr::variant_ctor(Self::ok(), v).with_ty(outcome))
            }
        }
    }

    /// `match scrutinee { `__ok(binder) → on_ok; `__raise𝑖(𝑧) → `__raise𝑖(𝑧) … }`: continue
    /// with `on_ok` where the outcome `scrutinee` holds a value, and pass each exception on as
    /// an outcome of type `result`.
    fn on_ok(
        scrutinee: Expr,
        binder: TypedBinding,
        on_ok: Expr,
        result: &Type,
        arms: &Arms,
    ) -> Expr {
        let mut branches = vec![(Self::ok(), binder, on_ok)];
        for (tag, ty) in arms {
            let z = binding(Name::fresh("__exc"), ty.clone());
            let pass =
                Expr::variant_ctor(tag.clone(), tvar(&z.name, ty.clone())).with_ty(result.clone());
            branches.push((tag.clone(), z, pass));
        }
        dispatch(scrutinee, branches, result)
    }

    /// The exception types that may escape `e`, in the order it raises them.
    fn escapes(e: &Expr, out: &mut Vec<Type>) {
        match &e.node {
            TypedExprNode::Raise { value } => {
                Self::escapes(value, out);
                out.push(raised_type(value));
            }
            TypedExprNode::Try { body, handlers } => {
                let mut inner = Vec::new();
                Self::escapes(body, &mut inner);
                out.extend(
                    inner
                        .into_iter()
                        .filter(|s| !handlers.iter().any(|h| caught(s, &h.catches))),
                );
                for h in handlers {
                    Self::escapes(&h.body, out);
                }
            }
            // A function raises where it is applied, and one applied where it stands raises
            // there. A collection's elements are evaluated where it stands.
            TypedExprNode::Apply { argument, function } => {
                Self::escapes(projected_element_ref(argument), out);
                let function = projected_element_ref(function);
                match function.node {
                    TypedExprNode::Lambda { .. } => {
                        function.walk_children(|c| Self::escapes(c, out));
                    }
                    _ => Self::escapes(function, out),
                }
            }
            // A loop that only feeds runs its body where it stands.
            TypedExprNode::Compose(elts) if is_feeding_loop(elts) => {
                for elt in elts {
                    match &elt.node {
                        TypedExprNode::Lambda { body, .. } => Self::escapes(body, out),
                        _ => Self::escapes(elt, out),
                    }
                }
            }
            TypedExprNode::Lambda { .. } if !e.ty.is_collection() => {}
            // A comprehension's filter is evaluated at each position before its element.
            TypedExprNode::Cast { target, value } => {
                crate::ccl::ccl_utils::walk_refined_predicates(
                    target,
                    &mut HashSet::new(),
                    &mut |predicate, _| Self::escapes(predicate, out),
                );
                Self::escapes(value, out);
            }
            _ => e.walk_children(|c| Self::escapes(c, out)),
        }
    }

    fn elim(&mut self, e: Expr, arms: &Arms) -> Elim {
        if !holds_raise(&e) {
            return Elim::Pure(e);
        }
        // A function an inlined call passes on stands in the tuple of its arguments,
        // `(𝑓, 𝑥) ▷ .0`, and raises where it is applied, so it is applied where it stands.
        let mut e = projected_element(e);
        if let TypedExprNode::Apply { argument, function } = &mut e.node {
            let taken = std::mem::take(&mut **function);
            **function = projected_element(taken);
            let taken = std::mem::take(&mut **argument);
            **argument = projected_element(taken);
        }
        let _g = provenance::enter(
            e.node_id(),
            "exceptions.eliminate",
            provenance::Nature::Expansion,
        );
        let id = e.node_id();
        let ty = e.ty.clone();
        let kind = e.node.kind_name();
        match e.node {
            TypedExprNode::Raise { value } => {
                let value_ty = raised_type(&value);
                let tag = self.tag(&value_ty);
                let result = Self::outcome(&ty, arms);
                match self.elim(*value, arms) {
                    Elim::Pure(v) => Elim::Raising(Expr::variant_ctor(tag, v).with_ty(result)),
                    Elim::Raising(o) => {
                        let x = binding(Name::fresh("__raised"), value_ty.clone());
                        let raise = Expr::variant_ctor(tag, tvar(&x.name, value_ty))
                            .with_ty(result.clone());
                        Elim::Raising(Self::on_ok(o, x, raise, &result, arms))
                    }
                }
            }
            TypedExprNode::Let {
                binding: b,
                bound_expr,
                body,
            } => {
                let bound = self.elim(*bound_expr, arms);
                let body = self.elim(*body, arms);
                // A definiens that is itself a statement sequence, as an eliminated `try` is,
                // has its statements spliced onto the spine before the binding.
                let bind = |bound: Expr, body: Expr, body_ty: Type| {
                    at_terminal(bound, |value| {
                        Expr::preserve(
                            id,
                            TypedExprNode::Let {
                                binding: b.clone(),
                                bound_expr: Box::new(value),
                                body: Box::new(body),
                            },
                        )
                        .with_ty(body_ty)
                    })
                };
                match (bound, body) {
                    (Elim::Pure(bound), Elim::Pure(body)) => Elim::Pure(bind(bound, body, ty)),
                    (Elim::Pure(bound), Elim::Raising(body)) => {
                        let body_ty = body.ty.clone();
                        Elim::Raising(bind(bound, body, body_ty))
                    }
                    (Elim::Raising(bound), body) => {
                        let result = Self::outcome(&ty, arms);
                        let body = Self::lift(body, &ty, arms);
                        Elim::Raising(Self::on_ok(bound, b, body, &result, arms))
                    }
                }
            }
            TypedExprNode::ExprStmt { expr, body } => {
                let effect_ty = expr.ty.clone();
                let effect = self.elim(*expr, arms);
                let body = self.elim(*body, arms);
                // A statement that is itself a statement sequence, as an eliminated `try` is,
                // has the statements after it spliced on after its own: a write in it then
                // reaches what follows it.
                let sequence = |effect: Expr, body: Expr, body_ty: Type| {
                    at_terminal(effect, |value| {
                        Expr::expr_stmt_preserving(id, value, body).with_ty(body_ty)
                    })
                };
                match (effect, body) {
                    (Elim::Pure(effect), Elim::Pure(body)) => {
                        Elim::Pure(sequence(effect, body, ty))
                    }
                    (Elim::Pure(effect), Elim::Raising(body)) => {
                        let body_ty = body.ty.clone();
                        Elim::Raising(sequence(effect, body, body_ty))
                    }
                    (Elim::Raising(effect), body) => {
                        let result = Self::outcome(&ty, arms);
                        let body = Self::lift(body, &ty, arms);
                        let unused = binding(Name::fresh("__done"), effect_ty);
                        Elim::Raising(Self::on_ok(effect, unused, body, &result, arms))
                    }
                }
            }
            TypedExprNode::Try { body, handlers } => self.elim_try(*body, handlers, &ty, arms),
            TypedExprNode::Case {
                scrutinee,
                branches,
            } => self.elim_case(id, scrutinee, branches, &ty, arms),
            TypedExprNode::MutDecl {
                binding: b,
                init,
                body,
            } => {
                let init = self.elim(*init, arms);
                let body = self.elim(*body, arms);
                let rebuild = |init: Expr, body: Expr, ty: Type| {
                    Expr::preserve(
                        id,
                        TypedExprNode::MutDecl {
                            binding: b.clone(),
                            init: Box::new(init),
                            body: Box::new(body),
                        },
                    )
                    .with_ty(ty)
                };
                match (init, body) {
                    (Elim::Pure(init), Elim::Pure(body)) => Elim::Pure(rebuild(init, body, ty)),
                    (Elim::Pure(init), Elim::Raising(body)) => {
                        let body_ty = body.ty.clone();
                        Elim::Raising(rebuild(init, body, body_ty))
                    }
                    (Elim::Raising(init), body) => {
                        let result = Self::outcome(&ty, arms);
                        let value_ty = init_value_type(&b);
                        let x = binding(Name::fresh("__init"), value_ty.clone());
                        let body = Self::lift(body, &ty, arms);
                        let decl = rebuild(tvar(&x.name, value_ty), body, result.clone());
                        Elim::Raising(Self::on_ok(init, x, decl, &result, arms))
                    }
                }
            }
            TypedExprNode::For { target, iter, body } => {
                self.elim_for(id, target, *iter, *body, &ty, arms)
            }
            // `𝑠 ≫ (λ 𝑥 → body)` with a `Unit` body is a loop that only feeds, which lowering
            // gives that form before inference says whether a call in it raises. One that may
            // raise is the loop it is.
            TypedExprNode::Compose(mut elts) if is_feeding_loop(&elts) => {
                let lambda = elts
                    .pop()
                    .expect("a feeding loop ends in its body's lambda");
                let iter = match elts.len() {
                    1 => elts.pop().expect("one element"),
                    _ => crate::ccl::ccl_utils::typed_compose(elts),
                };
                let TypedExprNode::Lambda { param, body } = lambda.node else {
                    unreachable!("`is_feeding_loop` reads a `Lambda`")
                };
                self.elim_for(id, param, iter, *body, &Type::Base(BaseType::Unit), arms)
            }
            // `𝑎 ▷ (λ 𝑥 → 𝑏)`, a comprehension's element applied to the generator's value at
            // each position: the lambda's body becomes its outcome, which the application
            // gives. An argument that may raise is matched on first, as `let 𝑥 = 𝑎 in 𝑏`.
            TypedExprNode::Apply { argument, function }
                if matches!(function.node, TypedExprNode::Lambda { .. }) =>
            {
                let function_id = function.node_id();
                let function_ty = function.ty.clone();
                let TypedExprNode::Lambda { param, body } = function.node else {
                    unreachable!("matched as a `Lambda`")
                };
                let argument = self.elim(*argument, arms);
                let body_ty = body.ty.clone();
                let body = self.elim(*body, arms);
                match (argument, body) {
                    (Elim::Pure(argument), Elim::Pure(body)) => {
                        let function = Expr::preserve(
                            function_id,
                            TypedExprNode::Lambda {
                                param,
                                body: Box::new(body),
                            },
                        )
                        .with_ty(function_ty);
                        Elim::Pure(
                            Expr::preserve(
                                id,
                                TypedExprNode::Apply {
                                    argument: Box::new(argument),
                                    function: Box::new(function),
                                },
                            )
                            .with_ty(ty),
                        )
                    }
                    (Elim::Pure(argument), Elim::Raising(body)) => {
                        // The lambda answers its body's outcome, which may read its parameter;
                        // the application answers it at the argument.
                        let result = Self::outcome(&ty, arms);
                        let function_ty = with_codomain_over(
                            &function_ty,
                            &param.name,
                            &Self::outcome(&body_ty, arms),
                        );
                        let function = Expr::preserve(
                            function_id,
                            TypedExprNode::Lambda {
                                param: param.clone(),
                                body: Box::new(body),
                            },
                        )
                        .with_ty(function_ty);
                        Elim::Raising(
                            Expr::preserve(
                                id,
                                TypedExprNode::Apply {
                                    argument: Box::new(argument),
                                    function: Box::new(function),
                                },
                            )
                            .with_ty(result),
                        )
                    }
                    (Elim::Raising(argument), body) => {
                        let result = Self::outcome(&ty, arms);
                        let body = Self::lift(body, &body_ty, arms);
                        Elim::Raising(Self::on_ok(argument, param, body, &result, arms))
                    }
                }
            }
            TypedExprNode::Lambda { param, body } if ty.is_collection() => {
                let lambda_ty = ty.clone();
                self.elim_collection(id, param, *body, &lambda_ty, None, &ty, arms)
            }
            TypedExprNode::Cast { value, target } if filter_raises(&target) => {
                self.elim_raising_filter(id, *value, target, &ty, arms)
            }
            // A filtered comprehension: the filter is the cast's, on the collection's domain.
            TypedExprNode::Cast { value, target }
                if ty.is_collection() && matches!(value.node, TypedExprNode::Lambda { .. }) =>
            {
                let lambda_id = value.node_id();
                let lambda_ty = value.ty.clone();
                let TypedExprNode::Lambda { param, body } = value.node else {
                    unreachable!("matched as a `Lambda`")
                };
                self.elim_collection(
                    lambda_id,
                    param,
                    *body,
                    &lambda_ty,
                    Some((id, target)),
                    &ty,
                    arms,
                )
            }
            TypedExprNode::Lambda { .. }
            | TypedExprNode::Begin { .. }
            | TypedExprNode::LetRec { .. }
            | TypedExprNode::DefGroup { .. } => {
                unimplemented!(
                    "exception elimination: a `raise` inside a {kind} is not handled yet"
                )
            }
            // `𝑎 and 𝑏` evaluates `𝑏` only where `𝑎` holds, and `𝑎 or 𝑏` only where it does not:
            // a `𝑏` that may raise is the branch of an `if`.
            TypedExprNode::BinOp {
                left,
                op: BinOpKind::BoolLogic(logic @ (LogicKind::And | LogicKind::Or)),
                right,
            } if holds_raise(&right) => {
                let constant = Expr::lit(Lit::Bool(logic == LogicKind::Or)).with_ty(ty.clone());
                let (then, otherwise) = match logic {
                    LogicKind::And => (*right, constant),
                    _ => (constant, *right),
                };
                let case = Expr::preserve(
                    id,
                    TypedExprNode::Case {
                        scrutinee: None,
                        branches: vec![
                            Branch {
                                pattern: None,
                                guard: *left,
                                body: then,
                            },
                            Branch {
                                pattern: None,
                                guard: bool_true(),
                                body: otherwise,
                            },
                        ],
                    },
                )
                .with_ty(ty);
                self.elim(case, arms)
            }
            node => self.elim_in_order(Expr::preserve(id, node).with_ty(ty), arms),
        }
    }

    /// A node whose children are evaluated in written order and bind nothing: each child that
    /// may raise is matched on in turn, and the node is built from their values.
    fn elim_in_order(&mut self, mut e: Expr, arms: &Arms) -> Elim {
        let mut binds = false;
        e.walk_binders(|_| binds = true);
        assert!(
            !binds,
            "exception elimination: a {} binds a name, so its children are not evaluated in \
             written order alone",
            e.node.kind_name()
        );
        let ty = e.ty.clone();
        let mut children = Vec::new();
        e.walk_children_mut(|c| children.push(std::mem::take(c)));
        let mut matched = Vec::new();
        let mut rebuilt = Vec::with_capacity(children.len());
        for child in children {
            let child_ty = child.ty.clone();
            match self.elim(child, arms) {
                Elim::Pure(c) => rebuilt.push(c),
                Elim::Raising(o) => {
                    let x = binding(Name::fresh("__operand"), child_ty.clone());
                    rebuilt.push(tvar(&x.name, child_ty));
                    matched.push((x, o));
                }
            }
        }
        let mut rebuilt = rebuilt.into_iter();
        e.walk_children_mut(|c| *c = rebuilt.next().expect("one child per child taken"));
        if matched.is_empty() {
            return Elim::Pure(e);
        }
        let result = Self::outcome(&ty, arms);
        let mut out = Self::lift(Elim::Pure(e), &ty, arms);
        for (x, o) in matched.into_iter().rev() {
            out = Self::on_ok(o, x, out, &result, arms);
        }
        Elim::Raising(out)
    }

    fn elim_case(
        &mut self,
        id: provenance::NodeId,
        scrutinee: Option<Box<Expr>>,
        branches: Vec<Branch>,
        ty: &Type,
        arms: &Arms,
    ) -> Elim {
        // A guard that may raise is evaluated where the guards before it all failed: the
        // `Case` splits there, `{𝑔₁ → 𝐴₁; …; true → let 𝑐 = 𝑔ᵢ in {𝑐 → 𝐴ᵢ; …}}`, and the binding
        // is matched on as any is.
        if scrutinee.is_none()
            && let Some(i) = branches.iter().position(|b| holds_raise(&b.guard))
        {
            let mut branches = branches;
            let rest = branches.split_off(i);
            let mut rest = rest.into_iter();
            let first = rest.next().expect("the raising branch");
            let c = binding(Name::fresh("__guard"), first.guard.ty.clone());
            let mut inner = vec![Branch {
                guard: tvar(&c.name, first.guard.ty.clone()),
                ..first
            }];
            inner.extend(rest);
            let inner = Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: inner,
            })
            .with_ty(ty.clone());
            let split = Expr::let_in(c, first.guard, inner).with_ty(ty.clone());
            let split = if branches.is_empty() {
                split
            } else {
                branches.push(Branch {
                    pattern: None,
                    guard: bool_true(),
                    body: split,
                });
                Expr::preserve(
                    id,
                    TypedExprNode::Case {
                        scrutinee: None,
                        branches,
                    },
                )
                .with_ty(ty.clone())
            };
            return self.elim(split, arms);
        }
        let mut bodies = Vec::with_capacity(branches.len());
        let mut heads = Vec::with_capacity(branches.len());
        for b in branches {
            assert!(
                !holds_raise(&b.guard),
                "exception elimination: a guard of a `match` arm that raises is not handled yet"
            );
            heads.push((b.pattern, b.guard));
            let body_ty = b.body.ty.clone();
            bodies.push((self.elim(b.body, arms), body_ty));
        }
        let raising = bodies.iter().any(|(b, _)| matches!(b, Elim::Raising(_)));
        let result = if raising {
            Self::outcome(ty, arms)
        } else {
            ty.clone()
        };
        let branches: Vec<Branch> = heads
            .into_iter()
            .zip(bodies)
            .map(|((pattern, guard), (body, body_ty))| Branch {
                pattern,
                guard,
                body: match body {
                    Elim::Pure(b) if !raising => b,
                    body => Self::lift(body, &body_ty, arms),
                },
            })
            .collect();
        let (scrutinee, matched) = match scrutinee {
            None => (None, None),
            Some(s) => {
                let s_ty = s.ty.clone();
                match self.elim(*s, arms) {
                    Elim::Pure(s) => (Some(Box::new(s)), None),
                    Elim::Raising(o) => {
                        let x = binding(Name::fresh("__scrutinee"), s_ty.clone());
                        (Some(Box::new(tvar(&x.name, s_ty))), Some((x, o)))
                    }
                }
            }
        };
        let case = Expr::preserve(
            id,
            TypedExprNode::Case {
                scrutinee,
                branches,
            },
        )
        .with_ty(result.clone());
        match matched {
            None if raising => Elim::Raising(case),
            None => Elim::Pure(case),
            Some((x, o)) => {
                let outcome = Self::outcome(ty, arms);
                let case = if raising {
                    case
                } else {
                    Self::lift(Elim::Pure(case), ty, arms)
                };
                Elim::Raising(Self::on_ok(o, x, case, &outcome, arms))
            }
        }
    }

    /// `for 𝑥 in 𝑠: body` with a body that may raise: each iteration runs while none before it
    /// has raised, and a synthesized mutable variable carries the first exception out.
    ///
    /// ```text
    /// __loop : Mut(𝑆, _) := `__ok(unit)
    /// in for 𝑥 in 𝑠 do (let 𝑙 ^= __loop in match 𝑙 { `__ok(_) → body′; `__raise𝑖(_) → unit });
    ///    let 𝑙′ ^= __loop in match 𝑙′ { `__ok(_) → `__ok(unit); `__raise𝑖(𝑧) → `__raise𝑖(𝑧) }
    /// ```
    ///
    /// `𝑆` is the outcome of a `Unit` at the exceptions the body raises, and `body′` the body's
    /// outcome dispatched: `unit` where it holds a value, and the write of the exception into
    /// `__loop` where it raised. The variable is an accumulator, so the loop's iterations are
    /// ordered as the spec orders a loop an exception escapes (`docs/chl-spec.md`,
    /// "Exceptions").
    fn elim_for(
        &mut self,
        id: provenance::NodeId,
        target: TypedBinding,
        iter: Expr,
        body: Expr,
        ty: &Type,
        arms: &Arms,
    ) -> Elim {
        let iter_ty = iter.ty.clone();
        let iter = self.elim(iter, arms);
        let mut raised = Vec::new();
        Self::escapes(&body, &mut raised);
        let inner = self.arms(&raised);
        let body = match self.elim(body, &inner) {
            Elim::Pure(body) => Elim::Pure(statement_form(body)),
            raising => raising,
        };
        let unit_ty = Type::Base(BaseType::Unit);
        let unit = || Expr::lit(Lit::Unit).with_ty(Type::Base(BaseType::Unit));
        let lp = |iter: Expr, body: Expr| {
            Expr::preserve(
                id,
                TypedExprNode::For {
                    target: target.clone(),
                    iter: Box::new(iter),
                    body: Box::new(body),
                },
            )
            .with_ty(ty.clone())
        };
        let (iter, matched) = match iter {
            Elim::Pure(iter) => (iter, None),
            Elim::Raising(o) => {
                let x = binding(Name::fresh("__source"), iter_ty.clone());
                (tvar(&x.name, iter_ty.clone()), Some((x, o)))
            }
        };
        let result = Self::outcome(ty, arms);
        let looped = match body {
            Elim::Pure(body) => match matched {
                None => return Elim::Pure(lp(iter, body)),
                Some(_) => Self::lift(Elim::Pure(lp(iter, body)), ty, arms),
            },
            Elim::Raising(body) => {
                let state_ty = Self::outcome(&unit_ty, &inner);
                let state = Name::fresh("__loop");
                // The accumulator of this one loop: its history is over the loop's positions.
                let positions = iter_ty
                    .read_view()
                    .domain()
                    .expect("a loop's source is a collection");
                let history = Type::mutable(positions, state_ty.clone());
                // `let 𝑙 ^= __loop in match 𝑙 { … }`: the arms over the variable's value here.
                let read = |arms: Vec<(Label, TypedBinding, Expr)>, result: &Type| {
                    let l = TypedBinding {
                        transparency: BindingTransparency::Opaque,
                        ..binding(Name::fresh("__loop"), state_ty.clone())
                    };
                    let case = value_match(&l, arms, result);
                    Expr::let_in(l, tvar(&state, history.clone()), case).with_ty(result.clone())
                };
                let done = || binding(Name::fresh("__done"), Type::Base(BaseType::Unit));
                let mut record = vec![(Self::ok(), done(), unit())];
                for (tag, t) in &inner {
                    let z = binding(Name::fresh("__exc"), t.clone());
                    let exc = Expr::variant_ctor(tag.clone(), tvar(&z.name, t.clone()))
                        .with_ty(state_ty.clone());
                    let write = Expr::mut_write(state.clone(), exc).with_ty(unit_ty.clone());
                    let recorded = Expr::expr_stmt(write, unit()).with_ty(unit_ty.clone());
                    record.push((tag.clone(), z, recorded));
                }
                let mut running = vec![(Self::ok(), done(), dispatch(body, record, &unit_ty))];
                let mut after = vec![(
                    Self::ok(),
                    done(),
                    Expr::variant_ctor(Self::ok(), unit()).with_ty(result.clone()),
                )];
                for (tag, t) in &inner {
                    running.push((
                        tag.clone(),
                        binding(Name::fresh("__exc"), t.clone()),
                        unit(),
                    ));
                    let z = binding(Name::fresh("__exc"), t.clone());
                    let pass = Expr::variant_ctor(tag.clone(), tvar(&z.name, t.clone()))
                        .with_ty(result.clone());
                    after.push((tag.clone(), z, pass));
                }
                let guarded = statement_form(read(running, &unit_ty));
                let after = read(after, &result);
                let start = Expr::variant_ctor(Self::ok(), unit()).with_ty(state_ty.clone());
                let sequenced = Expr::expr_stmt(lp(iter, guarded), after).with_ty(result.clone());
                Expr::mut_decl(state, history, start, sequenced).with_ty(result.clone())
            }
        };
        match matched {
            None => Elim::Raising(looped),
            Some((x, o)) => Elim::Raising(Self::on_ok(o, x, looped, &result, arms)),
        }
    }

    /// A collection `λ 𝑘 → body` whose elements may raise, a comprehension: it raises the
    /// exception of its first raising position in position order, as a loop over it would.
    ///
    /// ```text
    /// let __elements = λ 𝑘 → body′
    /// in for 𝑜 in __elements do match 𝑜 { `__ok(_) → unit; `__raise𝑖(𝑧) → raise 𝑧 };
    ///    __elements ≫ variant_project(`__ok)
    /// ```
    ///
    /// `body′` is each element's outcome. The loop is eliminated as any raising loop is
    /// ([`Self::elim_for`]), so its accumulator orders the positions, and the collection's
    /// value, read where nothing raised, is every element's value. A filtered comprehension's
    /// lambda stands in a `cast` to its filtered domain, which the outcomes keep, so a
    /// position the filter drops raises nothing.
    #[expect(
        clippy::too_many_arguments,
        reason = "the lambda's parts, the cast around it, and the collection's own type"
    )]
    fn elim_collection(
        &mut self,
        id: provenance::NodeId,
        param: TypedBinding,
        body: Expr,
        lambda_ty: &Type,
        cast: Option<(provenance::NodeId, Type)>,
        ty: &Type,
        arms: &Arms,
    ) -> Elim {
        let mut raised = Vec::new();
        Self::escapes(&body, &mut raised);
        let inner = self.arms(&raised);
        let value_ty = body.ty.clone();
        let element = self.elim(body, &inner);
        let element = Self::lift(element, &value_ty, &inner);
        let outcome_ty = Self::outcome(&value_ty, &inner);
        let lambda_ty = with_codomain_over(lambda_ty, &param.name, &outcome_ty);
        let lambda = Expr::preserve(
            id,
            TypedExprNode::Lambda {
                param,
                body: Box::new(element),
            },
        )
        .with_ty(lambda_ty);
        let elements_value = match cast {
            None => lambda,
            Some((cast_id, target)) => {
                let target = with_codomain(&target, &outcome_ty);
                Expr::preserve(
                    cast_id,
                    TypedExprNode::Cast {
                        value: Box::new(lambda),
                        target: target.clone(),
                    },
                )
                .with_ty(target)
            }
        };
        let elements_ty = elements_value.ty.clone();
        let domain_ty = elements_ty
            .domain()
            .expect("a collection is a function of its positions");
        let elements = binding(Name::fresh("__elements"), elements_ty.clone());
        let lambda = elements_value;
        let unit_ty = Type::Base(BaseType::Unit);
        let unit = || Expr::lit(Lit::Unit).with_ty(Type::Base(BaseType::Unit));
        let o = binding(Name::fresh("__element"), outcome_ty.clone());
        let mut scan = vec![(
            Self::ok(),
            binding(Name::fresh("__done"), value_ty.clone()),
            unit(),
        )];
        for (tag, t) in &inner {
            let z = binding(Name::fresh("__exc"), t.clone());
            let raise = Expr::new(TypedExprNode::Raise {
                value: Box::new(tvar(&z.name, t.clone())),
            })
            .with_ty(unit_ty.clone());
            scan.push((tag.clone(), z, raise));
        }
        let scan = Expr::new(TypedExprNode::For {
            target: o.clone(),
            iter: Box::new(tvar(&elements.name, elements_ty.clone())),
            body: Box::new(value_match(&o, scan, &unit_ty)),
        })
        .with_ty(unit_ty);
        let project = Expr::builtin(Builtin::VariantProject(FieldKey::Name(Self::ok())))
            .with_ty(Type::fun(outcome_ty.clone(), value_ty.clone()));
        // A collection whose element type reads its position names it in its type, and the
        // value's binder takes that name, so its body's type is the one the type states.
        let position = match ty.peel_refinements() {
            Type::Fun { name: Some(b), .. } => b.clone(),
            _ => Name::fresh("__position"),
        };
        let k = binding(position, domain_ty.clone());
        let at_k = Expr::apply(
            tvar(&k.name, domain_ty),
            tvar(&elements.name, elements_ty.clone()),
        )
        .with_ty(outcome_ty);
        let value = Expr::lambda(
            &k.name,
            k.ty.clone(),
            Expr::apply(at_k, project).with_ty(value_ty),
        )
        .with_ty(ty.clone());
        let read = Expr::expr_stmt(scan, value).with_ty(ty.clone());
        self.elim(
            Expr::let_in(elements, lambda, read).with_ty(ty.clone()),
            arms,
        )
    }

    /// A comprehension whose filter may raise, `cast(λ 𝑘 → body, {𝐷 | 𝑃})` with a `raise` in
    /// 𝑃: the loop `for 𝑘 in 𝐷: if 𝑃: …body…`, whose positions each evaluate the filter and,
    /// where it holds, the element, and whose first exception in position order escapes.
    ///
    /// ```text
    /// let __filter = λ 𝑘 → outcome(𝑃[𝑘])
    /// in let __kept = λ 𝑘 → match 𝑘 ▷ __filter {
    ///        `__ok(ℎ) → {ℎ → `__kept(body); true → `__dropped(unit)};
    ///        `__raise𝑖(𝑧) → raise 𝑧 }
    /// in cast(λ 𝑘 → 𝑘 ▷ __kept ▷ variant_project(`__kept), {𝐷 | holds(__elem ▷ __filter)})
    /// ```
    ///
    /// `__filter` is the filter's outcome at each position, and `__kept` reads it there, so
    /// each position evaluates the filter once and the element once. `__kept` is a collection
    /// whose elements may raise, eliminated as one ([`Self::elim_collection`]): its scan
    /// raises the first exception in position order, a filter's before its position's
    /// element. The cast restricts its domain to where the filter held, which stands for 𝑃
    /// in every type; [`eliminate`] then moves `__filter` as high as its free variables allow,
    /// so the types that state the domain stay in its scope ([`Self::place_filter`]).
    fn elim_raising_filter(
        &mut self,
        id: provenance::NodeId,
        value: Expr,
        mut target: Type,
        ty: &Type,
        arms: &Arms,
    ) -> Elim {
        let value_id = value.node_id();
        let mut lambda_ty = value.ty.clone();
        let TypedExprNode::Lambda { param, body } = value.node else {
            unreachable!("a filter is a comprehension's, and it filters a lambda")
        };
        let domain = target.domain().expect("a cast target is a collection");
        let filter = {
            let mut raising = domain
                .refinements()
                .iter()
                .filter(|r| holds_raise(&r.predicate));
            let filter = raising.next().expect("the filter raises");
            assert!(raising.next().is_none(), "a comprehension has one filter");
            Expr::clone(&filter.predicate)
        };
        let value_ty = body.ty.clone();
        let bool_ty = Type::Base(BaseType::Bool);
        let unit_ty = Type::Base(BaseType::Unit);

        // The filter's outcome at each position.
        let mut raised = Vec::new();
        Self::escapes(&filter, &mut raised);
        let inner = self.arms(&raised);
        let filter_at = TypedBinding {
            name: Name::fresh_like(&param.name),
            ..param.clone()
        };
        let guard = crate::ccl::lambda_elim::substitute(
            filter.clone(),
            &Name::elem(),
            &tvar(&filter_at.name, filter_at.ty.clone()),
        );
        // The filter's own type, which a constant filter narrows to a singleton.
        let guard_ty = guard.ty.clone();
        let held = self.elim(guard, &inner);
        let held = Self::lift(held, &guard_ty, &inner);
        let held_ty = Self::outcome(&guard_ty, &inner);
        let filter_value = Expr::lambda(&filter_at.name, filter_at.ty.clone(), held)
            .with_ty(with_codomain(&lambda_ty, &held_ty));
        let filter_b = binding(Name::fresh("__filter"), filter_value.ty.clone());
        let filter_read = |at: Expr| {
            Expr::apply(at, tvar(&filter_b.name, filter_b.ty.clone())).with_ty(held_ty.clone())
        };

        // Each position's element where its filter held.
        let (kept, dropped) = (Label::new("__kept"), Label::new("__dropped"));
        let kept_ty = Type::Variant(
            vec![
                (FieldKey::Name(kept.clone()), value_ty.clone()),
                (FieldKey::Name(dropped.clone()), unit_ty.clone()),
            ],
            Openness::Closed,
        );
        let dropped_value = || {
            Expr::variant_ctor(
                dropped.clone(),
                Expr::lit(Lit::Unit).with_ty(unit_ty.clone()),
            )
            .with_ty(kept_ty.clone())
        };
        // The scan's positions under a binder of their own: the cast keeps the element's.
        let at = TypedBinding {
            name: Name::fresh_like(&param.name),
            ..param.clone()
        };
        let read_at = tvar(&at.name, at.ty.clone());
        let scanned = crate::ccl::lambda_elim::substitute(*body, &param.name, &read_at);
        let outcome_b = binding(Name::fresh("__held"), held_ty.clone());
        let holds = binding(Name::fresh("__holds"), guard_ty.clone());
        let mut on_outcome = vec![(
            Self::ok(),
            holds.clone(),
            Expr::new(TypedExprNode::Case {
                scrutinee: None,
                branches: vec![
                    Branch {
                        pattern: None,
                        guard: tvar(&holds.name, guard_ty.clone()),
                        body: Expr::variant_ctor(kept.clone(), scanned).with_ty(kept_ty.clone()),
                    },
                    Branch {
                        pattern: None,
                        guard: bool_true(),
                        body: dropped_value(),
                    },
                ],
            })
            .with_ty(kept_ty.clone()),
        )];
        for (tag, t) in &inner {
            let z = binding(Name::fresh("__exc"), t.clone());
            let raise = Expr::new(TypedExprNode::Raise {
                value: Box::new(tvar(&z.name, t.clone())),
            })
            .with_ty(unit_ty.clone());
            on_outcome.push((
                tag.clone(),
                z,
                Expr::expr_stmt(raise, dropped_value()).with_ty(kept_ty.clone()),
            ));
        }
        let positions = Expr::lambda(
            &at.name,
            at.ty.clone(),
            Expr::let_in(
                outcome_b.clone(),
                filter_read(read_at),
                value_match(&outcome_b, on_outcome, &kept_ty),
            )
            .with_ty(kept_ty.clone()),
        )
        .with_ty(with_codomain(&lambda_ty, &kept_ty));
        let positions_b = binding(Name::fresh("__kept"), positions.ty.clone());
        // The element where it did not raise: the payload `__kept` holds at the position.
        let read = Expr::apply(
            tvar(&param.name, param.ty.clone()),
            tvar(&positions_b.name, positions_b.ty.clone()),
        )
        .with_ty(kept_ty.clone());
        let element = Expr::apply(
            read,
            Expr::builtin(Builtin::VariantProject(FieldKey::Name(kept)))
                .with_ty(Type::fun(kept_ty.clone(), value_ty.clone())),
        )
        .with_ty(value_ty.clone());

        // Where the filter held, as a predicate on `__elem`: what stands for 𝑃 in every type.
        let mut where_held = vec![(
            Self::ok(),
            holds.clone(),
            tvar(&holds.name, guard_ty.clone()),
        )];
        for (tag, t) in &inner {
            where_held.push((
                tag.clone(),
                binding(Name::fresh("__exc"), t.clone()),
                Expr::lit(Lit::Bool(false)).with_ty(bool_ty.clone()),
            ));
        }
        let held_here = dispatch(
            filter_read(tvar(&Name::elem(), domain.peel_refinements().clone())),
            where_held,
            &bool_ty,
        );
        let memo = PredMemo::default();
        replace_filter(&mut target, &memo, &filter, &held_here);
        replace_filter(&mut lambda_ty, &memo, &filter, &held_here);
        let mut ty = ty.clone();
        replace_filter(&mut ty, &memo, &filter, &held_here);
        self.lifted.push(LiftedFilter {
            at: id,
            name: filter_b.name.clone(),
            raising: filter,
            held: held_here,
        });

        let lambda = Expr::preserve(
            value_id,
            TypedExprNode::Lambda {
                param,
                body: Box::new(element),
            },
        )
        .with_ty(lambda_ty);
        let cast = Expr::preserve(
            id,
            TypedExprNode::Cast {
                value: Box::new(lambda),
                target,
            },
        )
        .with_ty(ty.clone());
        let kept_and_cast = Expr::let_in(positions_b, positions, cast).with_ty(ty.clone());
        self.elim(
            Expr::let_in(filter_b, filter_value, kept_and_cast).with_ty(ty),
            arms,
        )
    }

    /// Place the `__filter` binding [`Self::elim_raising_filter`] made for `lifted` in
    /// `expr`, the whole program: as high as its definition's free variables allow, with
    /// every type stating the comprehension's domain reading it, where that leaves no type
    /// naming it outside its scope. Where one would, a lambda's type stating the domain in
    /// terms of the lambda's parameter, the filter's pure form ([`Self::pure_filter`])
    /// states the domain instead, which evaluates the filter a second time.
    fn place_filter(&mut self, expr: Expr, lifted: LiftedFilter) -> Expr {
        let _g = provenance::enter(
            lifted.at,
            "exceptions.filter",
            provenance::Nature::Expansion,
        );
        // A rollback copy: at most one of `expr` and `floated` reaches the tree.
        let mut floated = expr.clone_preserving_ids();
        replace_filter_in(
            &mut floated,
            &PredMemo::default(),
            &lifted.raising,
            &lifted.held,
        );
        if let Some(taken) = take_let(&mut floated, &lifted.name) {
            let mut pending: HashSet<Name> = crate::ccl::ccl_utils::free_names(&taken.value)
                .into_iter()
                .collect();
            pending.remove(&lifted.name);
            if insert_let(&mut floated, &mut Some(taken), &mut pending)
                && crate::ccl::ccl_utils::count_free(&lifted.name, &floated) == 0
            {
                return floated;
            }
        }
        let mut expr = expr;
        let pure = self.pure_filter(lifted.raising.clone());
        replace_filter_in(&mut expr, &PredMemo::default(), &lifted.held, &pure);
        expr
    }

    /// A filter that may raise as a pure predicate: `false` where it raises, its value
    /// elsewhere. A position whose filter raised is dropped where nothing raised, which is
    /// the only place the filtered collection is read.
    fn pure_filter(&mut self, filter: Expr) -> Expr {
        let mut raised = Vec::new();
        Self::escapes(&filter, &mut raised);
        let inner = self.arms(&raised);
        let bool_ty = Type::Base(BaseType::Bool);
        let mut pure = match self.elim(filter, &inner) {
            Elim::Pure(filter) => filter,
            Elim::Raising(outcome) => {
                let holds = binding(Name::fresh("__holds"), bool_ty.clone());
                let mut arms = vec![(
                    Self::ok(),
                    holds.clone(),
                    tvar(&holds.name, bool_ty.clone()),
                )];
                for (tag, t) in &inner {
                    arms.push((
                        tag.clone(),
                        binding(Name::fresh("__exc"), t.clone()),
                        Expr::lit(Lit::Bool(false)).with_ty(bool_ty.clone()),
                    ));
                }
                dispatch(outcome, arms, &bool_ty)
            }
        };
        self.purify_tree(&mut pure);
        pure
    }

    /// `ty` with each filter in it that may raise in its pure form ([`Self::pure_filter`]).
    fn purify(&mut self, ty: &mut Type) {
        let filters = self.filters.clone();
        walk_refined_predicates_mut(ty, &filters, &(), &mut |predicate, _| {
            if !holds_raise(predicate) {
                return false;
            }
            *predicate = self.pure_filter(std::mem::take(predicate));
            true
        });
    }

    /// [`Self::purify`] at every type slot in `e`.
    fn purify_tree(&mut self, e: &mut Expr) {
        e.walk_type_slots_mut(|t| self.purify(t));
        e.walk_children_mut(|c| self.purify_tree(c));
    }

    /// `try: body except 𝑇ⱼ as 𝑒ⱼ: handlerⱼ`: the body's outcome, sorted by the clause that
    /// catches each exception, then each clause run once on what it caught.
    ///
    /// The first match sorts: the value goes to `` `__value ``, an exception the `𝑗`th clause
    /// catches to `` `__clause𝑗 `` at that clause's type, and any other on, under its own tag.
    /// The second runs each clause's body under its binder, so a clause catching several
    /// types is still one body.
    fn elim_try(&mut self, body: Expr, handlers: Vec<Handler>, ty: &Type, arms: &Arms) -> Elim {
        let mut raised = Vec::new();
        Self::escapes(&body, &mut raised);
        let inner = self.arms(&raised);
        let body_ty = body.ty.clone();
        let body = self.elim(body, &inner);
        let Elim::Raising(body) = body else {
            return body;
        };
        let value_tag = Label::new("__value");
        let clause_tag = |j: usize| Label::new(format!("__clause{j}"));
        let mut sorted_tags = vec![(FieldKey::Name(value_tag.clone()), body_ty.clone())];
        sorted_tags.extend(
            handlers
                .iter()
                .enumerate()
                .map(|(j, h)| (FieldKey::Name(clause_tag(j)), h.catches.clone())),
        );
        let mut passed: Vec<(Label, Type)> = Vec::new();
        let mut sort_branches = Vec::new();
        let v = binding(Name::fresh("__value"), body_ty.clone());
        let payload = tvar(&v.name, body_ty.clone());
        sort_branches.push((v, value_tag.clone(), payload));
        for (tag, raised_ty) in &inner {
            let z = binding(Name::fresh("__exc"), raised_ty.clone());
            let payload = tvar(&z.name, raised_ty.clone());
            match handlers.iter().position(|h| caught(raised_ty, &h.catches)) {
                Some(j) => sort_branches.push((z, clause_tag(j), payload)),
                None => {
                    if !passed.iter().any(|(t, _)| t == tag) {
                        passed.push((tag.clone(), raised_ty.clone()));
                    }
                    sort_branches.push((z, tag.clone(), payload));
                }
            }
        }
        sorted_tags.extend(
            passed
                .iter()
                .map(|(tag, t)| (FieldKey::Name(tag.clone()), t.clone())),
        );
        let sorted_ty = Type::Variant(sorted_tags, Openness::Closed);
        let ok_tag = Self::ok();
        let sort = dispatch(
            body,
            sort_branches
                .into_iter()
                .zip(std::iter::once(&ok_tag).chain(inner.iter().map(|(t, _)| t)))
                .map(|((binder, to, payload), from)| {
                    (
                        from.clone(),
                        binder,
                        Expr::variant_ctor(to, payload).with_ty(sorted_ty.clone()),
                    )
                })
                .collect(),
            &sorted_ty,
        );
        let mut clauses = Vec::with_capacity(handlers.len());
        for h in handlers {
            let handler_ty = h.body.ty.clone();
            clauses.push((h.binding, self.elim(h.body, arms), handler_ty));
        }
        let raising = !passed.is_empty()
            || clauses
                .iter()
                .any(|(_, c, _)| matches!(c, Elim::Raising(_)));
        let result = if raising {
            Self::outcome(ty, arms)
        } else {
            ty.clone()
        };
        let finish = |e: Elim, value_ty: &Type| match e {
            Elim::Pure(v) if !raising => v,
            e => Self::lift(e, value_ty, arms),
        };
        let v = binding(Name::fresh("__value"), body_ty.clone());
        let value = finish(Elim::Pure(tvar(&v.name, body_ty.clone())), &body_ty);
        let mut run = vec![(value_tag, v, value)];
        for (j, (binder, clause, clause_ty)) in clauses.into_iter().enumerate() {
            run.push((clause_tag(j), binder, finish(clause, &clause_ty)));
        }
        for (tag, t) in &passed {
            let z = binding(Name::fresh("__exc"), t.clone());
            let pass =
                Expr::variant_ctor(tag.clone(), tvar(&z.name, t.clone())).with_ty(result.clone());
            run.push((tag.clone(), z, pass));
        }
        let run = dispatch(sort, run, &result);
        if raising {
            Elim::Raising(run)
        } else {
            Elim::Pure(run)
        }
    }
}

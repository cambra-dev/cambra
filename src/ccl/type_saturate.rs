//! Post-coalesce saturation pass for simple-sub inference.
//!
//! **This pass is a temporary architectural workaround**, not a desired
//! long-term state. It now handles only *structural* blind spots the
//! solver's single-sided variable handling leaves behind — refinements no
//! longer pass through here (they ride the lattice natively; see
//! [`crate::ccl::simple_sub`]'s `# Refinements`). What remains:
//!
//! * **Lexical Var/Let propagation** — a `Var` node adopts its binding's
//!   resolved type from scope, and a `Let` splices its bound expression's
//!   type into the binding slot and the `Let`'s own `expr.ty`.
//! * **Projection-domain specialization** (`Compose`/`Apply`) — a `Proj`'s
//!   domain coalesces under-determined (single-sided `Var <: Var`), so it is
//!   monomorphized to the value flowing in: the preceding morphism's codomain in
//!   a `Compose`, the argument at an `Apply`. This is the **closed-form** case of
//!   the same use-site specialization `monomorphize` performs for generalized
//!   `let`s (see [`crate::ccl::infer_simple_sub::specialize_projection_domain`]);
//!   it runs *here*, in Pass 4, because the input's type is only resolved by the
//!   lexical propagation above — which must follow monomorphize (Pass 3).
//!
//! Contract: given an [`Expr`] tree whose every node carries a coalesced
//! [`Type`] (some correctly-typed, some carrying placeholders from the
//! structural blind spots above), [`saturate`] rewrites types in place so
//! every node agrees with its already-resolved children and bindings.
//!
//! The pass has **no dependency** on
//! [`SimpleSubContext`](crate::ccl::infer_simple_sub): it inspects already-
//! coalesced types directly.

use crate::ccl::ccl_utils::cast_target_refinement;
use crate::ccl::infer_simple_sub::specialize_projection_domain;
use crate::ccl::{Expr, RefinementKind, Type, TypedExprNode};
use crate::util::ScopeStack;

/// Walk `expr` top-down, rewriting each node's `expr.ty` to agree with its
/// already-coalesced children and the surrounding scope.
///
/// See module docs for the per-node rule set and the soundness rationale.
pub fn saturate(expr: &mut Expr) {
    let mut scope: ScopeStack<Type> = ScopeStack::new();
    let mut guard = scope.enter_scope();
    saturate_node(expr, &mut guard);
}

fn saturate_node(expr: &mut Expr, scope: &mut ScopeStack<Type>) {
    match &mut expr.node {
        // Var: pull the binding's resolved type out of scope, if any.
        // Replaces the targeted Let → body propagation that used to live in
        // `coalesce_node` as `propagate_var_ty`; also fixes Var references
        // bound by an enclosing lambda whose param.ty was decorated with
        // refinements after coalesce.
        TypedExprNode::Var(name) => {
            if let Some(ty) = scope.lookup(name) {
                expr.ty = ty.clone();
            }
        }

        // Lambda: refinements ride the inferred type natively (see
        // `infer_simple_sub::emit_lambda` + `constrain_subtype`), so the
        // domain/`param.ty` already carry their refinement tags out of
        // coalesce; saturate leaves them untouched. It still recurses —
        // to run the Var/Let lexical-propagation rules inside the body and
        // to saturate the predicate — binding `param` under the bare
        // (refinement-stripped) domain so `Var(param)` body references see
        // the unrefined value, matching how the body was bound at emit time.
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // The predicate is itself a CCL expression inferred during
            // emission; saturate it in a fresh isolated scope (its free
            // variables are not the surrounding lexical scope).
            if let Some(r) = refinement {
                let RefinementKind::Predicate(def) = &r.kind;
                if let Ok(mut pred) = def.try_borrow_mut() {
                    let mut pred_scope: ScopeStack<Type> = ScopeStack::new();
                    let mut pred_guard = pred_scope.enter_scope();
                    saturate_node(&mut pred, &mut pred_guard);
                }
            }

            let inner_dom: Type = match &expr.ty {
                // Bind the param under the *refined* domain so `Var(param)` body
                // references see the refinement the lambda's domain carries —
                // a body use that flows the param into a refined-domain consumer
                // (e.g. indexing a filtered collection) must itself be refined,
                // or the post-inference check rejects `unrefined ⊀ refined`.
                Type::Fun(d, _) => (**d).clone(),
                // Not a Fun — leave the node alone. Lambdas should always
                // coalesce to Fun, but if they didn't there's nothing
                // useful for us to do.
                _ => return,
            };
            let mut body_guard = scope.enter_scope();
            body_guard.bind(&param.name, inner_dom);
            saturate_node(body, &mut body_guard);
        }

        // Let: settle bound_expr first, push `binding.name` → resolved type
        // into scope, then settle body. The Let's own ty mirrors the body's
        // resolved ty.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            saturate_node(bound_expr, scope);
            binding.ty = bound_expr.ty.clone();
            let mut body_guard = scope.enter_scope();
            body_guard.bind(&binding.name, binding.ty.clone());
            saturate_node(body, &mut body_guard);
            drop(body_guard);
            expr.ty = body.ty.clone();
        }

        // Generic recursion for everything else. `expr.ty` was set by
        // coalesce and we don't touch it.
        TypedExprNode::Lit(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            saturate_node(function, scope);
            saturate_node(argument, scope);
            // A projection applied to a (now lexically-resolved) argument:
            // monomorphize its domain to the argument flowing in — the closed-form
            // use-site specialization, the structural replacement for the
            // emit-time reverse `domain <: arg` that `constrain_argument` dropped.
            specialize_projection_domain(function, &argument.ty);
        }
        // `value` is the saturated expression child. The cast `target`'s
        // refinement predicate (a `λ restr → ...` filter — e.g. a join
        // condition) is its own expression tree, not reached by the main walk,
        // so its projections' domains stay under-determined. Saturate it in an
        // isolated scope (its free variable is the predicate binder, not the
        // surrounding lexical scope) so its `Proj` recoveries fire, exactly as
        // for a `Lambda`'s own refinement above.
        TypedExprNode::Cast { value, target } => {
            saturate_node(value, scope);
            if let Some(r) = cast_target_refinement(target) {
                let RefinementKind::Predicate(def) = &r.kind;
                if let Ok(mut pred) = def.try_borrow_mut() {
                    let mut pred_scope: ScopeStack<Type> = ScopeStack::new();
                    let mut pred_guard = pred_scope.enter_scope();
                    saturate_node(&mut pred, &mut pred_guard);
                }
            }
        }
        TypedExprNode::BinOp { left, right, .. } => {
            saturate_node(left, scope);
            saturate_node(right, scope);
        }
        TypedExprNode::UnaryOp(_, inner) => saturate_node(inner, scope),
        TypedExprNode::Aggregate { input, .. } => saturate_node(input, scope),
        // CollectionUnion no longer needs a type-reconstruction arm:
        // `emit_collection_union` now emits a proper `Fun(Variant, _)`
        // shape directly, so coalesce already produces the correct
        // `expr.ty`. We only recurse to saturate the operands.
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::CollectionUnion(elts) => {
            for e in elts.iter_mut() {
                saturate_node(e, scope);
            }
        }
        // Compose: recurse for lexical (Var/Let) propagation, then monomorphize
        // each non-leading `Proj`'s domain to the preceding morphism's codomain
        // (the record/tuple flowing in) and rebuild the chain's own
        // `Fun(first.domain, last.codomain)` type. simple-sub's single-sided
        // `Var <: Var` rule leaves both under-determined; downstream operator
        // conversion demands a concrete domain. The per-`Proj` recovery is the
        // closed-form use-site specialization shared with the `Apply` arm — and
        // the closed-form sibling of `monomorphize`'s `specialize_def`.
        TypedExprNode::Compose(elts) => {
            for e in elts.iter_mut() {
                saturate_node(e, scope);
            }
            for i in 1..elts.len() {
                let prev_cod = match &elts[i - 1].ty {
                    Type::Fun(_, cod) => (**cod).clone(),
                    _ => continue,
                };
                specialize_projection_domain(&mut elts[i], &prev_cod);
            }
            if let (Some(first), Some(last)) = (elts.first(), elts.last())
                && let (Type::Fun(first_dom, _), Type::Fun(_, last_cod)) = (&first.ty, &last.ty)
            {
                expr.ty = Type::Fun(first_dom.clone(), last_cod.clone());
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                saturate_node(e, scope);
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                saturate_node(s, scope);
            }
            for b in branches.iter_mut() {
                // A structural pattern binds its payload over the branch's
                // guard and body; guard-only branches add nothing to scope.
                let mut arm_scope = scope.enter_scope();
                if let Some(p) = &b.pattern {
                    arm_scope.bind(&p.binding.name, p.binding.ty.clone());
                }
                saturate_node(&mut b.guard, &mut arm_scope);
                saturate_node(&mut b.body, &mut arm_scope);
            }
        }
        TypedExprNode::VariantCtor { payload, .. } => saturate_node(payload, scope),
        TypedExprNode::ExprStmt { expr: e, body } => {
            saturate_node(e, scope);
            saturate_node(body, scope);
        }
        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so saturation never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached saturation: {:?}",
                expr.node
            )
        }
        TypedExprNode::Loop { .. } => {
            expr.walk_children_mut(|e| saturate_node(e, scope));
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::simple_sub::FieldKey;
    use crate::ccl::{BaseType, Lit, TypedBinding, TypedExpr};

    /// Verify rule (b): `Let` with a complex-typed bound expression
    /// propagates that type to `Var(x)` references in the body and to
    /// the Let's own `ty`. Pre-set the bound expression's type
    /// directly — saturate's job is to splice it through, not to
    /// (re)construct it. (Previously the bound expression was a
    /// `BinOp(CollectionUnion)` and saturate had a dedicated arm to
    /// build the Union shape; that arm is gone now since inference
    /// produces the right shape directly.)
    #[test]
    fn let_propagates_bound_type_to_var() {
        let int_ty = Type::Base(BaseType::Int);
        let union_fun = Type::fun(
            Type::Variant(vec![
                (FieldKey::Index(0), int_ty.clone()),
                (FieldKey::Index(1), int_ty.clone()),
            ]),
            int_ty.clone(),
        );
        let bound = TypedExpr::new(TypedExprNode::Lit(Lit::Unit)).with_ty(union_fun.clone());
        let var_x = TypedExpr::new(TypedExprNode::Var("x".into())).with_ty(Type::Hole);
        let mut expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(bound),
            body: Box::new(var_x),
        });

        saturate(&mut expr);

        if let TypedExprNode::Let { body, binding, .. } = &expr.node {
            assert_eq!(binding.ty, union_fun);
            assert_eq!(body.ty, union_fun);
        } else {
            panic!("expected Let");
        }
        assert_eq!(expr.ty, union_fun);
    }

    // Note: refinement propagation onto a lambda domain is now done
    // natively by the solver, not by `saturate`. The former
    // `lambda_picks_up_body_usage_refinement_from_param_apply` test moved to
    // `tests/type_check.rs` as an `infer`-level test.

    /// Verify rule (c): an inner lambda re-binding the outer name stops
    /// Var-propagation from the enclosing Let.
    #[test]
    fn shadowing_inner_lambda_stops_var_propagation() {
        let int_ty = Type::Base(BaseType::Int);
        let union_fun_ty = Type::fun(
            Type::Variant(vec![
                (FieldKey::Index(0), int_ty.clone()),
                (FieldKey::Index(1), int_ty.clone()),
            ]),
            int_ty.clone(),
        );
        // Build a Let whose bound_expr resolves to `union_fun_ty` and whose
        // body is `\x. x` — the inner lambda shadows the outer let-binding.
        let inner_lambda = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: int_ty.clone(),
                user_annotation: None,
            },
            // The inner Var("x") was already coalesced as Int (it refers to
            // the lambda's own param, not the let-binding's "x").
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into())).with_ty(int_ty.clone())),
            refinement: None,
        })
        .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        // Pre-set the bound expression's type to the union shape
        // directly; saturate propagates it to the let binding without
        // needing the (removed) `BinOp(CollectionUnion)` reconstruct arm.
        let bound = TypedExpr::new(TypedExprNode::Lit(Lit::Unit)).with_ty(union_fun_ty.clone());
        let mut expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(bound),
            body: Box::new(inner_lambda),
        });

        saturate(&mut expr);

        // Outer binding sees the union; inner lambda still has Int -> Int;
        // the inner Var("x") inside the lambda body keeps its Int type
        // because the inner lambda's param shadowed the let-binding's name.
        if let TypedExprNode::Let { binding, body, .. } = &expr.node {
            assert_eq!(binding.ty, union_fun_ty);
            assert_eq!(body.ty, Type::fun(int_ty.clone(), int_ty.clone()));
            if let TypedExprNode::Lambda {
                body: inner_body, ..
            } = &body.node
            {
                assert_eq!(inner_body.ty, int_ty);
            } else {
                panic!("expected inner Lambda");
            }
        } else {
            panic!("expected Let");
        }
    }
}

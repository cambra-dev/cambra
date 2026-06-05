//! Post-coalesce saturation pass for simple-sub inference.
//!
//! **This pass is a temporary architectural workaround**, not a desired
//! long-term state. Tagged variants are now handled structurally inside the
//! lattice; the remaining goal is to eliminate this pass once the type system
//! also handles refinements directly (a future SMT-backed refinement pass).
//! Until then it consolidates all lattice-blindspot fixes in one place
//! so they are easy to find and remove together.
//!
//! Simple-sub's structural lattice is
//! intentionally **refinement-blind** (plan R1): the solver tracks structural
//! shapes only, so refinement predicates cannot ride along inside it.
//! (Tagged sums *are* structural and live in the lattice as
//! `Type::Variant`, so — unlike in earlier stages — collection-union
//! results no longer need fixing up here.) A couple of typing rules
//! (Refinement Propagation, Let Binding Resolution) still require
//! refinement/lexical-scope information to appear on `expr.ty` slots after
//! coalescing. Rather than smuggle them through the structural lattice, we run a
//! separate top-down pass that walks the already-coalesced tree with a
//! lexical scope environment and rewrites each affected node's `expr.ty`
//! based on its children's resolved types and the surrounding bindings.
//!
//! Contract: given an [`Expr`] tree whose every node carries a coalesced
//! [`Type`] (some correctly-typed, some carrying placeholders from
//! lattice-blind paths), [`saturate`] rewrites types in place so that
//! every node agrees with its already-resolved children and bindings.
//!
//! The pass has **no dependency** on [`SimpleSubContext`](crate::ccl::infer_simple_sub):
//! the sidecar refinement wrap (`ctx.refinements`) is applied inside
//! `coalesce_node` *before* this pass runs, so saturation inspects domain
//! types directly (looking for outer [`Type::Refinement`] wrappers) rather
//! than consulting any sidecar. Sidecar reads stay local to
//! `infer_simple_sub.rs`.

use crate::ccl::{Expr, Refinement, Type, TypedExprNode};
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

        // Lambda: Refinement Propagation — stitch refinements collected from
        // body usage into the domain, and splice the body's resolved type
        // into the codomain.
        //
        // The domain currently carries (after coalesce + sidecar wrap):
        //   - optional outer `Refinement(_, own_ref)` from the lambda's own
        //     sidecar refinement (sidecar wrap happened in coalesce_node);
        //   - inner: the solver-coalesced parameter shape.
        // We collect refinements coming from how the body USES `param`
        // (i.e. `Apply { function: f, argument: Var(param) }` where `f.ty`
        // is `Fun(Refinement(_, r), _)`) and wrap them inside the own_ref
        // layer so the final shape mirrors HM's nested
        // `Refinement(Refinement(inner, body_ref_n)…body_ref_1, own_ref)`.
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            // The refinement's predicate is itself a CCL expression that
            // was inferred during constraint emission; saturate it too so
            // its inner lambdas get the same body-splice / param.ty fix
            // that the surrounding tree does. Mirrors the predicate walk
            // in `coalesce_node`. The predicate's own free variables
            // shouldn't pick up the outer scope (they are bound either
            // inside the predicate or by a different mechanism), so we
            // recurse with a fresh, isolated scope.
            if let Some(r) = refinement {
                let crate::ccl::RefinementKind::Predicate(def) = &r.kind;
                if let Ok(mut pred) = def.try_borrow_mut() {
                    let mut pred_scope: ScopeStack<Type> = ScopeStack::new();
                    let mut pred_guard = pred_scope.enter_scope();
                    saturate_node(&mut pred, &mut pred_guard);
                }
            }

            // Read the lambda's own refinement off the AST node, not off
            // the inferred type's domain. (Coalesce no longer wraps
            // `Type::Refinement` around the domain; the refinement lives
            // on `Expr::Lambda.refinement` and `lambda_elim` adds the
            // wrap when it desugars a refined lambda.)
            let own_ref_opt: Option<Refinement> = refinement.clone();
            let inner_dom: Type = match &expr.ty {
                Type::Fun(d, _) => (**d).clone(),
                // Not a Fun — leave the node alone. Lambdas should always
                // coalesce to Fun, but if they didn't there's nothing
                // useful for us to do.
                _ => return,
            };

            // Bind `param` in scope using the *innermost* shape (no
            // refinement layers). Var(param) inside the body is the
            // solver-coalesced reference; matching `inner_dom` keeps
            // us consistent with what coalesce would already have written
            // there. The lambda's outer refinement decoration applies at
            // the function boundary, not at every reference.
            let mut body_guard = scope.enter_scope();
            body_guard.bind(&param.name, inner_dom.clone());
            saturate_node(body, &mut body_guard);
            drop(body_guard);

            // Now that the body is saturated, collect refinements from
            // how the body uses `param`.
            let mut usage_refs = Vec::new();
            collect_param_refinements(body, &param.name, &mut usage_refs);

            // Wrap inner_dom with usage refinements (innermost first), then
            // re-apply own_ref as the outermost layer.
            let mut stitched_inner = inner_dom;
            for r in usage_refs {
                stitched_inner = Type::Refinement(Box::new(stitched_inner), r);
            }
            let new_domain = match own_ref_opt {
                Some(r) => Type::Refinement(Box::new(stitched_inner.clone()), r),
                None => stitched_inner.clone(),
            };

            param.ty = stitched_inner;
            expr.ty = Type::Fun(Box::new(new_domain), Box::new(body.ty.clone()));
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
        // Compose: rebuild `expr.ty` as `Fun(first.domain, last.codomain)`
        // from the saturated children. simple-sub's coalesce can emit
        // `Fun(?, ?)` here because `constrain_subtype`'s Var <: Var rule is
        // single-sided (see `simple_sub.rs` Var arms, mirroring
        // upstream `Typer.scala`): a fresh negative-position var only
        // receives one bound side and compacts to `Type::Infer`. The
        // post-coalesce typecheck (`check_compose_types`) reconstructs
        // the same shape we materialise here.
        TypedExprNode::Compose(elts) => {
            for e in elts.iter_mut() {
                saturate_node(e, scope);
            }
            // simple-sub coalesces each `Proj` morphism independently, so its
            // domain captures only the field it touches — an open record-var
            // that never closed to a concrete shape (it coalesces to an
            // under-determined `Type::Infer`, or a record whose other fields
            // are `Infer`). Downstream passes (operator conversion) demand a
            // concrete domain;
            // replace each `Proj`'s domain with the preceding morphism's
            // codomain, which is the actual record/tuple flowing in.
            // The Proj's codomain still describes the field it extracts.
            for i in 1..elts.len() {
                let prev_cod = match &elts[i - 1].ty {
                    Type::Fun(_, cod) => (**cod).clone(),
                    _ => continue,
                };
                if matches!(&elts[i].node, TypedExprNode::Proj(_))
                    && let Type::Fun(_, cod) = &elts[i].ty
                {
                    let cod = (**cod).clone();
                    elts[i].ty = Type::Fun(Box::new(prev_cod), Box::new(cod));
                }
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

/// Walk `body` looking for `Apply { function: f, argument: Var(param_name) }`
/// nodes where `f.ty` is `Fun(Refinement(_, r), _)`; push each such `r` onto
/// `out`. Stops at inner shadowing (a nested lambda/let that re-binds
/// `param_name`).
///
/// Mirrors the previous in-tree walker in `infer_simple_sub.rs`. The
/// the solver's lattice carries structural shapes only, so refinements that
/// flow through `param` via callee domains cannot be observed without an
/// AST-level walk like this one.
fn collect_param_refinements(body: &Expr, param_name: &str, out: &mut Vec<Refinement>) {
    match &body.node {
        TypedExprNode::Apply { function, argument } => {
            if let TypedExprNode::Var(name) = &argument.node
                && name == param_name
                && let Type::Fun(domain, _) = &function.ty
            {
                let mut d: &Type = domain;
                while let Type::Refinement(inner, r) = d {
                    out.push(r.clone());
                    d = inner;
                }
            }
            collect_param_refinements(function, param_name, out);
            collect_param_refinements(argument, param_name, out);
        }
        TypedExprNode::Lambda { param, body, .. } => {
            if param.name != param_name {
                collect_param_refinements(body, param_name, out);
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_param_refinements(bound_expr, param_name, out);
            if binding.name != param_name {
                collect_param_refinements(body, param_name, out);
            }
        }
        TypedExprNode::BinOp { left, right, .. } => {
            collect_param_refinements(left, param_name, out);
            collect_param_refinements(right, param_name, out);
        }
        TypedExprNode::UnaryOp(_, inner) => collect_param_refinements(inner, param_name, out),
        TypedExprNode::Aggregate { input, .. } => collect_param_refinements(input, param_name, out),
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::Compose(elts)
        | TypedExprNode::CollectionUnion(elts) => {
            for e in elts {
                collect_param_refinements(e, param_name, out);
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs {
                collect_param_refinements(e, param_name, out);
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_param_refinements(s, param_name, out);
            }
            for b in branches {
                // A pattern that binds `param_name` shadows it inside the
                // branch, so don't collect refinements from there.
                if b.pattern
                    .as_ref()
                    .is_some_and(|p| p.binding.name == param_name)
                {
                    continue;
                }
                collect_param_refinements(&b.guard, param_name, out);
                collect_param_refinements(&b.body, param_name, out);
            }
        }
        TypedExprNode::VariantCtor { payload, .. } => {
            collect_param_refinements(payload, param_name, out);
        }
        TypedExprNode::ExprStmt { expr, body } => {
            collect_param_refinements(expr, param_name, out);
            collect_param_refinements(body, param_name, out);
        }
        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so this walker never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached collect_param_refinements: {:?}",
                body.node
            )
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Loop { .. } => {}

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::simple_sub::FieldKey;
    use crate::ccl::{BaseType, Lit, RefinementKind, TypedBinding, TypedExpr, next_refinement_id};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn lit_int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n)).with_ty(Type::Base(BaseType::Int))
    }

    fn make_refinement(desc: &str) -> Refinement {
        Refinement {
            id: next_refinement_id(),
            description: desc.into(),
            kind: RefinementKind::Predicate(Rc::new(RefCell::new(lit_int(0)))),
        }
    }

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

    /// Verify rule (a): a lambda whose body applies a refined callee to its
    /// own param picks up the callee's domain refinement via Refinement
    /// Propagation on the outer param's domain.
    #[test]
    fn lambda_picks_up_body_usage_refinement_from_param_apply() {
        let int_ty = Type::Base(BaseType::Int);
        let r = make_refinement("body_ref");
        // callee : Fun(Refinement(Int, r), Int)
        let callee_ty = Type::fun(
            Type::Refinement(Box::new(int_ty.clone()), r.clone()),
            int_ty.clone(),
        );
        let callee = TypedExpr::new(TypedExprNode::Var("g".into())).with_ty(callee_ty.clone());
        let arg = TypedExpr::new(TypedExprNode::Var("x".into())).with_ty(int_ty.clone());
        let apply = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(callee),
            argument: Box::new(arg),
        })
        .with_ty(int_ty.clone());
        // outer lambda: \x. g(x) — pre-saturate ty = Fun(Int, ?cod)
        let mut expr = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: int_ty.clone(),
                user_annotation: None,
            },
            body: Box::new(apply),
            refinement: None,
        })
        .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));

        saturate(&mut expr);

        let expected_dom = Type::Refinement(Box::new(int_ty.clone()), r);
        let expected_ty = Type::fun(expected_dom.clone(), int_ty);
        assert_eq!(expr.ty, expected_ty);
        if let TypedExprNode::Lambda { param, .. } = &expr.node {
            assert_eq!(param.ty, expected_dom);
        } else {
            panic!("expected Lambda");
        }
    }

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

//! Post-coalesce saturation pass for simple-sub inference.
//!
//! **This pass is a temporary architectural workaround**, not a desired
//! long-term state. The goal is to eliminate it once the type system handles
//! refinements and unions directly (Stage 2 variants + Stage 3 SMT
//! refinements). Until then it consolidates all `SimpleType`-blindspot fixes
//! in one place so they are easy to find and remove together.
//!
//! Simple-sub's [`SimpleType`](crate::ccl::simple_sub::SimpleType) lattice is
//! intentionally **refinement-blind** and **Union-blind** (plan R1, R5): the
//! solver's lattice tracks structural shapes only, so refinements and
//! tagged unions cannot ride along inside it. Most CCL programs do not need
//! either feature inside the lattice — but a handful of typing rules
//! (Refinement Propagation, Let Binding Resolution,
//! `BinOp::CollectionUnion`'s structural Union result) require those shapes
//! to appear on `expr.ty` slots after
//! coalescing. Rather than smuggle them through `SimpleType`, we run a
//! separate top-down pass that walks the already-coalesced tree with a
//! lexical scope environment and rewrites each affected node's `expr.ty`
//! based on its children's resolved types and the surrounding bindings.
//!
//! Contract: given an [`Expr`] tree whose every node carries a coalesced
//! [`Type`] (some correctly-typed, some carrying placeholders from
//! SimpleType-blind paths), [`saturate`] rewrites types in place so that
//! every node agrees with its already-resolved children and bindings.
//!
//! The pass has **no dependency** on [`SimpleSubContext`](crate::ccl::infer_simple_sub):
//! the sidecar refinement wrap (`ctx.refinements`) is applied inside
//! `coalesce_node` *before* this pass runs, so saturation inspects domain
//! types directly (looking for outer [`Type::Refinement`] wrappers) rather
//! than consulting any sidecar. Sidecar reads stay local to
//! `infer_simple_sub.rs`.

use crate::ccl::{Branch, Expr, Refinement, Type, TypedExprNode};
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
        //   - inner: the SimpleType-coalesced parameter shape.
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
            // SimpleType-coalesced reference; matching `inner_dom` keeps
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

        // `++` (CollectionUnion): rebuild the result as
        // `Fun(Union(dom_0, …, dom_n), dedup_union(cod_0, …, cod_n))` from
        // the operands' already-resolved Fun types. Simple-sub's coalesce
        // path can only see structural shapes and emits a `Fun(?dom, ?cod)`
        // from fresh vars (see `emit_collection_union`); this rule
        // materialises the proper Union shape after the fact. Stage 2's
        // `Variant` rule subsumes it once tagged variants land.
        TypedExprNode::CollectionUnion(operands) => {
            for op in operands.iter_mut() {
                saturate_node(op, scope);
            }
            // Only materialise when every operand coalesced to a Fun; if any
            // didn't, leave the generic coalesce result alone and let
            // downstream surface a diagnostic.
            if operands.iter().all(|op| matches!(op.ty, Type::Fun(_, _))) {
                let mut domains = Vec::with_capacity(operands.len());
                let mut codomain: Option<Type> = None;
                for op in operands.iter() {
                    let Type::Fun(dom, cod) = &op.ty else {
                        unreachable!("all-Fun checked above");
                    };
                    domains.push((**dom).clone());
                    codomain = Some(match codomain {
                        Some(acc) => dedup_union(acc, (**cod).clone()),
                        None => (**cod).clone(),
                    });
                }
                let codomain = codomain.expect("CollectionUnion has >= 2 operands");
                expr.ty = Type::Fun(Box::new(Type::Union(domains)), Box::new(codomain));
            }
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
        TypedExprNode::List(elts) | TypedExprNode::Tuple(elts) => {
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
            // domain captures only the field it touches — i.e. a `PartialTuple`
            // or a `Record` containing a `PartialTuple`/`PartialRecord` value.
            // Downstream passes (operator conversion) demand a concrete domain;
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
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches.iter_mut() {
                saturate_node(guard, scope);
                saturate_node(body, scope);
            }
        }
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
/// SimpleType graph carries structural shapes only, so refinements that
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
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches {
                collect_param_refinements(guard, param_name, out);
                collect_param_refinements(body, param_name, out);
            }
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

/// Flatten and deduplicate two types into a single [`Type::Union`].
///
/// Collapses adjacent `Type::Union` variants and removes structural
/// duplicates so `Int @ Int @ Int`'s codomain stays a single `Int`
/// rather than nesting `Union(Union(Int, Int), Int)`. Returns the lone
/// variant directly when only one survives.
fn dedup_union(a: Type, b: Type) -> Type {
    fn flatten(ty: Type, out: &mut Vec<Type>) {
        match ty {
            Type::Union(ts) => {
                for t in ts {
                    flatten(t, out);
                }
            }
            other => out.push(other),
        }
    }
    let mut variants = Vec::new();
    flatten(a, &mut variants);
    flatten(b, &mut variants);
    let mut seen: Vec<Type> = Vec::new();
    variants.retain(|v| {
        if seen.contains(v) {
            false
        } else {
            seen.push(v.clone());
            true
        }
    });
    if variants.len() == 1 {
        variants.remove(0)
    } else {
        Type::Union(variants)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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

    /// Verify rule (b): `Let` with a `CollectionUnion`-built `Fun(Union, …)`
    /// bound to a name, `Var` of that name in the body picks up the union.
    #[test]
    fn let_propagates_collection_union_type_to_var() {
        // post-coalesce shape:
        //   Let { x = (left @ right : Fun(?d, ?c))
        //         body = x : Fun(?d, ?c) }
        // expected: Var x.ty = Fun(Union(Int, Int), Int); Let.ty = same.
        let int_ty = Type::Base(BaseType::Int);
        let coll_l = TypedExpr::new(TypedExprNode::Lit(Lit::Unit))
            .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        let coll_r = TypedExpr::new(TypedExprNode::Lit(Lit::Unit))
            .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        let union = TypedExpr::new(TypedExprNode::CollectionUnion(vec![coll_l, coll_r]));
        let var_x = TypedExpr::new(TypedExprNode::Var("x".into()))
            .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        let mut expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(union),
            body: Box::new(var_x),
        });

        saturate(&mut expr);

        let expected_union_fun = Type::fun(
            Type::Union(vec![int_ty.clone(), int_ty.clone()]),
            int_ty.clone(),
        );
        // Let's body Var(x) picks up the resolved union shape.
        if let TypedExprNode::Let { body, binding, .. } = &expr.node {
            assert_eq!(binding.ty, expected_union_fun);
            assert_eq!(body.ty, expected_union_fun);
        } else {
            panic!("expected Let");
        }
        assert_eq!(expr.ty, expected_union_fun);
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
            Type::Union(vec![int_ty.clone(), int_ty.clone()]),
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
        // Mock a CollectionUnion-built bound expression so the outer
        // let-binding ends up with the union type after saturation.
        let coll_l = TypedExpr::new(TypedExprNode::Lit(Lit::Unit))
            .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        let coll_r = TypedExpr::new(TypedExprNode::Lit(Lit::Unit))
            .with_ty(Type::fun(int_ty.clone(), int_ty.clone()));
        let union = TypedExpr::new(TypedExprNode::CollectionUnion(vec![coll_l, coll_r]));
        let mut expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(union),
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

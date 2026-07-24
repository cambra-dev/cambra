//! Iteration-site planning (design §6.5).
//!
//! [`run`] is the pass entry point: it runs after `lambda_elim` and produces
//! the CCL that operator conversion will see. The work is split across
//! submodules:
//!
//! - [`predicates`] — refinement-predicate compilation (the lambda-elim →
//!   simplify sub-pipeline run on each predicate).
//! - [`groupby`] — the pointful group-by recognizer/rewrite.
//! - [`iterate`] — the iteration-site materialisation walk
//!   ([`iterate::insert_iterate_markers`]) and its per-site strategy dispatch.
//! - [`join`] — the hash/loop-join cluster (the specialised iteration
//!   strategy folded into the walk).
//!
//! Hash-join planning is just one *specialised* strategy folded in at a site,
//! not the whole job (hence `planning`, not `join_plan`).

use log::trace;

use crate::ccl::ccl_utils::{
    self, apply_function, make_iterate, make_restrict, refine_codomain, set_codomain,
    trivially_true_predicate, typed_compose,
};
// Re-exported so the `planning` submodules (`groupby`, `join`) can keep calling
// `is_builtin` unqualified through their `use super::*`.
pub(super) use crate::ccl::ccl_utils::is_builtin;
use crate::ccl::{
    BaseType, BinOpKind, Builtin, CompareKind, Expr, Lit, LogicKind, Name, ProjKey, Type,
    TypedExprNode,
    ccl_utils::apply_primitive,
    infer::typecheck,
    lambda_elim::{self, compose, id},
    simplify::simplify,
    symbolic::{symbolic, symbolic_typed},
};

mod groupby;
mod iterate;
mod join;
mod loops;
mod predicates;

// Preserve the `crate::ccl::planning::…` paths that other modules' doc-comments
// and prose reference (design docs link `insert_iterate_markers`; `ccl_utils` /
// `simplify` / `lambda_elim` mention `compile_refinement_predicates` and
// `fn_of_bare_predicate`). `run` calls the first two through these re-exports;
// `fn_of_bare_predicate` is only reached from `iterate`/`predicates`'s own
// imports today, so its re-export exists purely to keep the documented path
// resolvable — hence the `allow`.
pub(crate) use iterate::insert_iterate_markers;
pub(crate) use loops::plan_loops;
pub(crate) use predicates::compile_refinement_predicates;
#[allow(unused_imports)]
pub(crate) use predicates::fn_of_bare_predicate;

/// Materialize every iteration site in the post-lambda-elim CCL, choosing
/// an efficient implementation strategy at each one.
///
/// At each iteration site (aggregate arguments, mutation-loop sources,
/// `FinalOrDefault` streams, value-position `Record` fields, `CollectionUnion`
/// operands, the program's top-level function-valued result, top-level
/// let-bound function values, and a few other shapes enumerated by
/// [`iterate::insert_iterate_recurse`]), [`iterate::insert_iterate_markers`]
/// dispatches via [`iterate::wrap_with_iterate`] to:
///
/// 1. **Hash-join rewrite** ([`join::try_hash_join_rewrite`]) when the site's
///    domain is a refined tuple whose predicate decomposes into equality
///    join conditions.  Emitted as a `JoinPlan::Hash` / `JoinPlan::Loop`
///    tree compiled to a CCL chain whose leaves are iteration-bearing.
/// 2. **Iterate-then-restricts chain** otherwise — build the source by
///    *applying* one `restrict(p)` filter per refinement layer (innermost
///    first) to a chain-head `Apply(true ▷ const, Iterate)`, then compose
///    the value-producing body onto it: `(iterate ▷ (p_inner ▷ restrict)
///    ▷ … ▷ (p_outer ▷ restrict)) ≫ body`.  Each `restrict` *applies* to
///    its upstream — it is a function transformer, not a morphism composed
///    with the source (its honest type makes the composed form ill-typed;
///    see [`make_restrict`]).  Unrefined sites get just the chain-head
///    iterate.
///
/// Hash join is the specialised strategy; the iterate-then-restricts
/// chain is the default.  Both branches are materialising the same
/// iteration site — folding them into a single walk lets hash-join
/// planning fire at every site (not just the program root, as an earlier
/// pass did).
///
/// Also: the pointful group-by rewrite for keyed aggregates
/// ([`groupby::recognize_groupby_sites`], via `groupby::convert_groupby_pointful`)
/// runs before the materialisation walk.
pub fn run(mut expr: Expr) -> Expr {
    // Refinement predicates travel through inference and lambda-elim as bare
    // expressions over the implicit `REFINEMENT_BINDER` (design §6.3) and are
    // compiled to point-free form only when a refined type is iterated (§6.5).
    // The group-by recognizer runs first and matches the bare predicate
    // directly; the generic filter / hash-join paths compile the predicate
    // lazily at each iteration site (see `wrap_with_iterate`).
    groupby::recognize_groupby_sites(&mut expr);
    let mut expr = simplify(expr);
    insert_iterate_markers(&mut expr);
    // Normalize every remaining bare predicate tree-wide to point-free form.
    // `wrap_with_iterate` compiles each iteration *site*'s predicate, but a
    // refinement also rides **consumer contracts** that sit outside any site —
    // an aggregate's domain (`sum : ({D | p} ⇒ Int) ⇒ Int`), a composition
    // adjacency — carrying the same predicate as the producer they validate
    // against. With immutable predicate terms those are independent `Rc`s, so
    // the per-site compilation doesn't reach them; this whole-tree pass (one
    // shared memo) compiles them to the *same* point-free form, so the
    // post-planning typecheck's structural refinement match holds. It runs
    // after the recognizers (which already consumed the bare shapes they
    // match) and is idempotent on already-compiled predicates.
    compile_refinement_predicates(&mut expr, &mut predicates::PredMemo::new());
    // Re-run `simplify` to absorb the `id` leaves and nested `Compose`
    // boilerplate that [`join::try_hash_join_rewrite`] emits via
    // [`replace_tuple_project_with_id`].  `simplify` is marker-aware: its
    // structural-discard rules self-guard against dropping or relocating
    // the `Apply(_, Iterate)` / `Apply(_, Restrict)` markers just inserted,
    // so the only rules that fire here are the always-safe cleanups (plus
    // any reduction of a fully marker-free sub-tree, which is sound).
    let mut expr = simplify(expr);
    // Compilation rebuilt the immutable predicate on each node's `expr.ty`;
    // re-sync every `Cast`'s `target` slot so the post-planning typecheck's
    // reconstruction (which reads `target`) matches the compiled recorded type.
    ccl_utils::sync_cast_targets(&mut expr);
    // Live cross-endpoint reads are recognized earlier, in
    // `transact_phase::rewrite_live_reads` (pre-lambda-elim), so by here every
    // such read is already an `as_of` join — nothing to do at planning time.
    expr
}

/// Is `e` a bare `Var` other than the element binder (the free key binder)?
pub(super) fn is_free_var(e: &Expr) -> bool {
    matches!(&e.node, TypedExprNode::Var(n) if !n.is_elem())
}

// Returns whether the given expression is a constant, or a function of a constant.
pub(super) fn is_constant(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Apply { function, .. } if is_builtin(function, Builtin::Const) => true,
        TypedExprNode::Compose(elts) => elts.first().is_some_and(is_constant),
        _ => false,
    }
}

// Replaces the domain type of a constant expression with a new domain type.
// Requires `is_constant(expr)` to be true.
pub(super) fn replace_constant_domain_type(expr: &mut Expr, ty: &Type) {
    set_domain_ty(&mut expr.ty, ty);
    match &mut expr.node {
        TypedExprNode::Apply { .. } => {
            let output_ty = expr.ty.clone();
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(is_builtin(function, Builtin::Const));
                argument.clone()
            } else {
                unreachable!()
            };

            *expr = apply_primitive(*arg, Builtin::Const, output_ty)
        }
        TypedExprNode::Compose(elts) => {
            if let Some(e) = elts.first_mut() {
                replace_constant_domain_type(e, ty);
            }
        }
        _ => unreachable!(),
    };
}

// Returns whether the given expression relies only on a single arm of its input tuple type,
// and returns the index of that arm if so.
pub(super) fn is_function_of_single_tuple_arm(expr: &Expr) -> Option<usize> {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => Some(*i),
        TypedExprNode::Compose(elts) => elts.first().and_then(is_function_of_single_tuple_arm),
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            is_function_of_single_tuple_arm(argument)
        }
        TypedExprNode::Tuple(elts) => {
            let mut result = None;
            for elt in elts.iter() {
                if is_constant(elt) {
                    continue;
                }
                {
                    let idx = is_function_of_single_tuple_arm(elt)?;
                    if result.is_some_and(|x| x != idx) {
                        return None;
                    }
                    result = Some(idx);
                }
            }
            result
        }
        _ => None,
    }
}

pub(super) fn set_domain_ty(fun_ty: &mut Type, ty: &Type) {
    match fun_ty {
        Type::Fun { domain, .. } => {
            **domain = ty.clone();
        }
        _ => panic!("Not function type: {}", fun_ty),
    }
}

// Converts an expression that only reads a single arm of its input
// (as determined by is_function_of_single_tuple_arm) to a function
// of just that arm.
pub(super) fn replace_tuple_project_with_id(expr: &mut Expr, ty: &Type) {
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(_)) => {
            *expr = id().with_ty(Type::fun(ty.clone(), ty.clone()))
        }
        TypedExprNode::Compose(_) => {
            set_domain_ty(&mut expr.ty, ty);
            if let TypedExprNode::Compose(elts) = &mut expr.node
                && let Some(first) = elts.first_mut()
            {
                replace_tuple_project_with_id(first, ty);
            }
        }
        TypedExprNode::Apply { .. } => {
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, ty);
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(is_builtin(function, Builtin::Zip));
                replace_tuple_project_with_id(argument, ty);
                argument.clone()
            } else {
                unreachable!()
            };
            *expr = apply_primitive(*arg, Builtin::Zip, output_ty);
        }
        TypedExprNode::Tuple(_) => {
            if let Type::Tuple(elts) = &mut expr.ty {
                elts.iter_mut().for_each(|elt| match elt {
                    Type::Fun { domain, .. } => {
                        **domain = ty.clone();
                    }
                    _ => panic!(),
                });
            }
            if let TypedExprNode::Tuple(elts) = &mut expr.node {
                for elt in elts.iter_mut() {
                    if is_constant(elt) {
                        replace_constant_domain_type(elt, ty);
                    } else {
                        replace_tuple_project_with_id(elt, ty);
                    }
                }
            }
        }
        _ => {}
    };
}

/// Shared test constructors and shape-inspection helpers for the `planning`
/// submodule test suites. Each submodule's inline `tests` imports what it needs
/// (`use crate::ccl::planning::test_helpers::*`); they live here so the helpers
/// are written once and reachable from every sibling `tests` module.
#[cfg(test)]
pub(crate) mod test_helpers {
    use crate::ccl::{BaseType, Builtin, Expr, Lit, Refinement, Type, TypedExprNode};
    use std::rc::Rc;

    pub(crate) fn var(name: &str) -> Expr {
        Expr::var(name)
    }

    pub(crate) fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    pub(crate) fn fun_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    pub(crate) fn tuple_ty(tys: Vec<Type>) -> Type {
        Type::Tuple(tys)
    }

    pub(crate) fn compose(elts: Vec<Expr>) -> Expr {
        Expr::compose(elts)
    }

    pub(crate) fn bool_ty() -> Type {
        Type::Base(BaseType::Bool)
    }

    /// Build a [`Type::Refinement`] wrapping `base` with `predicate` as its
    /// predicate.  The predicate must have type `base ⇒ Bool` so the
    /// refinement is well-formed.
    pub(crate) fn refined_ty(base: Type, predicate: Expr) -> Type {
        Type::Refinement(Box::new(base), Refinement::born(Rc::new(predicate)))
    }

    /// Build an `Apply { argument, function: <builtin> }` whose function
    /// position carries the supplied `function_ty`.  Used to construct
    /// arms-internalising shapes (`Sum`, `Converse`, `MapDomain`, …)
    /// without going through the full lambda-elim pipeline.
    pub(crate) fn apply_builtin(
        argument: Expr,
        builtin: Builtin,
        function_ty: Type,
        result_ty: Type,
    ) -> Expr {
        Expr::apply(argument, Expr::builtin(builtin).with_ty(function_ty)).with_ty(result_ty)
    }

    /// Build a finite list literal `[1, 2, 3]` typed `[0, 2] ⇒ Int`.
    pub(crate) fn list_123() -> Expr {
        let int = int_ty();
        Expr::list(vec![
            Expr::lit(Lit::Int(1)).with_ty(int.clone()),
            Expr::lit(Lit::Int(2)).with_ty(int.clone()),
            Expr::lit(Lit::Int(3)).with_ty(int.clone()),
        ])
        .with_ty(fun_ty(Type::UIntRange(3), int))
    }

    /// Returns `true` if `expr` is `Apply { function: Builtin::Iterate, .. }`
    /// at the top level — used by the assertions below to check that a
    /// wrap actually fired.
    pub(crate) fn is_iterate_apply(expr: &Expr) -> bool {
        let TypedExprNode::Apply { function, .. } = &expr.node else {
            return false;
        };
        matches!(&function.node, TypedExprNode::Builtin(Builtin::Iterate))
    }

    /// Returns the upstream value-producer if `expr` is `restrict(p)`
    /// *applied* to it — the term `Apply { argument: upstream, function:
    /// Apply(p, Restrict) }`.  `restrict` is a function transformer applied
    /// to its upstream (not composed), so the marker lives in the `function`
    /// position one level down.  Used to assert mid-chain filter emission
    /// and to walk down a stack of applied restricts.
    pub(crate) fn restrict_application_upstream(expr: &Expr) -> Option<&Expr> {
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            return None;
        };
        let TypedExprNode::Apply {
            function: inner, ..
        } = &function.node
        else {
            return None;
        };
        matches!(&inner.node, TypedExprNode::Builtin(Builtin::Restrict)).then_some(argument)
    }

    /// Returns the leftmost element of `expr` if it is a [`Compose`], or
    /// `expr` itself otherwise.  Used to read the chain head out of a
    /// (possibly-wrapped) compose.
    pub(crate) fn chain_head(expr: &Expr) -> &Expr {
        match &expr.node {
            TypedExprNode::Compose(elts) => elts.first().unwrap_or(expr),
            _ => expr,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::test_helpers::*;
    use super::*;
    use crate::ccl::Expr;
    use crate::ccl::symbolic::symbolic;
    // `super::*` also glob-imports `lambda_elim::compose` into scope; name the
    // test-helper `compose` (`Expr::compose`) explicitly so it wins over the
    // glob and the two don't clash.
    use super::test_helpers::compose;

    #[test]
    fn test_is_function_of_single_tuple_arm_on_projection() {
        let expr = Expr::proj_index(0);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_second_index() {
        let expr = Expr::proj_index(1);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_var() {
        let expr = var("x");
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_with_projection_first() {
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![
            Expr::proj_index(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_compose_without_projection() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![var("f").with_ty(f_ty), var("g").with_ty(g_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&expr), None);
    }

    #[test]
    fn test_apply_primitive_basic() {
        let int_ty_val = int_ty();
        let expr = var("f").with_ty(int_ty_val.clone());
        let output_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let result = apply_primitive(expr, Builtin::Map, output_ty.clone());

        // Check that result is an apply expression
        assert!(matches!(result.node, TypedExprNode::Apply { .. }));
        // Check that the type is correct
        assert_eq!(result.ty, output_ty);
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_projection() {
        let int_ty_val = int_ty();
        let mut expr = Expr::proj_index(0);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be identity function
        assert!(matches!(expr.node, TypedExprNode::Builtin(Builtin::Id)));
        assert_eq!(expr.ty, fun_ty(int_ty_val.clone(), int_ty_val));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_compose() {
        let int_ty_val = int_ty();
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let mut expr = compose(vec![
            Expr::proj_index(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty.clone()),
        ])
        .with_ty(f_ty);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, first element should be identity
        if let TypedExprNode::Compose(elts) = &expr.node {
            assert!(matches!(elts[0].node, TypedExprNode::Builtin(Builtin::Id)));
        } else {
            panic!("Expected Compose node");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    // Tests for is_constant helper
    #[test]
    fn test_is_constant_on_const_apply() {
        let int_ty_val = int_ty();
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            int_ty_val,
        );
        assert!(is_constant(&const_expr));
    }

    #[test]
    fn test_is_constant_on_non_const_apply() {
        let int_ty_val = int_ty();
        let non_const_expr = apply_primitive(
            var("f").with_ty(int_ty_val.clone()),
            Builtin::Map,
            int_ty_val,
        );
        assert!(!is_constant(&non_const_expr));
    }

    #[test]
    fn test_is_constant_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );
        let compose_expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val));
        // A compose where the first element is const is considered constant
        assert!(is_constant(&compose_expr));
    }

    #[test]
    fn test_is_constant_on_var() {
        let expr = var("x");
        assert!(!is_constant(&expr));
    }

    // Tests for replace_tuple_project_with_id with Apply expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        );

        let mut expr = Expr::apply(
            Expr::proj_index(0).with_ty(proj_ty),
            Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty.clone()),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be Apply with zip function
        assert!(matches!(expr.node, TypedExprNode::Apply { .. }));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    // Tests for replace_tuple_project_with_id with Tuple expressions
    #[test]
    fn test_replace_tuple_project_with_id_on_tuple() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let mut expr = Expr::tuple(vec![
            Expr::proj_index(0).with_ty(proj_ty.clone()),
            Expr::proj_index(0).with_ty(proj_ty),
        ])
        .with_ty(tuple_ty(vec![
            fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
            fun_ty(tuple_ty_val, int_ty_val.clone()),
        ]));

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));

        // Check that the tuple type's function domains have been updated
        if let Type::Tuple(ref elts) = expr.ty {
            for elt in elts {
                match elt {
                    Type::Fun { domain, .. } => {
                        assert_eq!(**domain, int_ty_val);
                    }
                    _ => panic!("Expected function type in tuple"),
                }
            }
        } else {
            panic!("Expected tuple type");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_tuple_with_constants() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty.clone(),
        );

        let mut expr = Expr::tuple(vec![Expr::proj_index(0).with_ty(proj_ty), const_expr]).with_ty(
            tuple_ty(vec![
                fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
                const_fn_ty,
            ]),
        );

        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should still be a Tuple
        assert!(matches!(expr.node, TypedExprNode::Tuple(_)));
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_constant_domain_type_on_const_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val, int_ty_val.clone());

        let mut expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun { domain, .. } = &expr.ty {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    #[test]
    fn test_replace_constant_domain_type_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());

        let const_expr = apply_primitive(
            var("c").with_ty(int_ty_val.clone()),
            Builtin::Const,
            const_fn_ty,
        );

        let mut expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val.clone()));

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun { domain, .. } = &expr.ty {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    // -----------------------------------------------------------------
    // End-to-end: insert_iterate_markers
    // -----------------------------------------------------------------

    #[test]
    fn test_insert_iterate_markers_top_level_let_descends_into_bound_and_body() {
        // Full driver pass: a `let xs = [1,2,3] in xs ≫ id` program.  The
        // top-level wrap should reach the bound list (compiled with
        // `input=None` by op-conversion's `Let` arm) and the body's
        // compose head (also `input=None` from the same arm).  The
        // function-typed Var inside the body is already iteration-
        // bearing, so it doesn't get a second wrap.
        let int = int_ty();
        let list_ty = fun_ty(Type::UIntRange(3), int.clone());
        let body_chain = compose(vec![
            var("xs").with_ty(list_ty.clone()),
            Expr::builtin(Builtin::Id).with_ty(fun_ty(int.clone(), int)),
        ])
        .with_ty(list_ty.clone());

        let mut expr = Expr::let_bind("xs".to_string(), list_123(), body_chain).with_ty(list_ty);

        insert_iterate_markers(&mut expr);

        let TypedExprNode::Let {
            bound_expr, body, ..
        } = &expr.node
        else {
            panic!("expected Let, got: {}", symbolic(&expr));
        };
        assert!(
            is_iterate_apply(chain_head(bound_expr)),
            "bound list should be iterate-led, got: {}",
            symbolic(bound_expr)
        );
        // Body's compose head is `Var(xs)` (iteration-bearing) — the
        // pass should leave the compose alone.
        let head = chain_head(body);
        assert!(
            matches!(head.node, TypedExprNode::Var(_)),
            "body's chain head should remain `Var(xs)`, got: {}",
            symbolic(head)
        );
    }

    #[test]
    fn test_insert_iterate_markers_scalar_top_level_only_wraps_aggregate_arg() {
        // `sum([1,2,3])` — the program root is scalar (Int), so no
        // top-level wrap.  The aggregate's argument, however, *is* an
        // iteration site and must be wrapped by the recursive pass.
        let int = int_ty();
        let mut expr = apply_builtin(
            list_123(),
            Builtin::Sum,
            fun_ty(fun_ty(Type::UIntRange(3), int.clone()), int.clone()),
            int,
        );
        insert_iterate_markers(&mut expr);
        let TypedExprNode::Apply { argument, function } = &expr.node else {
            panic!("expected Apply, got: {}", symbolic(&expr));
        };
        // Function position untouched (Sum is still Sum).
        assert!(matches!(
            &function.node,
            TypedExprNode::Builtin(Builtin::Sum)
        ));
        // Argument is iterate-led.
        assert!(
            is_iterate_apply(chain_head(argument)),
            "Sum's argument should be iterate-led, got: {}",
            symbolic(argument)
        );
    }

    #[test]
    fn test_insert_iterate_markers_record_root_wraps_each_function_field() {
        // Programs that end in a sink-bound `Record` — each
        // function-typed field is an iteration site (`compile_program`
        // dispatches to `convert_record_fields_to_operators`, which
        // compiles each field with `input=None`).
        let int = int_ty();
        let field_ty = fun_ty(Type::UIntRange(3), int.clone());
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("out_a".to_string(), list_123()),
            ("out_b".to_string(), list_123()),
        ]))
        .with_ty(Type::Record(vec![
            ("out_a".to_string(), field_ty.clone()),
            ("out_b".to_string(), field_ty),
        ]));

        insert_iterate_markers(&mut expr);

        let TypedExprNode::Record(fields) = &expr.node else {
            panic!("expected Record, got: {}", symbolic(&expr));
        };
        for (name, value) in fields {
            assert!(
                is_iterate_apply(chain_head(value)),
                "sink field `{name}` should be iterate-led, got: {}",
                symbolic(value)
            );
        }
    }
}

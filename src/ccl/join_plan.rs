use std::mem::take;

use log::trace;

use crate::ccl::{
    infer::typecheck,
    lambda_elim::{compose, id},
    simplify::simplify,
    symbolic::{symbolic, symbolic_typed},
    Expr, ProjKey, Refinement, RefinementKind, Type, TypedExprNode,
};

/// Looks for patterns in an expression that can be run more efficiently than the loop joins
/// that come out of lambda elimination.
pub fn run(mut expr: Expr) -> Expr {
    create_hash_joins(&mut expr);
    replace_curried_correlated_refinements(&mut expr);
    simplify(expr)
}

/// Identifies constructs corresponding to partitioning by key and swaps from the key
/// being the outer variable to the collection being the outer variable.
fn replace_curried_correlated_refinements(expr: &mut Expr) {
    let new = match &mut expr.node {
        TypedExprNode::Apply { argument, function }
            if matches!(&function.node, TypedExprNode::Var(n) if n == "curry")
                && matches!(&argument.ty, Type::Refinement(..)) =>
        {
            let Type::Refinement(
                inner_ty,
                Refinement {
                    kind: RefinementKind::Predicate(p),
                    ..
                },
            ) = &argument.ty
            else {
                unreachable!();
            };
            convert_groupby(argument, inner_ty, &p.borrow())
        }

        TypedExprNode::Apply { function, argument } => {
            replace_curried_correlated_refinements(function);
            replace_curried_correlated_refinements(argument);
            None
        }
        TypedExprNode::Aggregate { input, .. } => {
            replace_curried_correlated_refinements(input);
            None
        }
        TypedExprNode::Compose(elts) => {
            elts.iter_mut()
                .for_each(replace_curried_correlated_refinements);
            None
        }
        TypedExprNode::Lambda {
            body, refinement, ..
        } => {
            replace_curried_correlated_refinements(body);
            if let Some(Refinement {
                kind: RefinementKind::Predicate(p),
                ..
            }) = refinement
            {
                replace_curried_correlated_refinements(&mut p.borrow_mut());
            }
            None
        }
        TypedExprNode::Let {
            binding: _,
            bound_expr,
            body,
        } => {
            replace_curried_correlated_refinements(bound_expr);
            replace_curried_correlated_refinements(body);
            None
        }
        _ => None,
    };
    if let Some(new) = new {
        *expr = new;
    }
}

fn apply_primitive(expr: Expr, primitive: &str, output_ty: Type) -> Expr {
    let expr_ty = expr.ty.clone();
    Expr::apply(
        expr,
        Expr::var(primitive).with_ty(Type::fun(expr_ty, output_ty.clone())),
    )
    .with_ty(output_ty)
}

/// Look for an expression that corresponds to a group-by and rewrite it to use Converse
/// instead of iterating over both the collection and key.
/// The expression must be the argument of curry, and the type must be a 2-tuple with a refinement
/// of the form `(x, y) ▷ zip ≫ eq` where:
/// - The input type is a 2-tuple
/// - x only depends on one of the elements of the tuple
/// - y only depends on the other element of the tuple
///
/// This allows us to rewrite into an expression that iterates over just one side, compute the value
/// of the other side, then use Converse to do the grouping.
///
/// Note: this is technically not handling empty groups properly.  The incoming CCL says we should
/// output a group for _every_ k, but here we only output non-empty groups
/// TODO pay attention to whether the key has a refinements that specifies empty group handling.
fn convert_groupby(body: &Expr, body_ty: &Type, refinement: &Expr) -> Option<Expr> {
    // First, check all the prereqs
    let TypedExprNode::Compose(elts) = &refinement.node else {
        return None;
    };
    if elts.len() != 2 {
        return None;
    }
    if !matches!(&elts[1].node, TypedExprNode::Var(v) if v == "eq") {
        return None;
    }
    let TypedExprNode::Apply {
        function: zip,
        argument: args,
    } = &elts[0].node
    else {
        return None;
    };
    if zip.node != TypedExprNode::Var(String::from("zip")) {
        return None;
    }
    let TypedExprNode::Tuple(args) = &args.node else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let arg0_tuple_idx = starts_with_tuple_project(&args[0])?;
    let arg1_tuple_idx = starts_with_tuple_project(&args[1])?;
    let value_tuple_idx = starts_with_tuple_project(body)?;
    if arg0_tuple_idx == arg1_tuple_idx {
        return None;
    }
    let key_tuple_idx = 1 - value_tuple_idx;
    let Some(Type::Tuple(subtypes)) = refinement.ty.domain().clone() else {
        return None;
    };
    if subtypes.len() != 2 {
        return None;
    }

    // Everything has matched, so build the output structure
    let value_idx_ty = subtypes[value_tuple_idx].clone();
    let key_ty = subtypes[key_tuple_idx].clone();

    let value_ty = body_ty
        .codomain()
        .unwrap_or_else(|| panic!("Expected function, got {}", body.ty));
    let mut values = body.clone();
    replace_tuple_project_with_id(&mut values, &value_idx_ty);
    values = values.with_ty(Type::fun(value_idx_ty.clone(), value_ty.clone()));
    let key_extract_idx = if arg0_tuple_idx == value_tuple_idx {
        0
    } else {
        1
    };
    let mut keys = args[key_extract_idx].clone();

    // Sanity check that the term on the other side of the key extraction doesn't do
    // any transformation
    if !matches!(
        args[1 - key_extract_idx].node,
        TypedExprNode::Proj(ProjKey::Index(_))
    ) {
        return None;
    }

    replace_tuple_project_with_id(&mut keys, &value_idx_ty);
    let keys = keys.with_ty(Type::fun(value_idx_ty.clone(), key_ty.clone()));
    let converse_ty = Type::fun(
        key_ty.clone(),
        Type::fun(value_idx_ty.clone(), value_idx_ty.clone()),
    );
    let grouped = apply_primitive(keys.clone(), "converse", converse_ty);
    typecheck(&grouped).expect("Bad group expr");

    trace!("Grouped: {} : {}", symbolic(&grouped), grouped.ty);

    let values_fn = apply_primitive(
        values.clone(),
        "map",
        Type::fun(
            Type::fun(value_idx_ty.clone(), value_idx_ty.clone()),
            Type::fun(value_idx_ty.clone(), value_ty.clone()),
        ),
    );

    let grouped_values_ty = Type::fun(
        key_ty.clone(),
        Type::fun(value_idx_ty.clone(), value_ty.clone()),
    );
    typecheck(&values_fn).expect("Bad values_fn expr");
    let grouped_values = compose(grouped, values_fn).with_ty(grouped_values_ty);
    trace!(
        "Grouped values {} : {}",
        symbolic_typed(&grouped_values),
        grouped_values.ty
    );
    typecheck(&grouped_values).expect("Bad grouped_values expr");

    Some(grouped_values)
}

fn starts_with_tuple_project(expr: &Expr) -> Option<usize> {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => Some(*i),
        TypedExprNode::Compose(elts) => elts.first().and_then(starts_with_tuple_project),
        _ => None,
    }
}

fn replace_tuple_project_with_id(expr: &mut Expr, ty: &Type) {
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(_)) => {
            *expr = id().with_ty(Type::fun(ty.clone(), ty.clone()))
        }
        TypedExprNode::Compose(elts) => {
            if let Some(first) = elts.first_mut() {
                replace_tuple_project_with_id(first, ty);
            }
        }
        _ => {}
    };
}

/// Try to convert a loop-join refinement pattern into a transformed expression using hash-join primitives.
/// The expression's type must be a refined 2-tuple where the refinement is of the form `(x, y) ▷ zip ≫ eq`.
/// This transformation rewrites a cross-product iteration into a more efficient hash join strategy where:
/// - One side builds a lookup table using converse
/// - The other side probes that lookup table
fn convert_loop_join(expr: &Expr, base_ty: &Type, refinement: &Expr) -> Option<Expr> {
    trace!(
        "convert_loop_join: base_ty={}, refinement={} : {}",
        base_ty,
        symbolic(refinement),
        refinement.ty
    );
    trace!("typed refinement\n{}", symbolic_typed(refinement));

    // Check that the base type is a 2-tuple
    let Type::Tuple(subtypes) = base_ty else {
        trace!("convert_loop_join: base_ty is not a tuple");
        return None;
    };
    if subtypes.len() != 2 {
        trace!(
            "convert_loop_join: tuple has {} elements, not 2",
            subtypes.len()
        );
        return None;
    }

    // Check that the refinement matches the pattern: compose(zip(args), eq)
    let TypedExprNode::Compose(elts) = &refinement.node else {
        trace!("convert_loop_join: refinement is not a Compose");
        return None;
    };
    if elts.len() != 2 {
        trace!(
            "convert_loop_join: compose has {} elements, not 2",
            elts.len()
        );
        return None;
    }
    if !matches!(&elts[1].node, TypedExprNode::Var(v) if v == "eq") {
        trace!("convert_loop_join: second element is not 'eq'");
        return None;
    }

    let TypedExprNode::Apply {
        function: zip,
        argument: args,
    } = &elts[0].node
    else {
        trace!("convert_loop_join: first element is not Apply");
        return None;
    };
    if zip.node != TypedExprNode::Var(String::from("zip")) {
        trace!("convert_loop_join: function in Apply is not 'zip'");
        return None;
    }

    let TypedExprNode::Tuple(zip_args) = &args.node else {
        trace!("convert_loop_join: argument to Apply is not Tuple");
        return None;
    };
    if zip_args.len() != 2 {
        trace!(
            "convert_loop_join: zip args has {} elements, not 2",
            zip_args.len()
        );
        return None;
    }

    // Determine which element of the body tuple corresponds to which key argument
    let key0_idx = starts_with_tuple_project(&zip_args[0])?;
    let key1_idx = starts_with_tuple_project(&zip_args[1])?;

    if key0_idx == key1_idx {
        trace!("convert_loop_join: both keys depend on same tuple element");
        return None;
    }

    // The body should be the same tuple applied with a different operation
    let TypedExprNode::Compose(body_elts) = &expr.node else {
        trace!("convert_loop_join: body is not a Compose");
        return None;
    };
    if body_elts.len() < 2 {
        trace!("convert_loop_join: body compose has < 2 elements");
        return None;
    }

    // Extract the tuple from the body (should match the refinement's tuple)
    let body_tuple = if body_elts.len() == 2 {
        &body_elts[0]
    } else {
        trace!("convert_loop_join: body structure doesn't match expected pattern");
        return None;
    };

    // Verify body tuple structure matches refinement tuple structure
    if let TypedExprNode::Apply {
        function: body_zip,
        argument: body_args,
    } = &body_tuple.node
    {
        if body_zip.node != TypedExprNode::Var(String::from("zip")) {
            trace!("convert_loop_join: body zip is not 'zip'");
            return None;
        }

        let TypedExprNode::Tuple(body_zip_args) = &body_args.node else {
            trace!("convert_loop_join: body zip args is not Tuple");
            return None;
        };
        if body_zip_args.len() != 2 {
            trace!(
                "convert_loop_join: body zip args has {} elements, not 2",
                body_zip_args.len()
            );
            return None;
        }

        // Verify that body tuple elements come from the same sources as refinement
        let body_key0_idx = starts_with_tuple_project(&body_zip_args[0])?;
        let body_key1_idx = starts_with_tuple_project(&body_zip_args[1])?;

        if body_key0_idx != key0_idx || body_key1_idx != key1_idx {
            // TODO remove this limit
            trace!("convert_loop_join: body tuple keys don't match refinement keys");
            return None;
        }

        let idx_ty0 = subtypes[key0_idx].clone();
        let idx_ty1 = subtypes[key1_idx].clone();
        let value_ty0 = body_zip_args[0].ty.codomain()?.clone();
        let value_ty1 = body_zip_args[1].ty.codomain()?.clone();
        let mut key0 = zip_args[0].clone();
        replace_tuple_project_with_id(&mut key0, &idx_ty0);
        key0 = key0.with_ty(Type::fun(idx_ty0.clone(), value_ty0.clone()));
        let mut key1 = zip_args[1].clone();
        replace_tuple_project_with_id(&mut key1, &idx_ty1);
        key1 = key1.with_ty(Type::fun(idx_ty1.clone(), value_ty1.clone()));

        trace!(
            "convert_loop_join: key0={} : {}\nkey1={} : {}",
            symbolic(&key0),
            key0.ty,
            symbolic(&key1),
            key1.ty
        );

        // Build side: group by the build projection using converse
        let converse_ty = Type::fun(
            value_ty1.clone(),
            Type::fun(idx_ty1.clone(), idx_ty1.clone()),
        );
        let build_side = apply_primitive(key1, "converse", converse_ty);
        typecheck(&build_side).expect("Bad build expr");

        trace!(
            "convert_loop_join: build_side={} : {}",
            symbolic(&build_side),
            build_side.ty
        );

        // Probe side: filter by the set of build keys that exist, then compose
        // with the build side
        let probe = compose(key0, build_side.clone()).with_ty(Type::fun(
            idx_ty0.clone(),
            Type::fun(idx_ty1.clone(), idx_ty1.clone()),
        ));
        typecheck(&probe).expect("Bad probe expr");
        trace!(
            "convert_loop_join: probe={} : {}",
            symbolic(&probe),
            probe.ty
        );

        let joined_indices = apply_primitive(
            probe,
            "uncurry",
            Type::fun(
                Type::Tuple(vec![idx_ty0.clone(), idx_ty1.clone()]),
                idx_ty1.clone(),
            ),
        );

        let map_domain = apply_primitive(
            joined_indices,
            "map_domain",
            Type::fun(
                Type::Tuple(vec![idx_ty0.clone(), idx_ty1.clone()]),
                Type::Tuple(vec![idx_ty0.clone(), idx_ty1.clone()]),
            ),
        );

        typecheck(&map_domain).expect("Bad hash join expr");

        Some(map_domain)
    } else {
        trace!("convert_loop_join: body tuple is not Apply");
        None
    }
}

/// Finds loop joins that can be converted into hash joins.
///
/// Loop joins can occur either at the top-level of an expression, or inside a global aggregate.
/// This function looks for cases where the type at those points is a refined 2-tuple where the
/// refinement is of the form `(x, y) ▷ zip ≫ eq` where:
/// - x only depends on one of the elements of the tuple
/// - y only depends on the other element of the tuple
///
/// Then, we transform this from iterating both elements as a cross product to iterating one, computing
/// the keys, and conversing, then iterating the other, computing the keys on that side, then looking up
/// the elements from the other side.
///
/// Currently, this function does just the most basic version.  Only two join members are supported,
/// build/probe selection is arbitrary, and predicates must be trivial to be detected.
fn create_hash_joins(expr: &mut Expr) {
    trace!(
        "replace_loop_joins called on: {} with type {}",
        symbolic(expr),
        expr.ty
    );
    if let Type::Fun(domain, codomain) = expr.ty.clone() {
        if let Type::Refinement(base, refinement) = (*domain).clone() {
            if let RefinementKind::Predicate(pred_rc) = &refinement.kind {
                let pred = pred_rc.borrow().clone();
                trace!("Attempting loop join conversion for: {}", symbolic(expr));
                if let Some(transformed) = convert_loop_join(expr, &base, &pred) {
                    trace!(
                        "Successfully transformed to: {} : {}",
                        symbolic(&transformed),
                        transformed.ty
                    );
                    let result_ty =
                        Type::fun(transformed.ty.domain().expect("non-function"), *codomain);
                    *expr = compose(transformed, take(expr)).with_ty(result_ty);
                } else {
                    trace!("Loop join pattern did not match");
                }
            }
        }
    }

    create_hash_joins_recurse(expr);
}

/// Helper to explore the expression tree for convertible loop joins.
fn create_hash_joins_recurse(expr: &mut Expr) {
    let new = match &mut expr.node {
        TypedExprNode::Apply { argument, function } => {
            create_hash_joins_recurse(argument);
            create_hash_joins_recurse(function);
            None
        }
        TypedExprNode::Aggregate { .. } => {
            create_hash_joins(expr);
            None
        }
        TypedExprNode::Compose(elts) => {
            elts.iter_mut().for_each(create_hash_joins_recurse);
            None
        }
        TypedExprNode::Tuple(elts) => {
            elts.iter_mut().for_each(create_hash_joins_recurse);
            None
        }
        TypedExprNode::Let {
            binding: _,
            bound_expr,
            body,
        } => {
            create_hash_joins_recurse(bound_expr);
            create_hash_joins_recurse(body);
            None
        }
        _ => None,
    };
    if let Some(new) = new {
        *expr = new;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Expr};

    fn var(name: &str) -> Expr {
        Expr::var(name)
    }

    fn proj_idx(n: usize) -> Expr {
        Expr::proj_index(n)
    }

    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    fn fun_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun(Box::new(domain), Box::new(codomain))
    }

    fn tuple_ty(tys: Vec<Type>) -> Type {
        Type::Tuple(tys)
    }

    fn compose(elts: Vec<Expr>) -> Expr {
        Expr::compose(elts)
    }

    #[test]
    fn test_starts_with_tuple_project_on_projection() {
        let expr = proj_idx(0);
        assert_eq!(starts_with_tuple_project(&expr), Some(0));
    }

    #[test]
    fn test_starts_with_tuple_project_on_second_index() {
        let expr = proj_idx(1);
        assert_eq!(starts_with_tuple_project(&expr), Some(1));
    }

    #[test]
    fn test_starts_with_tuple_project_on_var() {
        let expr = var("x");
        assert_eq!(starts_with_tuple_project(&expr), None);
    }

    #[test]
    fn test_starts_with_tuple_project_on_compose_with_projection_first() {
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![proj_idx(1).with_ty(proj0_ty), var("f").with_ty(f_ty)]);
        assert_eq!(starts_with_tuple_project(&expr), Some(1));
    }

    #[test]
    fn test_starts_with_tuple_project_on_compose_without_projection() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let expr = compose(vec![var("f").with_ty(f_ty), var("g").with_ty(g_ty)]);
        assert_eq!(starts_with_tuple_project(&expr), None);
    }

    #[test]
    fn test_apply_primitive_basic() {
        let int_ty_val = int_ty();
        let expr = var("f").with_ty(int_ty_val.clone());
        let output_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let result = apply_primitive(expr, "map", output_ty.clone());

        // Check that result is an apply expression
        assert!(matches!(result.node, TypedExprNode::Apply { .. }));
        // Check that the type is correct
        assert_eq!(result.ty, output_ty);
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_projection() {
        let int_ty_val = int_ty();
        let mut expr = proj_idx(0);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, should be identity function
        assert!(matches!(expr.node, TypedExprNode::Var(ref v) if v == "id"));
        assert_eq!(expr.ty, fun_ty(int_ty_val.clone(), int_ty_val));
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_compose() {
        let int_ty_val = int_ty();
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let mut expr = compose(vec![proj_idx(1).with_ty(proj0_ty), var("f").with_ty(f_ty)]);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, first element should be identity
        if let TypedExprNode::Compose(elts) = &expr.node {
            assert!(matches!(elts[0].node, TypedExprNode::Var(ref v) if v == "id"));
        } else {
            panic!("Expected Compose node");
        }
    }

    #[test]
    fn test_replace_curried_correlated_refinements_on_var() {
        let mut expr = var("x");
        replace_curried_correlated_refinements(&mut expr);
        // Should remain unchanged
        assert!(matches!(expr.node, TypedExprNode::Var(ref v) if v == "x"));
    }

    #[test]
    fn test_convert_groupby_basic() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let value_ty = int_ty_val.clone();

        // body: projects element 0 from a tuple
        // type: (int, int) -> int
        let body_ty = fun_ty(tuple_ty_val.clone(), value_ty.clone());
        let body = proj_idx(0).with_ty(body_ty.clone());

        // refinement: zip(proj_idx(0), proj_idx(1)) ≫ eq
        let zip_arg_ty = fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        );
        let eq_arg_ty = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let eq_ty = fun_ty(eq_arg_ty.clone(), int_ty_val.clone());

        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(zip_arg_ty.clone()),
            proj_idx(1).with_ty(zip_arg_ty.clone()),
        ]);

        let zip_applied = Expr::apply(
            args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let refinement = compose(vec![zip_applied, var("eq").with_ty(eq_ty)])
            .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone()));

        // Should successfully convert
        let result = convert_groupby(&body, &body_ty, &refinement);
        assert!(
            result.is_some(),
            "convert_groupby should succeed for valid input"
        );

        let grouped_values = result.unwrap();

        // Verify the result type: key_ty -> (input_idx_ty -> value_ty)
        assert_eq!(
            grouped_values.ty,
            fun_ty(
                int_ty_val.clone(),
                fun_ty(int_ty_val.clone(), value_ty.clone())
            )
        );

        // Verify the result is a composition of two elements
        let TypedExprNode::Compose(elts) = &grouped_values.node else {
            panic!("Expected Compose node, got {:?}", grouped_values.node);
        };
        assert_eq!(elts.len(), 2, "Expected 2 elements in composition");

        // First element should be: keys ≫ converse
        // (an Apply with converse as the function)
        let TypedExprNode::Apply {
            function: grouped_fn,
            argument: grouped_arg,
        } = &elts[0].node
        else {
            panic!(
                "Expected Apply node for first element, got {:?}",
                elts[0].node
            );
        };

        assert!(
            matches!(&grouped_fn.node, TypedExprNode::Var(v) if v == "converse"),
            "Expected first Apply to use 'converse' primitive"
        );

        // Verify grouped argument is the keys expression with id replacing the projection
        // Since the original expression is just a projection, it becomes just id
        assert!(
            matches!(&grouped_arg.node, TypedExprNode::Var(v) if v == "id"),
            "Expected keys to be 'id' (replaced projection), got {:?}",
            grouped_arg.node
        );

        // Second element should be: values ≫ map
        // (an Apply with map as the function)
        let TypedExprNode::Apply {
            function: values_fn,
            argument: values_arg,
        } = &elts[1].node
        else {
            panic!(
                "Expected Apply node for second element, got {:?}",
                elts[1].node
            );
        };

        assert!(
            matches!(&values_fn.node, TypedExprNode::Var(v) if v == "map"),
            "Expected second Apply to use 'map' primitive"
        );

        // Verify values argument is the body expression with id replacing the projection
        // Since the original expression is just a projection, it becomes just id
        assert!(
            matches!(&values_arg.node, TypedExprNode::Var(v) if v == "id"),
            "Expected values to be 'id' (replaced projection), got {:?}",
            values_arg.node
        );
    }

    #[test]
    fn test_convert_groupby_rejects_non_compose_refinement() {
        let int_ty_val = int_ty();
        let body = var("x").with_ty(int_ty_val.clone());
        let body_ty = int_ty_val.clone();
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Should return None because refinement is not a compose
        let result = convert_groupby(&body, &body_ty, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_groupby_rejects_wrong_refinement_length() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let body = proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty()));
        let body_ty = int_ty_val.clone();

        // Create a compose with three elements (not two)
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let refinement = compose(vec![
            var("f").with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
            var("h").with_ty(f_ty),
        ])
        .with_ty(fun_ty(tuple_ty_val, int_ty()));

        // Should return None because refinement doesn't have exactly 2 elements
        let result = convert_groupby(&body, &body_ty, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_groupby_rejects_non_eq_second_element() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let body = proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty()));
        let body_ty = int_ty_val.clone();

        // Create a compose where the second element is not "eq"
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let f_ty = fun_ty(tuple_ty_val.clone(), tuple_ty(vec![int_ty(), int_ty()]));
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("neq").with_ty(fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty())),
        ])
        .with_ty(ref_ty);

        // Should return None because second element is not "eq"
        let result = convert_groupby(&body, &body_ty, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_groupby_rejects_missing_zip() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let body = proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty()));
        let body_ty = int_ty_val.clone();

        // Create a compose where the first element is not a zip application
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let refinement = compose(vec![
            var("not_zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty(), int_ty()]),
            )),
            var("eq").with_ty(fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty())),
        ])
        .with_ty(ref_ty);

        // Should return None because there's no zip
        let result = convert_groupby(&body, &body_ty, &refinement);
        assert_eq!(result, None);
    }

    // Tests for convert_loop_join function
    #[test]
    fn test_convert_loop_join_rejects_non_tuple_base_type() {
        let int_ty_val = int_ty();
        let body = var("x").with_ty(int_ty_val.clone());
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Base type is not a tuple, should return None
        let result = convert_loop_join(&body, &int_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_wrong_tuple_size() {
        let int_ty_val = int_ty();
        let triple_tuple = tuple_ty(vec![
            int_ty_val.clone(),
            int_ty_val.clone(),
            int_ty_val.clone(),
        ]);
        let body = var("x").with_ty(int_ty_val.clone());
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Tuple has 3 elements, not 2, should return None
        let result = convert_loop_join(&body, &triple_tuple, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_compose_refinement() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Refinement is not a compose, should return None
        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_wrong_compose_size() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create a compose with 3 elements (not 2)
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
            var("h").with_ty(f_ty),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_eq_second_element() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create a compose where second element is not "eq"
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("ne").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_missing_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create a compose where first element is not an Apply
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_zip_function() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create an apply with function that is not "zip"
        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(int_ty_val.clone()),
            proj_idx(1).with_ty(int_ty_val.clone()),
        ]);
        let non_zip_apply = Expr::apply(
            args_tuple,
            var("not_zip").with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_zip_with_non_tuple_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create an apply where argument is not a tuple
        let non_tuple_apply = Expr::apply(
            var("arg").with_ty(int_ty_val.clone()),
            var("zip").with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_tuple_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_mismatched_zip_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create zip with only 1 argument (not 2)
        let args_tuple = Expr::tuple(vec![proj_idx(0).with_ty(int_ty_val.clone())]);
        let zip_apply = Expr::apply(
            args_tuple,
            var("zip").with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_same_key_index() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let body = var("x").with_ty(int_ty_val.clone());

        // Create zip where both args project from same tuple element
        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let zip_apply = Expr::apply(
            args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_compose_body() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        // Body is just a variable, not a compose
        let body = var("x").with_ty(int_ty_val.clone());

        // Create valid refinement
        let args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(1).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let zip_apply = Expr::apply(
            args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        // Body is not a compose, should fail
        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_mismatched_body_zip() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create body with zip that doesn't match refinement key indices
        let body_args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(1).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let body_zip_apply = Expr::apply(
            body_args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let body = compose(vec![
            body_zip_apply,
            var("id").with_ty(fun_ty(
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        ])
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        // Create refinement with swapped indices (1, 0 instead of 0, 1)
        let ref_args_tuple = Expr::tuple(vec![
            proj_idx(1).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let ref_zip_apply = Expr::apply(
            ref_args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            ref_zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        // Should fail because body keys don't match refinement keys
        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_succeeds_with_valid_input() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create body: compose(zip(proj(0), proj(1)), identity_func)
        let body_args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(1).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let body_zip_apply = Expr::apply(
            body_args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let body = compose(vec![
            body_zip_apply,
            var("id").with_ty(fun_ty(
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        ])
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        // Create refinement: compose(zip(proj(0), proj(1)), eq)
        let ref_args_tuple = Expr::tuple(vec![
            proj_idx(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            proj_idx(1).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let ref_zip_apply = Expr::apply(
            ref_args_tuple,
            var("zip").with_ty(fun_ty(
                tuple_ty_val.clone(),
                tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
            )),
        )
        .with_ty(fun_ty(
            tuple_ty_val.clone(),
            tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]),
        ));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            ref_zip_apply,
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        // Should successfully convert
        let result = convert_loop_join(&body, &tuple_ty_val, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed with valid hash join pattern"
        );

        let hash_join = result.unwrap();
        // Result should be a map_domain expression: Apply(map_domain, ...)
        let TypedExprNode::Apply {
            function: map_domain_fn,
            argument: uncurry_expr,
        } = &hash_join.node
        else {
            panic!("Expected Apply node (map_domain), got {:?}", hash_join.node);
        };

        // Validate that function is map_domain primitive
        assert!(
            matches!(&map_domain_fn.node, TypedExprNode::Var(v) if v == "map_domain"),
            "Top-level function should be 'map_domain' primitive, got {:?}",
            map_domain_fn.node
        );

        // Validate the argument is uncurry expression
        let TypedExprNode::Apply {
            function: uncurry_fn,
            argument: probe_expr,
        } = &uncurry_expr.node
        else {
            panic!(
                "Expected Apply node (uncurry) as argument to map_domain, got {:?}",
                uncurry_expr.node
            );
        };

        // Validate that function is uncurry primitive
        assert!(
            matches!(&uncurry_fn.node, TypedExprNode::Var(v) if v == "uncurry"),
            "Inner function should be 'uncurry' primitive, got {:?}",
            uncurry_fn.node
        );

        // Validate probe is a compose expression: compose(key0, build_side)
        let TypedExprNode::Compose(probe_elts) = &probe_expr.node else {
            panic!(
                "Expected Compose node (probe expression), got {:?}",
                probe_expr.node
            );
        };
        assert_eq!(
            probe_elts.len(),
            2,
            "Probe compose should have 2 elements (key0 and build_side)"
        );

        // Validate build_side (second element) is converse expression
        let TypedExprNode::Apply {
            function: build_fn,
            argument: _,
        } = &probe_elts[1].node
        else {
            panic!(
                "Expected Apply node (build_side with converse), got {:?}",
                probe_elts[1].node
            );
        };

        assert!(
            matches!(&build_fn.node, TypedExprNode::Var(v) if v == "converse"),
            "Build side should use 'converse' primitive, got {:?}",
            build_fn.node
        );

        // Validate output type is a curried function: int -> int -> int
        // (since both tuple elements are int in this test)
        assert!(
            matches!(hash_join.ty, Type::Fun(..)),
            "Hash join result should have function type, got {:?}",
            hash_join.ty
        );
    }
}

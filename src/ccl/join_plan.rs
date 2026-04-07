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
}

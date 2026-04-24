use std::collections::VecDeque;
use std::fmt::Debug;
use std::mem::take;

use log::trace;

use crate::ccl::{
    infer::typecheck,
    lambda_elim::{compose, id},
    simplify::simplify,
    symbolic::{symbolic, symbolic_typed},
    BaseType, Expr, Lit, ProjKey, Refinement, RefinementKind, Type, TypedExprNode,
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
    apply_function(expr, Expr::var(primitive), output_ty)
}

fn apply_function(expr: Expr, function: Expr, output_ty: Type) -> Expr {
    let expr_ty = expr.ty.clone();
    Expr::apply(
        expr,
        function.with_ty(Type::fun(expr_ty, output_ty.clone())),
    )
    .with_ty(output_ty)
}

fn typed_compose(elts: Vec<Expr>) -> Expr {
    let d_ty = elts[0].ty.domain().unwrap().clone();
    let c_ty = elts[elts.len() - 1].ty.codomain().unwrap().clone();
    Expr::compose(elts).with_ty(Type::fun(d_ty, c_ty))
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
    let arg0_tuple_idx = is_function_of_single_tuple_arm(&args[0])?;
    let arg1_tuple_idx = is_function_of_single_tuple_arm(&args[1])?;
    let value_tuple_idx = is_function_of_single_tuple_arm(body)?;
    if arg0_tuple_idx == arg1_tuple_idx {
        return None;
    }
    let key_tuple_idx = 1 - value_tuple_idx;
    let Some(Type::Tuple(arm_types)) = refinement.ty.domain().clone() else {
        return None;
    };
    if arm_types.len() != 2 {
        return None;
    }

    // Everything has matched, so build the output structure
    let value_idx_ty = arm_types[value_tuple_idx].clone();
    let key_ty = arm_types[key_tuple_idx].clone();

    let value_ty = body_ty
        .codomain()
        .unwrap_or_else(|| panic!("Expected function, got {}", body.ty));
    let mut values = body.clone();
    // Clear the refinement first before doing projection substitution.
    values = values.with_ty(Type::fun(
        Type::Tuple(vec![key_ty.clone(), value_idx_ty.clone()]),
        value_ty.clone(),
    ));
    replace_tuple_project_with_id(&mut values, &value_idx_ty);
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

// Returns whether the given expression is a constant, or a function of a constant.
fn is_constant(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Apply { function, .. } if function.node == Expr::var("const").node => true,
        TypedExprNode::Compose(elts) => elts.first().is_some_and(is_constant),
        _ => false,
    }
}

// Replaces the domain type of a constant expression with a new domain type.
// Requires `is_constant(expr)` to be true.
fn replace_constant_domain_type(expr: &mut Expr, ty: &Type) {
    set_domain_ty(&mut expr.ty, ty);
    match &mut expr.node {
        TypedExprNode::Apply { .. } => {
            let output_ty = expr.ty.clone();
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert_eq!(function.node, Expr::var("const").node);
                argument.clone()
            } else {
                unreachable!()
            };

            *expr = apply_primitive(*arg, "const", output_ty)
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
fn is_function_of_single_tuple_arm(expr: &Expr) -> Option<usize> {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => Some(*i),
        TypedExprNode::Compose(elts) => elts.first().and_then(is_function_of_single_tuple_arm),
        TypedExprNode::Apply { function, argument } if function.node == Expr::var("zip").node => {
            is_function_of_single_tuple_arm(argument)
        }
        TypedExprNode::Tuple(elts) => {
            let mut result = None;
            for elt in elts.iter() {
                if is_constant(elt) {
                    continue;
                }
                if let Some(idx) = is_function_of_single_tuple_arm(elt) {
                    if result.is_some_and(|x| x != idx) {
                        return None;
                    }
                    result = Some(idx);
                } else {
                    return None;
                }
            }
            result
        }
        _ => None,
    }
}

fn set_domain_ty(fun_ty: &mut Type, ty: &Type) {
    match fun_ty {
        Type::Fun(domain, _) => {
            **domain = ty.clone();
        }
        _ => panic!("Not function type: {}", fun_ty),
    }
}

// Converts an expression that only reads a single arm of its input
// (as determined by is_function_of_single_tuple_arm) to a function
// of just that arm.
fn replace_tuple_project_with_id(expr: &mut Expr, ty: &Type) {
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(_)) => {
            *expr = id().with_ty(Type::fun(ty.clone(), ty.clone()))
        }
        TypedExprNode::Compose(_) => {
            set_domain_ty(&mut expr.ty, ty);
            if let TypedExprNode::Compose(elts) = &mut expr.node {
                if let Some(first) = elts.first_mut() {
                    replace_tuple_project_with_id(first, ty);
                }
            }
        }
        TypedExprNode::Apply { .. } => {
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, ty);
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert_eq!(function.node, Expr::var("zip").node);
                replace_tuple_project_with_id(argument, ty);
                argument.clone()
            } else {
                unreachable!()
            };
            *expr = apply_primitive(*arg, "zip", output_ty);
        }
        TypedExprNode::Tuple(_) => {
            if let Type::Tuple(elts) = &mut expr.ty {
                elts.iter_mut().for_each(|elt| match elt {
                    Type::Fun(domain, _) => {
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

/// Extracts `(key_a, key_b)` from a single equality condition `(key_a, key_b) ▷ zip ≫ eq`.
fn extract_single_eq_condition(cond: &Expr) -> Option<(&Expr, &Expr)> {
    let TypedExprNode::Compose(elts) = &cond.node else {
        return None;
    };
    if elts.len() != 2 {
        return None;
    }
    if !matches!(&elts[1].node, TypedExprNode::Var(v) if v == "eq") {
        return None;
    }
    let TypedExprNode::Apply {
        function: zip_fn,
        argument: args,
    } = &elts[0].node
    else {
        return None;
    };
    if !matches!(&zip_fn.node, TypedExprNode::Var(v) if v == "zip") {
        return None;
    }
    let TypedExprNode::Tuple(zip_args) = &args.node else {
        return None;
    };
    if zip_args.len() != 2 {
        return None;
    }
    Some((&zip_args[0], &zip_args[1]))
}

/// Collects individual equality join conditions from a refinement predicate.
///
/// Handles two forms:
/// - Single: `(key_a, key_b) ▷ zip ≫ eq`
/// - AND of N conditions: `(cond_1, …, cond_N) ▷ zip ≫ and` where each cond is the single form
fn collect_join_conditions(refinement: &Expr) -> Option<Vec<(Expr, Expr)>> {
    // Single condition
    if let Some((ka, kb)) = extract_single_eq_condition(refinement) {
        return Some(vec![(ka.clone(), kb.clone())]);
    }
    // AND of conditions: (cond1, ..., condN) ▷ zip ≫ and
    // Conditions may themselves be nested ANDs (left-associative lowering of `a and b and c`).
    let TypedExprNode::Compose(elts) = &refinement.node else {
        return None;
    };
    if elts.len() != 2 {
        return None;
    }
    if !matches!(&elts[1].node, TypedExprNode::Var(v) if v == "and") {
        return None;
    }
    let TypedExprNode::Apply {
        function: zip_fn,
        argument: args,
    } = &elts[0].node
    else {
        return None;
    };
    if !matches!(&zip_fn.node, TypedExprNode::Var(v) if v == "zip") {
        return None;
    }
    let TypedExprNode::Tuple(conds) = &args.node else {
        return None;
    };
    let mut result = Vec::new();
    for c in conds {
        // Recursively flatten nested ANDs; otherwise expect a single eq condition.
        if let Some(nested) = collect_join_conditions(c) {
            result.extend(nested);
        } else {
            let (ka, kb) = extract_single_eq_condition(c)?;
            result.push((ka.clone(), kb.clone()));
        }
    }
    Some(result)
}

/// Runs a BFS over the join condition graph and returns the spanning-tree children list.
///
/// `conditions` is a list of `(arm_a, arm_b, key_expr_a, key_expr_b)` tuples representing
/// undirected edges between arms.  `n` is the total number of arms (nodes in the graph).
///
/// The returned `Vec` has one slot per arm; `result[i]` lists the BFS children of arm `i`
/// in discovery order.  Returns `None` if the graph is disconnected (not all `n` arms are
/// reachable from arm 0).
fn spanning_tree_children(
    conditions: &[(usize, usize, Expr, Expr)],
    n: usize,
) -> Option<Vec<Vec<usize>>> {
    if n == 0 {
        return None;
    }
    let mut visited = vec![false; n];
    let mut children: Vec<Vec<usize>> = vec![vec![]; n];
    let mut queue = VecDeque::new();
    visited[0] = true;
    queue.push_back(0);
    while let Some(node) = queue.pop_front() {
        for &(a, b, _, _) in conditions.iter() {
            let neighbor = if a == node && !visited[b] {
                Some(b)
            } else if b == node && !visited[a] {
                Some(a)
            } else {
                None
            };
            if let Some(nbr) = neighbor {
                visited[nbr] = true;
                children[node].push(nbr);
                queue.push_back(nbr);
            }
        }
    }
    visited.iter().all(|&v| v).then_some(children)
}

/// A tree of joins.  Hash joins are two-way joins with an equality predicate between the two sides,
/// and loop joins are iteration of a tuple of inputs, along with a predicate over those inputs.
/// The leafs of the tree are always Loop joins (ideally the trivial case containing a single input).
#[allow(clippy::large_enum_variant)]
enum JoinPlan {
    Loop {
        /// Which of the original input arms need to be iterated
        arms: Vec<usize>,
        /// Optionally, a predicate to apply after iteration.
        /// The predicate must only rely on the arms present in the loop join.
        predicate: Option<Expr>,
    },
    Hash {
        /// Build side of the join.  May itself be the output of another join.
        build: Box<JoinPlan>,
        /// Probe side of the join.  May itself be the output of another join.
        probe: Box<JoinPlan>,
        /// Index of the build-side key in the type of the build side.  This does not correspond
        /// directly with the indices in the original, unplanned tuple type.
        build_key_idx: Option<usize>,
        /// Expression which is a function from domain type to key type for the build side. This
        /// does not contain the projection to extract the domain value from the input tuple type;
        /// that needs to be constructed as part of translating the join plan to CCL.
        build_key_expr: Expr,
        /// Index of the probe-side key in the type of the probe side.  This does not correspond
        /// directly with the indices in the original, unplanned tuple type.
        probe_key_idx: Option<usize>,
        /// Expression which is a function from domain type to key type for the probe side. This
        /// does not contain the projection to extract the domain value from the input tuple type;
        /// that needs to be constructed as part of translating the join plan to CCL.
        probe_key_expr: Expr,
        /// Additional, non-hash-join, predicate to apply to the result of the join.
        predicate: Option<Expr>,
    },
}

impl Debug for JoinPlan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JoinPlan::Loop { arms, predicate } => f
                .debug_struct("Loop")
                .field("arms", arms)
                .field(
                    "predicate",
                    &predicate.as_ref().map(symbolic).unwrap_or("None".into()),
                )
                .finish(),
            JoinPlan::Hash {
                build,
                probe,
                build_key_idx,
                build_key_expr,
                probe_key_idx,
                probe_key_expr,
                predicate,
            } => f
                .debug_struct("Hash")
                .field("build", build)
                .field("probe", probe)
                .field("build_key_idx", build_key_idx)
                .field("build_key_expr", &symbolic(build_key_expr))
                .field("probe_key_idx", probe_key_idx)
                .field("probe_key_expr", &symbolic(probe_key_expr))
                .field(
                    "predicate",
                    &predicate.as_ref().map(symbolic).unwrap_or("None".into()),
                )
                .finish(),
        }
    }
}

/// Returns all arm indices in the BFS subtree rooted at `node`, in pre-order.
///
/// `children[i]` is the list of direct children of arm `i` in the spanning tree (as
/// produced by [`spanning_tree_children`]).
fn subtree_arms(node: usize, children: &[Vec<usize>]) -> Vec<usize> {
    let mut arms = vec![node];
    for &child in &children[node] {
        arms.extend(subtree_arms(child, children));
    }
    arms
}

/// Builds a residual predicate expression from extra (non-spanning-tree) join conditions.
///
/// `extra` is a slice of `(arm_a, arm_b, key_a, key_b)` conditions that were not used as
/// hash-join keys.  `arm_order[i]` gives the canonical arm index at flat-domain position `i`;
/// it is used to compute the tuple projections.  `arm_types` provides the type of each arm.
///
/// Each condition becomes an equality check `(proj_a ≫ key_a, proj_b ≫ key_b) ▷ zip ≫ eq`
/// over the flat domain tuple; multiple conditions are combined with `and`.
fn build_residual_predicate(
    extra: &[&(usize, usize, Expr, Expr)],
    arm_order: &[usize],
    arm_types: &[Type],
) -> Option<Expr> {
    if extra.is_empty() {
        return None;
    }

    let flat_domain_ty = Type::Tuple(arm_order.iter().map(|&i| arm_types[i].clone()).collect());
    let bool_ty = Type::Base(BaseType::Bool);

    let preds: Vec<Expr> = extra
        .iter()
        .map(|(arm_a, arm_b, key_a, key_b)| {
            let pos_a = arm_order.iter().position(|&a| a == *arm_a).unwrap();
            let pos_b = arm_order.iter().position(|&a| a == *arm_b).unwrap();

            let arm_ty_a = key_a.ty.domain().unwrap().clone();
            let arm_ty_b = key_b.ty.domain().unwrap().clone();
            let key_ty = key_a.ty.codomain().unwrap().clone();

            let proj_a =
                Expr::proj_index(pos_a).with_ty(Type::fun(flat_domain_ty.clone(), arm_ty_a));
            let lhs = typed_compose(vec![proj_a, key_a.clone()]);

            let proj_b =
                Expr::proj_index(pos_b).with_ty(Type::fun(flat_domain_ty.clone(), arm_ty_b));
            let rhs = typed_compose(vec![proj_b, key_b.clone()]);

            // (lhs, rhs) ▷ zip ≫ eq : flat_domain_ty → Bool
            let zip_input_ty = Type::Tuple(vec![
                Type::fun(flat_domain_ty.clone(), key_ty.clone()),
                Type::fun(flat_domain_ty.clone(), key_ty.clone()),
            ]);
            let zip_out_ty = Type::fun(
                flat_domain_ty.clone(),
                Type::Tuple(vec![key_ty.clone(), key_ty.clone()]),
            );
            let zip_args = Expr::tuple(vec![lhs, rhs]).with_ty(zip_input_ty);
            let zipped = apply_function(zip_args, Expr::var("zip"), zip_out_ty);

            typed_compose(vec![
                zipped,
                Expr::var("eq").with_ty(Type::fun(
                    Type::Tuple(vec![key_ty.clone(), key_ty]),
                    bool_ty.clone(),
                )),
            ])
        })
        .collect();

    if preds.len() == 1 {
        preds.into_iter().next()
    } else {
        // (pred_1, ..., pred_n) ▷ zip ≫ and : flat_domain_ty → Bool
        let n = preds.len();
        let preds_tuple_ty = Type::Tuple(
            (0..n)
                .map(|_| Type::fun(flat_domain_ty.clone(), bool_ty.clone()))
                .collect(),
        );
        let zip_out_ty = Type::fun(
            flat_domain_ty.clone(),
            Type::Tuple((0..n).map(|_| bool_ty.clone()).collect()),
        );
        let preds_tuple = Expr::tuple(preds).with_ty(preds_tuple_ty);
        let zipped = apply_function(preds_tuple, Expr::var("zip"), zip_out_ty);
        let bool_tuple_ty = Type::Tuple((0..n).map(|_| bool_ty.clone()).collect());
        Some(typed_compose(vec![
            zipped,
            Expr::var("and").with_ty(Type::fun(bool_tuple_ty, bool_ty)),
        ]))
    }
}

/// Recursively builds a [`JoinPlan`] from a BFS spanning-tree, rooted at `node`.
///
/// `children[i]` lists the direct children of arm `i` in the spanning tree (see
/// [`spanning_tree_children`]).  `conditions` is the full list of equality conditions
/// `(arm_a, arm_b, key_expr_a, key_expr_b)`.  `arm_types[i]` is the type of arm `i`.
///
/// Returns `(plan, arm_order)` where `arm_order[i]` is the canonical arm index at output
/// position `i` of the plan's domain tuple, or `None` if any required condition is missing.
fn build_join_plan(
    node: usize,
    children: &[Vec<usize>],
    conditions: &[(usize, usize, Expr, Expr)],
    arm_types: &[Type],
) -> Option<(JoinPlan, Vec<usize>)> {
    let mut probe_plan = JoinPlan::Loop {
        arms: vec![node],
        predicate: None,
    };
    let mut probe_arms = vec![node];

    // Build a left-deep sequence of hash joins: for each BFS child, hash-join its subtree
    // (build side) onto the accumulated probe side.  The first straddling condition drives
    // the hash key; any remaining ones become a residual predicate at this node.
    for &child in &children[node] {
        let build_arms = subtree_arms(child, children);
        let (build_plan, _) = build_join_plan(child, children, conditions, arm_types)?;

        // Collect all conditions straddling the current probe side and the child's subtree.
        let straddling: Vec<&(usize, usize, Expr, Expr)> = conditions
            .iter()
            .filter(|(a, b, _, _)| {
                (probe_arms.contains(a) && build_arms.contains(b))
                    || (probe_arms.contains(b) && build_arms.contains(a))
            })
            .collect();

        // The first straddling condition drives the hash join key.
        let (arm_a, arm_b, key_a, key_b) = *straddling.first()?;

        // Orient so that probe_arm is on the probe side.
        let (probe_arm, build_arm, probe_key_expr, build_key_expr) = if probe_arms.contains(arm_a) {
            (*arm_a, *arm_b, key_a.clone(), key_b.clone())
        } else {
            (*arm_b, *arm_a, key_b.clone(), key_a.clone())
        };

        let probe_key_idx = probe_arms.iter().position(|&a| a == probe_arm)?;
        let build_key_idx = build_arms.iter().position(|&a| a == build_arm)?;

        let probe_len_before = probe_arms.len();
        let build_len = build_arms.len();

        // Extend probe_arms to the combined arm order before building the predicate,
        // so that projections reference the correct positions in the flat domain.
        probe_arms.extend(build_arms.iter().copied());

        // Any remaining straddling conditions become a residual predicate at this node.
        let predicate = build_residual_predicate(&straddling[1..], &probe_arms, arm_types);

        probe_plan = JoinPlan::Hash {
            probe: Box::new(probe_plan),
            build: Box::new(build_plan),
            probe_key_idx: if probe_len_before == 1 {
                None
            } else {
                Some(probe_key_idx)
            },
            probe_key_expr,
            build_key_idx: if build_len == 1 {
                None
            } else {
                Some(build_key_idx)
            },
            build_key_expr,
            predicate,
        };
    }

    Some((probe_plan, probe_arms))
}

/// Analyzes a loop-join refinement and returns a [`JoinPlan`] if it can be converted to
/// hash joins, or `None` otherwise.
///
/// `arm_types` is the ordered list of types for each arm of the loop join (length ≥ 2).
/// `refinement` is the join predicate over the n-tuple domain; it must decompose into
/// single-arm equality conditions (see [`collect_join_conditions`]).  Returns `None` if the
/// condition graph is disconnected or any condition spans more than one arm per side.
fn plan_loop_join(arm_types: &[Type], refinement: &Expr) -> Option<(JoinPlan, Vec<usize>)> {
    let n = arm_types.len();
    if n < 2 {
        trace!("plan_loop_join: tuple has {} elements, need at least 2", n);
        return None;
    }

    let conditions = collect_join_conditions(refinement)?;

    // For each condition, determine which arms each side depends on and strip the
    // tuple projection, leaving a function of just that arm's type.
    let mut processed: Vec<(usize, usize, Expr, Expr)> = Vec::new();

    for (raw_a, raw_b) in &conditions {
        let arm_a = is_function_of_single_tuple_arm(raw_a)?;
        let arm_b = is_function_of_single_tuple_arm(raw_b)?;

        if arm_a == arm_b {
            trace!("plan_loop_join: condition has both keys on same arm {arm_a}");
            return None;
        }
        if arm_a >= n || arm_b >= n {
            trace!("plan_loop_join: arm index out of range ({arm_a}, {arm_b}) for n={n}");
            return None;
        }

        let mut key_a = raw_a.clone();
        let mut key_b = raw_b.clone();
        replace_tuple_project_with_id(&mut key_a, &arm_types[arm_a]);
        typecheck(&key_a).ok()?;
        replace_tuple_project_with_id(&mut key_b, &arm_types[arm_b]);
        typecheck(&key_b).ok()?;

        trace!(
            "plan_loop_join: condition arm{arm_a}={} : {}  arm{arm_b}={} : {}",
            symbolic(&key_a),
            key_a.ty,
            symbolic(&key_b),
            key_b.ty,
        );

        processed.push((arm_a, arm_b, key_a, key_b));
    }

    let children = spanning_tree_children(&processed, n)?;
    build_join_plan(0, &children, &processed, arm_types)
}

/// Concatenates two types into a single flat tuple type.
///
/// `indices_to_flatten` controls which arguments are unpacked: if `0` is present, `a` is
/// flattened (its tuple elements are spliced in directly); if `1` is present, `b` is
/// flattened; otherwise the type is treated as a single-element contribution.  Used to
/// compute the flat output domain of a hash join.
fn flatten_tuple_types(indices_to_flatten: &[i64], a: &Type, b: &Type) -> Type {
    let mut elts: Vec<Type> = match a {
        Type::Tuple(v) if indices_to_flatten.contains(&0) => v.clone(),
        other => vec![other.clone()],
    };
    match b {
        Type::Tuple(v) if indices_to_flatten.contains(&1) => elts.extend(v.clone()),
        other => elts.push(other.clone()),
    }
    Type::Tuple(elts)
}

/// Generates a CCL expression from a [`JoinPlan`].
///
/// `types[i]` is the type of the i-th original input arm.  `plan` is the tree of
/// [`JoinPlan::Hash`] and [`JoinPlan::Loop`] nodes produced by [`build_join_plan`].
fn join_plan_to_expr(plan: &JoinPlan, types: &[Type]) -> Expr {
    match plan {
        // For loop joins (including the trivial one-branch sort), iterate a tuple
        // type consisting of the types of just the arms in this join.
        JoinPlan::Loop { arms, predicate } => {
            let base_iteration = (|| {
                if arms.len() == 1 {
                    if let Type::Refinement(base_ty, refinement) = &types[arms[0]] {
                        if let RefinementKind::Predicate(pred_rc) = &refinement.kind {
                            let pred = pred_rc.borrow().clone();
                            trace!("Attempting loop join conversion inside iteration");
                            if let Some(transformed) = convert_loop_join(base_ty, &pred) {
                                trace!(
                                    "Converted iteration to {} : {}",
                                    symbolic(&transformed),
                                    transformed.ty
                                );
                                return transformed;
                            }
                        }
                    }
                    Expr::var("id")
                        .with_ty(Type::fun(types[arms[0]].clone(), types[arms[0]].clone()))
                } else {
                    let ty = Type::Tuple(arms.iter().map(|&i| types[i].clone()).collect());
                    Expr::var("id").with_ty(Type::fun(ty.clone(), ty))
                }
            })();
            if let Some(predicate) = predicate {
                let result_ty = base_iteration.ty.clone();
                apply_primitive(
                    typed_compose(vec![base_iteration, predicate.clone()]),
                    "restrict",
                    result_ty,
                )
            } else {
                base_iteration
            }
        }

        // For hash joins, recursively build up the expressions for the build side and probe
        // side, then combine them as follows:
        //
        // Compute the build key:
        //    build_key = build ≫ .build_key_idx ≫ build_key_expr
        // Compute the probe key:
        //    probe_key: probe ≫ .probe_key_idx ≫ probe_key_expr
        // Run the hash join by conversing the build key, composing that with the probe key,
        // then massaging the domain to get back to the expected tuple structure:
        //    (probe_key ≫ build_key ▷ converse) ▷ uncurry ▷ flatten_domain ▷ map_domain
        //
        // Using the full probe/build output tuple types (not just the scalar key-arm types)
        // ensures that `flatten_domain` correctly flattens a tuple-of-tuples domain into a
        // single flat tuple, which `map_domain` then exposes as the final iteration domain.
        JoinPlan::Hash {
            build,
            probe,
            build_key_idx,
            build_key_expr,
            probe_key_idx,
            probe_key_expr,
            predicate,
        } => {
            let key_ty = build_key_expr
                .ty
                .codomain()
                .expect("build key must be a function")
                .clone();

            // Build side: group by the build key using converse.
            // Use the full build output tuple type so that converse groups entire
            // build tuples (not just the key arm), preserving all arms through the join.
            let build_input = join_plan_to_expr(build, types);
            let build_output_ty = build_input.ty.codomain().unwrap().clone();
            let build_key = if let Some(build_key_idx) = build_key_idx {
                typed_compose(vec![
                    build_input.clone(),
                    Expr::proj_index(*build_key_idx).with_ty(Type::fun(
                        build_output_ty.clone(),
                        build_key_expr.ty.domain().unwrap().clone(),
                    )),
                    build_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![build_input.clone(), build_key_expr.clone()])
            };

            let converse_ty = Type::fun(
                key_ty.clone(),
                Type::fun(build_output_ty.clone(), build_output_ty.clone()),
            );
            let build_side = apply_primitive(build_key, "converse", converse_ty);
            typecheck(&build_side).expect("Bad build expr");

            trace!(
                "join_plan_to_expr: build_side={} : {}",
                symbolic(&build_side),
                build_side.ty
            );

            // Probe side: compose the probe key with the build side lookup.
            // Use the full probe output tuple type for the same reason.
            let probe_input = join_plan_to_expr(probe, types);
            let probe_output_ty = probe_input.ty.codomain().unwrap().clone();
            let probe_key = if let Some(probe_key_idx) = probe_key_idx {
                typed_compose(vec![
                    probe_input.clone(),
                    Expr::proj_index(*probe_key_idx).with_ty(Type::fun(
                        probe_output_ty.clone(),
                        probe_key_expr.ty.domain().unwrap().clone(),
                    )),
                    probe_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![probe_input.clone(), probe_key_expr.clone()])
            };

            let probe_expr = typed_compose(vec![probe_key, build_side.clone()]);
            typecheck(&probe_expr).expect("Bad probe expr");

            trace!(
                "join_plan_to_expr: probe={} : {}",
                symbolic(&probe_expr),
                probe_expr.ty
            );

            // uncurry: (probe_output_ty, build_output_ty) -> build_output_ty
            let uncurry = apply_primitive(
                probe_expr,
                "uncurry",
                Type::fun(
                    Type::Tuple(vec![probe_output_ty.clone(), build_output_ty.clone()]),
                    build_output_ty.clone(),
                ),
            );

            trace!(
                "join_plan_to_expr: uncurry={} : {}",
                symbolic(&uncurry),
                uncurry.ty
            );

            // For each join input that is itself a Hash join, we need to flatten its domain
            // tuple into the result domain tuple.
            let mut indices_to_flatten = Vec::<i64>::new();
            if probe_key_idx.is_some() {
                indices_to_flatten.push(0);
            }
            if build_key_idx.is_some() {
                indices_to_flatten.push(1);
            }
            let flattened = if indices_to_flatten.is_empty() {
                uncurry
            } else {
                let flat_ty =
                    flatten_tuple_types(&indices_to_flatten, &probe_output_ty, &build_output_ty);
                let flatten_func = apply_primitive(
                    Expr::list(
                        indices_to_flatten
                            .iter()
                            .map(|i| Expr::lit(Lit::Int(*i)).with_ty(Type::Base(BaseType::Int)))
                            .collect(),
                    )
                    .with_ty(Type::fun(
                        Type::UIntRange(indices_to_flatten.len()),
                        Type::Base(BaseType::Int),
                    )),
                    "flatten_domain",
                    Type::fun(
                        Type::fun(
                            Type::Tuple(vec![probe_output_ty.clone(), build_output_ty.clone()]),
                            build_output_ty.clone(),
                        ),
                        Type::fun(flat_ty.clone(), build_output_ty.clone()),
                    ),
                );
                let flattened = apply_function(
                    uncurry,
                    flatten_func,
                    Type::fun(flat_ty.clone(), build_output_ty.clone()),
                );

                trace!(
                    "join_plan_to_expr: flattened={} : {}",
                    symbolic(&flattened),
                    flattened.ty
                );
                flattened
            };

            let final_domain_ty = flattened.ty.domain().unwrap().clone();
            // map_domain: replace the codomain with Scalar(domain), yielding flat_ty -> flat_ty.
            let map_domain = apply_primitive(
                flattened,
                "map_domain",
                Type::fun(final_domain_ty.clone(), final_domain_ty.clone()),
            );

            let result = if let Some(predicate) = predicate {
                let result_ty = map_domain.ty.clone();
                apply_primitive(
                    typed_compose(vec![map_domain, predicate.clone()]),
                    "restrict",
                    result_ty,
                )
            } else {
                map_domain
            };

            typecheck(&result).expect("Bad hash join expr");
            result
        }
    }
}

/// Converts a loop-join refinement pattern into a hash-join expression.
///
/// Delegates to [`plan_loop_join`] to build a [`JoinPlan`], then to [`join_plan_to_expr`]
/// to generate the CCL output. Returns `None` if the pattern does not match.
fn convert_loop_join(base_ty: &Type, refinement: &Expr) -> Option<Expr> {
    trace!(
        "convert_loop_join: base_ty={}, refinement={} : {}",
        base_ty,
        symbolic(refinement),
        refinement.ty
    );
    trace!("typed refinement\n{}", symbolic_typed(refinement));

    let Type::Tuple(arm_types) = base_ty else {
        trace!("convert_loop_join: base_ty is not a tuple");
        return None;
    };
    let (plan, arm_order) = plan_loop_join(arm_types, refinement)?;
    trace!("convert_loop_join: planning succeeded. Plan:\n{plan:#?}");
    let expr = join_plan_to_expr(&plan, arm_types);

    // If BFS produced arms out of canonical order, undo the permutation so that the
    // output domain matches the original tuple type expected by the caller.
    let canonical: Vec<usize> = (0..arm_types.len()).collect();
    if arm_order == canonical {
        return Some(expr);
    }

    // perm[j] = position of canonical arm j in arm_order (i.e. where to find it in actual).
    // permute_domain(perm)(f : actual → X) : canonical → X
    let actual_ty = Type::Tuple(arm_order.iter().map(|&i| arm_types[i].clone()).collect());
    let canonical_ty = Type::Tuple(arm_types.to_vec());
    let perm: Vec<i64> = canonical
        .iter()
        .map(|&j| arm_order.iter().position(|&a| a == j).unwrap() as i64)
        .collect();

    let perm_arg = Expr::list(
        perm.iter()
            .map(|&i| Expr::lit(Lit::Int(i)).with_ty(Type::Base(BaseType::Int)))
            .collect(),
    )
    .with_ty(Type::fun(
        Type::UIntRange(perm.len()),
        Type::Base(BaseType::Int),
    ));

    let permute_func = apply_primitive(
        perm_arg,
        "permute_domain",
        Type::fun(
            Type::fun(actual_ty.clone(), actual_ty.clone()),
            Type::fun(canonical_ty.clone(), actual_ty.clone()),
        ),
    );
    let permuted = apply_function(
        expr,
        permute_func,
        Type::fun(canonical_ty.clone(), actual_ty.clone()),
    );
    let result = apply_primitive(
        permuted,
        "map_domain",
        Type::fun(canonical_ty.clone(), canonical_ty.clone()),
    );
    typecheck(&result).expect("Bad permute_domain expr");
    Some(result)
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
/// Supports n-way joins (n ≥ 2) when all arms are connected via equality conditions that
/// form a spanning tree.  Build/probe assignment follows the BFS order of that spanning tree.
/// For now, predicates must be expressed as conjunctions of single-arm equality conditions.
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
                if let Some(transformed) = convert_loop_join(&base, &pred) {
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
    fn test_is_function_of_single_tuple_arm_on_projection() {
        let expr = proj_idx(0);
        assert_eq!(is_function_of_single_tuple_arm(&expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_second_index() {
        let expr = proj_idx(1);
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
        let expr = compose(vec![proj_idx(1).with_ty(proj0_ty), var("f").with_ty(f_ty)]);
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
        typecheck(&expr).expect("Type checking failed after replacement");
    }

    #[test]
    fn test_replace_tuple_project_with_id_on_compose() {
        let int_ty_val = int_ty();
        let proj0_ty = fun_ty(tuple_ty(vec![int_ty(), int_ty()]), int_ty());
        let f_ty = fun_ty(int_ty(), int_ty());
        let mut expr = compose(vec![
            proj_idx(1).with_ty(proj0_ty),
            var("f").with_ty(f_ty.clone()),
        ])
        .with_ty(f_ty);
        replace_tuple_project_with_id(&mut expr, &int_ty_val);

        // After replacement, first element should be identity
        if let TypedExprNode::Compose(elts) = &expr.node {
            assert!(matches!(elts[0].node, TypedExprNode::Var(ref v) if v == "id"));
        } else {
            panic!("Expected Compose node");
        }
        typecheck(&expr).expect("Type checking failed after replacement");
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
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Base type is not a tuple, should return None
        let result = convert_loop_join(&int_ty_val, &refinement);
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
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Refinement is not a valid join condition, should return None
        let result = convert_loop_join(&triple_tuple, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_compose_refinement() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let refinement = var("ref").with_ty(int_ty_val.clone());

        // Refinement is not a compose, should return None
        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_wrong_compose_size() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose with 3 elements (not 2)
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
            var("h").with_ty(f_ty),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_eq_second_element() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose where second element is not "eq"
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("ne").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_missing_zip_apply() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Create a compose where first element is not an Apply
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            var("f").with_ty(f_ty),
            var("eq").with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_non_zip_function() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

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

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_zip_with_non_tuple_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

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

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_mismatched_zip_args() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

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

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_rejects_same_key_index() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

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

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    #[test]
    fn test_convert_loop_join_succeeds_with_valid_input() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

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
        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed with valid hash join pattern"
        );

        assert_eq!(
            symbolic(&result.unwrap()),
            "(id ≫ id ≫ (id ≫ id) ▷ converse) ▷ uncurry ▷ map_domain"
        );
    }

    // Tests for is_function_of_single_tuple_arm with zip applications
    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_with_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(proj(0), ...) should return 0
        let arg = proj_idx(0).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, var("zip").with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_with_second_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(proj(1), ...) should return 1
        let arg = proj_idx(1).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, var("zip").with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), Some(1));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_zip_without_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let zip_fn_ty = fun_ty(
            tuple_ty(vec![int_ty(), int_ty()]),
            tuple_ty(vec![int_ty(), int_ty()]),
        );
        // zip(f, ...) where f is not a projection should return None
        let arg = var("f").with_ty(f_ty);
        let zip_app = Expr::apply(arg, var("zip").with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), None);
    }

    // Tests for is_function_of_single_tuple_arm with tuples
    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_single_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        // A tuple containing a single projection should return that projection's index
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let tuple_expr = Expr::tuple(vec![proj_idx(0).with_ty(proj_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_all_same_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where all non-constant elements use the same projection
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(0).with_ty(proj_ty.clone()),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_different_projections() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where elements use different projections should return None
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(1).with_ty(proj_ty.clone()),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), None);
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_with_constants() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple with a projection and constant expressions should ignore constants
        let tuple_expr = Expr::tuple(vec![
            proj_idx(0).with_ty(proj_ty),
            apply_primitive(var("c").with_ty(int_ty()), "const", const_fn_ty),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_no_projections() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        // A tuple with no projections (non-constant) should return None
        let f_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let tuple_expr = Expr::tuple(vec![var("f").with_ty(f_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), None);
    }

    // Tests for is_constant helper
    #[test]
    fn test_is_constant_on_const_apply() {
        let int_ty_val = int_ty();
        let const_expr = apply_primitive(var("c").with_ty(int_ty_val.clone()), "const", int_ty_val);
        assert!(is_constant(&const_expr));
    }

    #[test]
    fn test_is_constant_on_non_const_apply() {
        let int_ty_val = int_ty();
        let non_const_expr =
            apply_primitive(var("f").with_ty(int_ty_val.clone()), "map", int_ty_val);
        assert!(!is_constant(&non_const_expr));
    }

    #[test]
    fn test_is_constant_on_compose_with_const() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);
        let const_fn_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let g_ty = fun_ty(int_ty_val.clone(), int_ty_val.clone());
        let const_expr =
            apply_primitive(var("c").with_ty(int_ty_val.clone()), "const", const_fn_ty);
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
            proj_idx(0).with_ty(proj_ty),
            var("zip").with_ty(zip_fn_ty.clone()),
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
            proj_idx(0).with_ty(proj_ty.clone()),
            proj_idx(0).with_ty(proj_ty),
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
                    Type::Fun(domain, _) => {
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
            "const",
            const_fn_ty.clone(),
        );

        let mut expr =
            Expr::tuple(vec![proj_idx(0).with_ty(proj_ty), const_expr]).with_ty(tuple_ty(vec![
                fun_ty(tuple_ty_val.clone(), int_ty_val.clone()),
                const_fn_ty,
            ]));

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

        let mut expr = apply_primitive(var("c").with_ty(int_ty_val.clone()), "const", const_fn_ty);

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun(domain, _) = &expr.ty {
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

        let const_expr =
            apply_primitive(var("c").with_ty(int_ty_val.clone()), "const", const_fn_ty);

        let mut expr = compose(vec![const_expr, var("g").with_ty(g_ty)])
            .with_ty(fun_ty(tuple_ty_val, int_ty_val.clone()));

        replace_constant_domain_type(&mut expr, &int_ty_val);

        // After replacement, domain should be updated
        if let Type::Fun(domain, _) = &expr.ty {
            assert_eq!(**domain, int_ty_val);
        } else {
            panic!("Expected function type");
        }
    }

    /// Builds a dummy condition tuple; the Expr fields are placeholders since
    /// `spanning_tree_children` and `build_join_plan` only inspect the arm indices.
    fn cond(a: usize, b: usize) -> (usize, usize, Expr, Expr) {
        (a, b, var("k"), var("k"))
    }

    // --- spanning_tree_children ---

    #[test]
    fn test_spanning_tree_n_zero_returns_none() {
        assert_eq!(spanning_tree_children(&[], 0), None);
    }

    #[test]
    fn test_spanning_tree_n_one_single_leaf() {
        // No edges needed; the single node is already its own spanning tree.
        let children = spanning_tree_children(&[], 1).unwrap();
        assert_eq!(children, vec![vec![]]);
    }

    #[test]
    fn test_spanning_tree_two_arm_linear() {
        let children = spanning_tree_children(&[cond(0, 1)], 2).unwrap();
        assert_eq!(children, vec![vec![1], vec![]]);
    }

    #[test]
    fn test_spanning_tree_three_arm_linear() {
        // 0-1-2 chain; BFS from 0 should visit 1 then 2.
        let children = spanning_tree_children(&[cond(0, 1), cond(1, 2)], 3).unwrap();
        assert_eq!(children, vec![vec![1], vec![2], vec![]]);
    }

    #[test]
    fn test_spanning_tree_star_canonical_condition_order() {
        // Hub 0 connects to 1 then 2; conditions listed 0-1 before 0-2.
        let children = spanning_tree_children(&[cond(0, 1), cond(0, 2)], 3).unwrap();
        assert_eq!(children, vec![vec![1, 2], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_star_reversed_condition_order() {
        // Same topology but 0-2 listed first; BFS picks up 2 before 1.
        let children = spanning_tree_children(&[cond(0, 2), cond(0, 1)], 3).unwrap();
        assert_eq!(children, vec![vec![2, 1], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_two_level_branching() {
        // 0 -> {1, 2}, 1 -> {3, 4}: branching at root and at an intermediate node.
        let children =
            spanning_tree_children(&[cond(0, 1), cond(0, 2), cond(1, 3), cond(1, 4)], 5).unwrap();
        assert_eq!(
            children,
            vec![vec![1, 2], vec![3, 4], vec![], vec![], vec![]]
        );
    }

    #[test]
    fn test_spanning_tree_cyclic_graph() {
        // Triangle 0-1-2-0: BFS from 0 reaches 1 via cond(0,1) and 2 via cond(2,0) in the
        // same round, so the cycle edge cond(1,2) is pruned and all nodes are still reached.
        let children = spanning_tree_children(&[cond(0, 1), cond(1, 2), cond(2, 0)], 3).unwrap();
        assert_eq!(children, vec![vec![1, 2], vec![], vec![]]);
    }

    #[test]
    fn test_spanning_tree_disconnected_returns_none() {
        // Only arm 0 and 1 are connected; arm 2 is unreachable.
        assert_eq!(spanning_tree_children(&[cond(0, 1)], 3), None);
    }

    // --- subtree_arms ---

    #[test]
    fn test_subtree_arms_single_leaf() {
        let children = vec![vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0]);
    }

    #[test]
    fn test_subtree_arms_linear_chain_from_root() {
        // 0 -> 1 -> 2
        let children = vec![vec![1], vec![2], vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0, 1, 2]);
    }

    #[test]
    fn test_subtree_arms_linear_chain_from_middle() {
        // Starting at node 1 should only include 1 and 2.
        let children = vec![vec![1], vec![2], vec![]];
        assert_eq!(subtree_arms(1, &children), vec![1, 2]);
    }

    #[test]
    fn test_subtree_arms_star() {
        // 0 -> {1, 2}; all three arms should appear.
        let children = vec![vec![1, 2], vec![], vec![]];
        assert_eq!(subtree_arms(0, &children), vec![0, 1, 2]);
    }

    // --- build_join_plan ---

    #[test]
    fn test_build_join_plan_two_arms_canonical_order() {
        let conditions = vec![cond(0, 1)];
        let children = vec![vec![1], vec![]];
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[]).unwrap();
        assert_eq!(arm_order, vec![0, 1]);
        // Single join: no tuple projection needed on either side.
        let JoinPlan::Hash {
            probe_key_idx,
            build_key_idx,
            ..
        } = plan
        else {
            panic!("expected Hash");
        };
        assert_eq!(probe_key_idx, None);
        assert_eq!(build_key_idx, None);
    }

    #[test]
    fn test_build_join_plan_three_arm_linear_canonical_order() {
        // 0-1-2 chain; conditions x==y (0,1) then y==z (1,2).
        let conditions = vec![cond(0, 1), cond(1, 2)];
        let children = vec![vec![1], vec![2], vec![]];
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[]).unwrap();
        assert_eq!(arm_order, vec![0, 1, 2]);
        // Outer join probes with Loop([0]) (single arm → probe_key_idx=None) against the
        // inner Hash{Loop([1]),Loop([2])}.  The join key is arm 1, which sits at position 0
        // in the inner join's output arms [1,2], so build_key_idx=Some(0).
        let JoinPlan::Hash {
            probe_key_idx,
            build_key_idx,
            ..
        } = plan
        else {
            panic!("expected outer Hash");
        };
        assert_eq!(probe_key_idx, None);
        assert_eq!(build_key_idx, Some(0));
    }

    #[test]
    fn test_build_join_plan_star_out_of_order_produces_permuted_arm_order() {
        // x==z (0,2) listed before x==y (0,1); BFS visits arm 2 before arm 1.
        // arm_order must be [0,2,1], which triggers the permute_domain path.
        let conditions = vec![cond(0, 2), cond(0, 1)];
        let children = vec![vec![2, 1], vec![], vec![]];
        let (_, arm_order) = build_join_plan(0, &children, &conditions, &[]).unwrap();
        assert_eq!(arm_order, vec![0, 2, 1]);
    }

    #[test]
    fn test_build_join_plan_no_straddling_condition_returns_none() {
        // children say arm 1 is a child of arm 0, but conditions only mention arms 0 and 2 —
        // no condition straddles the {0} / {1} split, so planning must fail.
        let conditions = vec![cond(0, 2)];
        let children = vec![vec![1], vec![], vec![]];
        assert!(build_join_plan(0, &children, &conditions, &[]).is_none());
    }
}

//! Hash/loop-join planning (design §6.5).
//!
//! The specialised iteration strategy folded into the materialisation walk:
//! when a site's domain is a refined tuple whose predicate decomposes into
//! equality join conditions, [`try_hash_join_rewrite`] recognises it
//! ([`plan_loop_join`] / [`convert_loop_join`]) and emits a [`JoinPlan`] tree
//! ([`join_plan_to_expr`]) whose leaves are iteration-bearing.

use std::collections::{BTreeSet, VecDeque};
use std::fmt::Debug;
use std::mem::take;

use super::*;

/// Splits a (pointful) join predicate into equality join conditions and
/// residual predicates, each compiled to a point-free morphism over the tuple
/// domain (design §6.5).
///
/// The predicate is **bare** — the refinement binds the implicit
/// REFINEMENT_BINDER as the record `rec`, of type `rec_ty` — and has the shape
/// `rec.0 ▷ l0 ▷ (λ v0 → … rec.k ▷ lk ▷ (λ vk → <bool over v0…vk>))`:
/// each `rec.i ▷ li` binds the element `vi` of arm `i`, and the innermost
/// boolean is a conjunction of `==` conditions and residual predicates over
/// those element binders. We build the `vi ↦ rec.i ▷ li` environment,
/// decompose the boolean (`and` / `==` / other), and for each side substitute
/// the environment and lambda-eliminate `λ rec → side` to recover the
/// combinator morphism over `rec` that [`plan_loop_join`] consumes.
fn split_join_conditions(refinement: &Expr, rec_ty: &Type) -> (Vec<(Expr, Expr)>, Vec<Expr>) {
    let mut eq_conds = Vec::new();
    let mut other_preds = Vec::new();
    // A bare predicate is `Bool`-typed; a function-typed expression here is not a
    // decomposable join predicate, so treat the whole thing as one residual (no
    // join forms — plan_loop_join then bails on the empty equality set).
    if refinement.ty.domain().is_some() {
        other_preds.push(refinement.clone());
        return (eq_conds, other_preds);
    }
    // env: element binder name → its extraction morphism `rec.i ▷ li` (over rec).
    let mut env: Vec<(Name, Expr)> = Vec::new();
    let mut cur = refinement;
    while let TypedExprNode::Apply { argument, function } = &cur.node
        && let TypedExprNode::Lambda {
            param, body: inner, ..
        } = &function.node
    {
        env.push((param.name.clone(), (**argument).clone()));
        cur = inner.as_ref();
    }
    decompose_join_bool(
        cur,
        &env,
        &Name::elem(),
        rec_ty,
        &mut eq_conds,
        &mut other_preds,
    );
    (eq_conds, other_preds)
}

/// Decompose the innermost boolean of a join predicate into equality conditions
/// (`==`, recorded as a pair of compiled sides) and residual predicates,
/// splitting top-level conjunctions.
fn decompose_join_bool(
    e: &Expr,
    env: &[(Name, Expr)],
    rec_name: &Name,
    rec_ty: &Type,
    eq_conds: &mut Vec<(Expr, Expr)>,
    other_preds: &mut Vec<Expr>,
) {
    match &e.node {
        TypedExprNode::BinOp {
            left,
            op: BinOpKind::BoolLogic(LogicKind::And),
            right,
        } => {
            decompose_join_bool(left, env, rec_name, rec_ty, eq_conds, other_preds);
            decompose_join_bool(right, env, rec_name, rec_ty, eq_conds, other_preds);
        }
        TypedExprNode::BinOp {
            left,
            op: BinOpKind::Compare(CompareKind::Equals),
            right,
        } => {
            let ka = compile_join_side(left, env, rec_name, rec_ty);
            let kb = compile_join_side(right, env, rec_name, rec_ty);
            eq_conds.push((ka, kb));
        }
        _ => other_preds.push(compile_join_side(e, env, rec_name, rec_ty)),
    }
}

/// Substitute the element-binder environment into `side` (an expression over
/// the element binders) and lambda-eliminate `λ rec → side` to the point-free
/// morphism over the tuple domain.
fn compile_join_side(side: &Expr, env: &[(Name, Expr)], rec_name: &Name, rec_ty: &Type) -> Expr {
    let mut body = side.clone();
    for (var, morph) in env {
        body = lambda_elim::substitute(body, var, morph);
    }
    let side_ty = body.ty.clone();
    let lam =
        Expr::lambda(rec_name, rec_ty.clone(), body).with_ty(Type::fun(rec_ty.clone(), side_ty));
    lambda_elim::run(lam).expect("lambda-elim of join-condition side")
}

/// Collects the original arm indices accessed by `expr` at domain-accessing positions.
///
/// Follows the same structural rules as [`is_function_of_single_tuple_arm`] but collects
/// all arm indices rather than requiring exactly one.
fn collect_arms_used(expr: &Expr, result: &mut BTreeSet<usize>) {
    match &expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => {
            result.insert(*i);
        }
        TypedExprNode::Compose(elts) => {
            if let Some(first) = elts.first() {
                collect_arms_used(first, result);
            }
        }
        TypedExprNode::Apply { function, argument } if is_builtin(function, Builtin::Zip) => {
            collect_arms_used(argument, result);
        }
        TypedExprNode::Tuple(elts) => {
            for elt in elts {
                if !is_constant(elt) {
                    collect_arms_used(elt, result);
                }
            }
        }
        _ => {}
    }
}

/// Rewrites domain-accessing Proj nodes in a predicate to match a new flat domain ordering.
///
/// `arm_order[j]` is the original arm index at position `j` in the new flat domain.
/// Only rewrites positions that access the tuple domain (Proj at the start of Compose chains,
/// arguments of `zip` applications, elements of domain-valued Tuples).  Domain types throughout
/// the expression are updated to `new_domain_ty`; codomains are left unchanged.
///
/// Mirrors the structural traversal of [`replace_tuple_project_with_id`].
fn reindex_for_domain(expr: &mut Expr, new_domain_ty: &Type, arm_order: &[usize]) {
    // Constant expressions ignore their domain; just update the type.
    if is_constant(expr) {
        replace_constant_domain_type(expr, new_domain_ty);
        return;
    }
    match &mut expr.node {
        TypedExprNode::Proj(ProjKey::Index(i)) => {
            *i = arm_order
                .iter()
                .position(|&a| a == *i)
                .expect("arm index not in arm_order");
            set_domain_ty(&mut expr.ty, new_domain_ty);
        }
        TypedExprNode::Compose(_) => {
            set_domain_ty(&mut expr.ty, new_domain_ty);
            if let TypedExprNode::Compose(elts) = &mut expr.node
                && let Some(first) = elts.first_mut()
            {
                reindex_for_domain(first, new_domain_ty, arm_order);
            }
        }
        TypedExprNode::Apply { .. } => {
            // Only zip applications appear at domain-accessing positions.
            let mut output_ty = expr.ty.clone();
            set_domain_ty(&mut output_ty, new_domain_ty);
            let arg = if let TypedExprNode::Apply { function, argument } = &mut expr.node {
                assert!(
                    is_builtin(function, Builtin::Zip),
                    "unexpected Apply at domain position: {:?}",
                    function.node
                );
                reindex_for_domain(argument, new_domain_ty, arm_order);
                argument.clone()
            } else {
                unreachable!()
            };
            *expr = apply_primitive(*arg, Builtin::Zip, output_ty);
        }
        TypedExprNode::Tuple(_) => {
            if let Type::Tuple(tys) = &mut expr.ty {
                for ty in tys.iter_mut() {
                    if matches!(ty, Type::Fun { .. }) {
                        set_domain_ty(ty, new_domain_ty);
                    }
                }
            }
            if let TypedExprNode::Tuple(elts) = &mut expr.node {
                for elt in elts.iter_mut() {
                    if is_constant(elt) {
                        replace_constant_domain_type(elt, new_domain_ty);
                    } else {
                        reindex_for_domain(elt, new_domain_ty, arm_order);
                    }
                }
            }
        }
        _ => {
            if matches!(expr.ty, Type::Fun { .. }) {
                set_domain_ty(&mut expr.ty, new_domain_ty);
            }
        }
    }
}

/// Combines two optional predicates over the same flat domain with a logical AND.
fn combine_predicates(a: Option<Expr>, b: Option<Expr>) -> Option<Expr> {
    match (a, b) {
        (None, None) => None,
        (Some(p), None) | (None, Some(p)) => Some(p),
        (Some(pa), Some(pb)) => {
            let flat_domain_ty = pa.ty.domain().unwrap().clone();
            let bool_ty = Type::Base(BaseType::Bool);
            let zip_input_ty = Type::Tuple(vec![pa.ty.clone(), pb.ty.clone()]);
            let zip_out_ty = Type::fun(
                flat_domain_ty.clone(),
                Type::Tuple(vec![bool_ty.clone(), bool_ty.clone()]),
            );
            let preds_tuple = Expr::tuple(vec![pa, pb]).with_ty(zip_input_ty);
            let zipped = apply_function(preds_tuple, Expr::builtin(Builtin::Zip), zip_out_ty);
            Some(typed_compose(vec![
                zipped,
                Expr::builtin(Builtin::BinOp(BinOpKind::BoolLogic(LogicKind::And))).with_ty(
                    Type::fun(Type::Tuple(vec![bool_ty.clone(), bool_ty.clone()]), bool_ty),
                ),
            ]))
        }
    }
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
            let zipped = apply_function(zip_args, Expr::builtin(Builtin::Zip), zip_out_ty);

            typed_compose(vec![
                zipped,
                Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals))).with_ty(
                    Type::fun(Type::Tuple(vec![key_ty.clone(), key_ty]), bool_ty.clone()),
                ),
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
        let zipped = apply_function(preds_tuple, Expr::builtin(Builtin::Zip), zip_out_ty);
        let bool_tuple_ty = Type::Tuple((0..n).map(|_| bool_ty.clone()).collect());
        Some(typed_compose(vec![
            zipped,
            Expr::builtin(Builtin::BinOp(BinOpKind::BoolLogic(LogicKind::And)))
                .with_ty(Type::fun(bool_tuple_ty, bool_ty)),
        ]))
    }
}

/// Recursively builds a [`JoinPlan`] from a BFS spanning-tree, rooted at `node`.
///
/// `children[i]` lists the direct children of arm `i` in the spanning tree (see
/// [`spanning_tree_children`]).  `conditions` is the full list of equality conditions
/// `(arm_a, arm_b, key_expr_a, key_expr_b)`.  `arm_types[i]` is the type of arm `i`.
///
/// Starting from `node`, each of its BFS children is joined onto the accumulated
/// probe side in order, producing a left-deep sequence of hash joins.  For each
/// child, ALL conditions straddling the current probe side and the child's subtree
/// are identified: the first drives the hash join key, and any remaining ones become
/// a residual predicate applied at this node.
///
/// `other_predicates` contains non-equality predicates (as original-domain expressions paired
/// with their required arm sets) that should be pushed to the lowest join node where all
/// required arms are present.  Predicates entirely within a child subtree are forwarded to
/// that child's recursive call; predicates that straddle or depend on the current probe side
/// are applied at the first hash join where all their arms are available.
///
/// Returns `(plan, arm_order)` where `arm_order[i]` is the canonical arm index at output
/// position `i` of the plan's domain tuple, or `None` if any required condition is missing.
fn build_join_plan(
    node: usize,
    children: &[Vec<usize>],
    conditions: &[(usize, usize, Expr, Expr)],
    arm_types: &[Type],
    other_predicates: &[(Expr, BTreeSet<usize>)],
) -> Option<(JoinPlan, Vec<usize>)> {
    let mut probe_plan = JoinPlan::Loop {
        arms: vec![node],
        predicate: None,
    };
    let mut probe_arms = vec![node];
    let mut remaining_preds: Vec<(Expr, BTreeSet<usize>)> = other_predicates.to_vec();

    // Build a left-deep sequence of hash joins: for each BFS child, hash-join its subtree
    // (build side) onto the accumulated probe side.  The first straddling condition drives
    // the hash key; any remaining ones become a residual predicate at this node.
    for &child in &children[node] {
        let build_arms = subtree_arms(child, children);

        // Predicates whose required arms are entirely within the child subtree are pushed
        // into the child's plan.  Constant predicates (empty arms_used) are kept at the
        // current level so they can be applied once a flat domain exists.
        let mut child_preds: Vec<(Expr, BTreeSet<usize>)> = Vec::new();
        remaining_preds.retain(|(pred, arms_used)| {
            if !arms_used.is_empty() && arms_used.iter().all(|a| build_arms.contains(a)) {
                child_preds.push((pred.clone(), arms_used.clone()));
                false
            } else {
                true
            }
        });

        let (build_plan, _) =
            build_join_plan(child, children, conditions, arm_types, &child_preds)?;

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

        // Residual equality conditions beyond the first straddling one.
        let mut predicate = build_residual_predicate(&straddling[1..], &probe_arms, arm_types);

        // Apply any other predicates now that all their required arms are available.
        // Build the flat domain type lazily — only when there are other predicates to adapt.
        let applicable: Vec<Expr> = if remaining_preds.is_empty() {
            Vec::new()
        } else {
            let flat_domain_ty =
                Type::Tuple(probe_arms.iter().map(|&i| arm_types[i].clone()).collect());
            let mut app = Vec::new();
            remaining_preds.retain(|(pred, arms_used)| {
                if arms_used.iter().all(|a| probe_arms.contains(a)) {
                    let mut adapted = pred.clone();
                    reindex_for_domain(&mut adapted, &flat_domain_ty, &probe_arms);
                    app.push(adapted);
                    false
                } else {
                    true
                }
            });
            app
        };
        for adapted in applicable {
            predicate = combine_predicates(predicate, Some(adapted));
        }

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

    // For leaf nodes (no children were joined), remaining predicates whose arms are all within
    // the current probe set can be applied directly to the loop plan's predicate field.  This
    // covers the case where a predicate depends only on a single arm (e.g. `y < 2` for an arm
    // `y`), and that arm is itself a leaf with no children to push it into.
    if !remaining_preds.is_empty() {
        let leaf_ty = arm_types[probe_arms[0]].clone();
        let mut leaf_pred: Option<Expr> = None;
        remaining_preds.retain(|(pred, arms_used)| {
            if arms_used.iter().all(|a| probe_arms.contains(a)) {
                let mut adapted = pred.clone();
                replace_tuple_project_with_id(&mut adapted, &leaf_ty);
                leaf_pred = combine_predicates(leaf_pred.take(), Some(adapted));
                false
            } else {
                true
            }
        });
        if let Some(p) = leaf_pred
            && let JoinPlan::Loop { predicate, .. } = &mut probe_plan
        {
            *predicate = combine_predicates(predicate.take(), Some(p));
        }
    }

    assert!(
        remaining_preds.is_empty(),
        "other predicates not placed: {:?}",
        remaining_preds
            .iter()
            .map(|(p, _)| symbolic(p))
            .collect::<Vec<_>>()
    );

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

    let (eq_conditions_raw, other_preds_raw) =
        split_join_conditions(refinement, &Type::Tuple(arm_types.to_vec()));

    if eq_conditions_raw.is_empty() {
        trace!("plan_loop_join: no equality conditions, cannot build hash join");
        return None;
    }

    // For each equality condition, determine which arms each side depends on and strip the
    // tuple projection, leaving a function of just that arm's type.
    let mut processed: Vec<(usize, usize, Expr, Expr)> = Vec::new();

    for (raw_a, raw_b) in &eq_conditions_raw {
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

    // Pair each other predicate with the set of arms it depends on.
    let other_predicates: Vec<(Expr, BTreeSet<usize>)> = other_preds_raw
        .into_iter()
        .map(|pred| {
            let mut arms = BTreeSet::new();
            collect_arms_used(&pred, &mut arms);
            // TODO support constant predicates by constant-folding them away
            assert!(
                !arms.is_empty(),
                "TODO support constant predicates in joins"
            );
            (pred, arms)
        })
        .collect();

    build_join_plan(0, &children, &processed, arm_types, &other_predicates)
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
        //
        // The leaf emission is always `iterate(pred)` — the iteration-site
        // marker that op-conversion compiles to an `IterateExtent` (plus a
        // `Restrict` filter when `pred` is non-trivial).  When the loop has
        // its own residual predicate, it is composed with the base
        // identity and passed as `iterate`'s predicate; when there is no
        // predicate, the trivially-true predicate `true ▷ const` is used
        // and op-conversion recognises it as a filter-free iteration.
        JoinPlan::Loop { arms, predicate } => {
            let base_iteration = (|| {
                if arms.len() == 1 {
                    if let Some(transformed) = convert_refinement_to_join(&types[arms[0]]) {
                        trace!(
                            "Converted iteration to {} : {}",
                            symbolic(&transformed),
                            transformed.ty
                        );
                        return transformed;
                    }
                    make_iterate(trivially_true_predicate(types[arms[0]].clone()))
                } else {
                    let ty = Type::Tuple(arms.iter().map(|&i| types[i].clone()).collect());
                    make_iterate(trivially_true_predicate(ty))
                }
            })();
            if let Some(predicate) = predicate {
                // Apply `restrict(predicate)` to the base iteration source as
                // a downstream filter step.  `restrict(p)` is the transformer
                // `(D ⇒ T) ⇒ ({d : D | p(d)} ⇒ T)`; applying it to
                // `base_iteration` narrows the domain and yields
                // `{D | predicate} ⇒ T`.  Op-conversion compiles this via the
                // generic applied-combinator arm: `base_iteration` is the
                // upstream (`input=None`), then the Restrict arm consumes it
                // (`input=Some(_)`) and emits a `Restrict` tile.
                make_restrict(predicate.clone(), base_iteration)
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
                    build_input,
                    Expr::proj_index(*build_key_idx).with_ty(Type::fun(
                        build_output_ty.clone(),
                        build_key_expr.ty.domain().unwrap().clone(),
                    )),
                    build_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![build_input, build_key_expr.clone()])
            };

            // The build side is a hash index — a collection keyed by `K` whose
            // groups are collections of build rows. Both are data.
            let converse_ty = Type::data_fun(
                key_ty.clone(),
                Type::data_fun(build_output_ty.clone(), build_output_ty.clone()),
            );
            let build_side = apply_primitive(build_key, Builtin::Converse, converse_ty);
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
                    probe_input,
                    Expr::proj_index(*probe_key_idx).with_ty(Type::fun(
                        probe_output_ty.clone(),
                        probe_key_expr.ty.domain().unwrap().clone(),
                    )),
                    probe_key_expr.clone(),
                ])
            } else {
                typed_compose(vec![probe_input, probe_key_expr.clone()])
            };

            let probe_expr = typed_compose(vec![probe_key, build_side]);
            typecheck(&probe_expr).expect("Bad probe expr");

            trace!(
                "join_plan_to_expr: probe={} : {}",
                symbolic(&probe_expr),
                probe_expr.ty
            );

            // uncurry: (probe_output_ty, build_output_ty) -> build_output_ty
            let uncurry = apply_primitive(
                probe_expr,
                Builtin::Uncurry,
                Type::data_fun(
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
                    // A list literal is a collection, and the kinds are
                    // incomparable — stamping the capability kind here makes the
                    // post-planning wall reject the node against its own rule.
                    .with_ty(Type::data_fun(
                        Type::UIntRange(indices_to_flatten.len()),
                        Type::Base(BaseType::Int),
                    )),
                    Builtin::FlattenDomain,
                    // Both functions are collections: the operand is the uncurried
                    // join output (stamped `data_fun` above) and the result is
                    // that same output re-addressed over a flattened domain.
                    // Flattening re-indexes rows; it does not turn them into a
                    // capability.
                    Type::fun(
                        Type::data_fun(
                            Type::Tuple(vec![probe_output_ty.clone(), build_output_ty.clone()]),
                            build_output_ty.clone(),
                        ),
                        Type::data_fun(flat_ty.clone(), build_output_ty.clone()),
                    ),
                );
                let flattened = apply_function(
                    uncurry,
                    flatten_func,
                    Type::data_fun(flat_ty.clone(), build_output_ty.clone()),
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
                Builtin::MapDomain,
                Type::data_fun(final_domain_ty.clone(), final_domain_ty.clone()),
            );

            let result = if let Some(predicate) = predicate {
                // Apply `restrict(predicate)` to `map_domain` (the iteration
                // source over the joined flat-tuple domain) as a downstream
                // filter step.  `map_domain` is the upstream value-producer
                // that `restrict` consumes — op-conversion converts it with
                // `input=None` (preserving the invariant `MapDomain`
                // requires), then the Restrict arm filters the joined output.
                make_restrict(predicate.clone(), map_domain)
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

    // The morphism produces the join-satisfying extent; surface that on its
    // codomain so downstream consumers (e.g. a `cast({base | r} ⇒ …)` reading
    // the produced tuples) see the refinement they expect. A hash join folds
    // its equi-conditions into the key structure with no residual `Restrict`,
    // so the extent would otherwise be bare — see [`refine_extent`]. Apply
    // it to whichever morphism is returned (the refinement is the extent's,
    // independent of the BFS arm permutation, which only reorders the domain).

    // If BFS produced arms out of canonical order, undo the permutation so that the
    // output domain matches the original tuple type expected by the caller.
    let canonical: Vec<usize> = (0..arm_types.len()).collect();
    if arm_order == canonical {
        return Some(refine_extent(expr, refinement));
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
    // A list literal is a collection (`emit_list`), and the kinds are
    // incomparable — the capability kind here is a claim the node's own rule
    // contradicts at the next wall.
    .with_ty(Type::data_fun(
        Type::UIntRange(perm.len()),
        Type::Base(BaseType::Int),
    ));

    // permute_domain is polymorphic in the morphism it rearranges: it takes
    // `expr` (the join morphism, whose domain may carry the join-condition
    // refinement) and produces a canonical-ordered morphism. Declare its input
    // as `expr`'s *actual* type, not a bare `actual_ty ⇒ actual_ty`. Otherwise
    // `apply_function` re-stamps `permute_func`'s recorded type to
    // `fun(expr.ty, …)` (carrying expr's refinement) while its inner
    // `PermuteDomain` builtin keeps the bare declaration — an internally
    // inconsistent node the post-inference reconstruction can't rebuild
    // (the refinement rides the morphism's invariant domain⇒codomain position).
    let morphism_ty = expr.ty.clone();
    let permute_func = apply_primitive(
        perm_arg,
        Builtin::PermuteDomain,
        Type::fun(
            morphism_ty,
            Type::data_fun(canonical_ty.clone(), actual_ty.clone()),
        ),
    );
    let permuted = apply_function(
        expr,
        permute_func,
        Type::data_fun(canonical_ty.clone(), actual_ty.clone()),
    );
    let result = apply_primitive(
        permuted,
        Builtin::MapDomain,
        Type::data_fun(canonical_ty.clone(), canonical_ty.clone()),
    );
    let result = refine_extent(result, refinement);
    typecheck(&result).expect("Bad permute_domain expr");
    Some(result)
}

/// Compile **one** of a refined domain's refinements into a join, leaving the others
/// as ordinary restrictions on the domain the join reads.
///
/// Any refinement may be the join condition — the set is unordered, so there is no
/// "the" predicate to read — and the first that [`convert_loop_join`] accepts
/// wins. That also gives planning latitude it could not have while refinements were
/// a chain: when several are joinable, which one becomes the join is a free
/// choice a cost model may later make, and the rest remain filters either way.
/// `None` for an unrefined domain or when no refinement forms a join.
fn convert_refinement_to_join(domain_ty: &Type) -> Option<Expr> {
    let Type::Refinement(base, refinements) = domain_ty else {
        return None;
    };
    trace!("Attempting loop join conversion inside iteration");
    refinements.iter().enumerate().find_map(|(i, r)| {
        let rest = Type::refined(
            (**base).clone(),
            refinements
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, c)| c.clone())
                .collect(),
        );
        // `convert_loop_join` only reads the predicate (it builds a new expr),
        // so borrow the immutable term rather than clone it.
        convert_loop_join(&rest, &r.predicate)
    })
}

/// Try the hash-join rewrite at an iteration site whose domain is `domain_ty`.
///
/// Called from [`super::iterate::wrap_with_iterate`] before its iterate-then-restricts
/// fallback: hash join is the specialised iteration strategy when the site's
/// domain is a refined tuple whose predicate decomposes into equality join
/// conditions (the recogniser is implemented by [`plan_loop_join`] /
/// [`convert_loop_join`]).  Returns `true` and rewrites `expr` to
/// `Compose([transformed, original])` on success, leaving `expr` untouched
/// and returning `false` otherwise.  `transformed` is itself iteration-bearing
/// at its leaves (`JoinPlan::Loop` emits `Apply(true ▷ const, Iterate)`),
/// so the resulting chain already has explicit iterate markers — no
/// further wrap is needed.
///
/// Loop joins can occur anywhere an iteration site appears: at the program
/// root, at sink-bound `Record` fields, at aggregate arguments, at
/// `FinalOrDefault` streams, at `Loop` sources, at `Copair`
/// operands, or as a let-bound function value.
///
/// Supports n-way joins (n ≥ 2) when all arms are connected via equality
/// conditions that form a spanning tree.  Build/probe assignment follows
/// the BFS order of that spanning tree.  For now, predicates must be
/// expressed as conjunctions of single-arm equality conditions.
pub(super) fn try_hash_join_rewrite(expr: &mut Expr, domain_ty: &Type) -> bool {
    trace!(
        "Attempting hash-join rewrite at iteration site: {}",
        symbolic(expr),
    );
    // The iteration site is what the recording names. Every product of the plan
    // — the per-arm `iterate` leaves, the key morphisms, the
    // `map_domain`/`permute_domain` scaffolding, the residual `restrict`s — is
    // how *this* site is being materialised, so it is the node they all replace.
    // Coarse by construction: an n-way plan, and a nested loop-join re-entering
    // through `join_plan_to_expr`, all descend from this one node. The join
    // conditions are read out of whichever of the domain's refinements
    // `convert_refinement_to_join` accepts, and the material lifted from there
    // keeps that refinement's own parentage — a clone's copy carries the node it
    // was freshened from, not the node named here.
    //
    // Not a fusion: the site's original value-producer is kept rather than
    // consumed, spliced in as the second element of the compose below with its
    // id intact. The arms the plan reads come from the domain **type**, and a
    // type carries no identity to consume.
    //
    // The recording spans the *attempts*, as simplify's rule combinator does:
    // `convert_refinement_to_join` tries each refinement in turn, and both a
    // rejected refinement and a wholly unmatched domain return through this one
    // guard's `Drop`. What a half-built plan minted before bailing — the key
    // copies `plan_loop_join` freshens before `spanning_tree_children` refuses
    // the condition graph — composes away as a transient: a copy that never
    // reaches the output tree is not `Unrecorded`, that class being found by
    // walking that tree, and its parent is this site, so it is no
    // `DanglingParent` either. Naming the firing instead would mean threading
    // the site id down through `convert_refinement_to_join` into
    // `convert_loop_join`.
    //
    // How many such transients a compile writes therefore depends on the order
    // the refinement set is iterated in, which nothing about a set makes
    // meaningful. That stays unobservable for the same reason they compose away:
    // the rejected attempts reach no pane, and the accepted plan is the same
    // whichever refinement supplied it.
    let _g = provenance::enter(
        expr.node_id(),
        "planning.hash_join",
        provenance::Nature::Machinery,
    );
    let Some(transformed) = convert_refinement_to_join(domain_ty) else {
        trace!("Hash-join pattern did not match");
        return false;
    };
    trace!(
        "Hash-join rewrite succeeded: {} : {}",
        symbolic(&transformed),
        transformed.ty,
    );
    let codomain = expr.ty.codomain().expect("function-typed iteration site");
    // The rewritten site denotes the same collection, so the kind rides across —
    // and its domain is `transformed`'s, which [`refine_extent`] has already made
    // the join-satisfying extent rather than the full product.
    let result_ty = Type::fun_like(
        &expr.ty,
        transformed
            .ty
            .domain()
            .expect("convert_loop_join output must be function-typed"),
        codomain,
    );
    *expr = compose(transformed, take(expr)).with_ty(result_ty);
    true
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::*;
    use crate::ccl::symbolic::symbolic;
    // `super::*` also glob-imports `lambda_elim::compose`; name the test-helper
    // `compose` (`Expr::compose`) explicitly so it wins over the glob.
    use super::super::test_helpers::compose;

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
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
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
            Expr::proj_index(0).with_ty(int_ty_val.clone()),
            Expr::proj_index(1).with_ty(int_ty_val.clone()),
        ]);
        let non_zip_apply = Expr::apply(
            args_tuple,
            var("not_zip").with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(tuple_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_zip_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
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
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), tuple_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            non_tuple_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
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
        let args_tuple = Expr::tuple(vec![Expr::proj_index(0).with_ty(int_ty_val.clone())]);
        let zip_apply = Expr::apply(
            args_tuple,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone())),
        )
        .with_ty(fun_ty(int_ty_val.clone(), int_ty_val.clone()));

        let ref_ty = fun_ty(tuple_ty_val.clone(), int_ty_val.clone());
        let refinement = compose(vec![
            zip_apply,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
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
            Expr::proj_index(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
            Expr::proj_index(0).with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ]);
        let zip_apply = Expr::apply(
            args_tuple,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(
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
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals)))
                .with_ty(fun_ty(tuple_ty_val.clone(), int_ty_val.clone())),
        ])
        .with_ty(ref_ty);

        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert_eq!(result, None);
    }

    /// Build a **bare** 2-arm join predicate `__elem.0 ▷ (λ x → __elem.1 ▷
    /// (λ y → <mk_bool(x, y)>))` over `(scalar, scalar)` — the implicit
    /// REFINEMENT_BINDER form `split_join_conditions` decomposes (the element
    /// binder is the refinement's own, no enclosing `λ rec`).
    fn pointful_2arm_pred(scalar: &Type, mk_bool: impl FnOnce(Expr, Expr) -> Expr) -> Expr {
        let b = Type::Base(BaseType::Bool);
        let rec_ty = tuple_ty(vec![scalar.clone(), scalar.clone()]);
        let rec_arm = |i: usize| {
            Expr::apply(
                Expr::var(Name::elem()).with_ty(rec_ty.clone()),
                Expr::proj_index(i).with_ty(fun_ty(rec_ty.clone(), scalar.clone())),
            )
            .with_ty(scalar.clone())
        };
        let body = mk_bool(
            var("x").with_ty(scalar.clone()),
            var("y").with_ty(scalar.clone()),
        );
        let inner =
            Expr::lambda("y", scalar.clone(), body).with_ty(fun_ty(scalar.clone(), b.clone()));
        let mid = Expr::apply(rec_arm(1), inner).with_ty(b.clone());
        let outer =
            Expr::lambda("x", scalar.clone(), mid).with_ty(fun_ty(scalar.clone(), b.clone()));
        Expr::apply(rec_arm(0), outer).with_ty(b)
    }

    #[test]
    fn test_convert_loop_join_succeeds_with_valid_input() {
        let int_ty_val = int_ty();
        let tuple_ty_val = tuple_ty(vec![int_ty_val.clone(), int_ty_val.clone()]);

        // Pointful predicate: λ rec → rec.0 ▷ (λ x → rec.1 ▷ (λ y → x == y)).
        let refinement = pointful_2arm_pred(&int_ty_val, |x, y| {
            Expr::binop(x, BinOpKind::Compare(CompareKind::Equals), y)
                .with_ty(Type::Base(BaseType::Bool))
        });

        // Should successfully convert
        let result = convert_loop_join(&tuple_ty_val, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed with valid hash join pattern"
        );

        assert_eq!(
            symbolic(&result.unwrap()),
            "(iterate ≫ id ≫ (iterate ≫ id) ▷ converse) ▷ uncurry ▷ map_domain"
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
        let arg = Expr::proj_index(0).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
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
        let arg = Expr::proj_index(1).with_ty(proj_ty);
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
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
        let zip_app = Expr::apply(arg, Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty));
        assert_eq!(is_function_of_single_tuple_arm(&zip_app), None);
    }

    // Tests for is_function_of_single_tuple_arm with tuples
    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_single_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        // A tuple containing a single projection should return that projection's index
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        let tuple_expr = Expr::tuple(vec![Expr::proj_index(0).with_ty(proj_ty)]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_all_same_projection() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where all non-constant elements use the same projection
        let tuple_expr = Expr::tuple(vec![
            Expr::proj_index(0).with_ty(proj_ty.clone()),
            Expr::proj_index(0).with_ty(proj_ty.clone()),
        ]);
        assert_eq!(is_function_of_single_tuple_arm(&tuple_expr), Some(0));
    }

    #[test]
    fn test_is_function_of_single_tuple_arm_on_tuple_different_projections() {
        let tuple_ty_val = tuple_ty(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(tuple_ty_val.clone(), int_ty());
        // A tuple where elements use different projections should return None
        let tuple_expr = Expr::tuple(vec![
            Expr::proj_index(0).with_ty(proj_ty.clone()),
            Expr::proj_index(1).with_ty(proj_ty.clone()),
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
            Expr::proj_index(0).with_ty(proj_ty),
            apply_primitive(var("c").with_ty(int_ty()), Builtin::Const, const_fn_ty),
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
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
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
        let (plan, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
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
        let (_, arm_order) = build_join_plan(0, &children, &conditions, &[], &[]).unwrap();
        assert_eq!(arm_order, vec![0, 2, 1]);
    }

    #[test]
    fn test_build_join_plan_no_straddling_condition_returns_none() {
        // children say arm 1 is a child of arm 0, but conditions only mention arms 0 and 2 —
        // no condition straddles the {0} / {1} split, so planning must fail.
        let conditions = vec![cond(0, 2)];
        let children = vec![vec![1], vec![], vec![]];
        assert!(build_join_plan(0, &children, &conditions, &[], &[]).is_none());
    }

    // --- split_join_conditions ---

    fn make_eq_cond(tup: &Type, scalar: &Type) -> Expr {
        let args = Expr::tuple(vec![
            Expr::proj_index(0).with_ty(fun_ty(tup.clone(), scalar.clone())),
            Expr::proj_index(1).with_ty(fun_ty(tup.clone(), scalar.clone())),
        ]);
        let zip_out = fun_ty(tup.clone(), tuple_ty(vec![scalar.clone(), scalar.clone()]));
        let zipped = Expr::apply(
            args,
            Expr::builtin(Builtin::Zip).with_ty(fun_ty(
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
            )),
        )
        .with_ty(zip_out);
        compose(vec![
            zipped,
            Expr::builtin(Builtin::BinOp(BinOpKind::Compare(CompareKind::Equals))).with_ty(fun_ty(
                tuple_ty(vec![scalar.clone(), scalar.clone()]),
                scalar.clone(),
            )),
        ])
        .with_ty(fun_ty(tup.clone(), scalar.clone()))
    }

    fn make_filter_pred(tup: &Type, scalar: &Type, arm: usize) -> Expr {
        // proj(arm) ≫ filter_fn : tup -> scalar
        compose(vec![
            Expr::proj_index(arm).with_ty(fun_ty(tup.clone(), scalar.clone())),
            var("filter_fn").with_ty(fun_ty(scalar.clone(), scalar.clone())),
        ])
        .with_ty(fun_ty(tup.clone(), scalar.clone()))
    }

    // `split_join_conditions` now decomposes the *pointful* predicate form
    // (`λ rec → rec.i ▷ li ▷ (λ vi → <bool>)`); it is exercised end-to-end by
    // the join goldens (`test_joins` — including the unsound-zip-substitution
    // probe — and the multi-arm AND/residual/permute cases in
    // `test_new_compile`), which run it on real inferred predicates rather than
    // hand-built combinator ASTs.

    // --- collect_arms_used ---

    #[test]
    fn test_collect_arms_used_single_proj() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let expr = Expr::proj_index(1).with_ty(fun_ty(t, i));
        let mut arms = BTreeSet::new();
        collect_arms_used(&expr, &mut arms);
        assert_eq!(arms, BTreeSet::from([1]));
    }

    #[test]
    fn test_collect_arms_used_compose() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let expr = make_filter_pred(&t, &i, 0);
        let mut arms = BTreeSet::new();
        collect_arms_used(&expr, &mut arms);
        assert_eq!(arms, BTreeSet::from([0]));
    }

    #[test]
    fn test_collect_arms_used_zip_with_two_arms() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let eq_cond = make_eq_cond(&t, &i);
        // The eq condition uses arms 0 and 1 via the zip
        let mut arms = BTreeSet::new();
        collect_arms_used(&eq_cond, &mut arms);
        assert_eq!(arms, BTreeSet::from([0, 1]));
    }

    // --- convert_loop_join with mixed predicate ---

    #[test]
    fn test_convert_loop_join_succeeds_with_eq_plus_filter_predicate() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let b = Type::Base(BaseType::Bool);

        // Pointful: λ rec → rec.0 ▷ (λ x → rec.1 ▷ (λ y → x == y and x ▷ some_filter)).
        // The equality drives the join; `x ▷ some_filter` is a residual on arm 0.
        let refinement = pointful_2arm_pred(&i, |x, y| {
            let eq = Expr::binop(x.clone(), BinOpKind::Compare(CompareKind::Equals), y)
                .with_ty(b.clone());
            let filt = Expr::apply(x, var("some_filter").with_ty(fun_ty(i.clone(), b.clone())))
                .with_ty(b.clone());
            Expr::binop(eq, BinOpKind::BoolLogic(LogicKind::And), filt).with_ty(b.clone())
        });

        // Should succeed: eq condition drives the hash join, filter becomes a predicate.
        let result = convert_loop_join(&t, &refinement);
        assert!(
            result.is_some(),
            "convert_loop_join should succeed when eq conditions + extra filter are present"
        );

        // The output should contain "iterate" with the pushed-down filter attached
        // (filter predicates ride into the iteration via iterate(p) rather than the
        // legacy `restrict` builtin).
        let sym = symbolic(&result.unwrap());
        assert!(
            sym.contains("iterate"),
            "expected 'iterate' in output for pushed-down filter, got: {sym}"
        );
    }

    #[test]
    fn test_convert_loop_join_rejects_pure_non_eq_predicate() {
        let i = int_ty();
        let t = tuple_ty(vec![i.clone(), i.clone()]);
        let bool_ty_val = Type::Base(BaseType::Bool);

        // A pure filter predicate with no equality condition — cannot build hash join.
        let filter = compose(vec![
            Expr::proj_index(0).with_ty(fun_ty(t.clone(), i.clone())),
            var("some_filter").with_ty(fun_ty(i.clone(), bool_ty_val.clone())),
        ])
        .with_ty(fun_ty(t.clone(), bool_ty_val));

        assert_eq!(
            convert_loop_join(&t, &filter),
            None,
            "should return None when no equality conditions are present"
        );
    }
}

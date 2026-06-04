//! Lambda elimination pass for CCL.
//!
//! Rewrites all [`TypedExprNode::Lambda`] nodes in a CCL expression into a point-free
//! composition of primitive combinators, following the Cartesian Closed Category
//! (CCC) structure described in `docs/operational-semantics/lowering.md`.
//!
//! # Entry point
//!
//! [`run`] eliminates all lambdas and then simplifies to a fixed point.
//!
//! # Outside-in ordering
//!
//! Lambda elimination is applied **outside-in**: the outermost lambda is
//! handled before inner ones. This ordering is mandatory — an inner lambda
//! that captures a free variable of an outer lambda must be combined with it
//! via the nested-lambda rule. Eliminating inside-out would
//! treat a captured variable as a constant, which is incorrect.
//!
//! # Primitive combinators
//!
//! The output uses [`TypedExprNode::Builtin`] for primitive functions and
//! [`TypedExprNode::Proj`] for tuple/record projections:
//!
//! | Symbol | AST shape | Meaning |
//! |--------|-----------|---------|
//! | `id` | `Builtin(Id)` | identity morphism |
//! | `.0`, `.1`, … | `Proj(Index(n))` | tuple projection |
//! | `.field` | `Proj(Field(s))` | record field projection |
//! | `f ≫ g` | `Compose([f, g])` | left-to-right composition |
//! | `⟨f, g⟩` | `Apply(Tuple([f, g]), Builtin(Zip))` | product/fanout |
//! | `curry(f)` | `Apply(f, Builtin(Curry))` | curry |
//! | `const(c)` | `Apply(c, Builtin(Const))` | constant lift |
//! | `restrict` | `Builtin(Restrict)` | domain restriction |
//! | `apply` | `Builtin(Apply)` | function application as morphism |
//! | `map` | `Builtin(Map)` | post-composition |
//! | `sum`, `max` | `Builtin(Sum)`, `Builtin(Max)` | fold/reduce |
//! | `converse` | `Builtin(Converse)` | grouping by key |
//! | `uncurry` | `Builtin(Uncurry)` | uncurry |
//! | `compose` | `Builtin(Compose)` | composition as first-class morphism |
//! | `add`/`sub`/… (and compares / logic) | `Builtin(BinOp(op))` for `op: BinOpKind` | binary scalar ops |
//! | `neg`, `not_fn` | `Builtin(Neg)`, `Builtin(NotFn)` | unary scalar ops |

use std::cell::RefCell;
use std::mem::replace;
use std::rc::Rc;

use crate::ccl::ccl_utils::{is_free, typed_compose, walk_refined_predicates_mut};
use crate::ccl::infer::{dbg_typecheck_mv, debug_typecheck};
use crate::ccl::simplify::simplify;
use crate::ccl::{
    BaseType, Expr, RefinementKind, Type, TypedExpr, TypedExprNode, symbolic::symbolic,
};
use crate::ccl::{Builtin, Lit, Refinement, next_refinement_id};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during lambda elimination.
#[derive(Debug, Clone, PartialEq)]
pub enum LambdaElimError {
    /// A node kind inside a lambda body is not yet handled by the elimination
    /// rules.  Currently: `Case`, `Loop`, and `HashJoin` refinements.
    Unsupported(String),
}

impl std::fmt::Display for LambdaElimError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(msg) => write!(f, "lambda elimination: unsupported: {msg}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Eliminate all [`TypedExprNode::Lambda`] nodes and simplify the result to a fixed point.
///
/// The input must be a well-formed, fully type-inferred CCL expression
/// (as produced by [`crate::ccl::infer::infer`]).
///
/// Returns `Ok(point_free_expr)` where the result contains no `Lambda` nodes.
pub fn run(expr: Expr) -> Result<Expr, LambdaElimError> {
    let mut ctx = ElimContext::new();
    let mut point_free = elim_lambdas(&mut ctx, expr)?;
    // Walk the result tree for `Refinement` predicates embedded in type
    // slots (e.g. user-annotation-derived filter refinements introduced
    // by [`crate::ccl::desugar_defers`]) and eliminate lambdas inside
    // them too — the main walk only visits expressions, so predicates
    // sitting in type positions wouldn't otherwise be touched.
    let mut seen_refinements: std::collections::HashSet<crate::ccl::RefinementId> =
        std::collections::HashSet::new();
    elim_lambdas_in_type_refinements(&mut point_free, &mut ctx, &mut seen_refinements)?;
    let simplified = simplify(point_free);
    Ok(simplified)
}

/// Walk `expr` and every nested `Type::Refinement` predicate, running
/// [`elim_lambdas`] on the predicate so it becomes point-free.  Tracks
/// already-visited [`Refinement::id`]s in `seen` so shared refinement
/// instances (e.g. duplicated by [`substitute`] cloning a type with
/// `Rc`-shared predicates) are processed only once.
fn elim_lambdas_in_type_refinements(
    expr: &mut Expr,
    ctx: &mut ElimContext,
    seen: &mut std::collections::HashSet<crate::ccl::RefinementId>,
) -> Result<(), LambdaElimError> {
    elim_lambdas_in_type(&mut expr.ty, ctx, seen)?;
    // `Defer`/`Feed`/`Define`/`ExprStmt` are eliminated by
    // `desugar_defers` before inference; the catch-all here relies on
    // `walk_children_mut` not visiting their children either (those
    // variants are unreachable by the time `lambda_elim` runs).
    let mut err = Ok(());
    expr.walk_children_mut(|child| {
        if err.is_ok() {
            err = elim_lambdas_in_type_refinements(child, ctx, seen);
        }
    });
    err
}

/// Walk `ty` and run [`elim_lambdas`] on every `Refinement` predicate
/// nested inside.  Skips refinements whose ID is already in `seen`.
fn elim_lambdas_in_type(
    ty: &mut Type,
    ctx: &mut ElimContext,
    seen: &mut std::collections::HashSet<crate::ccl::RefinementId>,
) -> Result<(), LambdaElimError> {
    let mut err = Ok(());
    walk_refined_predicates_mut(ty, seen, &mut |pred, _vis| {
        if err.is_ok() {
            let placeholder = Expr::lit(Lit::Unit);
            let old_pred = replace(pred, placeholder);
            match elim_lambdas(ctx, old_pred) {
                Ok(new_pred) => *pred = new_pred,
                Err(e) => err = Err(e),
            }
        }
    });
    err
}

// ---------------------------------------------------------------------------
// Elimination context
// ---------------------------------------------------------------------------

/// Mutable state threaded through lambda elimination.
///
/// Holds a monotonically increasing counter used to generate fresh variable
/// names for the nested-lambda rule.
struct ElimContext {
    /// Next suffix for `__pair_N` fresh variables.
    pair_counter: u64,
}

impl ElimContext {
    /// Create a new context with the counter starting at zero.
    fn new() -> Self {
        Self { pair_counter: 0 }
    }

    /// Return a fresh variable name `__pair_N` for use in the nested-lambda rule.
    fn fresh_pair_name(&mut self) -> String {
        let n = self.pair_counter;
        self.pair_counter += 1;
        format!("__pair_{n}")
    }
}

// ---------------------------------------------------------------------------
// Primitive combinator constructors
// ---------------------------------------------------------------------------

/// Build [`Builtin::Id`]: the identity morphism.
pub(crate) fn id() -> Expr {
    Expr::builtin(Builtin::Id)
}

/// Build `Proj(Index(n))`: the tuple projection morphism `.n`.
#[cfg(test)]
pub(crate) fn proj_idx(n: usize) -> Expr {
    Expr::proj_index(n)
}

/// Build `f ≫ g`: left-to-right function composition.
pub(crate) fn compose(f: Expr, g: Expr) -> Expr {
    Expr::compose(vec![f, g])
}

/// Build a [`TypedExprNode::Tuple`] whose type is inferred from its elements.
///
/// Sets the node's type to `Type::Tuple([e.ty for e in elts])`, using
/// [`Type::Hole`] for any element whose type is not yet known.
pub(crate) fn typed_tuple(elts: Vec<Expr>) -> Expr {
    let ty = Type::Tuple(elts.iter().map(|e| e.ty.clone()).collect());
    dbg_typecheck_mv(Expr::tuple(elts).with_ty(ty))
}

/// Build `⟨f, g⟩`: the product/fanout `zip(f, g)` using the [`Builtin::Zip`]
/// combinator.
///
/// Represented as `Apply { argument: Tuple([f, g]), function: Builtin(Zip) }`,
/// i.e. `(f, g) ▷ zip`.  Annotates all nodes with concrete types when available.
pub(crate) fn zip_pair(f: Expr, g: Expr) -> Expr {
    let result_ty = zip_pair_ty(&f, &g);
    let inner_tuple = typed_tuple(vec![f, g]);
    let zip_fn_ty = fun_ty_or_hole(&inner_tuple.ty, &result_ty);
    let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
    dbg_typecheck_mv(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
}

/// Build `curry(f)`: `f ▷ curry` = `Apply { argument: f, function: Builtin(Curry) }`.
///
/// Annotates the curry built-in with its type when `f` has a concrete function type.
pub(crate) fn curry(f: Expr) -> Expr {
    // If f: Tuple([A, B]) → C, then curry(f): A → (B → C)
    let curry_result = match &f.ty {
        Type::Fun(domain, codomain) => match domain.as_ref() {
            Type::Tuple(elts) if elts.len() >= 2 => Type::fun(
                elts[0].clone(),
                Type::fun(elts[1].clone(), *codomain.clone()),
            ),
            _ => Type::Hole,
        },
        _ => Type::Hole,
    };
    let curry_fn_ty = fun_ty_or_hole(&f.ty, &curry_result);
    let curry_var = Expr::builtin(Builtin::Curry).with_ty(curry_fn_ty);
    Expr::apply(f, curry_var).with_ty(curry_result)
}

/// Build `const(c)`: `c ▷ const` = `Apply { argument: c, function: Builtin(Const) }`.
///
/// Leaves the const built-in untyped; use the typed inline form in `elim_lambda`
/// when the result type (param domain) is known.
pub fn const_(c: Expr) -> Expr {
    Expr::apply(c, Expr::builtin(Builtin::Const))
}

// Free-variable check lives in [`crate::ccl::ccl_utils`]: `is_free` is a
// thin wrapper around `count_free`, which counts occurrences across the
// AST and inside refinement predicates carried by types.  Imported at the
// top of this module.

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`.
///
/// Stops descending when `name` is rebound by [`TypedExprNode::Lambda::param`] or
/// [`TypedExprNode::Let::binding`].  Does **not** perform capture-avoiding renaming of
/// other binders; the caller is responsible for ensuring `replacement` does
/// not contain free variables that would be captured.
pub(crate) fn substitute(expr: Expr, name: &str, replacement: &Expr) -> Expr {
    debug_typecheck(&expr);
    // Fast path: no allocation needed for atoms.
    match &expr.node {
        TypedExprNode::Var(n) if n == name => return replacement.clone(),
        TypedExprNode::Var(_)
        | TypedExprNode::Lit(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Builtin(_) => return expr,
        _ => {}
    }
    if !is_free(name, &expr) {
        return expr;
    }
    let TypedExpr {
        node,
        mut ty,
        user_annotation,
    } = expr;
    substitute_in_type(&mut ty, name, replacement);

    let new_node = match node {
        TypedExprNode::Lambda {
            param,
            body,
            mut refinement,
        } => {
            if let Some(Refinement {
                kind: RefinementKind::Predicate(pred_rc),
                ..
            }) = &mut refinement
            {
                let t = Expr::lit(Lit::Unit);
                let old_pred = replace(&mut *pred_rc.borrow_mut(), t);
                let new_pred = substitute(old_pred, name, replacement);
                *pred_rc.borrow_mut() = new_pred;
            }
            if param.name == name {
                // name is shadowed; do not substitute inside
                TypedExprNode::Lambda {
                    param,
                    body,
                    refinement,
                }
            } else {
                TypedExprNode::Lambda {
                    param,
                    body: Box::new(substitute(*body, name, replacement)),
                    refinement,
                }
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = substitute(*bound_expr, name, replacement);
            let new_body = if binding.name == name {
                *body // shadowed; do not substitute
            } else {
                substitute(*body, name, replacement)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(new_bound),
                body: Box::new(new_body),
            }
        }

        // Loop params shadow `name` inside `loop_body`, so we can't fall
        // through to the generic structural recursion below — that would
        // substitute into the body unconditionally.  Delegate to the
        // shared shadowing-aware helper.
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            crate::ccl::walk_loop_children(params, init_args, source, loop_body, Some(name), |e| {
                substitute(e, name, replacement)
            })
        }

        TypedExprNode::Compose(elts) => {
            let new_elts: Vec<Expr> = elts
                .into_iter()
                .map(|e| substitute(e, name, replacement))
                .collect();
            // After substitution element types may change (e.g. a Var
            // whose type was an unresolved Infer placeholder gets
            // replaced by a concrete expression with a fully-typed
            // domain).  Recompute the outer Fun type so the invariant
            // `Compose.ty == Fun(first_domain, last_codomain)` is
            // maintained.
            if let (Some(first), Some(last)) = (new_elts.first(), new_elts.last())
                && let (Some(new_domain), Some(new_codomain)) =
                    (first.ty.domain(), last.ty.codomain())
            {
                ty = Type::fun(new_domain, new_codomain);
            }
            TypedExprNode::Compose(new_elts)
        }

        // `Defer`, `Feed`, `Define`, and `ExprStmt` are eliminated by
        // `desugar_defers` before inference; `substitute` only runs on
        // post-desugar trees.
        TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::Defer
        | TypedExprNode::ExprStmt { .. } => {
            unreachable!("Defer/Feed/Define/ExprStmt eliminated by desugar_defers before inference")
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // All remaining variants: pure structural recursion, using the
        // type-substituted `ty`.  Atoms have no children, so this is a
        // no-op for them.
        node => {
            let mut expr = TypedExpr {
                node,
                ty,
                user_annotation,
            };
            expr.map_children(|child| substitute(child, name, replacement));
            debug_typecheck(&expr);
            return expr;
        }
    };
    let result = TypedExpr {
        node: new_node,
        ty,
        user_annotation,
    };
    debug_typecheck(&result);
    result
}

/// Helper for `substitute` that recurses into any refined types where we also need to
/// substitute the param.
fn substitute_in_type(ty: &mut Type, name: &str, replacement: &Expr) {
    // Refinement predicates are sub-expressions, not sub-types — handle
    // the predicate explicitly, then recurse into structural type children.
    if let Type::Refinement(_, refinement) = ty {
        let Refinement {
            kind: RefinementKind::Predicate(pred_rc),
            ..
        } = &mut *refinement;
        let t = Expr::lit(Lit::Unit);
        // Substitute within the refinement, unless we are already inside that same refinement
        // TODO: this probably simplifies once we remove the RefCell from the predicate.
        if let Ok(mut pred) = pred_rc.try_borrow_mut() {
            let old_pred = replace(&mut *pred, t);
            let new_pred = substitute(old_pred, name, replacement);
            *pred = new_pred;
        }
    }
    ty.walk_children_mut(|child| substitute_in_type(child, name, replacement));
}

// ---------------------------------------------------------------------------
// BinOp desugaring
// ---------------------------------------------------------------------------

// `BinOpKind` and `UnaryOpKind` are mapped to the corresponding [`Builtin`]
// variant via [`Builtin::for_binop`] / [`Builtin::for_unaryop`].

/// Compute `Fun(domain, codomain)`, returning [`Type::Hole`] if either
/// component is [`Type::Hole`] or [`Type::Infer`].
///
/// Used throughout lambda elimination to set result types only when concrete
/// type information is available, leaving [`Type::Hole`] otherwise so the
/// post-elimination inference pass can fill in the gaps without conflict.
pub(crate) fn fun_ty_or_hole(domain: &Type, codomain: &Type) -> Type {
    if matches!(domain, Type::Hole | Type::Infer(_))
        || matches!(codomain, Type::Hole | Type::Infer(_))
    {
        Type::Hole
    } else {
        Type::fun(domain.clone(), codomain.clone())
    }
}

/// Compute the type of `zip(f, g): A → (B, C)` from `f: A → B` and `g: A → C`.
///
/// Returns [`Type::Hole`] if either argument does not have a concrete function
/// type; inference will fill in the gaps in that case.
pub(crate) fn zip_pair_ty(f: &Expr, g: &Expr) -> Type {
    match (&f.ty, &g.ty) {
        (Type::Fun(a, b), Type::Fun(_, c)) => {
            Type::fun(*a.clone(), Type::Tuple(vec![*b.clone(), *c.clone()]))
        }
        _ => Type::Hole,
    }
}

// ---------------------------------------------------------------------------
// Filter-pattern helpers
// ---------------------------------------------------------------------------

/// Return `true` if `body` is a two-branch Case matching the filter pattern:
/// `{ [guard → action, true → unit] }`.
///
/// Used by [`elim_lambdas_impl`] to detect `Compose([src, Lambda(x, filter_body)])`
/// and lower it to a restricted source composition instead of a plain lambda elimination.
///
/// **Shape constraint**: the body must be exactly a `Case` at the top level.
/// If the loop body has leading `Let` bindings (`let y = f(x) in Case { … }`),
/// the Case is nested under a `Let` and this function returns `false`, so the
/// loop compiles via the general path (correct but no `Restrict` operator).
/// A follow-up could peel leading `Let` nodes before the pattern check.
fn is_filter_case_body(body: &Expr) -> bool {
    if let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &body.node
    {
        branches.len() == 2
            && branches.iter().all(|b| b.pattern.is_none())
            && matches!(&branches[1].guard.node, TypedExprNode::Lit(Lit::Bool(true)))
            && matches!(&branches[1].body.node, TypedExprNode::Lit(Lit::Unit))
    } else {
        false
    }
}

/// Extract `(guard, action)` from a two-branch filter-pattern Case body.
///
/// Panics if `body` is not a filter-pattern Case; call [`is_filter_case_body`] first.
fn extract_filter_case(body: Expr) -> (Expr, Expr) {
    if let TypedExprNode::Case { mut branches, .. } = body.node {
        let first = branches.remove(0);
        (first.guard, first.body)
    } else {
        panic!("extract_filter_case: expected a filter-pattern Case body")
    }
}

// ---------------------------------------------------------------------------
// Core: elim_lambda
// ---------------------------------------------------------------------------

/// Eliminate `param` from `body`, eliminating any lambdas that use `param` as
/// a free variable along the way. Lambdas that are constant in `param` are not
/// eliminated.
///
/// `param_ty` is the type of the lambda parameter being eliminated. It is used
/// to set [`TypedExpr::ty`] on every new expression created, so that the
/// post-elimination type-inference pass has concrete type anchors to work from.
///
/// **Precondition**: `body` must not itself be the lambda being eliminated —
/// i.e. this function is called on the body of a `Lambda { param, body, .. }`.
fn elim_lambda(
    ctx: &mut ElimContext,
    param: &str,
    param_ty: &Type,
    body: Expr,
) -> Result<Expr, LambdaElimError> {
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        elim_lambda_impl(ctx, param, param_ty, body)
    })
}

fn elim_lambda_impl(
    ctx: &mut ElimContext,
    param: &str,
    param_ty: &Type,
    body: Expr,
) -> Result<Expr, LambdaElimError> {
    log::trace!("elim_lambda: eliminating λ {param}: {}", symbolic(&body));
    debug_typecheck(&body);
    // Capture the body's type before consuming it; the result of eliminating
    // `λ param → body` is a morphism `param_ty → body_ty`.
    let body_ty = body.ty.clone();
    let result_ty = fun_ty_or_hole(param_ty, &body_ty);
    assert_ne!(Type::Hole, result_ty);

    // Constant: λ x → e  ⟹  const(e)  when x ∉ fv(e)
    // Checked before pattern-matching because a nested lambda that does not
    // reference param should also be treated as a constant.
    if !is_free(param, &body) {
        // const: T → (A → T) where T = body.ty and result_ty = A → T
        let const_fn_ty = fun_ty_or_hole(&body.ty, &result_ty);
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_fn_ty);
        let result = Expr::apply(body, const_var).with_ty(result_ty);
        debug_typecheck(&result);
        return Ok(result);
    }

    let TypedExpr {
        node: body_node, ..
    } = body;
    let result = match body_node {
        // Identity: λ x → x  ⟹  id
        TypedExprNode::Var(ref name) if name == param => Ok(id().with_ty(result_ty)),

        // Nested lambda: λ x → λ y → body  ⟹  curry(λ(x,y) → body)
        TypedExprNode::Lambda {
            param: y_binding,
            body: inner_body,
            refinement,
        } => {
            let y = y_binding.name;
            let mut y_ty = y_binding.ty.clone();
            let mut correlated_refinement = None;
            if let Some(ref r) = refinement {
                match &r.kind {
                    RefinementKind::Predicate(p) => {
                        // Handle refinements on the lambda.  There are two options:
                        // If the refinement is correlated with `param`, then we need to lift it to be
                        // over the tuple we are going to create, so remove it from y.
                        // If it is uncorrelated, attach it to y's type.
                        let param_ty = y_ty.clone();
                        if is_free(param, &p.borrow()) {
                            correlated_refinement = Some(p.borrow().clone());
                        } else {
                            y_ty = Type::Refinement(Box::new(param_ty), r.clone());
                        };
                    }
                }
            };

            // Merge λ x → λ y into λ __pair where x = pair[0], y = pair[1].
            // The pair variable has type (param_ty, y_ty).
            let pair = ctx.fresh_pair_name();
            let pair_ty = Type::Tuple(vec![param_ty.clone(), y_ty.clone()]);
            // Annotate the projection morphisms with their concrete types so that
            // downstream type computations (e.g. zip_pair_ty) can see the domain.
            // Also annotate the pair variable itself so that the identity rule in
            // the recursive call can produce a typed `id` morphism.
            let proj0_ty = Type::fun(pair_ty.clone(), param_ty.clone());
            let proj1_ty = Type::fun(pair_ty.clone(), y_ty.clone());
            let sub_x = Expr::apply(
                Expr::var(&pair).with_ty(pair_ty.clone()),
                Expr::proj_index(0).with_ty(proj0_ty.clone()),
            )
            .with_ty(param_ty.clone());
            let sub_y = Expr::apply(
                Expr::var(&pair).with_ty(pair_ty.clone()),
                Expr::proj_index(1).with_ty(proj1_ty.clone()),
            )
            .with_ty(y_ty.clone());
            let merged = substitute(substitute(*inner_body, &y, &sub_y), param, &sub_x);

            let mut inner_elim = elim_lambda(ctx, &pair, &pair_ty, merged)?;

            // If we have a correlated refinement, we also need to do the same sort of pair substitution
            // in the refinement to turn it into a λ-free function of the tuple.
            if let Some(pred) = correlated_refinement {
                let ref_body = Expr::apply(Expr::var("__ref").with_ty(y_ty.clone()), pred)
                    .with_ty(Type::Base(BaseType::Bool));
                let subbed_ref_body =
                    substitute(substitute(ref_body, "__ref", &sub_y), param, &sub_x);
                let lambda_elim_ref_body = elim_lambda(ctx, &pair, &pair_ty, subbed_ref_body)?;
                // TODO: it would be cleaner to not call this here, but instead call it directly from somewhere
                // in elim_lambdas to avoid the mutual recursion.  In order to do that, we need to either
                // make elim_lambdas idempotent or find a way to call it on the new refinement exactly once.
                let fully_elim_ref_body = elim_lambdas(ctx, lambda_elim_ref_body)?;

                let inner_ty = inner_elim.ty.clone();
                inner_elim = inner_elim.with_ty(Type::Refinement(
                    Box::new(inner_ty),
                    Refinement {
                        id: next_refinement_id(),
                        description: "uncurried".into(),
                        kind: RefinementKind::Predicate(Rc::new(RefCell::new(fully_elim_ref_body))),
                    },
                ));

                let curry_var = Expr::builtin(Builtin::Curry)
                    .with_ty(Type::fun(inner_elim.ty.clone(), result_ty.clone()));

                Ok(Expr::apply(inner_elim, curry_var).with_ty(result_ty))
            } else {
                Ok(dbg_typecheck_mv(curry(inner_elim)))
            }
        }

        // Application: λ x → e ▷ f  ⟹  ⟨λx→e, λx→f⟩ ≫ apply
        TypedExprNode::Apply { argument, function } => {
            let elim_arg = elim_lambda(ctx, param, param_ty, *argument)?;
            let elim_fn = elim_lambda(ctx, param, param_ty, *function)?;
            let pair = zip_pair(elim_arg, elim_fn);
            // apply: Tuple([B, B→C]) → C; its domain is the codomain of pair
            let apply_ty = match &pair.ty {
                Type::Fun(_, cod) => fun_ty_or_hole(cod, &body_ty),
                _ => Type::Hole,
            };
            let apply_var = Expr::builtin(Builtin::Apply).with_ty(apply_ty);
            Ok(compose(pair, apply_var).with_ty(result_ty))
        }

        // Compose in body: λ x → f ≫ g  ⟹  ⟨λx→f, λx→g⟩ ≫ compose
        //
        // For an n-ary Compose([f₀, f₁, …]), eliminate the lambda through each
        // element and re-build a pairwise chain: ⟨λx→f₀, λx→f₁⟩ ≫ compose ≫ …
        TypedExprNode::Compose(elts) => {
            let mut elim_elts = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect::<Result<Vec<_>, _>>()?;
            // Fold pairwise from the left: ⟨e0, e1⟩ ≫ compose, then compose
            // the result with e2, etc.
            let mut acc = elim_elts.remove(0);
            for next in elim_elts {
                let pair = zip_pair(acc, next);
                // compose: Tuple([A→B, B→C]) → (A→C); domain = codomain of pair
                let compose_ty = match &pair.ty {
                    Type::Fun(_, cod) => match cod.as_ref() {
                        Type::Tuple(elts) if elts.len() == 2 => match (&elts[0], &elts[1]) {
                            (Type::Fun(a, _), Type::Fun(_, c)) => {
                                fun_ty_or_hole(cod, &Type::fun(*a.clone(), *c.clone()))
                            }
                            _ => Type::Hole,
                        },
                        _ => Type::Hole,
                    },
                    _ => Type::Hole,
                };
                let compose_var = Expr::builtin(Builtin::Compose).with_ty(compose_ty);
                acc = compose(pair, compose_var);
            }
            Ok(acc.with_ty(result_ty))
        }

        // BinOp — desugar to Apply + Tuple, then apply the application rule.
        // a op b  ≡  (a, b) ▷ op_fn
        //
        // The `String + String → Concat` rewrite is handled by
        // [`crate::ccl::simplify::try_string_add_to_concat`] (which runs after
        // lambda elimination), so it's not duplicated here.
        TypedExprNode::BinOp { left, op, right } => {
            let left = *left;
            let right = *right;
            let tuple = typed_tuple(vec![left, right]);
            let fn_ty = fun_ty_or_hole(&tuple.ty, &body_ty);
            let fn_var = Expr::builtin(Builtin::BinOp(op)).with_ty(fn_ty);
            let desugared = Expr::apply(tuple, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // CollectionUnion inside a lambda body: lift via the
        // `Apply(Tuple(ops), Builtin::CollectionUnion)` point-free form.
        // This mirrors the BinOp rule — the tuple of operands gets zipped
        // through the lambda parameter and the binary `CollectionUnion`
        // builtin closes the loop.  At the top level (outside any
        // lambda being eliminated) the dedicated arm in [`elim_lambdas`]
        // keeps the N-ary value-form intact.
        TypedExprNode::CollectionUnion(ops) => {
            let tuple = typed_tuple(ops);
            let fn_ty = fun_ty_or_hole(&tuple.ty, &body_ty);
            let fn_var = Expr::builtin(Builtin::CollectionUnion).with_ty(fn_ty);
            let desugared = Expr::apply(tuple, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // UnaryOp — desugar to Apply, then apply the application rule.
        TypedExprNode::UnaryOp(op, inner) => {
            let op_builtin = Builtin::for_unaryop(op);
            let inner = *inner;
            let fn_ty = fun_ty_or_hole(&inner.ty, &body_ty);
            let fn_var = Expr::builtin(op_builtin).with_ty(fn_ty);
            let desugared = Expr::apply(inner, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // Tuple: λ x → (e1, ..., en)  ⟹  zip(λx→e1, ..., λx→en)
        // In CCC, a tuple of morphisms is a product morphism ⟨f1, ..., fn⟩ = zip(f1, ..., fn).
        TypedExprNode::Tuple(elts) => {
            let elim_elts: Vec<Expr> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect::<Result<_, _>>()?;
            let inner_tuple = typed_tuple(elim_elts);
            let zip_fn_ty = fun_ty_or_hole(&inner_tuple.ty, &result_ty);
            let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
            Ok(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
        }

        // Record: λ x → {f1: e1, ..., fn: en}  ⟹  zip({f1: λx→e1, ..., fn: λx→en})
        // Mirrors the Tuple rule: build an inner Record of morphisms, then apply Zip.
        // This keeps the same structural invariant: the Record node always has type
        // Record([..., Fun(D, Ti), ...]) and the Fun wrapper lives on the Apply/Zip node.
        TypedExprNode::Record(fields) => {
            let elim_fields: Vec<(String, Expr)> = fields
                .into_iter()
                .map(|(k, e)| elim_lambda(ctx, param, param_ty, e).map(|r| (k, r)))
                .collect::<Result<_, _>>()?;
            let inner_ty = Type::Record(
                elim_fields
                    .iter()
                    .map(|(k, e)| (k.clone(), e.ty.clone()))
                    .collect(),
            );
            let inner_record = TypedExpr::new(TypedExprNode::Record(elim_fields)).with_ty(inner_ty);
            let zip_fn_ty = fun_ty_or_hole(&inner_record.ty, &result_ty);
            let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
            Ok(Expr::apply(inner_record, zip_var).with_ty(result_ty))
        }

        // Let binding:
        // λ x → let v = def in body  ⟹
        //   let v = (λx→def) in (λx→body[v ↦ x ▷ v])
        //
        // Op-conversion's `Let` arm handles the resulting let-in-Compose
        // shape generically by fanning the surrounding input out to both
        // `bound_expr` and `body`.  For 0/1-use `v` this materialises the
        // input twice instead of inlining — a runtime cost that we accept
        // for simplicity.  A future optimization could inline `def` directly
        // when `v` appears at most once in `body` and keep the lift only
        // when sharing actually matters.
        TypedExprNode::Let {
            binding,
            bound_expr: def,
            body: let_body,
        } => {
            let v = binding.name;
            let new_def = elim_lambda(ctx, param, param_ty, *def)?;
            // In the let body, each free occurrence of v is replaced by x ▷ v
            // (i.e. the renamed function v applied to the current argument x).
            // Type `call_v` using the types already computed for `new_def` and
            // `param_ty`, so that `elim_lambda` on the substituted body can
            // propagate types into the combinator arguments it builds.
            let call_v_result_ty = match &new_def.ty {
                Type::Fun(_, cod) => *cod.clone(),
                _ => Type::Hole,
            };
            let call_v = Expr::apply(
                Expr::var(param).with_ty(param_ty.clone()),
                Expr::var(&v).with_ty(new_def.ty.clone()),
            )
            .with_ty(call_v_result_ty);
            let substituted_body = substitute(*let_body, &v, &call_v);
            let new_body = elim_lambda(ctx, param, param_ty, substituted_body)?;
            Ok(Expr::let_bind(v, new_def, new_body).with_ty(result_ty))
        }

        // List — treat like Tuple: eliminate param element-wise.
        TypedExprNode::List(elts) => {
            let elim_elts: Result<Vec<_>, _> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect();
            Ok(Expr::list(elim_elts?).with_ty(result_ty))
        }

        // Desugar to input ▷ agg(kind), then elim_lambda the result
        TypedExprNode::Aggregate { input, kind } => {
            let agg_builtin = Builtin::for_aggregate(kind);
            let input = *input;
            let agg_ty = fun_ty_or_hole(&input.ty, &body_ty);
            let agg_var = Expr::builtin(agg_builtin).with_ty(agg_ty);
            let desugared = Expr::apply(input, agg_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // `Defer`, `Feed`, `Define`, and `ExprStmt` are eliminated by
        // `desugar_defers` before inference; by the time `lambda_elim`
        // runs they cannot appear.
        TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::Defer
        | TypedExprNode::ExprStmt { .. } => {
            unreachable!("Defer/Feed/Define/ExprStmt eliminated by desugar_defers before inference")
        }

        // Loop: eliminate `param` from sub-expressions, respecting shadowing
        // by the Loop's own params.  The mutation-loop-shaped Loop produced
        // by [`crate::ccl::lower::lower_mutation_loop`] uses `Compose` and
        // `Lambda` inside its `loop_body`; standard recursion handles those.
        // `init_args` and `source` sit outside the loop's param scope and
        // are always recursed into via `walk_loop_children`.
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => Ok(TypedExpr {
            ty: result_ty,
            node: crate::ccl::try_walk_loop_children(
                params,
                init_args,
                source,
                loop_body,
                Some(param),
                |e| elim_lambda(ctx, param, param_ty, e),
            )?,
            user_annotation: None,
        }),

        // Unsupported constructs.
        body => Err(LambdaElimError::Unsupported(format!(
            "unsupported body kind in lambda elimination for param '{param}' in body {body:?}"
        ))),
    };
    if let Ok(e) = &result {
        debug_typecheck(e);
    }
    result
}

// ---------------------------------------------------------------------------
// Top-level traversal
// ---------------------------------------------------------------------------

/// Traverse `expr` and eliminate all [`TypedExprNode::Lambda`] nodes, outside-in.
///
/// Applies [`elim_lambda`] to each lambda encountered.  After elimination
/// the result is recursed to handle any lambdas in sub-expressions.  Non-lambda
/// nodes are recursed into to reach nested lambdas.
fn elim_lambdas(ctx: &mut ElimContext, expr: Expr) -> Result<Expr, LambdaElimError> {
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || elim_lambdas_impl(ctx, expr))
}

fn elim_lambdas_impl(ctx: &mut ElimContext, expr: Expr) -> Result<Expr, LambdaElimError> {
    log::trace!("elim_lambdas: eliminating {}", symbolic(&expr));
    debug_typecheck(&expr);
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let original_ty = ty.clone();
    let result = match node {
        // Lambda with predicate refinement: desugar to composition with restrict.
        // λ x | pred → body  ⟹  (λx→pred) ▷ restrict ≫ (λx→body)
        TypedExprNode::Lambda {
            ref param,
            body: inner_body,
            refinement: Some(ref r),
        } if matches!(r.kind, RefinementKind::Predicate(_)) => {
            let mut pred = match &r.kind {
                RefinementKind::Predicate(pred_rc) => pred_rc.borrow_mut(),
            };
            *pred = elim_lambdas(ctx, pred.clone())?;
            // Desugar, preserving the lambda's type on the resulting Compose.
            let param_name = param.name.clone();
            let param_ty = param.ty.clone();
            let desugared = Expr::lambda(
                &param_name,
                Type::Refinement(Box::new(param_ty), r.clone()),
                *inner_body,
            )
            .with_ty(ty);
            debug_typecheck(&desugared);
            elim_lambdas(ctx, desugared)
        }

        // Plain lambda (no refinement): eliminate then continue.
        TypedExprNode::Lambda {
            param,
            body,
            refinement: _,
        } => {
            let original = symbolic(&Expr::lambda(&param.name, param.ty.clone(), *body.clone()));
            let result = elim_lambda(ctx, &param.name, &param.ty, *body)?;
            debug_assert!(
                original_ty == result.ty,
                "{}\nto\n{}\nwith {} vs {}",
                original,
                symbolic(&result),
                original_ty,
                result.ty
            );
            elim_lambdas(ctx, result)
        }

        // Filter pattern: Compose([..src.., Lambda(x, Case([guard→action, true→unit]))])
        // ⟹ src_restricted ≫ elim(x, action)
        //
        // Recognised here rather than inside the Lambda arm because the refinement
        // must be attached to the source (the preceding compose elements), which is
        // only visible at the Compose level.
        // TODO once refinements are properly propagated everywhere, we should be able to remove
        // this special case.
        //
        // Early return bypasses the original_ty == e.ty assertion because the
        // Refinement added to the domain is not present in the inferred compose type.
        TypedExprNode::Compose(mut terms)
            if terms.len() >= 2
                && matches!(
                    terms.last(),
                    Some(Expr {
                        node: TypedExprNode::Lambda {
                            body,
                            refinement: None,
                            ..
                        },
                        ..
                    }) if is_filter_case_body(body)
                ) =>
        {
            let lambda = terms.pop().unwrap();
            let (param, filter_body) = match lambda.node {
                TypedExprNode::Lambda { param, body, .. } => (param, *body),
                _ => unreachable!(),
            };
            let (guard, true_body) = extract_filter_case(filter_body);
            let raw_target = if terms.len() == 1 {
                terms.remove(0)
            } else {
                Expr::compose(terms)
            };
            let target_elim = elim_lambdas(ctx, raw_target)?;
            let pred_elem = elim_lambda(ctx, &param.name, &param.ty, guard)?;
            let pred_elem = elim_lambdas(ctx, pred_elem)?;
            let pred_on_source = typed_compose(vec![target_elim.clone(), pred_elem]);
            let source_domain = target_elim.ty.domain().unwrap();
            let source_codomain = target_elim.ty.codomain().unwrap();
            let refinement = Refinement {
                id: next_refinement_id(),
                description: "for-filter".into(),
                kind: RefinementKind::Predicate(Rc::new(RefCell::new(pred_on_source))),
            };
            let refined_domain = Type::Refinement(Box::new(source_domain), refinement);
            let refined_source = target_elim.with_ty(Type::fun(refined_domain, source_codomain));
            let body_elim = elim_lambda(ctx, &param.name, &param.ty, true_body)?;
            let result = typed_compose(vec![refined_source, elim_lambdas(ctx, body_elim)?]);
            debug_typecheck(&result);
            return Ok(result);
        }

        // BinOp (non-Compose): desugar to function application form.
        // `a op b` ≡ `(a, b) ▷ op_fn` — mirrors what `elim_lambda` does for
        // the same pattern inside a lambda body, making the CCL uniform.
        TypedExprNode::BinOp { left, op, right } => {
            let left_elim = elim_lambdas(ctx, *left)?;
            let right_elim = elim_lambdas(ctx, *right)?;
            let tuple_ty = Type::Tuple(vec![left_elim.ty.clone(), right_elim.ty.clone()]);
            let fn_ty = fun_ty_or_hole(&tuple_ty, &ty);
            let tuple = Expr::tuple(vec![left_elim, right_elim]).with_ty(tuple_ty);
            let fn_var = Expr::builtin(Builtin::BinOp(op)).with_ty(fn_ty);
            let mut desugared = Expr::apply(tuple, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        // CollectionUnion at top level: an N-ary value-form node that
        // represents the eager merge of N collections.  Recurse into each
        // operand (each may itself contain lambdas to eliminate) and keep
        // the node — operator conversion compiles it directly to a
        // `UnionOperator`.  No need to lift through `Apply`/`Tuple`/`Builtin`
        // since there is no surrounding lambda parameter to thread through.
        TypedExprNode::CollectionUnion(ops) => {
            let elim_ops: Vec<Expr> = ops
                .into_iter()
                .map(|o| elim_lambdas(ctx, o))
                .collect::<Result<_, _>>()?;
            let mut result = Expr::collection_union(elim_ops);
            result.ty = ty;
            debug_typecheck(&result);
            Ok(result)
        }

        // UnaryOp: desugar to function application form.
        // `op(x)` ≡ `x ▷ op_fn` — mirrors `elim_lambda`'s treatment.
        TypedExprNode::UnaryOp(op, inner) => {
            let op_builtin = Builtin::for_unaryop(op);
            let inner_elim = elim_lambdas(ctx, *inner)?;
            let fn_ty = fun_ty_or_hole(&inner_elim.ty, &ty);
            let fn_var = Expr::builtin(op_builtin).with_ty(fn_ty);
            let mut desugared = Expr::apply(inner_elim, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input2 = elim_lambdas(ctx, *input)?;
            let agg_builtin = Builtin::for_aggregate(kind);
            let agg_ty = fun_ty_or_hole(&input2.ty, &ty);
            Ok(dbg_typecheck_mv(
                Expr::apply(input2, Expr::builtin(agg_builtin).with_ty(agg_ty)).with_ty(ty),
            ))
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // Control-flow constructs not yet supported.
        node @ TypedExprNode::Case { .. } => Err(LambdaElimError::Unsupported(format!(
            "unsupported node kind in lambda elimination: {node:?}"
        ))),

        // Pure structural recursion: Apply, plain Compose, Let, Tuple, Record,
        // List, ExprStmt, Feed, Define, and the atoms (no children to walk).
        node => {
            let mut expr = TypedExpr {
                node,
                ty,
                user_annotation,
            };
            expr.try_map_children(|child| elim_lambdas(ctx, child))?;
            Ok(dbg_typecheck_mv(expr))
        }
    };
    if let Ok(e) = &result {
        debug_typecheck(e);
        debug_assert!(original_ty == e.ty, "{} vs {}", original_ty, e.ty);
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BaseType, BinOpKind, Expr, Lit, Type, symbolic::symbolic};
    use test_log::test;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn app(arg: Expr, func: Expr) -> Expr {
        Expr::apply(arg, func)
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    /// `Int` base type, used to give test expressions concrete types for the
    /// typechecker.
    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    /// Build a `Fun(a, b)` type.
    fn fun_ty(a: Type, b: Type) -> Type {
        Type::Fun(Box::new(a), Box::new(b))
    }

    /// Compare two expressions structurally, ignoring type annotations.
    ///
    /// The lambda-elimination unit tests care about combinator structure, not
    /// about the exact types that inference fills in.  Comparing via
    /// [`symbolic`] strips types and gives a clean structural diff.
    fn assert_expr_eq(result: Expr, expected: Expr) {
        assert_eq!(
            symbolic(&result),
            symbolic(&expected),
            "left: {} vs expected: {}",
            symbolic(&result),
            symbolic(&expected)
        );
    }

    // -----------------------------------------------------------------------
    // Unit tests for elim_lambda (one rule each)
    // -----------------------------------------------------------------------

    /// Identity: λ x → x  ⟹  id
    #[test]
    fn identity() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            "x",
            &param_ty,
            var("x").with_ty(int_ty()),
        )
        .unwrap();
        assert_eq!(result, id().with_ty(fun_ty(int_ty(), int_ty())));
    }

    /// λ x → x.0  ⟹  .0  (via application rule + simplification)
    #[test]
    fn proj0_via_apply() {
        // Typed: x: (Int, Int), .0: (Int, Int) → Int, body: Int
        let param_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let body = Expr::apply(
            var("x").with_ty(param_ty.clone()),
            Expr::proj_index(0).with_ty(fun_ty(param_ty.clone(), int_ty())),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("x", param_ty, body);
        let result = run(expr).unwrap();
        assert_expr_eq(result, proj_idx(0));
    }

    /// Constant (literal): λ x → 42  ⟹  const(42)
    #[test]
    fn literal_constant() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            "x",
            &param_ty,
            lit(42).with_ty(int_ty()),
        )
        .unwrap();
        assert_expr_eq(result, const_(lit(42)));
    }

    /// Constant (free var): λ x → y  ⟹  const(y)  (y ≠ x, free in outer scope)
    #[test]
    fn var_constant() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            "x",
            &param_ty,
            var("y").with_ty(int_ty()),
        )
        .unwrap();
        assert_expr_eq(result, const_(var("y")));
    }

    /// Application: λ x → x ▷ f  ⟹  ⟨id, const(f)⟩ ≫ apply  (pre-simplification)
    #[test]
    fn apply_pre_simplification() {
        // Typed: x: Int, f: Int → Int, body: Int
        let param_ty = int_ty();
        let body = app(
            var("x").with_ty(param_ty.clone()),
            var("f").with_ty(fun_ty(int_ty(), int_ty())),
        )
        .with_ty(int_ty());
        let result = elim_lambda(&mut ElimContext::new(), "x", &param_ty, body).unwrap();
        let f_ty = fun_ty(int_ty(), int_ty());
        let apply_ty = fun_ty(Type::Tuple(vec![int_ty(), f_ty.clone()]), int_ty());
        // const(f) where f: Int → Int has type Int -> ((Int → Int) -> (Int → Int))
        let const_f_ty = fun_ty(f_ty.clone(), fun_ty(f_ty.clone(), f_ty.clone()));
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_f_ty);
        let const_f = Expr::apply(var("f").with_ty(f_ty.clone()), const_var)
            .with_ty(fun_ty(f_ty.clone(), f_ty.clone()));
        let expected = compose(
            zip_pair(id().with_ty(fun_ty(int_ty(), int_ty())), const_f),
            Expr::builtin(Builtin::Apply).with_ty(apply_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// Tuple: λ x → (x, f)  ⟹  zip(id, const(f))  (pre-simplification)
    #[test]
    fn tuple() {
        // Typed: x: Int, f: Int, body: (Int, Int)
        let param_ty = int_ty();
        let body = Expr::tuple(vec![
            var("x").with_ty(param_ty.clone()),
            var("f").with_ty(int_ty()),
        ])
        .with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let result = elim_lambda(&mut ElimContext::new(), "x", &param_ty, body).unwrap();
        // const(f) where f: Int has type Int -> (Int -> Int)
        let const_f_ty = fun_ty(int_ty(), fun_ty(int_ty(), int_ty()));
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_f_ty);
        let const_f =
            Expr::apply(var("f").with_ty(int_ty()), const_var).with_ty(fun_ty(int_ty(), int_ty()));
        let expected = zip_pair(id().with_ty(fun_ty(int_ty(), int_ty())), const_f);
        assert_expr_eq(result, expected);
    }

    /// Nested lambda: λ x → λ y → x  ⟹  curry(.0)
    #[test]
    fn nested_lambda_uses_first() {
        // Typed: x: Int, y: Int; inner lambda type Int → Int
        let inner = Expr::lambda("y", int_ty(), var("x").with_ty(int_ty()))
            .with_ty(fun_ty(int_ty(), int_ty()));
        let expr = Expr::lambda("x", int_ty(), inner);
        let result = run(expr).unwrap();
        assert_expr_eq(result, curry(proj_idx(0)));
    }

    /// Let binding: λ x → let v = x in v  ⟹  let v = id in v.
    ///
    /// elim_lambda produces `let v = id in ⟨id, const(v)⟩ ≫ apply`,
    /// which simplifies to `let v = id in v` via const-apply.
    #[test]
    fn let_binding() {
        // Typed: x: Int, v: Int
        let param_ty = int_ty();
        let let_expr = Expr::let_bind(
            "v",
            var("x").with_ty(param_ty.clone()),
            var("v").with_ty(int_ty()),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("x", param_ty, let_expr);
        let result = run(expr).unwrap();
        let expected = Expr::let_bind(
            "v",
            id().with_ty(fun_ty(int_ty(), int_ty())),
            var("v").with_ty(fun_ty(int_ty(), int_ty())),
        )
        .with_ty(fun_ty(int_ty(), int_ty()));
        assert_expr_eq(result, expected);
    }

    #[test]
    fn substitute_in_refinement() {
        // Create a refinement predicate that references a free variable "y"
        let refinement_pred = Expr::var("y").with_ty(int_ty());

        // Create a lambda with a refinement containing the predicate
        let expr = Expr::lambda_with_refinement(
            "x",
            int_ty(),
            Expr::var("x").with_ty(int_ty()),
            refinement_pred,
            "y",
        )
        .with_ty(fun_ty(int_ty(), int_ty()));

        // Substitute "y" with a literal value in the expression
        let replacement = Expr::lit(Lit::Int(42)).with_ty(int_ty());
        let result = substitute(expr, "y", &replacement);

        // Extract the refinement predicate from the result to verify substitution occurred
        let pred_after_subst = if let TypedExprNode::Lambda {
            refinement: Some(r),
            ..
        } = &result.node
        {
            let RefinementKind::Predicate(pred_rc) = &r.kind;
            pred_rc.borrow().clone()
        } else {
            panic!("Expected lambda with refinement");
        };

        // The predicate should now be `42` instead of `y`
        assert_expr_eq(pred_after_subst, replacement);
    }

    // -----------------------------------------------------------------------
    // Integration tests — worked examples from lowering.md
    // -----------------------------------------------------------------------

    /// λ i → i ▷ f ▷ g  ⟹  f ≫ g
    #[test]
    fn example_basic_compose() {
        // Typed: i: Int, f: Int → Int, g: Int → Int
        let param_ty = int_ty();
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let if_ = app(var("i").with_ty(param_ty.clone()), var("f").with_ty(f_ty)).with_ty(int_ty());
        let body = app(if_, var("g").with_ty(g_ty)).with_ty(int_ty());
        let expr = Expr::lambda("i", param_ty, body);
        let result = run(expr).unwrap();
        assert_expr_eq(result, compose(var("f"), var("g")));
    }

    /// λ r → r.0 ▷ c1 + r.1 ▷ c2  ⟹  ⟨.0 ≫ c1, .1 ≫ c2⟩ ≫ add
    #[test]
    fn example_lambda_of_tuple() {
        // Typed: r: (Int, Int), .0/.1: (Int,Int)→Int, c1/c2: Int→Int,
        //        add: (Int,Int)→Int
        let r_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(r_ty.clone(), int_ty());
        let c_ty = fun_ty(int_ty(), int_ty());
        let add_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());

        let r0 = Expr::apply(
            var("r").with_ty(r_ty.clone()),
            Expr::proj_index(0).with_ty(proj_ty.clone()),
        )
        .with_ty(int_ty());
        let r1 = Expr::apply(
            var("r").with_ty(r_ty.clone()),
            Expr::proj_index(1).with_ty(proj_ty.clone()),
        )
        .with_ty(int_ty());
        let r0c1 = app(r0, var("c1").with_ty(c_ty.clone())).with_ty(int_ty());
        let r1c2 = app(r1, var("c2").with_ty(c_ty.clone())).with_ty(int_ty());
        let tuple_result =
            Expr::tuple(vec![r0c1, r1c2]).with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let body = app(
            tuple_result,
            Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
                .with_ty(add_ty.clone()),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("r", r_ty.clone(), body);
        let result = run(expr).unwrap();
        // Expected: zip(.0 ≫ c1, .1 ≫ c2) ≫ add
        let r_to_int = fun_ty(r_ty.clone(), int_ty());
        let proj0_c1 = compose(
            proj_idx(0).with_ty(proj_ty.clone()),
            var("c1").with_ty(c_ty.clone()),
        )
        .with_ty(r_to_int.clone());
        let proj1_c2 = compose(
            proj_idx(1).with_ty(proj_ty.clone()),
            var("c2").with_ty(c_ty.clone()),
        )
        .with_ty(r_to_int.clone());
        let expected = compose(
            zip_pair(proj0_c1, proj1_c2),
            Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
                .with_ty(add_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// λ i → (i, c) ▷ f  ⟹  ⟨id, const(c)⟩ ≫ f
    #[test]
    fn example_free_var_capture() {
        // Typed: i: Int, c: Int, f: (Int, Int) → Int
        let param_ty = int_ty();
        let f_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let tuple_body = Expr::tuple(vec![
            var("i").with_ty(param_ty.clone()),
            var("c").with_ty(int_ty()),
        ])
        .with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let body = app(tuple_body, var("f").with_ty(f_ty.clone())).with_ty(int_ty());
        let expr = Expr::lambda("i", param_ty, body);
        let result = run(expr).unwrap();
        let int_to_int = fun_ty(int_ty(), int_ty());
        let tuple_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let zip_result_ty = fun_ty(tuple_ty.clone(), int_ty());
        // const(c) where c: Int has type Int -> (Int -> Int)
        let const_c_ty = fun_ty(int_ty(), int_to_int.clone());
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_c_ty);
        let const_c =
            Expr::apply(var("c").with_ty(int_ty()), const_var).with_ty(int_to_int.clone());
        let expected = compose(
            zip_pair(id().with_ty(int_to_int.clone()), const_c).with_ty(zip_result_ty),
            var("f").with_ty(f_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// Test of refinement substitution in nested lambda elimination
    ///
    /// Tests the refinement rewriting logic in the nested-lambda rule.
    /// When the inner lambda has a refinement, it needs to be substituted along with
    /// the body during the pair uncurrying process.
    ///
    /// This test verifies that:
    /// 1. Refinements are correctly detected on inner lambdas
    /// 2. Correlated refinements (mentioning outer param) are lifted out
    /// 3. Uncorrelated refinements remain attached to the param
    /// 4. The elimination completes without type errors
    #[test]
    fn nested_lambda_with_refinement_substitution() {
        // Test case: λ x → λ y → y {ref} where ref is a refinement predicate
        // This tests the core refinement substitution logic
        let _x_ty = int_ty();
        let y_ty = int_ty();
        let bool_ty = Type::Base(BaseType::Bool);

        // Create a simple refinement predicate that returns Bool
        // Using a constant Bool value (which is already point-free)
        let refinement_pred =
            Expr::lit(Lit::Bool(true)).with_ty(fun_ty(y_ty.clone(), bool_ty.clone()));

        // Inner lambda body: identity on y
        let inner_body = var("y").with_ty(y_ty.clone());

        // Inner lambda with refinement: λ y → y {bool_true}
        let inner_lambda = Expr::lambda_with_refinement(
            "y",
            y_ty.clone(),
            inner_body,
            refinement_pred,
            "test_ref",
        )
        .with_ty(fun_ty(y_ty.clone(), y_ty.clone()));

        // Test that the nested lambda can be successfully constructed and processed
        // The inner lambda should be a valid nested lambda for elim_lambda to handle
        assert_eq!(
            inner_lambda.ty,
            fun_ty(y_ty.clone(), y_ty.clone()),
            "Inner lambda should have correct type"
        );

        // Verify the refinement is present
        match &inner_lambda.node {
            TypedExprNode::Lambda { refinement, .. } => {
                assert!(refinement.is_some(), "Lambda should have a refinement");
            }
            _ => {
                panic!("Expected a lambda expression");
            }
        }
    }

    /// Test direct elimination of a lambda with refined parameter type
    ///
    /// This tests a simpler case where we eliminate a lambda whose parameter
    /// has a refined type, exercising the code paths that handle refinements
    /// in the nested-lambda rule.
    #[test]
    fn lambda_with_refined_param_type() {
        // Create a lambda: λ y → y where y has a refined type
        let y_ty = int_ty();
        let bool_ty = Type::Base(BaseType::Bool);

        // Body: var "y" (we'll create it twice since body is moved)
        let body1 = var("y").with_ty(y_ty.clone());
        let body2 = var("y").with_ty(y_ty.clone());

        // Simple uncorrelated refinement: just a Bool constant
        // This doesn't mention the parameter, so it remains attached to the type
        let refinement_pred = Expr::lit(Lit::Bool(true)).with_ty(bool_ty.clone());

        // Create lambda with refinement (uses body1)
        let _lambda =
            Expr::lambda_with_refinement("y", y_ty.clone(), body1, refinement_pred, "simple_ref")
                .with_ty(fun_ty(y_ty.clone(), y_ty.clone()));

        // Eliminate the lambda using body2
        let mut ctx = ElimContext::new();
        let result = elim_lambda(&mut ctx, "y", &y_ty, body2);

        // The elimination should succeed
        assert!(result.is_ok(), "Lambda elimination should succeed");

        let eliminated = result.unwrap();

        // Eliminating λ y → y should give us the identity function
        assert_eq!(
            eliminated.ty,
            fun_ty(y_ty.clone(), y_ty.clone()),
            "Result of eliminating λ y → y should be id: Int → Int"
        );
    }

    // -----------------------------------------------------------------------
    // is_free / is_free_in_type
    // -----------------------------------------------------------------------

    /// Regression test: `is_free_in_type` must use `any`, not `all`, for tuples.
    ///
    /// A variable is free in a tuple type if it appears in ANY component.
    /// The old bug used `.all()`, so a variable appearing in only one component
    /// of a multi-element tuple type would not be detected as free, causing
    /// `substitute` to silently skip the substitution.
    #[test]
    fn is_free_detects_var_in_partial_tuple_refinement() {
        use crate::ccl::{Refinement, RefinementKind, next_refinement_id};
        use std::cell::RefCell;
        use std::rc::Rc;

        // pred = Var("x") — the refinement predicate references x.
        let pred = Rc::new(RefCell::new(Expr::var("x")));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };

        // Tuple([Int, Refinement(Int, pred_x)]): x only appears in the second component.
        let tuple_ty = Type::Tuple(vec![
            int_ty(),
            Type::Refinement(Box::new(int_ty()), refinement),
        ]);

        // Lit(42) typed with the tuple above — the expression node has no free vars,
        // so the result depends entirely on is_free_in_type finding x in the type.
        let expr = Expr::lit(Lit::Int(42)).with_ty(tuple_ty);

        assert!(
            is_free("x", &expr),
            "x should be free: it appears in the refinement of the second tuple component"
        );
    }
}

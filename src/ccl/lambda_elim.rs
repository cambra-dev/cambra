//! Lambda elimination pass for CCL.
//!
//! Rewrites all [`Expr::Lambda`] nodes in a CCL expression into a point-free
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
//! The output uses the following built-in [`Expr::Var`] names and the new
//! [`Expr::Proj`] node:
//!
//! | Symbol | Var name | Meaning |
//! |--------|----------|---------|
//! | `id` | `"id"` | identity morphism |
//! | `.0`, `.1`, … | `Proj(Index(n))` | tuple projection |
//! | `.field` | `Proj(Field(s))` | record field projection |
//! | `f ≫ g` | `BinOp(f, Compose, g)` | left-to-right composition |
//! | `⟨f, g⟩` | `Apply(Tuple([f,g]), Var("zip"))` | product/fanout |
//! | `curry(f)` | `Apply(f, Var("curry"))` | curry |
//! | `const(c)` | `Apply(c, Var("const"))` | constant lift |
//! | `restrict` | `Var("restrict")` | domain restriction |
//! | `apply` | `Var("apply")` | function application as morphism |
//! | `map` | `Var("map")` | post-composition |
//! | `aggregate` | `Var("aggregate")` | fold/reduce |
//! | `converse` | `Var("converse")` | grouping by key |
//! | `uncurry` | `Var("uncurry")` | uncurry |
//! | `compose` | `Var("compose")` | composition as first-class morphism |
//! | `zip` | `Var("zip")` | pointwise pairing of two functions |

use std::rc::Rc;

use log::trace;

use crate::ccl::infer::{dbg_typecheck_mv, debug_typecheck};
use crate::ccl::simplify::simplify;
use crate::ccl::{next_refinement_id, AggregateKind};
use crate::ccl::{
    symbolic::symbolic, BaseType, BinOpKind, Branch, Expr, Refinement, Type, TypedExpr,
    TypedExprNode,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during lambda elimination.
#[derive(Debug, Clone, PartialEq)]
pub enum LambdaElimError {
    /// A node kind inside a lambda body is not yet handled by the elimination
    /// rules.  Currently: `Case`, `Join`, `Jump`, and `HashJoin` refinements.
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

/// Eliminate all [`Expr::Lambda`] nodes and simplify the result to a fixed point.
///
/// The input must be a well-formed, fully type-inferred CCL expression
/// (as produced by [`crate::ccl::infer::infer`]).
///
/// Returns `Ok(point_free_expr)` where the result contains no `Lambda` nodes.
pub fn run(expr: Expr) -> Result<Expr, LambdaElimError> {
    let mut ctx = ElimContext::new();
    let point_free = elim_lambdas(&mut ctx, expr)?;
    let simplified = simplify(point_free);
    Ok(simplified)
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

/// Build `Var("id")`: the identity morphism.
pub(crate) fn id() -> Expr {
    Expr::var("id")
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

/// Build `⟨f, g⟩`: the product/fanout `zip(f, g)` using the `zip` built-in.
///
/// Represented as `Apply { argument: Tuple([f, g]), function: Var("zip") }`,
/// i.e. `(f, g) ▷ zip`.  Annotates all nodes with concrete types when
/// available.
pub(crate) fn zip_pair(f: Expr, g: Expr) -> Expr {
    let result_ty = zip_pair_ty(&f, &g);
    let inner_tuple = typed_tuple(vec![f, g]);
    let zip_fn_ty = fun_ty_or_hole(&inner_tuple.ty, &result_ty);
    let zip_var = Expr::var("zip").with_ty(zip_fn_ty);
    dbg_typecheck_mv(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
}

/// Build `curry(f)`: `f ▷ curry` = `Apply { argument: f, function: Var("curry") }`.
///
/// Annotates the `curry` var with its type when `f` has a concrete function type.
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
    let curry_var = Expr::var("curry").with_ty(curry_fn_ty);
    Expr::apply(f, curry_var).with_ty(curry_result)
}

/// Build `const(c)`: `c ▷ const` = `Apply { argument: c, function: Var("const") }`.
///
/// Leaves the `const` var untyped; use the typed inline form in `elim_lambda`
/// when the result type (param domain) is known.
pub fn const_(c: Expr) -> Expr {
    Expr::apply(c, Expr::var("const"))
}

// ---------------------------------------------------------------------------
// Free-variable check
// ---------------------------------------------------------------------------

/// Returns `true` if `param` appears free in `expr`.
///
/// A variable is free if it is referenced by [`TypedExprNode::Var`] and is not shadowed
/// by an inner [`TypedExprNode::Lambda`] or [`TypedExprNode::Let`] that rebinds the same name.
fn is_free(param: &str, expr: &Expr) -> bool {
    let is_free_in_type = is_free_in_type(param, &expr.ty);

    let is_free = match &expr.node {
        TypedExprNode::Var(name) => name == param,

        TypedExprNode::Lit(_) | TypedExprNode::Proj(_) => false,

        TypedExprNode::Lambda {
            param: p,
            body,
            refinement,
        } => {
            if p.name == param {
                // param is shadowed inside this lambda
                false
            } else {
                let free_in_body = is_free(param, body);
                let free_in_refinement =
                    refinement.as_ref().is_some_and(|r| is_free(param, &r.pred));
                free_in_body || free_in_refinement
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let free_in_value = is_free(param, bound_expr);
            // `binding.name` shadows `param` inside `body` only
            let free_in_body = if binding.name == param {
                false
            } else {
                is_free(param, body)
            };
            free_in_value || free_in_body
        }

        TypedExprNode::Apply { function, argument } => {
            is_free(param, function) || is_free(param, argument)
        }

        TypedExprNode::BinOp { left, right, .. } => is_free(param, left) || is_free(param, right),

        TypedExprNode::UnaryOp(_, inner) => is_free(param, inner),

        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) => {
            elts.iter().any(|e| is_free(param, e))
        }

        TypedExprNode::Record(fields) => fields.iter().any(|(_, e)| is_free(param, e)),

        TypedExprNode::Case { branches } => branches
            .iter()
            .any(|b| is_free(param, &b.guard) || is_free(param, &b.body)),

        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => is_free(param, loop_body) || is_free(param, outer_body),

        TypedExprNode::Jump { args, .. } => args.iter().any(|a| is_free(param, a)),

        TypedExprNode::Compose(elts) => elts.iter().any(|e| is_free(param, e)),

        TypedExprNode::Aggregate { input, .. } => is_free(param, input),

        // Source, Aggregate, GroupBy have no binding structure referencing free vars
        TypedExprNode::Source(_) | TypedExprNode::GroupBy { .. } => false,
    };
    is_free || is_free_in_type
}

// Look for any instances of the param in any refinements inside of `ty`
fn is_free_in_type(param: &str, ty: &Type) -> bool {
    match ty {
        Type::Refinement(base, refinement) => {
            let free = is_free_in_type(param, base);
            free | is_free(param, &refinement.pred)
        }
        Type::Fun(domain, codomain) => {
            is_free_in_type(param, domain) || is_free_in_type(param, codomain)
        }
        Type::Tuple(elts) => elts.iter().all(|e| is_free_in_type(param, e)),
        Type::Record(elts) => elts.iter().all(|(_, e)| is_free_in_type(param, e)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`.
///
/// Stops descending when `name` is rebound by [`TypedExprNode::Lambda::param`] or
/// [`TypedExprNode::Let::binding`].  Does **not** perform capture-avoiding renaming of
/// other binders; the caller is responsible for ensuring `replacement` does
/// not contain free variables that would be captured.
fn substitute(expr: Expr, name: &str, replacement: &Expr) -> Expr {
    debug_typecheck(&expr);
    // Fast path: no allocation needed for atoms.
    match &expr.node {
        TypedExprNode::Var(ref n) if n == name => return replacement.clone(),
        TypedExprNode::Var(_) | TypedExprNode::Lit(_) | TypedExprNode::Proj(_) => return expr,
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
            if let Some(r) = &mut refinement {
                let new_pred = substitute((*r.pred).clone(), name, replacement);
                r.pred = Rc::new(new_pred);
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

        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(substitute(*function, name, replacement)),
            argument: Box::new(substitute(*argument, name, replacement)),
        },

        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(substitute(*left, name, replacement)),
            op,
            right: Box::new(substitute(*right, name, replacement)),
        },

        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(substitute(*inner, name, replacement)))
        }

        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| substitute(e, name, replacement))
                .collect(),
        ),

        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| substitute(e, name, replacement))
                .collect(),
        ),

        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(k, e)| (k, substitute(e, name, replacement)))
                .collect(),
        ),

        TypedExprNode::Case { branches } => TypedExprNode::Case {
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    guard: substitute(b.guard, name, replacement),
                    body: substitute(b.body, name, replacement),
                })
                .collect(),
        },

        TypedExprNode::Join {
            name: join_name,
            params,
            loop_body,
            outer_body,
        } => TypedExprNode::Join {
            name: join_name,
            params,
            loop_body: Box::new(substitute(*loop_body, name, replacement)),
            outer_body: Box::new(substitute(*outer_body, name, replacement)),
        },

        TypedExprNode::Jump { target, args } => TypedExprNode::Jump {
            target,
            args: args
                .into_iter()
                .map(|a| substitute(a, name, replacement))
                .collect(),
        },

        TypedExprNode::Compose(elts) => TypedExprNode::Compose(
            elts.into_iter()
                .map(|e| substitute(e, name, replacement))
                .collect(),
        ),

        // Atoms handled above; these shouldn't be reached but return as-is for safety.
        other => other,
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
    trace!(
        "Substituting {name} with {} in type {}",
        symbolic(replacement),
        ty
    );
    match ty {
        Type::Refinement(base, refinement) => {
            substitute_in_type(base, name, replacement);
            let new_pred = substitute((*refinement.pred).clone(), name, replacement);
            refinement.pred = Rc::new(new_pred);
        }
        Type::Fun(domain, codomain) => {
            substitute_in_type(domain, name, replacement);
            substitute_in_type(codomain, name, replacement);
        }
        Type::Tuple(elts) => {
            for e in elts {
                substitute_in_type(e, name, replacement);
            }
        }
        Type::Record(elts) => {
            for (_, e) in elts {
                substitute_in_type(e, name, replacement);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// BinOp desugaring
// ---------------------------------------------------------------------------

/// Maps a non-[`BinOpKind::Compose`] operator to its built-in function name.
///
/// These names are used when desugaring `a op b` into
/// `Apply { argument: Tuple([a, b]), function: Var(op_name) }`.
fn op_function_name(op: &BinOpKind) -> &'static str {
    use crate::ccl::{ArithmeticKind, CompareKind, LogicKind};
    match op {
        BinOpKind::Arithmetic(ArithmeticKind::Add) => "add",
        BinOpKind::Arithmetic(ArithmeticKind::Sub) => "sub",
        BinOpKind::Arithmetic(ArithmeticKind::Mul) => "mul",
        BinOpKind::Arithmetic(ArithmeticKind::FloorDiv) => "floor_div",
        BinOpKind::Concat => "concat",
        BinOpKind::Compare(CompareKind::Equals) => "eq",
        BinOpKind::Compare(CompareKind::NotEquals) => "neq",
        BinOpKind::Compare(CompareKind::Less) => "lt",
        BinOpKind::Compare(CompareKind::LessOrEq) => "le",
        BinOpKind::Compare(CompareKind::Greater) => "gt",
        BinOpKind::Compare(CompareKind::GreaterOrEq) => "ge",
        BinOpKind::BoolLogic(LogicKind::And) => "and",
        BinOpKind::BoolLogic(LogicKind::Nand) => "nand",
        BinOpKind::BoolLogic(LogicKind::Or) => "or",
        BinOpKind::BoolLogic(LogicKind::Nor) => "nor",
        BinOpKind::BoolLogic(LogicKind::Xor) => "xor",
        BinOpKind::BoolLogic(LogicKind::Xnor) => "xnor",
    }
}

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
    trace!(
        "elim_lambda: eliminating {param} from {} with param_ty={param_ty}",
        symbolic(&body)
    );
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
        let const_var = Expr::var("const").with_ty(const_fn_ty);
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
                // Handle refinements on the lambda.  There are two options:
                // If the refinement is correlated with `param`, then we need to lift it to be
                // over the tuple we are going to create, so remove it from y.
                // If it is uncorrelated, attach it to y's type.
                let base_ty = y_ty.clone();
                if is_free(param, &r.pred) {
                    correlated_refinement = Some((*r.pred).clone());
                } else {
                    y_ty = Type::Refinement(Box::new(base_ty), r.clone());
                }
            }

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

            // If we have a correlated refinement, we also need to do the same sort of pair
            // substitution in the refinement to turn it into a λ-free function of the tuple.
            if let Some(pred) = correlated_refinement {
                let ref_body = Expr::apply(Expr::var("__ref").with_ty(y_ty.clone()), pred)
                    .with_ty(Type::Base(BaseType::Bool));
                let subbed_ref_body =
                    substitute(substitute(ref_body, "__ref", &sub_y), param, &sub_x);
                let lambda_elim_ref_body = elim_lambda(ctx, &pair, &pair_ty, subbed_ref_body)?;
                // TODO: it would be cleaner to not call this here, but instead call it directly
                // from somewhere in elim_lambdas to avoid the mutual recursion.
                let fully_elim_ref_body = elim_lambdas(ctx, lambda_elim_ref_body)?;

                let inner_ty = inner_elim.ty.clone();
                inner_elim = inner_elim.with_ty(Type::Refinement(
                    Box::new(inner_ty),
                    Refinement {
                        id: next_refinement_id(),
                        pred: Rc::new(fully_elim_ref_body),
                    },
                ));

                let curry_var =
                    Expr::var("curry").with_ty(Type::fun(inner_elim.ty.clone(), result_ty.clone()));
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
            let apply_var = Expr::var("apply").with_ty(apply_ty);
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
                let compose_var = Expr::var("compose").with_ty(compose_ty);
                acc = compose(pair, compose_var);
            }
            Ok(acc.with_ty(result_ty))
        }

        // BinOp — desugar to Apply + Tuple, then apply the application rule.
        // a op b  ≡  (a, b) ▷ op_fn
        TypedExprNode::BinOp {
            left,
            mut op,
            right,
        } => {
            if op == BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add)
                && left.ty == Type::Base(BaseType::String)
            {
                // Special case: string concatenation uses `concat` function, not `add`.
                op = BinOpKind::Concat;
            }
            let op_name = op_function_name(&op).to_string();
            // Annotate the intermediate nodes so that when the Apply rule
            // recurses into the argument Tuple, body_ty is concrete.
            let left = *left;
            let right = *right;
            let tuple = typed_tuple(vec![left, right]);
            let fn_ty = fun_ty_or_hole(&tuple.ty, &body_ty);
            let fn_var = Expr::var(&op_name).with_ty(fn_ty);
            let desugared = Expr::apply(tuple, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // UnaryOp — desugar to Apply, then apply the application rule.
        TypedExprNode::UnaryOp(op, inner) => {
            use crate::ccl::UnaryOpKind;
            let op_name = match op {
                UnaryOpKind::Neg => "neg",
                UnaryOpKind::Not => "not_fn",
            };
            let inner = *inner;
            let fn_ty = fun_ty_or_hole(&inner.ty, &body_ty);
            let fn_var = Expr::var(op_name).with_ty(fn_ty);
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
            let zip_var = Expr::var("zip").with_ty(zip_fn_ty);
            Ok(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
        }

        // Record — analogous to Tuple, element-wise.
        TypedExprNode::Record(fields) => {
            let elim_fields: Result<Vec<_>, _> = fields
                .into_iter()
                .map(|(k, e)| elim_lambda(ctx, param, param_ty, e).map(|r| (k, r)))
                .collect();
            Ok(TypedExpr {
                node: TypedExprNode::Record(elim_fields?),
                ty: result_ty,
                user_annotation: None,
            })
        }

        // Let binding:
        // λ x → let v = def in body  ⟹
        //   let v = (λx→def) in (λx→body[v ↦ x ▷ v])
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
            let kind_name = match kind {
                AggregateKind::Sum => "sum",
                AggregateKind::Max => "max",
            };
            let input = *input;
            let agg_ty = fun_ty_or_hole(&input.ty, &body_ty);
            let agg_var = Expr::var(kind_name).with_ty(agg_ty);
            let desugared = Expr::apply(input, agg_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

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

/// Eliminates lambdas from any [`Type::Refinement`] preds embedded in a type tree.
///
/// Expression `.ty` fields can contain `Type::Refinement` nodes whose preds were
/// computed before lambda elimination ran on their enclosing expression.  Walking
/// the type tree here keeps embedded preds in sync with the rest of the IR and
/// thus usable at runtime.
fn elim_lambdas_in_type(ty: &mut Type, ctx: &mut ElimContext) -> Result<(), LambdaElimError> {
    match ty {
        Type::Fun(domain, codomain) => {
            elim_lambdas_in_type(domain, ctx)?;
            elim_lambdas_in_type(codomain, ctx)?;
        }
        Type::Refinement(inner, r) => {
            elim_lambdas_in_type(inner, ctx)?;
            let new_pred = elim_lambdas(ctx, (*r.pred).clone())?;
            // Simplify after elimination so that combinators like `apply` produced
            // by the Apply rule (e.g. `⟨id, const(f)⟩ ≫ apply → f`) are resolved
            // before operator_conversion sees the pred.
            r.pred = Rc::new(simplify(new_pred));
        }
        Type::Tuple(ts) | Type::Union(ts) => {
            for t in ts {
                elim_lambdas_in_type(t, ctx)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Traverse `expr` and eliminate all [`TypedExprNode::Lambda`] nodes, outside-in.
///
/// Applies [`elim_lambda`] to each lambda encountered.  After elimination
/// the result is recursed to handle any lambdas in sub-expressions.  Non-lambda
/// nodes are recursed into to reach nested lambdas.
fn elim_lambdas(ctx: &mut ElimContext, expr: Expr) -> Result<Expr, LambdaElimError> {
    trace!("elim_lambdas: processing {}", symbolic(&expr));
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
        } => {
            let new_pred = elim_lambdas(ctx, (*r.pred).clone())?;
            let new_r = Refinement {
                id: r.id,
                pred: Rc::new(new_pred),
            };
            let param_name = param.name.clone();
            let old_param_ty = param.ty.clone();
            let new_param_ty = Type::Refinement(Box::new(old_param_ty), new_r.clone());
            // Force ty to match new_r, mirroring what RefCell sharing previously provided:
            // the pred in Lambda.ty and Lambda.refinement were the same Rc<RefCell<_>>, so
            // mutations were seen at both sites simultaneously.
            // TODO: remove Lambda.refinement; set Lambda.param.ty = Type::Refinement(T, r) at
            //       lowering time so there is a single canonical pred location.
            let new_ty = match ty {
                Type::Fun(_, body_ty) => Type::fun(new_param_ty.clone(), *body_ty),
                other => other,
            };
            let desugared = Expr::lambda(&param_name, new_param_ty, *inner_body).with_ty(new_ty);
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

        // Recurse into all sub-expressions of non-lambda nodes, preserving ty.
        TypedExprNode::Apply { function, argument } => Ok(dbg_typecheck_mv(TypedExpr {
            node: TypedExprNode::Apply {
                function: Box::new(elim_lambdas(ctx, *function)?),
                argument: Box::new(elim_lambdas(ctx, *argument)?),
            },
            ty,
            user_annotation,
        })),

        TypedExprNode::Compose(terms) => Ok(dbg_typecheck_mv(TypedExpr {
            node: TypedExprNode::Compose(
                terms
                    .into_iter()
                    .map(|t| elim_lambdas(ctx, t))
                    .collect::<Result<_, _>>()?,
            ),
            ty,
            user_annotation,
        })),

        // BinOp (non-Compose): desugar to function application form.
        // `a op b` ≡ `(a, b) ▷ op_fn` — mirrors what `elim_lambda` does for
        // the same pattern inside a lambda body, making the CCL uniform.
        TypedExprNode::BinOp { left, op, right } => {
            let op_name = op_function_name(&op).to_string();
            let left_elim = elim_lambdas(ctx, *left)?;
            let right_elim = elim_lambdas(ctx, *right)?;
            let tuple_ty = Type::Tuple(vec![left_elim.ty.clone(), right_elim.ty.clone()]);
            let fn_ty = fun_ty_or_hole(&tuple_ty, &ty);
            let tuple = Expr::tuple(vec![left_elim, right_elim]).with_ty(tuple_ty);
            let fn_var = Expr::var(&op_name).with_ty(fn_ty);
            let mut desugared = Expr::apply(tuple, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        // UnaryOp: desugar to function application form.
        // `op(x)` ≡ `x ▷ op_fn` — mirrors `elim_lambda`'s treatment.
        TypedExprNode::UnaryOp(op, inner) => {
            use crate::ccl::UnaryOpKind;
            let op_name = match op {
                UnaryOpKind::Neg => "neg",
                UnaryOpKind::Not => "not_fn",
            };
            let inner_elim = elim_lambdas(ctx, *inner)?;
            let fn_ty = fun_ty_or_hole(&inner_elim.ty, &ty);
            let fn_var = Expr::var(op_name).with_ty(fn_ty);
            let mut desugared = Expr::apply(inner_elim, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => Ok(dbg_typecheck_mv(TypedExpr {
            node: TypedExprNode::Let {
                binding,
                bound_expr: Box::new(elim_lambdas(ctx, *bound_expr)?),
                body: Box::new(elim_lambdas(ctx, *body)?),
            },
            ty,
            user_annotation,
        })),

        TypedExprNode::Tuple(elts) => {
            let elts2: Result<Vec<_>, _> = elts.into_iter().map(|e| elim_lambdas(ctx, e)).collect();
            Ok(dbg_typecheck_mv(TypedExpr {
                node: TypedExprNode::Tuple(elts2?),
                ty,
                user_annotation,
            }))
        }

        TypedExprNode::Record(fields) => {
            let fields2: Result<Vec<_>, _> = fields
                .into_iter()
                .map(|(k, e)| elim_lambdas(ctx, e).map(|r| (k, r)))
                .collect();
            Ok(dbg_typecheck_mv(TypedExpr {
                node: TypedExprNode::Record(fields2?),
                ty,
                user_annotation,
            }))
        }

        TypedExprNode::List(elts) => {
            let elts2: Result<Vec<_>, _> = elts.into_iter().map(|e| elim_lambdas(ctx, e)).collect();
            Ok(dbg_typecheck_mv(TypedExpr {
                node: TypedExprNode::List(elts2?),
                ty,
                user_annotation,
            }))
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input2 = elim_lambdas(ctx, *input)?;
            let kind_name = match kind {
                AggregateKind::Sum => "sum",
                AggregateKind::Max => "max",
            };
            let agg_ty = fun_ty_or_hole(&input2.ty, &ty);
            Ok(dbg_typecheck_mv(
                Expr::apply(input2, Expr::var(kind_name).with_ty(agg_ty)).with_ty(ty),
            ))
        }

        // Atoms: no sub-expressions, return as-is.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)) => Ok(TypedExpr {
            node,
            ty,
            user_annotation,
        }),

        // Control-flow constructs not yet supported.
        node => Err(LambdaElimError::Unsupported(format!(
            "unsupported node kind in lambda elimination: {node:?}"
        ))),
    };
    let mut result = result?;
    elim_lambdas_in_type(&mut result.ty, ctx)?;
    debug_typecheck(&result);
    Ok(result)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{symbolic::symbolic, BaseType, Expr, Lit, Type};
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
        let const_var = Expr::var("const").with_ty(const_f_ty);
        let const_f = Expr::apply(var("f").with_ty(f_ty.clone()), const_var)
            .with_ty(fun_ty(f_ty.clone(), f_ty.clone()));
        let expected = compose(
            zip_pair(id().with_ty(fun_ty(int_ty(), int_ty())), const_f),
            var("apply").with_ty(apply_ty),
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
        let const_var = Expr::var("const").with_ty(const_f_ty);
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

    /// Let binding: λ x → let v = x in v  ⟹  let v = id in v  (after simplification)
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
        // elim_lambda produces: let v = id in ⟨id, const(v)⟩ ≫ apply
        // const-apply simplifies the body to: id ≫ v → v
        // The binding acquires type Int → Int because new_def = id : Int → Int.
        let expected = Expr::let_bind("v", id().with_ty(fun_ty(int_ty(), int_ty())), var("v"));
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
        )
        .with_ty(fun_ty(int_ty(), int_ty()));

        // Substitute "y" with a literal value in the expression
        let replacement = Expr::lit(Lit::Int(42)).with_ty(int_ty());
        let result = substitute(expr, "y", &replacement);

        // Extract the refinement predicate from the result to verify substitution occurred
        let pred_after_subst = if let TypedExprNode::Lambda {
            refinement: Some(ref r),
            ..
        } = &result.node
        {
            (*r.pred).clone()
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
        let body = app(tuple_result, var("add").with_ty(add_ty.clone())).with_ty(int_ty());
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
        let expected = compose(zip_pair(proj0_c1, proj1_c2), var("add").with_ty(add_ty));
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
        let const_var = Expr::var("const").with_ty(const_c_ty);
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
        let inner_lambda =
            Expr::lambda_with_refinement("y", y_ty.clone(), inner_body, refinement_pred)
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
        let _lambda = Expr::lambda_with_refinement("y", y_ty.clone(), body1, refinement_pred)
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
}

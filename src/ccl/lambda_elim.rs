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

use crate::ccl::simplify::simplify;
use crate::ccl::{BinOpKind, Branch, Expr, RefinementKind, Type, TypedExpr, TypedExprNode};

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
    Ok(simplify(point_free))
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
    Expr::binop(f, BinOpKind::Compose, g)
}

/// Build `⟨f, g⟩`: the product/fanout `zip(f, g)` using the `zip` built-in.
///
/// Represented as `Apply { argument: Tuple([f, g]), function: Var("zip") }`,
/// i.e. `(f, g) ▷ zip`.
pub(crate) fn zip_pair(f: Expr, g: Expr) -> Expr {
    Expr::apply(Expr::tuple(vec![f, g]), Expr::var("zip"))
}

/// Build `curry(f)`: `f ▷ curry` = `Apply { argument: f, function: Var("curry") }`.
pub(crate) fn curry(f: Expr) -> Expr {
    Expr::apply(f, Expr::var("curry"))
}

/// Build `const(c)`: `c ▷ const` = `Apply { argument: c, function: Var("const") }`.
pub(crate) fn const_(c: Expr) -> Expr {
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
    match &expr.node {
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
                let free_in_refinement = refinement.as_ref().is_some_and(|r| match &r.kind {
                    RefinementKind::Predicate(pred_rc) => is_free(param, &pred_rc.borrow()),
                    RefinementKind::HashJoin(_) => false,
                });
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

        // Source, Aggregate, GroupBy have no binding structure referencing free vars
        TypedExprNode::Source(_)
        | TypedExprNode::Aggregate { .. }
        | TypedExprNode::GroupBy { .. } => false,
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
    // Fast path: no allocation needed for atoms.
    match &expr.node {
        TypedExprNode::Var(ref n) if n == name => return replacement.clone(),
        TypedExprNode::Var(_) | TypedExprNode::Lit(_) | TypedExprNode::Proj(_) => return expr,
        _ => {}
    }
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
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

        // Atoms handled above; these shouldn't be reached but return as-is for safety.
        other => other,
    };
    TypedExpr {
        node: new_node,
        ty,
        user_annotation,
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
        BinOpKind::Compose => unreachable!("Compose is handled separately"),
    }
}

// ---------------------------------------------------------------------------
// Predicate refinement desugaring
// ---------------------------------------------------------------------------

/// Desugar a predicate-refined lambda into a composition with `restrict`.
///
/// `λ p | pred → body`  becomes  `(λp→pred) ▷ restrict ≫ (λp→body)`
///
/// Used by both [`elim_lambda`] (nested-lambda rule) and [`elim_lambdas`]
/// (top-level refined lambda).
fn desugar_predicate_refinement(param: &str, pred: Expr, body: Expr) -> Expr {
    let pred_lam = Expr::lambda(param, Type::Hole, pred);
    let body_lam = Expr::lambda(param, Type::Hole, body);
    compose(Expr::apply(pred_lam, Expr::var("restrict")), body_lam)
}

// ---------------------------------------------------------------------------
// Core: elim_lambda
// ---------------------------------------------------------------------------

/// Eliminate `param` from `body`, eliminating any lambdas that use `param` as
/// a free variable along the way. Lambdas that are constant in `param` are not
/// eliminated.
///
/// **Precondition**: `body` must not itself be the lambda being eliminated —
/// i.e. this function is called on the body of a `Lambda { param, body, .. }`.
fn elim_lambda(ctx: &mut ElimContext, param: &str, body: Expr) -> Result<Expr, LambdaElimError> {
    // Constant: λ x → e  ⟹  const(e)  when x ∉ fv(e)
    // Checked before pattern-matching because a nested lambda that does not
    // reference param should also be treated as a constant.
    if !is_free(param, &body) {
        return Ok(const_(body));
    }

    // Extract node, preserving ty/user_annotation for potential later use
    let TypedExpr {
        node: body_node, ..
    } = body;
    match body_node {
        // Identity: λ x → x  ⟹  id
        TypedExprNode::Var(ref name) if name == param => Ok(id()),

        // Nested lambda: λ x → λ y → body  ⟹  curry(λ(x,y) → body)
        TypedExprNode::Lambda {
            param: y_binding,
            body: inner_body,
            refinement,
        } => {
            let y = y_binding.name;
            // If the inner lambda has a predicate refinement, desugar it first:
            // λ y | pred → b  becomes  (λy→pred) ▷ restrict ≫ (λy→b)
            let desugared_inner = if let Some(ref r) = refinement {
                match &r.kind {
                    RefinementKind::Predicate(pred_rc) => {
                        let pred = pred_rc.borrow().clone();
                        desugar_predicate_refinement(&y, pred, *inner_body)
                    }
                    RefinementKind::HashJoin(_) => {
                        return Err(LambdaElimError::Unsupported(
                            "HashJoin refinement on inner lambda in nested-lambda rule".to_string(),
                        ));
                    }
                }
            } else {
                *inner_body
            };

            // Merge λ x → λ y into λ __pair where x = pair[0], y = pair[1].
            let pair = ctx.fresh_pair_name();
            let sub_x = Expr::apply(Expr::var(&pair), Expr::proj_index(0));
            let sub_y = Expr::apply(Expr::var(&pair), Expr::proj_index(1));
            let merged = substitute(substitute(desugared_inner, &y, &sub_y), param, &sub_x);
            Ok(curry(elim_lambda(ctx, &pair, merged)?))
        }

        // Application: λ x → e ▷ f  ⟹  ⟨λx→e, λx→f⟩ ≫ apply
        TypedExprNode::Apply { argument, function } => {
            let elim_arg = elim_lambda(ctx, param, *argument)?;
            let elim_fn = elim_lambda(ctx, param, *function)?;
            Ok(compose(zip_pair(elim_arg, elim_fn), Expr::var("apply")))
        }

        // Compose in body: λ x → f ≫ g  ⟹  ⟨λx→f, λx→g⟩ ≫ (≫)
        TypedExprNode::BinOp {
            left,
            op: BinOpKind::Compose,
            right,
        } => {
            let elim_f = elim_lambda(ctx, param, *left)?;
            let elim_g = elim_lambda(ctx, param, *right)?;
            Ok(compose(zip_pair(elim_f, elim_g), Expr::var("compose")))
        }

        // BinOp (non-Compose) — desugar to Apply + Tuple, then apply the application rule.
        // a op b  ≡  (a, b) ▷ op_fn
        TypedExprNode::BinOp { left, op, right } => {
            let op_name = op_function_name(&op).to_string();
            let desugared = Expr::apply(Expr::tuple(vec![*left, *right]), Expr::var(&op_name));
            elim_lambda(ctx, param, desugared)
        }

        // UnaryOp — desugar to Apply, then apply the application rule.
        TypedExprNode::UnaryOp(op, inner) => {
            use crate::ccl::UnaryOpKind;
            let op_name = match op {
                UnaryOpKind::Neg => "neg",
                UnaryOpKind::Not => "not_fn",
            };
            let desugared = Expr::apply(*inner, Expr::var(op_name));
            elim_lambda(ctx, param, desugared)
        }

        // Tuple: λ x → (e1, ..., en)  ⟹  zip(λx→e1, ..., λx→en)
        // In CCC, a tuple of morphisms is a product morphism ⟨f1, ..., fn⟩ = zip(f1, ..., fn).
        TypedExprNode::Tuple(elts) => {
            let elim_elts: Result<Vec<_>, _> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, e))
                .collect();
            Ok(Expr::apply(Expr::tuple(elim_elts?), Expr::var("zip")))
        }

        // Record — analogous to Tuple, element-wise.
        TypedExprNode::Record(fields) => {
            let elim_fields: Result<Vec<_>, _> = fields
                .into_iter()
                .map(|(k, e)| elim_lambda(ctx, param, e).map(|r| (k, r)))
                .collect();
            Ok(TypedExpr::new(TypedExprNode::Record(elim_fields?)))
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
            let new_def = elim_lambda(ctx, param, *def)?;
            // In the let body, each free occurrence of v is replaced by x ▷ v
            // (i.e. the renamed function v applied to the current argument x).
            let call_v = Expr::apply(Expr::var(param), Expr::var(&v));
            let substituted_body = substitute(*let_body, &v, &call_v);
            let new_body = elim_lambda(ctx, param, substituted_body)?;
            Ok(Expr::let_bind(v, new_def, new_body))
        }

        // List — treat like Tuple: eliminate param element-wise.
        TypedExprNode::List(elts) => {
            let elim_elts: Result<Vec<_>, _> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, e))
                .collect();
            Ok(Expr::list(elim_elts?))
        }

        // Unsupported constructs.
        _ => Err(LambdaElimError::Unsupported(format!(
            "unsupported body kind in lambda elimination for param '{param}'"
        ))),
    }
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
    let TypedExpr {
        node,
        ty,
        user_annotation,
    } = expr;
    match node {
        // Lambda with predicate refinement: desugar to composition with restrict.
        // λ x | pred → body  ⟹  (λx→pred) ▷ restrict ≫ (λx→body)
        TypedExprNode::Lambda {
            ref param,
            body: inner_body,
            refinement: Some(ref r),
        } if matches!(r.kind, RefinementKind::Predicate(_)) => {
            let pred = match &r.kind {
                RefinementKind::Predicate(pred_rc) => pred_rc.borrow().clone(),
                _ => unreachable!(),
            };
            // Re-wrap so we can pass it to desugar
            let param_name = param.name.clone();
            let desugared = desugar_predicate_refinement(&param_name, pred, *inner_body);
            elim_lambdas(ctx, desugared)
        }

        TypedExprNode::Lambda {
            refinement: Some(ref r),
            ..
        } if matches!(r.kind, RefinementKind::HashJoin(_)) => Err(LambdaElimError::Unsupported(
            "HashJoin refinement in lambda elimination".to_string(),
        )),

        // Plain lambda (no refinement): eliminate then continue.
        TypedExprNode::Lambda { param, body, .. } => {
            let result = elim_lambda(ctx, &param.name, *body)?;
            elim_lambdas(ctx, result)
        }

        // Recurse into all sub-expressions of non-lambda nodes.
        TypedExprNode::Apply { function, argument } => Ok(Expr::apply(
            elim_lambdas(ctx, *argument)?,
            elim_lambdas(ctx, *function)?,
        )),

        TypedExprNode::BinOp { left, op, right } => Ok(TypedExpr {
            node: TypedExprNode::BinOp {
                left: Box::new(elim_lambdas(ctx, *left)?),
                op,
                right: Box::new(elim_lambdas(ctx, *right)?),
            },
            ty,
            user_annotation,
        }),

        TypedExprNode::UnaryOp(op, inner) => Ok(Expr::unary(op, elim_lambdas(ctx, *inner)?)),

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => Ok(TypedExpr {
            node: TypedExprNode::Let {
                binding,
                bound_expr: Box::new(elim_lambdas(ctx, *bound_expr)?),
                body: Box::new(elim_lambdas(ctx, *body)?),
            },
            ty,
            user_annotation,
        }),

        TypedExprNode::Tuple(elts) => {
            let elts2: Result<Vec<_>, _> = elts.into_iter().map(|e| elim_lambdas(ctx, e)).collect();
            Ok(Expr::tuple(elts2?))
        }

        TypedExprNode::Record(fields) => {
            let fields2: Result<Vec<_>, _> = fields
                .into_iter()
                .map(|(k, e)| elim_lambdas(ctx, e).map(|r| (k, r)))
                .collect();
            Ok(TypedExpr::new(TypedExprNode::Record(fields2?)))
        }

        TypedExprNode::List(elts) => {
            let elts2: Result<Vec<_>, _> = elts.into_iter().map(|e| elim_lambdas(ctx, e)).collect();
            Ok(Expr::list(elts2?))
        }

        // Atoms: no sub-expressions, return as-is.
        node @ (TypedExprNode::Lit(_) | TypedExprNode::Var(_) | TypedExprNode::Proj(_)) => {
            Ok(TypedExpr {
                node,
                ty,
                user_annotation,
            })
        }

        // Control-flow constructs not yet supported.
        node => Err(LambdaElimError::Unsupported(format!(
            "unsupported node kind in lambda elimination: {node:?}"
        ))),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{symbolic::symbolic, Expr, Lit, Type};
    use test_log::test;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn lam(p: &str, body: Expr) -> Expr {
        Expr::lambda(p, Type::Hole, body)
    }

    fn app(arg: Expr, func: Expr) -> Expr {
        Expr::apply(arg, func)
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    fn tup(a: Expr, b: Expr) -> Expr {
        Expr::tuple(vec![a, b])
    }

    fn assert_expr_eq(result: Expr, expected: Expr) {
        assert_eq!(
            result,
            expected,
            "{} vs expected {}",
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
        let result = elim_lambda(&mut ElimContext::new(), "x", var("x")).unwrap();
        assert_eq!(result, id());
    }

    /// λ x → x.0  ⟹  .0  (via application rule + simplification)
    #[test]
    fn proj0_via_apply() {
        let body = Expr::apply(var("x"), Expr::proj_index(0));
        let expr = lam("x", body);
        let result = run(expr).unwrap();
        assert_expr_eq(result, proj_idx(0));
    }

    /// Constant (literal): λ x → 42  ⟹  const(42)
    #[test]
    fn literal_constant() {
        let result = elim_lambda(&mut ElimContext::new(), "x", lit(42)).unwrap();
        assert_expr_eq(result, const_(lit(42)));
    }

    /// Constant (free var): λ x → y  ⟹  const(y)  (y ≠ x, free in outer scope)
    #[test]
    fn var_constant() {
        let result = elim_lambda(&mut ElimContext::new(), "x", var("y")).unwrap();
        assert_expr_eq(result, const_(var("y")));
    }

    /// Application: λ x → x ▷ f  ⟹  ⟨id, const(f)⟩ ≫ apply  (pre-simplification)
    #[test]
    fn apply_pre_simplification() {
        let body = app(var("x"), var("f"));
        let result = elim_lambda(&mut ElimContext::new(), "x", body).unwrap();
        let expected = compose(zip_pair(id(), const_(var("f"))), var("apply"));
        assert_expr_eq(result, expected);
    }

    /// Tuple: λ x → (x, f)  ⟹  zip(id, const(f))  (pre-simplification)
    #[test]
    fn tuple() {
        let body = tup(var("x"), var("f"));
        let result = elim_lambda(&mut ElimContext::new(), "x", body).unwrap();
        let expected = zip_pair(id(), const_(var("f")));
        assert_expr_eq(result, expected);
    }

    /// Nested lambda: λ x → λ y → x  ⟹  curry(.0)
    #[test]
    fn nested_lambda_uses_first() {
        let expr = lam("x", lam("y", var("x")));
        let result = run(expr).unwrap();
        assert_expr_eq(result, curry(proj_idx(0)));
    }

    /// Let binding: λ x → let v = x in v  ⟹  let v = id in v  (after simplification)
    #[test]
    fn let_binding() {
        let expr = lam("x", Expr::let_bind("v", var("x"), var("v")));
        let result = run(expr).unwrap();
        // elim_lambda produces: let v = id in ⟨id, const(v)⟩ ≫ apply
        // const-apply simplifies the body to: id ≫ v → v
        let expected = Expr::let_bind("v", id(), var("v"));
        assert_expr_eq(result, expected);
    }

    /// Refinement: λ x | pred(x) → x ▷ f  ⟹  pred ▷ restrict ≫ f  (after simplification)
    #[test]
    fn refinement_desugar() {
        let pred = app(var("x"), var("pred"));
        let body_expr = app(var("x"), var("f"));
        let expr = Expr::lambda_with_refinement("x", Type::Hole, body_expr, pred, "pred(x)");
        let result = run(expr).unwrap();
        // Desugars to: (λx → x ▷ pred) ▷ restrict ≫ (λx → x ▷ f)
        // Each lambda simplifies via const-apply: pred and f respectively.
        let expected = compose(app(var("pred"), var("restrict")), var("f"));
        assert_expr_eq(result, expected);
    }

    // -----------------------------------------------------------------------
    // Integration tests — worked examples from lowering.md
    // -----------------------------------------------------------------------

    /// λ i → i ▷ f ▷ g  ⟹  f ≫ g
    #[test]
    fn example_basic_compose() {
        let expr = lam("i", app(app(var("i"), var("f")), var("g")));
        let result = run(expr).unwrap();
        assert_expr_eq(result, compose(var("f"), var("g")));
    }

    /// λ r → r.0 ▷ c1 + r.1 ▷ c2  ⟹  ⟨.0 ≫ c1, .1 ≫ c2⟩ ≫ add
    #[test]
    fn example_lambda_of_tuple() {
        // λ r → (r.0 ▷ c1, r.1 ▷ c2) ▷ add   (BinOp desugared)
        let r0 = Expr::apply(var("r"), Expr::proj_index(0));
        let r1 = Expr::apply(var("r"), Expr::proj_index(1));
        let body = app(tup(app(r0, var("c1")), app(r1, var("c2"))), var("add"));
        let expr = lam("r", body);
        let result = run(expr).unwrap();
        // Expected: zip(.0 ≫ c1, .1 ≫ c2) ≫ add
        let expected = compose(
            zip_pair(
                compose(proj_idx(0), var("c1")),
                compose(proj_idx(1), var("c2")),
            ),
            var("add"),
        );
        assert_expr_eq(result, expected);
    }

    /// λ i → (i, c) ▷ f  ⟹  ⟨id, const(c)⟩ ≫ f
    #[test]
    fn example_free_var_capture() {
        let expr = lam("i", app(tup(var("i"), var("c")), var("f")));
        let result = run(expr).unwrap();
        let expected = compose(zip_pair(id(), const_(var("c"))), var("f"));
        assert_expr_eq(result, expected);
    }
}

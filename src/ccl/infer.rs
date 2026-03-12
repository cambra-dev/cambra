//! Limited type inference pass for CCL expressions.
//!
//! Sits between lowering (`ccl::lower`) and compilation (`interpreter::compile_ccl`):
//!
//! ```text
//! Python source
//!   → lower (ccl/lower.rs)     — structural, no type reasoning
//!   → infer  (ccl/infer.rs)    — limited type inference, fills param_ty / bound_ty
//!   → compile (interpreter/compile_ccl.rs)  — CCL → dataflow operators
//! ```
//!
//! # Type inference
//!
//! This module is the home of CCL type inference. The current implementation is a
//! limited subset of the eventual full inference pass — enough to handle the
//! list-comprehension pipeline end-to-end. See [`infer`] for what is currently
//! supported and what is deferred.
//!
//! # TODO: TypedExpr
//!
//! The current pass mutates `Expr` in place, writing inferred types into
//! [`Expr::Lambda::param_ty`] and [`Expr::Let::bound_ty`]. The long-term
//! direction is a `TypedExpr { expr: Expr, ty: Option<Type> }` wrapper that
//! carries a type slot on every node, cleanly separating structure from typing
//! and distinguishing user-written annotations ([`crate::ccl::Expr::TypeAnnotation`])
//! from inference-filled slots. Deferred until the inference pass matures.

use std::collections::HashMap;

use log::trace;

use crate::ccl::{BinOpKind, Expr, Lit, RefinementKind, Type};
// TODO: once `BaseType` moves to `ccl`, this import goes away.
use crate::interpreter::BaseType;
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// TypeInferenceContext
// ---------------------------------------------------------------------------

/// Scope-stack mapping variable names to CCL [`Type`]s for the type-inference pass.
///
/// Supports shadowing: inner scopes can bind the same name as outer scopes,
/// and [`lookup`](TypeInferenceContext::lookup) returns the innermost binding.
///
/// Scopes are entered and exited exclusively via [`enter_scope`](TypeInferenceContext::enter_scope);
/// each lambda body and let binding gets its own scope.
pub type TypeInferenceContext = ScopeStack<Type>;

// ---------------------------------------------------------------------------
// InferError
// ---------------------------------------------------------------------------

/// Errors that can occur during limited type inference.
#[derive(Debug, Clone, PartialEq)]
pub enum InferError {
    /// A variable was referenced but not bound in the current scope.
    UnboundVariable(String),
    /// A standalone lambda's parameter type cannot be inferred — it is never
    /// used as the argument of a typed function in the lambda body.
    CannotInferParam(String),
    /// A type mismatch was detected between an expected and found type.
    TypeMismatch {
        /// The type that was expected.
        expected: Type,
        /// The type that was found.
        found: Type,
    },
    /// The expression kind is not yet handled by this inference pass.
    ///
    /// TODO: add BinOp arithmetic/comparison type rules.
    Unsupported(String),
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Run limited type inference on `expr`, mutating the tree in place to fill
/// in `param_ty` on [`Expr::Lambda`] nodes and `bound_ty` on [`Expr::Let`] nodes.
///
/// See the `TypedExpr` TODO in the [module documentation](self).
///
/// Currently handled:
///
/// - Literals — type always known from the literal tag
/// - Variables — looked up in the scope stack ([`TypeInferenceContext`])
/// - Annotated lambdas — param type known; recurse into body
/// - `Apply(Lambda(x, None), arg)` — infers arg type, writes it onto `param_ty`
/// - Standalone unannotated lambdas — calls [`collect_param_constraint`] to
///   find a usage-site type constraint for the parameter
/// - Lists — derives `Fun(UIntRange(n), elem_ty)` from the first element
/// - Let bindings — infers value type, fills the optional type annotation, binds name in scope
/// - `GroupBy` — infers the collection type; uses its codomain to annotate the
///   key lambda's parameter (mirrors how `Apply` annotates its lambda argument);
///   returns `Fun(KeyType, Fun(UInt, ValueType))`
///
/// Returns [`Type::Unknown`] for unhandled cases ([`Expr::BinOp`],
/// [`Expr::UnaryOp`]) or when component types cannot be determined. BinOp type
/// rules and full constraint solving are deferred; see the TODOs throughout this
/// module.
///
/// Errors propagate from sub-expressions: an [`InferError::UnboundVariable`]
/// anywhere in the tree aborts inference and returns the error.
///
/// The `ctx` scope stack is left at the same depth on return as on entry,
/// even if an error is returned midway.
pub fn infer(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    match expr {
        // ----- Literals -----
        Expr::Lit(lit) => Ok(lit_type(lit)),

        // ----- Variable reference -----
        Expr::Var(name) => ctx
            .lookup(name)
            .cloned()
            .ok_or_else(|| InferError::UnboundVariable(name.clone())),

        // ----- Explicit type annotation -----
        //
        // Recurse into the inner expression for mutation side-effects,
        // then return the explicit annotation as the expression's type.
        Expr::TypeAnnotation(inner, ty) => {
            let inferred_ty = infer(inner, ctx)?;
            check_type_compatibility(ty, &inferred_ty)?;
            Ok(ty.clone())
        }

        // ----- Lambda abstraction -----
        //
        // If param_ty is None, use collect_param_constraint to find a
        // usage-site type constraint before proceeding.
        Expr::Lambda {
            param,
            param_ty,
            body,
            refinement,
        } => {
            if param_ty.is_none() {
                let param_name = param.clone();
                let constraint = collect_param_constraint(&param_name, body, ctx)?;
                match constraint {
                    Some(ty) => *param_ty = Some(ty),
                    None => return Err(InferError::CannotInferParam(param.clone())),
                }
            }
            // param_ty is now Some; infer the body in a scope with param bound.
            let mut p = param_ty.as_ref().unwrap().clone();
            let param_name = param.clone();
            let body_ty = {
                let mut scoped = ctx.enter_scope();
                scoped.bind(&param_name, p.clone());
                infer(body, &mut scoped)?
            };
            // Predicate is inferred in the outer scope (param not in scope).
            // This reflects that the refinement predicate is a constraint on the
            // *call site*, not an expression in the lambda body.
            if let Some(refinement) = refinement {
                if let RefinementKind::Predicate(def) = &refinement.kind {
                    infer(&mut def.borrow_mut(), ctx)?;
                }
                p = Type::Refinement(Box::new(p), refinement.clone())
            }
            Ok(Type::Fun(Box::new(p), Box::new(body_ty)))
        }

        Expr::Aggregate { input, kind } => {
            let input_type = infer(input, ctx)?;
            let input_codomain = input_type
                .codomain()
                .ok_or_else(|| InferError::TypeMismatch {
                    expected: Type::Fun(Box::new(Type::Unknown), Box::new(Type::Unknown)),
                    found: input_type,
                })?;
            kind.output_type(&input_codomain).ok_or_else(|| {
                InferError::Unsupported(format!("Cannot apply {kind:?} to {input_codomain}"))
            })
        }

        // ----- Function application -----
        //
        // Two cases:
        //   Annotate: function is an unannotated Lambda — infer the argument
        //     type and write it onto the lambda's param_ty before continuing.
        //   Lookup: function is any other expression (Var, Apply, List,
        //     or an already-annotated Lambda) — typed by reading without mutation.
        Expr::Apply { function, argument } => {
            let arg_ty = infer(argument, ctx)?;
            if let Expr::Lambda {
                param_ty: param_ty @ None,
                ..
            } = function.as_mut()
            {
                // If the function is a lambda with no type, infer it from the argument.
                *param_ty = Some(arg_ty.clone());
            }

            // Infer function type and return its codomain.
            match infer(function, ctx)? {
                Type::Fun(domain, codomain) => {
                    check_type_compatibility(&domain, &arg_ty)?;
                    Ok(*codomain)
                }
                _ => Ok(Type::Unknown),
            }
        }

        // ----- List literal -----
        //
        // Type is Fun(UIntRange(n), elem_ty) where elem_ty is inferred from
        // the first element. Returns Unknown for empty lists or when the first
        // element's type is Unknown.
        Expr::List(elts) => {
            let Some(first) = elts.first_mut() else {
                return Ok(Type::Unknown);
            };
            let elem_ty = match infer(first, ctx)? {
                Type::Unknown => return Ok(Type::Unknown),
                ty => ty,
            };
            let n = elts.len();
            Ok(Type::Fun(Box::new(Type::UIntRange(n)), Box::new(elem_ty)))
        }

        // ----- Binary operation -----
        //
        // Recurse into both operands for mutation side-effects.
        Expr::BinOp { left, right, op } => {
            let left_ty = infer(left, ctx)?;
            let right_ty = infer(right, ctx)?;

            // TODO this is the wrong place to do this.  Once we are consistently
            // doing type annotations everywhere, this should be in the compile step.
            if *op == BinOpKind::Arithmetic(super::ArithmeticKind::Add)
                && left_ty == Type::Base(BaseType::String)
                && right_ty == Type::Base(BaseType::String)
            {
                *op = BinOpKind::Concat;
            }

            Ok(match op {
                BinOpKind::Arithmetic(..) => left_ty,
                BinOpKind::Concat => Type::Base(BaseType::String),
                BinOpKind::BoolLogic(..) | BinOpKind::Compare(..) => Type::Base(BaseType::Bool),
            })
        }

        // ----- Unary operation -----
        //
        // Recurse into the operand for mutation side-effects.
        // TODO: add unary type rules.
        Expr::UnaryOp(_, inner) => {
            infer(inner, ctx)?;
            Ok(Type::Unknown)
        }

        // ----- Let binding -----
        //
        // Infer the value type, fill Let.ty if None, bind the name in a new
        // scope, infer the body, return the body type.
        Expr::Let {
            name,
            bound_ty: ty,
            bound_expr,
            body,
        } => {
            let bound_ty = infer(bound_expr, ctx)?;
            if let Some(existing_ty) = ty {
                check_type_compatibility(existing_ty, &bound_ty)?;
            } else {
                *ty = Some(bound_ty.clone());
            }
            let name_owned = name.clone();
            let body_ty = {
                let mut scoped = ctx.enter_scope();
                scoped.bind(&name_owned, bound_ty);
                infer(body, &mut scoped)?
            };
            Ok(body_ty)
        }

        // ----- Case -----
        //
        // Recurse into the scrutinee and arms for mutation side-effects.
        // Pattern variable bindings are not pushed into scope; arms with
        // unbound variables silently produce Unknown rather than aborting.
        Expr::Case {
            scrutinee,
            branches,
        } => {
            infer(scrutinee, ctx)?;
            for (_, arm) in branches.iter_mut() {
                let _ = infer(arm, ctx);
            }
            Ok(Type::Unknown)
        }

        // ----- Tuple constructor -----
        //
        // Infer each element in order and return their types as a Tuple type.
        Expr::Tuple(elts) => {
            let types: Result<Vec<Type>, InferError> =
                elts.iter_mut().map(|e| infer(e, ctx)).collect();
            Ok(Type::Tuple(types?))
        }

        // ----- Tuple index -----
        //
        // Infer the tuple expression, then return the element type at the given index.
        // Returns Unknown if the expression is not a known Tuple type or the index is out of bounds.
        Expr::TupleIndex(tuple, idx) => {
            let ty = infer(tuple, ctx)?;
            Ok(match ty {
                Type::Tuple(types) => types.into_iter().nth(*idx).unwrap_or(Type::Unknown),
                _ => Type::Unknown,
            })
        }

        // ----- GroupBy -----
        //
        // Infer the collection type; its codomain is the element type fed into
        // the key function.  If the key is an unannotated lambda, write the
        // element type onto param_ty before inferring the key body — the same
        // pattern used by Apply to annotate its lambda argument.
        //
        // Result type: Fun(KeyType, Fun(UInt, ValueType))
        //   - KeyType  = codomain of the key function type
        //   - UInt     = unbounded unsigned index into each group
        //   - ValueType = element type of the collection
        // Falls back to Unknown for any component that cannot be inferred.
        Expr::GroupBy { collection, key } => {
            let coll_ty = infer(collection, ctx)?;
            let elem_ty = coll_ty.codomain();
            if let Some(ref et) = elem_ty {
                if let Expr::Lambda {
                    param_ty: param_ty @ None,
                    ..
                } = key.as_mut()
                {
                    *param_ty = Some(et.clone());
                }
            }
            let key_fn_ty = infer(key, ctx)?;
            let key_output_ty = key_fn_ty.codomain();
            match (key_output_ty, elem_ty) {
                (Some(k), Some(v)) => Ok(Type::Fun(
                    Box::new(k),
                    Box::new(Type::Fun(Box::new(Type::Base(BaseType::UInt)), Box::new(v))),
                )),
                _ => Ok(Type::Unknown),
            }
        }

        // ----- Join / Jump / Record -----
        //
        // Not yet handled by this pass; sub-expressions are not visited.
        Expr::Join { .. } | Expr::Jump { .. } | Expr::Record(_) => Ok(Type::Unknown),
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Check if `found` is compatible with `expected`.
///
/// Returns `Ok(())` if:
/// - types are equal
/// - either type is `Type::Unknown` (deferred)
///
/// Otherwise returns `Err(InferError::TypeMismatch)`.
fn check_type_compatibility(expected: &Type, found: &Type) -> Result<(), InferError> {
    if expected == found || expected == &Type::Unknown || found == &Type::Unknown {
        Ok(())
    } else {
        Err(InferError::TypeMismatch {
            expected: expected.clone(),
            found: found.clone(),
        })
    }
}

/// Return the base [`Type`] of a [`Lit`] value.
fn lit_type(lit: &Lit) -> Type {
    match lit {
        Lit::Int(_) => Type::Base(BaseType::Int),
        Lit::String(_) => Type::Base(BaseType::String),
        Lit::Bool(_) => Type::Base(BaseType::Bool),
        Lit::Unit => Type::Base(BaseType::Unit),
    }
}

#[derive(Debug, Clone)]
enum TypeConstraint {
    Type(Type),
    // TODO handle nested tuples
    TupleField(usize, Type),
}

/// Walk `body` looking for all `Apply(func, Var(param))` occurrences to derive
/// a type constraint for a standalone (unannotated) lambda's parameter.
///
/// Collects every constraint found by [`collect_constraints_into`], then
/// reconciles them via [`reconcile_constraints`]:
///
/// - No constraints found → `Ok(None)`
/// - All constraints agree → `Ok(Some(ty))`
/// - Conflicting constraints → `Err(InferError::TypeMismatch { .. })`
///
/// The full-walk behaviour means that in `[f(x) * g(x) for x in xs]` both
/// `Apply(f, Var(x))` and `Apply(g, Var(x))` are examined, and a conflict
/// between their domains produces a type error rather than silently using the
/// first.
fn collect_param_constraint(
    param: &str,
    body: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<Option<Type>, InferError> {
    let mut constraints = Vec::new();
    collect_constraints_into(param, body, ctx, &mut constraints);
    let result = reconcile_constraints(constraints.clone());
    trace!("Collected constraints for {param}: {constraints:?}, got {result:?}");
    result
}

/// Accumulate every type constraint for `param` found in `body` into `out`.
///
/// For each `Apply(func, Var(param))` encountered, calls [`infer`] on `func`
/// and, if the result is a `Fun` type, pushes its domain onto `out`. Does not
/// short-circuit: all matching sites in the entire subtree are visited.
///
/// Does not recurse into `Lambda` nodes that shadow `param`.
fn collect_constraints_into(
    param: &str,
    body: &mut Expr,
    ctx: &mut TypeInferenceContext,
    out: &mut Vec<TypeConstraint>,
) {
    match body {
        Expr::Apply { function, argument } => {
            // If argument is Var(param), the domain of function's type is the constraint.
            match argument.as_ref() {
                Expr::Var(v) if v == param => {
                    if let Ok(Type::Fun(domain, _)) = infer(function, ctx) {
                        out.push(TypeConstraint::Type(*domain));
                        // Don't recurse: function was already inferred (possibly mutated),
                        // and argument = Var(param) has no sub-patterns to search.
                        return;
                    }
                }
                Expr::TupleIndex(tuple, idx) => {
                    if matches!(tuple.as_ref(), Expr::Var(v) if v == param) {
                        if let Ok(Type::Fun(domain, _)) = infer(function, ctx) {
                            out.push(TypeConstraint::TupleField(*idx, *domain));
                            return;
                        }
                    }
                }
                // infer failed or returned a non-Fun type; fall through to recursive search.
                _ => {}
            }
            collect_constraints_into(param, function, ctx, out);
            collect_constraints_into(param, argument, ctx, out);
        }

        // Don't recurse into a lambda that shadows param.
        Expr::Lambda {
            param: lam_param,
            body,
            ..
        } => {
            if lam_param != param {
                collect_constraints_into(param, body, ctx, out);
            }
        }

        Expr::Let {
            name,
            bound_expr: value,
            body,
            ..
        } => {
            // Always search the value: it is evaluated in the outer scope, so
            // `param` is still in play even if `name == param`.
            collect_constraints_into(param, value, ctx, out);
            // Don't recurse into `body` when `name == param`: the let-binding
            // shadows `param` there, mirroring the Lambda shadowing guard above.
            if name != param {
                collect_constraints_into(param, body, ctx, out);
            }
        }

        Expr::BinOp { left, right, .. } => {
            collect_constraints_into(param, left, ctx, out);
            collect_constraints_into(param, right, ctx, out);
        }

        Expr::UnaryOp(_, inner) => collect_constraints_into(param, inner, ctx, out),

        Expr::TypeAnnotation(inner, _) => collect_constraints_into(param, inner, ctx, out),

        Expr::Tuple(elts) => {
            for elt in elts {
                collect_constraints_into(param, elt, ctx, out);
            }
        }

        // idx is a usize constant, not an expression; nothing to search.
        Expr::TupleIndex(tuple, _) => collect_constraints_into(param, tuple, ctx, out),

        _ => {}
    }
}

/// Reconcile a list of type constraints into a single optional type.
///
/// - Empty list → `Ok(None)` (no constraint found)
/// - All equal → `Ok(Some(ty))` (unique constraint)
/// - Any differ → `Err(TypeMismatch { expected: first, found: other })`
fn reconcile_constraints(constraints: Vec<TypeConstraint>) -> Result<Option<Type>, InferError> {
    let iter = constraints.into_iter();
    let mut base_type: Option<Type> = None;
    let mut tuple_type = HashMap::new();
    for other in iter {
        match other {
            TypeConstraint::Type(ty) => {
                if let Some(base) = &base_type {
                    if *base != ty {
                        return Err(InferError::TypeMismatch {
                            expected: base.clone(),
                            found: ty,
                        });
                    }
                } else {
                    base_type = Some(ty);
                }
            }
            TypeConstraint::TupleField(idx, ty) => {
                let prev = tuple_type.insert(idx, ty.clone());
                if prev.clone().map(|p| p != ty).unwrap_or(false) {
                    return Err(InferError::TypeMismatch {
                        expected: prev.unwrap(),
                        found: ty,
                    });
                }
            }
        }
    }
    if base_type.is_some() {
        Ok(base_type)
    } else if !tuple_type.is_empty() {
        if tuple_type.keys().cloned().max().unwrap_or(0) != tuple_type.len() - 1 {
            return Ok(None);
        }
        Ok(Some(Type::Tuple(
            (0..tuple_type.len())
                .map(|i| tuple_type[&i].clone())
                .collect(),
        )))
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, CompareKind, Expr, Lit, LogicKind, Type,
    };
    use crate::interpreter::BaseType;

    // -----------------------------------------------------------------------
    // Unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_literals() {
        let mut ctx = TypeInferenceContext::new();
        assert_eq!(
            infer(&mut Expr::Lit(Lit::Int(42)), &mut ctx),
            Ok(Type::Base(BaseType::Int))
        );
        assert_eq!(
            infer(&mut Expr::Lit(Lit::String("hello".into())), &mut ctx),
            Ok(Type::Base(BaseType::String))
        );
        assert_eq!(
            infer(&mut Expr::Lit(Lit::Bool(true)), &mut ctx),
            Ok(Type::Base(BaseType::Bool))
        );
        assert_eq!(
            infer(&mut Expr::Lit(Lit::Unit), &mut ctx),
            Ok(Type::Base(BaseType::Unit))
        );
    }

    #[test]
    fn test_infer_annotated_lambda() {
        let mut ctx = TypeInferenceContext::new();
        // λ x : Int → x  =>  Fun(Int, Int)
        let mut expr = Expr::lambda("x", Some(Type::Base(BaseType::Int)), Expr::Var("x".into()));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(
            ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Int))
            )
        );
    }

    #[test]
    fn test_infer_apply_annotates_lambda() {
        let mut ctx = TypeInferenceContext::new();
        // Apply(λ x → x, 42) should annotate x : Int and return Int.
        let mut expr = Expr::apply(
            Expr::Lit(Lit::Int(42)),
            Expr::lambda("x", None, Expr::Var("x".into())),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
        // Verify the lambda was annotated in place.
        if let Expr::Apply { function, .. } = &expr {
            if let Expr::Lambda { param_ty, .. } = function.as_ref() {
                assert_eq!(*param_ty, Some(Type::Base(BaseType::Int)));
            } else {
                panic!("expected Lambda in function position");
            }
        }
    }

    #[test]
    fn test_infer_list() {
        let mut ctx = TypeInferenceContext::new();
        // [10, 20]  =>  Fun(UIntRange(2), Int)
        let mut expr = Expr::List(vec![Expr::Lit(Lit::Int(10)), Expr::Lit(Lit::Int(20))]);
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(
            ty,
            Type::Fun(
                Box::new(Type::UIntRange(2)),
                Box::new(Type::Base(BaseType::Int))
            )
        );
    }

    #[test]
    fn test_infer_list_empty() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::List(vec![]);
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Unknown);
    }

    #[test]
    fn test_infer_unbound_var() {
        let mut ctx = TypeInferenceContext::new();
        let result = infer(&mut Expr::Var("y".into()), &mut ctx);
        assert_eq!(result, Err(InferError::UnboundVariable("y".into())));
    }

    #[test]
    fn test_infer_cannot_infer_param() {
        let mut ctx = TypeInferenceContext::new();
        // λ x → x  — standalone; x is referenced but never used as an Apply argument.
        let mut expr = Expr::lambda("x", None, Expr::Var("x".into()));
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(result, Err(InferError::CannotInferParam("x".into())));
    }

    /// Builds the unannotated list-comp CCL for `[elt for var in source]`.
    ///
    /// Produces:
    /// ```text
    /// λ __list_comp_var (None) →
    ///   Apply(λ var (None) → elt,
    ///         Apply(source, Var(__list_comp_var)))
    /// ```
    fn list_comp_unannotated(source: Expr, var: &str, elt: Expr) -> Expr {
        Expr::lambda(
            "__list_comp_var",
            None,
            Expr::apply(
                Expr::apply(Expr::Var("__list_comp_var".into()), source),
                Expr::lambda(var, None, elt),
            ),
        )
    }

    #[test]
    fn test_infer_outer_lambda_constraint() {
        // [x for x in [10, 20]] — unannotated; infer should annotate both lambdas.
        let mut expr = list_comp_unannotated(
            Expr::List(vec![Expr::Lit(Lit::Int(10)), Expr::Lit(Lit::Int(20))]),
            "x",
            Expr::Var("x".into()),
        );
        let mut ctx = TypeInferenceContext::new();
        infer(&mut expr, &mut ctx).unwrap();

        assert_eq!(
            symbolic(&expr),
            "λ __list_comp_var : [0, 2) → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x)"
        );
    }

    #[test]
    fn test_infer_const_body_comp() {
        // [42 for x in [10, 20]]
        let mut expr = list_comp_unannotated(
            Expr::List(vec![Expr::Lit(Lit::Int(10)), Expr::Lit(Lit::Int(20))]),
            "x",
            Expr::Lit(Lit::Int(42)),
        );
        let mut ctx = TypeInferenceContext::new();
        infer(&mut expr, &mut ctx).unwrap();

        assert_eq!(
            symbolic(&expr),
            "λ __list_comp_var : [0, 2) → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → 42)"
        );
    }

    #[test]
    fn test_infer_binop_body_comp() {
        // [x + 2 for x in [10, 20]]
        let body = Expr::BinOp {
            left: Box::new(Expr::Var("x".into())),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(Expr::Lit(Lit::Int(2))),
        };
        let mut expr = list_comp_unannotated(
            Expr::List(vec![Expr::Lit(Lit::Int(10)), Expr::Lit(Lit::Int(20))]),
            "x",
            body,
        );
        let mut ctx = TypeInferenceContext::new();
        infer(&mut expr, &mut ctx).unwrap();

        assert_eq!(
            symbolic(&expr),
            "λ __list_comp_var : [0, 2) → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x + 2)"
        );
    }

    #[test]
    fn test_infer_nested_comprehension() {
        // [y for y in [x for x in [10, 20]]]
        // Both outer and inner comp lambdas start unannotated.
        let inner_comp = list_comp_unannotated(
            Expr::List(vec![Expr::Lit(Lit::Int(10)), Expr::Lit(Lit::Int(20))]),
            "x",
            Expr::Var("x".into()),
        );
        let mut outer_comp = list_comp_unannotated(inner_comp, "y", Expr::Var("y".into()));
        let mut ctx = TypeInferenceContext::new();
        infer(&mut outer_comp, &mut ctx).unwrap();

        assert_eq!(
            symbolic(&outer_comp),
            "λ __list_comp_var : [0, 2) → __list_comp_var \
             ▷ (λ __list_comp_var : [0, 2) → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x)) \
             ▷ (λ y : Int → y)"
        );
    }

    // -----------------------------------------------------------------------
    // collect_param_constraint: multi-use tests
    // -----------------------------------------------------------------------

    /// Builds `λ x → BinOp(Apply(f, Var(x)), op, Apply(g, Var(x)))` where `f`
    /// and `g` are annotated lambdas with the given param types.
    fn double_apply_lambda(f_param_ty: Type, g_param_ty: Type) -> Expr {
        let f = Expr::lambda("a", Some(f_param_ty), Expr::Var("a".into()));
        let g = Expr::lambda("b", Some(g_param_ty), Expr::Var("b".into()));
        Expr::lambda(
            "x",
            None,
            Expr::BinOp {
                left: Box::new(Expr::apply(Expr::Var("x".into()), f)),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(Expr::apply(Expr::Var("x".into()), g)),
            },
        )
    }

    #[test]
    fn test_collect_multi_same_type() {
        // λ x → Apply(λ a:Int → a, Var(x)) + Apply(λ b:Int → b, Var(x))
        // Both constraints are Int → infers x : Int.
        let mut expr = double_apply_lambda(Type::Base(BaseType::Int), Type::Base(BaseType::Int));
        let mut ctx = TypeInferenceContext::new();
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(
            ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Int))
            )
        );
        // The param_ty was filled in as Int.
        if let Expr::Lambda { param_ty, .. } = &expr {
            assert_eq!(*param_ty, Some(Type::Base(BaseType::Int)));
        } else {
            panic!("expected Lambda");
        }
    }

    #[test]
    fn test_infer_type_annotation_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // (42 : String)  =>  TypeMismatch { expected: String, found: Int }
        let mut expr = Expr::TypeAnnotation(
            Box::new(Expr::Lit(Lit::Int(42))),
            Type::Base(BaseType::String),
        );
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::TypeMismatch {
                expected: Type::Base(BaseType::String),
                found: Type::Base(BaseType::Int),
            })
        );
    }

    #[test]
    fn test_infer_type_annotation_ok() {
        let mut ctx = TypeInferenceContext::new();
        // (42 : Int)  =>  Int
        let mut expr =
            Expr::TypeAnnotation(Box::new(Expr::Lit(Lit::Int(42))), Type::Base(BaseType::Int));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn test_infer_type_annotation_unknown_ignored() {
        let mut ctx = TypeInferenceContext::new();
        // (BinOp : Int)  =>  Int (since BinOp returns Unknown currently)
        let mut expr = Expr::TypeAnnotation(
            Box::new(Expr::BinOp {
                left: Box::new(Expr::Lit(Lit::Int(1))),
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                right: Box::new(Expr::Lit(Lit::Int(2))),
            }),
            Type::Base(BaseType::Int),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn test_infer_let_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // let x : String = 42 in x  =>  TypeMismatch
        let mut expr = Expr::Let {
            name: "x".into(),
            bound_ty: Some(Type::Base(BaseType::String)),
            bound_expr: Box::new(Expr::Lit(Lit::Int(42))),
            body: Box::new(Expr::Var("x".into())),
        };
        let result = infer(&mut expr, &mut ctx);
        // This currently passes or ignores the mismatch in the current code;
        // we want this to eventually fail.
        assert!(
            result.is_err(),
            "Let should catch type mismatch between annotation and value"
        );
    }

    #[test]
    fn test_infer_apply_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // (λ x : String → x)(42)  =>  TypeMismatch
        let mut expr = Expr::Apply {
            function: Box::new(Expr::lambda(
                "x",
                Some(Type::Base(BaseType::String)),
                Expr::Var("x".into()),
            )),
            argument: Box::new(Expr::Lit(Lit::Int(42))),
        };
        let result = infer(&mut expr, &mut ctx);
        assert!(
            result.is_err(),
            "Apply should catch type mismatch between param_ty and argument"
        );
    }

    #[test]
    fn test_lambda_scope_not_leaked_on_error() {
        // λ x : Int → unbound_var
        //
        // Inferring the body fails with UnboundVariable. The scope pushed for
        // the lambda parameter must be popped even on error; otherwise "x"
        // remains visible in `ctx` after the call returns.
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::lambda(
            "x",
            Some(Type::Base(BaseType::Int)),
            Expr::Var("unbound_var".into()),
        );
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::UnboundVariable("unbound_var".into()))
        );
        // The scope stack must be empty: "x" should not be visible.
        assert_eq!(ctx.lookup("x"), None);
    }

    #[test]
    fn test_let_shadowing_no_constraint() {
        // λ x → let x = 42 in Apply(λ b:String → b, Var(x))
        //
        // `let x = 42` shadows the outer lambda param `x`. The outer `x` never
        // appears in an Apply before the shadowing, so no constraint exists for it.
        // The body is skipped (shadowed), so Apply(f_string, Var(x)) — which refers
        // to the *let-bound* x, not the outer param — does not create a false
        // String constraint. Result: CannotInferParam("x").
        let f_string = Expr::lambda(
            "b",
            Some(Type::Base(BaseType::String)),
            Expr::Var("b".into()),
        );
        let mut expr = Expr::lambda(
            "x",
            None,
            Expr::Let {
                name: "x".into(),
                bound_ty: None,
                bound_expr: Box::new(Expr::Lit(Lit::Int(42))),
                body: Box::new(Expr::Apply {
                    function: Box::new(f_string),
                    argument: Box::new(Expr::Var("x".into())),
                }),
            },
        );
        let mut ctx = TypeInferenceContext::new();
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::CannotInferParam("x".into()))
        );
    }

    #[test]
    fn test_collect_multi_conflict() {
        // λ x → Apply(λ a:Int → a, Var(x)) + Apply(λ b:String → b, Var(x))
        // Constraints are [Int, String] → TypeMismatch.
        let mut expr = double_apply_lambda(Type::Base(BaseType::Int), Type::Base(BaseType::String));
        let mut ctx = TypeInferenceContext::new();
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::TypeMismatch {
                expected: Type::Base(BaseType::Int),
                found: Type::Base(BaseType::String),
            })
        );
    }

    // -----------------------------------------------------------------------
    // BinOp return type tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_binop_compare_returns_bool() {
        let mut ctx = TypeInferenceContext::new();
        // 1 < 2  =>  Bool
        let mut expr = Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Int(1))),
            op: BinOpKind::Compare(CompareKind::Less),
            right: Box::new(Expr::Lit(Lit::Int(2))),
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_infer_binop_bool_logic_returns_bool() {
        let mut ctx = TypeInferenceContext::new();
        // True and False  =>  Bool
        let mut expr = Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::Bool(true))),
            op: BinOpKind::BoolLogic(LogicKind::And),
            right: Box::new(Expr::Lit(Lit::Bool(false))),
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_infer_string_add_mutates_to_concat() {
        let mut ctx = TypeInferenceContext::new();
        // "hello" + "world"  =>  String; op mutated to Concat in place
        let mut expr = Expr::BinOp {
            left: Box::new(Expr::Lit(Lit::String("hello".into()))),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(Expr::Lit(Lit::String("world".into()))),
        };
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::String));
        // The op must have been rewritten from Add to Concat.
        if let Expr::BinOp { op, .. } = &expr {
            assert_eq!(
                *op,
                BinOpKind::Concat,
                "expected Add to be rewritten to Concat"
            );
        } else {
            panic!("expected BinOp");
        }
    }

    // -----------------------------------------------------------------------
    // Predicate refinement tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_lambda_with_predicate_refinement() {
        // λ x : Int {λ _ : Int → True} → x
        // The predicate is a standalone annotated lambda; no outer vars needed.
        // Return type must be Fun(Refinement(Int, r), Int).
        let mut ctx = TypeInferenceContext::new();
        let predicate = Expr::lambda(
            "_",
            Some(Type::Base(BaseType::Int)),
            Expr::Lit(Lit::Bool(true)),
        );
        let mut expr = Expr::lambda_with_refinement(
            "x",
            Some(Type::Base(BaseType::Int)),
            Expr::Var("x".into()),
            predicate,
            "test predicate",
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        match ty {
            Type::Fun(domain, codomain) => {
                assert_eq!(*codomain, Type::Base(BaseType::Int));
                match *domain {
                    Type::Refinement(inner, _) => {
                        assert_eq!(*inner, Type::Base(BaseType::Int));
                    }
                    other => panic!("expected Refinement domain, got {other:?}"),
                }
            }
            other => panic!("expected Fun, got {other:?}"),
        }
    }

    #[test]
    fn test_infer_predicate_uses_outer_not_body_scope() {
        // λ x : Int {Var("x")} → x
        // The predicate references `x`. Since the predicate is inferred in the
        // outer scope (after the body's with_scope closes), `x` is NOT bound
        // there, so inference fails with UnboundVariable rather than succeeding
        // by accidentally seeing the body's scope.
        let mut ctx = TypeInferenceContext::new();
        let predicate = Expr::Var("x".into());
        let mut expr = Expr::lambda_with_refinement(
            "x",
            Some(Type::Base(BaseType::Int)),
            Expr::Var("x".into()),
            predicate,
            "outer scope test",
        );
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(result, Err(InferError::UnboundVariable("x".into())));
    }

    // -----------------------------------------------------------------------
    // Aggregate type inference tests
    // -----------------------------------------------------------------------

    /// `Sum` over a list of ints: `sum([1, 2, 3])` → `Int`.
    ///
    /// The input list infers as `Fun(UIntRange(3), Int)`; the codomain is `Int`;
    /// `Sum.output_type(Int)` → `Int`.
    #[test]
    fn test_infer_aggregate_sum_int_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::Aggregate {
            input: Box::new(Expr::List(vec![
                Expr::Lit(Lit::Int(1)),
                Expr::Lit(Lit::Int(2)),
                Expr::Lit(Lit::Int(3)),
            ])),
            kind: AggregateKind::Sum,
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    /// `Max` over a list of ints: `max([10, 20])` → `Int`.
    ///
    /// `Max.output_type` accepts any base type, returning it unchanged.
    #[test]
    fn test_infer_aggregate_max_int_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::Aggregate {
            input: Box::new(Expr::List(vec![
                Expr::Lit(Lit::Int(10)),
                Expr::Lit(Lit::Int(20)),
            ])),
            kind: AggregateKind::Max,
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    /// `Max` over a list of strings: `max(["a", "b"])` → `String`.
    ///
    /// `Max` is defined for any base type; codomain of the list is `String`.
    #[test]
    fn test_infer_aggregate_max_string_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::Aggregate {
            input: Box::new(Expr::List(vec![
                Expr::Lit(Lit::String("a".into())),
                Expr::Lit(Lit::String("b".into())),
            ])),
            kind: AggregateKind::Max,
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::String)));
    }

    /// `Sum` over a list of strings → `Unsupported`.
    ///
    /// `Sum.output_type(String)` returns `None`; the aggregate arm converts
    /// that to `InferError::Unsupported`.
    #[test]
    fn test_infer_aggregate_sum_string_unsupported() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::Aggregate {
            input: Box::new(Expr::List(vec![
                Expr::Lit(Lit::String("x".into())),
                Expr::Lit(Lit::String("y".into())),
            ])),
            kind: AggregateKind::Sum,
        };
        assert!(
            matches!(infer(&mut expr, &mut ctx), Err(InferError::Unsupported(_))),
            "Sum over String should be Unsupported"
        );
    }

    /// `Sum` with a non-function input → `TypeMismatch`.
    ///
    /// The input infers as `Int` (a bare literal), which has no codomain.
    /// The aggregate arm expects a `Fun(_, _)`.
    #[test]
    fn test_infer_aggregate_non_function_input_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::Aggregate {
            input: Box::new(Expr::Lit(Lit::Int(42))),
            kind: AggregateKind::Sum,
        };
        assert!(
            matches!(
                infer(&mut expr, &mut ctx),
                Err(InferError::TypeMismatch { .. })
            ),
            "Aggregate with non-function input should be TypeMismatch"
        );
    }

    /// `Sum` wrapping a list-comprehension lambda: `sum([x for x in [1, 2]])`.
    ///
    /// The unannotated lambda is fully annotated by inference; its type is
    /// `Fun(UIntRange(2), Int)` and the aggregate returns `Int`.
    #[test]
    fn test_infer_aggregate_sum_over_list_comp() {
        let mut ctx = TypeInferenceContext::new();
        // The list-comp CCL: λ __list_comp_var → __list_comp_var ▷ [1, 2] ▷ (λ x → x)
        let comp = list_comp_unannotated(
            Expr::List(vec![Expr::Lit(Lit::Int(1)), Expr::Lit(Lit::Int(2))]),
            "x",
            Expr::Var("x".into()),
        );
        let mut expr = Expr::Aggregate {
            input: Box::new(comp),
            kind: AggregateKind::Sum,
        };
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    // -----------------------------------------------------------------------
    // GroupBy type inference tests
    // -----------------------------------------------------------------------

    /// `groupby` with a list collection: the key lambda's param_ty is annotated
    /// and the result type is `Fun(KeyType, Fun(UInt, ValueType))`.
    #[test]
    fn test_infer_groupby() {
        let mut ctx = TypeInferenceContext::new();
        // groupby([1, 2, 3], lambda x: x)
        // Collection: [1, 2, 3] has type Fun(UIntRange(3), Int).
        // Key lambda (identity): Fun(Int, Int) after annotation.
        // Expected return: Fun(Int, Fun(UInt, Int))
        let mut expr = Expr::GroupBy {
            collection: Box::new(Expr::List(vec![
                Expr::Lit(Lit::Int(1)),
                Expr::Lit(Lit::Int(2)),
                Expr::Lit(Lit::Int(3)),
            ])),
            key: Box::new(Expr::lambda("x", None, Expr::Var("x".into()))),
        };
        let result_ty = infer(&mut expr, &mut ctx).unwrap();
        // Verify param_ty annotation on the key lambda
        if let Expr::GroupBy { key, .. } = &expr {
            if let Expr::Lambda { param_ty, .. } = key.as_ref() {
                assert_eq!(*param_ty, Some(Type::Base(BaseType::Int)));
            } else {
                panic!("expected Lambda for key");
            }
        }
        // Verify return type: Fun(Int, Fun(UInt, Int))
        assert_eq!(
            result_ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Fun(
                    Box::new(Type::Base(BaseType::UInt)),
                    Box::new(Type::Base(BaseType::Int)),
                )),
            )
        );
    }

    /// `[sum(group) for group in groupby([1, 2, 3], lambda x: x)]`
    ///
    /// The list-comp encoding:
    /// ```text
    /// λ __list_comp_var →
    ///   Apply(λ group → sum(group),
    ///         Apply(GroupBy([1,2,3], λ x → x), __list_comp_var))
    /// ```
    ///
    /// - `GroupBy(...)` : `Fun(Int, Fun(UInt, Int))`
    /// - `Apply(groupby, __list_comp_var)` constrains `__list_comp_var : Int`, returns `Fun(UInt, Int)`
    /// - `sum(group)` where `group : Fun(UInt, Int)` → `Int`
    /// - Full result: `Fun(Int, Int)`
    #[test]
    fn test_infer_groupby_aggregate() {
        let mut ctx = TypeInferenceContext::new();
        let groupby_expr = Expr::GroupBy {
            collection: Box::new(Expr::List(vec![
                Expr::Lit(Lit::Int(1)),
                Expr::Lit(Lit::Int(2)),
                Expr::Lit(Lit::Int(3)),
            ])),
            key: Box::new(Expr::lambda("x", None, Expr::Var("x".into()))),
        };
        let mut expr = list_comp_unannotated(
            groupby_expr,
            "group",
            Expr::Aggregate {
                input: Box::new(Expr::Var("group".into())),
                kind: AggregateKind::Sum,
            },
        );
        let result_ty = infer(&mut expr, &mut ctx).unwrap();
        // __list_comp_var iterates over the groupby result's domain (Int);
        // each group is Fun(UInt, Int); sum of that is Int.
        assert_eq!(
            result_ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Int)),
            )
        );
    }

    /// When the collection inference fails, the error propagates and the key is
    /// not visited — `UnboundVariable` from the collection short-circuits inference.
    #[test]
    fn test_infer_groupby_collection_error_propagates() {
        let mut ctx = TypeInferenceContext::new();
        // groupby(xs, lambda x: x) — xs is unbound; collection inference returns
        // UnboundVariable, which propagates before the key is touched.
        let mut expr = Expr::GroupBy {
            collection: Box::new(Expr::Var("xs".into())),
            key: Box::new(Expr::lambda("x", None, Expr::Var("x".into()))),
        };
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::UnboundVariable("xs".into()))
        );
    }

    // -----------------------------------------------------------------------
    // reconcile_constraints / TupleField tests (via collect_param_constraint)
    // -----------------------------------------------------------------------

    #[test]
    fn test_reconcile_tuple_field_gap_returns_cannot_infer() {
        // λ p → f(p._0) + g(p._2)
        // TupleField constraints at indices 0 and 2 — index 1 is missing.
        // reconcile_constraints detects the gap (max 2 != len-1 = 1) → Ok(None)
        // → collect_param_constraint returns None → CannotInferParam("p").
        let f = Expr::lambda("a", Some(Type::Base(BaseType::Int)), Expr::Var("a".into()));
        let g = Expr::lambda("b", Some(Type::Base(BaseType::Bool)), Expr::Var("b".into()));
        let mut expr = Expr::lambda(
            "p",
            None,
            Expr::BinOp {
                left: Box::new(Expr::Apply {
                    function: Box::new(f),
                    argument: Box::new(Expr::TupleIndex(Box::new(Expr::Var("p".into())), 0)),
                }),
                op: BinOpKind::BoolLogic(LogicKind::And),
                right: Box::new(Expr::Apply {
                    function: Box::new(g),
                    argument: Box::new(Expr::TupleIndex(Box::new(Expr::Var("p".into())), 2)),
                }),
            },
        );
        let mut ctx = TypeInferenceContext::new();
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::CannotInferParam("p".into()))
        );
    }

    #[test]
    fn test_reconcile_tuple_field_conflict_returns_mismatch() {
        // λ p → f(p._0) + g(p._0)
        // where f : Int → Int and g : String → String.
        // TupleField constraints at the same index 0 with conflicting types →
        // reconcile_constraints returns TypeMismatch.
        let f = Expr::lambda("a", Some(Type::Base(BaseType::Int)), Expr::Var("a".into()));
        let g = Expr::lambda(
            "b",
            Some(Type::Base(BaseType::String)),
            Expr::Var("b".into()),
        );
        let mut expr = Expr::lambda(
            "p",
            None,
            Expr::BinOp {
                left: Box::new(Expr::Apply {
                    function: Box::new(f),
                    argument: Box::new(Expr::TupleIndex(Box::new(Expr::Var("p".into())), 0)),
                }),
                op: BinOpKind::BoolLogic(LogicKind::And),
                right: Box::new(Expr::Apply {
                    function: Box::new(g),
                    argument: Box::new(Expr::TupleIndex(Box::new(Expr::Var("p".into())), 0)),
                }),
            },
        );
        let mut ctx = TypeInferenceContext::new();
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::TypeMismatch {
                expected: Type::Base(BaseType::Int),
                found: Type::Base(BaseType::String),
            })
        );
    }
}

//! Limited type inference pass for CCL expressions.
//!
//! Sits between lowering (`ccl::lower`) and compilation (`interpreter::compile_ccl`):
//!
//! ```text
//! Python source
//!   → lower (ccl/lower.rs)     — structural, no type reasoning
//!   → infer  (ccl/infer.rs)    — type inference, fills ty on every TypedExpr node
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
//! The pass fills in [`TypedExpr::ty`] on every node it visits. User-written
//! annotations are carried in [`TypedExpr::user_annotation`]; they are checked for
//! compatibility with the inferred type at the end of each [`infer`] call.

use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use log::trace;

use crate::ccl::{BinOpKind, Expr, Lit, RefinementKind, Type, TypedExprNode};
// TODO: once `BaseType` moves to `ccl`, this import goes away.
use crate::interpreter::BaseType;
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// TypeInferenceContext
// ---------------------------------------------------------------------------

/// Context for the CCL type-inference pass.
///
/// Combines a lexical scope stack (for lambda parameters and let bindings)
/// with a registry of externally-registered data-source types.
/// Source types are consulted when [`infer`] encounters an [`Expr::Source`] node.
///
/// Scopes are entered and exited exclusively via [`enter_scope`](TypeInferenceContext::enter_scope);
/// each lambda body and let binding gets its own scope.
#[derive(Default)]
pub struct TypeInferenceContext {
    /// Lexical scopes
    scopes: ScopeStack<Type>,

    /// Types of known sources
    source_types: HashMap<String, Type>,
}

/// RAII guard returned by [`TypeInferenceContext::enter_scope`].
///
/// Pops the innermost lexical scope when dropped, ensuring every
/// `enter_scope` call is paired with a scope exit regardless of how
/// control leaves the enclosing block.
pub struct TypeInferenceContextGuard<'a> {
    ctx: &'a mut TypeInferenceContext,
}

impl<'a> Deref for TypeInferenceContextGuard<'a> {
    type Target = TypeInferenceContext;
    fn deref(&self) -> &TypeInferenceContext {
        self.ctx
    }
}

impl<'a> DerefMut for TypeInferenceContextGuard<'a> {
    fn deref_mut(&mut self) -> &mut TypeInferenceContext {
        self.ctx
    }
}

impl<'a> Drop for TypeInferenceContextGuard<'a> {
    fn drop(&mut self) {
        self.ctx.scopes.pop_scope();
    }
}

impl TypeInferenceContext {
    /// Create a new, empty context with no scopes and no registered sources.
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a fresh lexical scope and return a guard that pops it on drop.
    ///
    /// Use this for every lambda body and let binding to ensure shadowing
    /// is correctly scoped.
    pub fn enter_scope(&mut self) -> TypeInferenceContextGuard<'_> {
        self.scopes.push_scope();
        TypeInferenceContextGuard { ctx: self }
    }

    /// Register the CCL type for an externally-managed data source.
    ///
    /// Typically called by [`crate::ccl::context::GlobalContext`] when a source
    /// is registered; the type is a `Fun(DataSource(name), output_type)`.
    pub fn register_source_type(&mut self, name: &str, ty: Type) {
        self.source_types.insert(name.to_string(), ty);
    }

    /// Look up the CCL type for a registered source by name.
    pub fn source_type(&self, name: &str) -> Option<Type> {
        self.source_types.get(name).cloned()
    }
}

impl Deref for TypeInferenceContext {
    type Target = ScopeStack<Type>;
    fn deref(&self) -> &Self::Target {
        &self.scopes
    }
}

impl DerefMut for TypeInferenceContext {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.scopes
    }
}

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
    /// A user-written annotation on a binding site conflicts with the inferred type.
    ///
    /// Distinct from [`TypeMismatch`] so error messages can say
    /// "you annotated X as T but it has type U" vs. "expected T found U".
    AnnotationMismatch {
        /// The type the user wrote in the annotation.
        annotation: Type,
        /// The type that inference determined.
        inferred: Type,
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
/// in `ty` on every [`TypedExpr`](crate::ccl::TypedExpr) node.
///
/// Currently handled:
///
/// - Literals — type always known from the literal tag
/// - Variables — looked up in the scope stack ([`TypeInferenceContext`])
/// - Annotated lambdas — param type known; recurse into body
/// - `Apply(Lambda(x, Unknown), arg)` — infers arg type, writes it onto `param.ty`
/// - Standalone unannotated lambdas — calls [`collect_param_constraint`] to
///   find a usage-site type constraint for the parameter
/// - Lists — derives `Fun(UIntRange(n), elem_ty)` from the first element
/// - Let bindings — infers value type, stores it in `bound_expr.ty`, binds name in scope
/// - `GroupBy` — infers the collection type; uses its codomain to annotate the
///   key lambda's parameter (mirrors how `Apply` annotates its lambda argument);
///   returns `Fun(KeyType, Fun(UInt, ValueType))`
///
/// Returns [`Type::Unknown`] for unhandled cases or when component types cannot
/// be determined. BinOp type rules and full constraint solving are deferred;
/// see the TODOs throughout this module.
///
/// After computing the result type, checks `expr.user_annotation` compatibility
/// and stores the final type in `expr.ty`.
///
/// Errors propagate from sub-expressions: an [`InferError::UnboundVariable`]
/// anywhere in the tree aborts inference and returns the error.
///
/// The `ctx` scope stack is left at the same depth on return as on entry,
/// even if an error is returned midway.
pub fn infer(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    let result_ty = match &mut expr.node {
        // ----- Literals -----
        TypedExprNode::Lit(lit) => Ok(lit_type(lit)),

        // ----- Variable reference -----
        TypedExprNode::Var(name) => ctx
            .lookup(name)
            .cloned()
            .ok_or_else(|| InferError::UnboundVariable(name.clone())),

        // ----- Lambda abstraction -----
        //
        // If param.ty is Unknown, use collect_param_constraint to find a
        // usage-site type constraint before proceeding.
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            if param.ty == Type::Unknown {
                let constraint = collect_param_constraint(&param.name, body, ctx)?;
                match constraint {
                    Some(inferred) => {
                        // If a user annotation is present, verify it matches.
                        if let Some(ref annotation) = param.user_annotation {
                            if *annotation != inferred {
                                return Err(InferError::AnnotationMismatch {
                                    annotation: annotation.clone(),
                                    inferred,
                                });
                            }
                        }
                        param.ty = inferred;
                    }
                    None => {
                        // Body provides no usable constraint. If the user wrote an annotation,
                        // trust it — the annotation *is* the type (no inference needed to
                        // confirm it). Without an annotation there is no information at all.
                        match param.user_annotation.clone() {
                            Some(annotation) => param.ty = annotation,
                            None => return Err(InferError::CannotInferParam(param.name.clone())),
                        }
                    }
                }
            }
            // param.ty is now known; infer the body in a scope with param bound.
            let mut p = param.ty.clone();
            let param_name = param.name.clone();
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

        TypedExprNode::Aggregate { input, kind } => {
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
        TypedExprNode::Apply { function, argument } => {
            let arg_ty = infer(argument, ctx)?;
            if let TypedExprNode::Lambda { param, .. } = &mut function.node {
                if param.ty == Type::Unknown {
                    // If the function is a lambda with unknown type, infer it from the argument.
                    // If a user annotation is present, verify it matches before accepting arg_ty.
                    if let Some(ref annotation) = param.user_annotation {
                        if *annotation != arg_ty {
                            return Err(InferError::AnnotationMismatch {
                                annotation: annotation.clone(),
                                inferred: arg_ty,
                            });
                        }
                    }
                    param.ty = arg_ty.clone();
                }
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
        TypedExprNode::List(elts) => {
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
        TypedExprNode::BinOp { left, right, op } => {
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
        TypedExprNode::UnaryOp(_, inner) => {
            infer(inner, ctx)?;
            Ok(Type::Unknown)
        }

        // ----- Let binding -----
        //
        // Infer the value type, check any user annotation on the binding site,
        // fill binding.ty, bind the name in a new scope, infer the body, return
        // the body type.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_ty = infer(bound_expr, ctx)?;
            // Check user annotation on the binding site (e.g. `x: Int = expr`)
            // against the inferred expression type.
            if let Some(ref annotation) = binding.user_annotation {
                if *annotation != bound_ty {
                    return Err(InferError::AnnotationMismatch {
                        annotation: annotation.clone(),
                        inferred: bound_ty,
                    });
                }
            }
            if binding.ty == Type::Unknown {
                binding.ty = bound_ty.clone();
            }
            let body_ty = {
                let mut scoped = ctx.enter_scope();
                scoped.bind(&binding.name, bound_ty);
                infer(body, &mut scoped)?
            };
            Ok(body_ty)
        }

        // ----- Case -----
        //
        // Recurse into the scrutinee and arms for mutation side-effects.
        // Pattern variable bindings are not pushed into scope; arms with
        // unbound variables silently produce Unknown rather than aborting.
        TypedExprNode::Case {
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
        TypedExprNode::Tuple(elts) => {
            let types: Result<Vec<Type>, InferError> =
                elts.iter_mut().map(|e| infer(e, ctx)).collect();
            Ok(Type::Tuple(types?))
        }

        // ----- Tuple index -----
        //
        // Infer the tuple expression, then return the element type at the given index.
        // Returns Unknown if the expression is not a known Tuple type or the index is out of bounds.
        TypedExprNode::TupleIndex(tuple, idx) => {
            let ty = infer(tuple, ctx)?;
            let idx = *idx;
            Ok(match ty {
                Type::Tuple(types) => types.into_iter().nth(idx).unwrap_or(Type::Unknown),
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
        TypedExprNode::GroupBy { collection, key } => {
            let coll_ty = infer(collection, ctx)?;
            let elem_ty = coll_ty.codomain();
            if let Some(ref et) = elem_ty {
                if let TypedExprNode::Lambda { param, .. } = &mut key.node {
                    // If the key lambda's param type is unknown, infer it from the collection element type.
                    if param.ty == Type::Unknown {
                        param.ty = et.clone();
                    }
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
        TypedExprNode::Join { .. } | TypedExprNode::Jump { .. } | TypedExprNode::Record(_) => {
            Ok(Type::Unknown)
        }

        // ----- External data source reference -----
        //
        // Look up the source's function type in the source registry.
        // Returns `InferError::UnboundVariable` if the source was not registered
        // before inference was run.
        TypedExprNode::Source(name) => ctx
            .source_type(name)
            .ok_or_else(|| InferError::UnboundVariable(name.clone())),
    }?;

    // Check user_annotation compatibility. If the user provided an explicit annotation,
    // verify it is compatible with the inferred type and use it as the final type.
    //
    // Note: we always infer the full subtree before checking user_annotation.
    // Skipping recursion when an annotation is present would leave sub-node `ty`
    // fields as Unknown and miss lambda-param mutations at Apply/GroupBy sites.
    if let Some(ref annotation) = expr.user_annotation {
        check_type_compatibility(annotation, &result_ty)?;
        expr.ty = annotation.clone();
        return Ok(annotation.clone());
    }

    expr.ty = result_ty.clone();
    Ok(result_ty)
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
    match &mut body.node {
        TypedExprNode::Apply { function, argument } => {
            // If argument is Var(param), the domain of function's type is the constraint.
            match &argument.node {
                TypedExprNode::Var(v) if v == param => {
                    if let Ok(Type::Fun(domain, _)) = infer(function, ctx) {
                        out.push(TypeConstraint::Type(*domain));
                        // Don't recurse: function was already inferred (possibly mutated),
                        // and argument = Var(param) has no sub-patterns to search.
                        return;
                    }
                }
                TypedExprNode::TupleIndex(tuple, idx) => {
                    let idx = *idx;
                    if matches!(&tuple.node, TypedExprNode::Var(v) if v == param) {
                        if let Ok(Type::Fun(domain, _)) = infer(function, ctx) {
                            out.push(TypeConstraint::TupleField(idx, *domain));
                            return;
                        }
                    }
                }
                // infer failed or returned a non-Fun type; fall through to recursive search.
                _ => {}
            }
            // Need to split borrows — collect separately on each child.
            // We can't hold `&mut body.node` while calling collect_constraints_into on parts.
            // So we reborrow here by calling the function with the child nodes directly.
            // The match already extracted function and argument as mutable refs.
            collect_constraints_into(param, function, ctx, out);
            collect_constraints_into(param, argument, ctx, out);
        }

        // Don't recurse into a lambda that shadows param.
        TypedExprNode::Lambda {
            param: lam_param,
            body: lam_body,
            ..
        } => {
            if lam_param.name != param {
                collect_constraints_into(param, lam_body, ctx, out);
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr: value,
            body: let_body,
            ..
        } => {
            // Always search the value: it is evaluated in the outer scope, so
            // `param` is still in play even if `binding.name == param`.
            collect_constraints_into(param, value, ctx, out);
            // Don't recurse into `body` when `binding.name == param`: the let-binding
            // shadows `param` there, mirroring the Lambda shadowing guard above.
            if binding.name != param {
                collect_constraints_into(param, let_body, ctx, out);
            }
        }

        TypedExprNode::BinOp { left, right, .. } => {
            collect_constraints_into(param, left, ctx, out);
            collect_constraints_into(param, right, ctx, out);
        }

        TypedExprNode::UnaryOp(_, inner) => collect_constraints_into(param, inner, ctx, out),

        TypedExprNode::Tuple(elts) => {
            for elt in elts {
                collect_constraints_into(param, elt, ctx, out);
            }
        }

        // idx is a usize constant, not an expression; nothing to search.
        TypedExprNode::TupleIndex(tuple, _) => collect_constraints_into(param, tuple, ctx, out),

        // Leaf nodes with no sub-expressions to search.
        TypedExprNode::Source(_) | TypedExprNode::Lit(_) | TypedExprNode::Var(_) => {}

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
        TypedBinding, TypedExpr, TypedExprNode,
    };
    use crate::interpreter::BaseType;

    // -----------------------------------------------------------------------
    // Unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_literals() {
        let mut ctx = TypeInferenceContext::new();
        assert_eq!(
            infer(&mut Expr::lit(Lit::Int(42)), &mut ctx),
            Ok(Type::Base(BaseType::Int))
        );
        assert_eq!(
            infer(&mut Expr::lit(Lit::String("hello".into())), &mut ctx),
            Ok(Type::Base(BaseType::String))
        );
        assert_eq!(
            infer(&mut Expr::lit(Lit::Bool(true)), &mut ctx),
            Ok(Type::Base(BaseType::Bool))
        );
        assert_eq!(
            infer(&mut Expr::lit(Lit::Unit), &mut ctx),
            Ok(Type::Base(BaseType::Unit))
        );
    }

    #[test]
    fn test_infer_annotated_lambda() {
        let mut ctx = TypeInferenceContext::new();
        // λ x : Int → x  =>  Fun(Int, Int)
        let mut expr = Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("x"));
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
            Expr::lit(Lit::Int(42)),
            Expr::lambda("x", Type::Unknown, Expr::var("x")),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
        // Verify the lambda was annotated in place.
        if let TypedExprNode::Apply { function, .. } = &expr.node {
            if let TypedExprNode::Lambda { param, .. } = &function.node {
                assert_eq!(param.ty, Type::Base(BaseType::Int));
            } else {
                panic!("expected Lambda in function position");
            }
        }
    }

    #[test]
    fn test_infer_list() {
        let mut ctx = TypeInferenceContext::new();
        // [10, 20]  =>  Fun(UIntRange(2), Int)
        let mut expr = Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]);
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
        let mut expr = Expr::list(vec![]);
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Unknown);
    }

    #[test]
    fn test_infer_unbound_var() {
        let mut ctx = TypeInferenceContext::new();
        let result = infer(&mut Expr::var("y"), &mut ctx);
        assert_eq!(result, Err(InferError::UnboundVariable("y".into())));
    }

    #[test]
    fn test_infer_cannot_infer_param() {
        let mut ctx = TypeInferenceContext::new();
        // λ x → x  — standalone; x is referenced but never used as an Apply argument.
        let mut expr = Expr::lambda("x", Type::Unknown, Expr::var("x"));
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(result, Err(InferError::CannotInferParam("x".into())));
    }

    /// Builds the unannotated list-comp CCL for `[elt for var in source]`.
    ///
    /// Produces:
    /// ```text
    /// λ __list_comp_var (Unknown) →
    ///   Apply(λ var (Unknown) → elt,
    ///         Apply(source, Var(__list_comp_var)))
    /// ```
    fn list_comp_unannotated(source: Expr, var: &str, elt: Expr) -> Expr {
        Expr::lambda(
            "__list_comp_var",
            Type::Unknown,
            Expr::apply(
                Expr::apply(Expr::var("__list_comp_var"), source),
                Expr::lambda(var, Type::Unknown, elt),
            ),
        )
    }

    #[test]
    fn test_infer_outer_lambda_constraint() {
        // [x for x in [10, 20]] — unannotated; infer should annotate both lambdas.
        let mut expr = list_comp_unannotated(
            Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]),
            "x",
            Expr::var("x"),
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
            Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]),
            "x",
            Expr::lit(Lit::Int(42)),
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
        let body = Expr::binop(
            Expr::var("x"),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Int(2)),
        );
        let mut expr = list_comp_unannotated(
            Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]),
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
            Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]),
            "x",
            Expr::var("x"),
        );
        let mut outer_comp = list_comp_unannotated(inner_comp, "y", Expr::var("y"));
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
        let f = Expr::lambda("a", f_param_ty, Expr::var("a"));
        let g = Expr::lambda("b", g_param_ty, Expr::var("b"));
        Expr::lambda(
            "x",
            Type::Unknown,
            Expr::binop(
                Expr::apply(Expr::var("x"), f),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::apply(Expr::var("x"), g),
            ),
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
        // The param.ty was filled in as Int.
        if let TypedExprNode::Lambda { param, .. } = &expr.node {
            assert_eq!(param.ty, Type::Base(BaseType::Int));
        } else {
            panic!("expected Lambda");
        }
    }

    #[test]
    fn test_infer_type_annotation_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // (42 : String)  =>  TypeMismatch { expected: String, found: Int }
        let mut expr = Expr::lit(Lit::Int(42)).with_user_annotation(Type::Base(BaseType::String));
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
        let mut expr = Expr::lit(Lit::Int(42)).with_user_annotation(Type::Base(BaseType::Int));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn test_infer_type_annotation_unknown_ignored() {
        let mut ctx = TypeInferenceContext::new();
        // (BinOp : Int)  =>  Int (since BinOp returns Unknown currently)
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Int(2)),
        )
        .with_user_annotation(Type::Base(BaseType::Int));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn test_infer_let_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // let x : String = 42 in x  =>  AnnotationMismatch
        let mut expr = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Unknown,
                user_annotation: Some(Type::Base(BaseType::String)),
            },
            bound_expr: Box::new(Expr::lit(Lit::Int(42))),
            body: Box::new(Expr::var("x")),
        });
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::String),
                inferred: Type::Base(BaseType::Int),
            })
        );
    }

    #[test]
    fn test_infer_apply_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // (λ x : String → x)(42)  =>  TypeMismatch
        let mut expr = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(Expr::lambda(
                "x",
                Type::Base(BaseType::String),
                Expr::var("x"),
            )),
            argument: Box::new(Expr::lit(Lit::Int(42))),
        });
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
        let mut expr = Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("unbound_var"));
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
        let f_string = Expr::lambda("b", Type::Base(BaseType::String), Expr::var("b"));
        let mut expr = Expr::lambda(
            "x",
            Type::Unknown,
            Expr::let_bind(
                "x",
                Expr::lit(Lit::Int(42)),
                TypedExpr::new(TypedExprNode::Apply {
                    function: Box::new(f_string),
                    argument: Box::new(Expr::var("x")),
                }),
            ),
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
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Compare(CompareKind::Less),
            Expr::lit(Lit::Int(2)),
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_infer_binop_bool_logic_returns_bool() {
        let mut ctx = TypeInferenceContext::new();
        // True and False  =>  Bool
        let mut expr = Expr::binop(
            Expr::lit(Lit::Bool(true)),
            BinOpKind::BoolLogic(LogicKind::And),
            Expr::lit(Lit::Bool(false)),
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_infer_string_add_mutates_to_concat() {
        let mut ctx = TypeInferenceContext::new();
        // "hello" + "world"  =>  String; op mutated to Concat in place
        let mut expr = Expr::binop(
            Expr::lit(Lit::String("hello".into())),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::String("world".into())),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::String));
        // The op must have been rewritten from Add to Concat.
        if let TypedExprNode::BinOp { op, .. } = &expr.node {
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
        let predicate = Expr::lambda("_", Type::Base(BaseType::Int), Expr::lit(Lit::Bool(true)));
        let mut expr = Expr::lambda_with_refinement(
            "x",
            Type::Base(BaseType::Int),
            Expr::var("x"),
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
        let predicate = Expr::var("x");
        let mut expr = Expr::lambda_with_refinement(
            "x",
            Type::Base(BaseType::Int),
            Expr::var("x"),
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
        let mut expr = Expr::aggregate(
            Expr::list(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::Int(2)),
                Expr::lit(Lit::Int(3)),
            ]),
            AggregateKind::Sum,
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    /// `Max` over a list of ints: `max([10, 20])` → `Int`.
    ///
    /// `Max.output_type` accepts any base type, returning it unchanged.
    #[test]
    fn test_infer_aggregate_max_int_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::aggregate(
            Expr::list(vec![Expr::lit(Lit::Int(10)), Expr::lit(Lit::Int(20))]),
            AggregateKind::Max,
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    /// `Max` over a list of strings: `max(["a", "b"])` → `String`.
    ///
    /// `Max` is defined for any base type; codomain of the list is `String`.
    #[test]
    fn test_infer_aggregate_max_string_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::aggregate(
            Expr::list(vec![
                Expr::lit(Lit::String("a".into())),
                Expr::lit(Lit::String("b".into())),
            ]),
            AggregateKind::Max,
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::String)));
    }

    /// `Sum` over a list of strings → `Unsupported`.
    ///
    /// `Sum.output_type(String)` returns `None`; the aggregate arm converts
    /// that to `InferError::Unsupported`.
    #[test]
    fn test_infer_aggregate_sum_string_unsupported() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::aggregate(
            Expr::list(vec![
                Expr::lit(Lit::String("x".into())),
                Expr::lit(Lit::String("y".into())),
            ]),
            AggregateKind::Sum,
        );
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
        let mut expr = Expr::aggregate(Expr::lit(Lit::Int(42)), AggregateKind::Sum);
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
            Expr::list(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]),
            "x",
            Expr::var("x"),
        );
        let mut expr = Expr::aggregate(comp, AggregateKind::Sum);
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
        let mut expr = Expr::groupby(
            Expr::list(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::Int(2)),
                Expr::lit(Lit::Int(3)),
            ]),
            Expr::lambda("x", Type::Unknown, Expr::var("x")),
        );
        let result_ty = infer(&mut expr, &mut ctx).unwrap();
        // Verify param.ty annotation on the key lambda
        if let TypedExprNode::GroupBy { key, .. } = &expr.node {
            if let TypedExprNode::Lambda { param, .. } = &key.node {
                assert_eq!(param.ty, Type::Base(BaseType::Int));
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
        let groupby_expr = Expr::groupby(
            Expr::list(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::Int(2)),
                Expr::lit(Lit::Int(3)),
            ]),
            Expr::lambda("x", Type::Unknown, Expr::var("x")),
        );
        let mut expr = list_comp_unannotated(
            groupby_expr,
            "group",
            Expr::aggregate(Expr::var("group"), AggregateKind::Sum),
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
        let mut expr = Expr::groupby(
            Expr::var("xs"),
            Expr::lambda("x", Type::Unknown, Expr::var("x")),
        );
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
        let f = Expr::lambda("a", Type::Base(BaseType::Int), Expr::var("a"));
        let g = Expr::lambda("b", Type::Base(BaseType::Bool), Expr::var("b"));
        let mut expr = Expr::lambda(
            "p",
            Type::Unknown,
            Expr::binop(
                Expr::apply(Expr::tuple_index(Expr::var("p"), 0), f),
                BinOpKind::BoolLogic(LogicKind::And),
                Expr::apply(Expr::tuple_index(Expr::var("p"), 2), g),
            ),
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
        let f = Expr::lambda("a", Type::Base(BaseType::Int), Expr::var("a"));
        let g = Expr::lambda("b", Type::Base(BaseType::String), Expr::var("b"));
        let mut expr = Expr::lambda(
            "p",
            Type::Unknown,
            Expr::binop(
                Expr::apply(Expr::tuple_index(Expr::var("p"), 0), f),
                BinOpKind::BoolLogic(LogicKind::And),
                Expr::apply(Expr::tuple_index(Expr::var("p"), 0), g),
            ),
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

    // -----------------------------------------------------------------------
    // AnnotationMismatch: user_annotation conflicts with inferred type
    // -----------------------------------------------------------------------

    /// Constructs a `Lambda` with `user_annotation: Some(Int)` but a body that
    /// produces `String`. Inference should return `AnnotationMismatch`.
    ///
    /// This path is not yet reachable from the pipeline (lowering always sets
    /// `user_annotation: None`), but the error variant must be exercised
    /// directly so it does not bitrot.
    #[test]
    fn test_infer_annotation_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // λ [x : annotated Int] → Apply(λ s : String → s, x)
        // Constraint from Apply: x must be String, but annotation says Int.
        let inner = Expr::lambda("s", Type::Base(BaseType::String), Expr::var("s"));
        let mut expr = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".to_string(),
                ty: Type::Unknown,
                user_annotation: Some(Type::Base(BaseType::Int)),
            },
            body: Box::new(Expr::apply(Expr::var("x"), inner)),
            refinement: None,
        });
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::Int),
                inferred: Type::Base(BaseType::String),
            })
        );
    }

    // -----------------------------------------------------------------------
    // AnnotationMismatch in Apply position
    // -----------------------------------------------------------------------

    /// `Apply(λ [x : annotated String] → x, 42)` — argument is Int but annotation says String.
    /// The Apply arm must check user_annotation against the argument type.
    #[test]
    fn test_infer_apply_annotation_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(TypedExpr::new(TypedExprNode::Lambda {
                param: TypedBinding {
                    name: "x".to_string(),
                    ty: Type::Unknown,
                    user_annotation: Some(Type::Base(BaseType::String)),
                },
                body: Box::new(Expr::var("x")),
                refinement: None,
            })),
            argument: Box::new(Expr::lit(Lit::Int(42))),
        });
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::String),
                inferred: Type::Base(BaseType::Int),
            })
        );
    }

    // -----------------------------------------------------------------------
    // user_annotation used as fallback when body provides no constraint
    // -----------------------------------------------------------------------

    /// `λ [x : annotated Int] → unit` — body does not reference x, so
    /// `collect_param_constraint` returns `None`. The annotation must be
    /// accepted as the param type rather than returning `CannotInferParam`.
    #[test]
    fn test_infer_annotation_used_when_no_body_constraint() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".to_string(),
                ty: Type::Unknown,
                user_annotation: Some(Type::Base(BaseType::Int)),
            },
            body: Box::new(Expr::lit(Lit::Unit)),
            refinement: None,
        });
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(
            ty,
            Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Unit))
            )
        );
        if let TypedExprNode::Lambda { param, .. } = &expr.node {
            assert_eq!(param.ty, Type::Base(BaseType::Int));
        }
    }

    // -----------------------------------------------------------------------
    // Source inference tests
    // -----------------------------------------------------------------------

    /// A registered `Expr::Source` infers to the type it was registered with.
    #[test]
    fn test_infer_source_returns_registered_type() {
        let mut ctx = TypeInferenceContext::new();
        let source_ty = Type::Fun(
            Box::new(Type::DataSource("mystream".into())),
            Box::new(Type::Base(BaseType::String)),
        );
        ctx.register_source_type("mystream", source_ty.clone());
        let mut expr = Expr::new(TypedExprNode::Source("mystream".into()));
        assert_eq!(infer(&mut expr, &mut ctx), Ok(source_ty));
    }

    /// An `Expr::Source` whose name was never registered produces `UnboundVariable`.
    #[test]
    fn test_infer_source_unregistered_is_unbound() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::new(TypedExprNode::Source("ghost".into()));
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::UnboundVariable("ghost".into()))
        );
    }

    /// Multiple distinct sources can coexist in the registry and each resolves
    /// to its own type independently.
    #[test]
    fn test_infer_multiple_sources_resolve_independently() {
        let mut ctx = TypeInferenceContext::new();
        let int_ty = Type::Fun(
            Box::new(Type::DataSource("ints".into())),
            Box::new(Type::Base(BaseType::Int)),
        );
        let str_ty = Type::Fun(
            Box::new(Type::DataSource("strs".into())),
            Box::new(Type::Base(BaseType::String)),
        );
        ctx.register_source_type("ints", int_ty.clone());
        ctx.register_source_type("strs", str_ty.clone());

        let mut e1 = Expr::new(TypedExprNode::Source("ints".into()));
        let mut e2 = Expr::new(TypedExprNode::Source("strs".into()));
        assert_eq!(infer(&mut e1, &mut ctx), Ok(int_ty));
        assert_eq!(infer(&mut e2, &mut ctx), Ok(str_ty));
    }
}

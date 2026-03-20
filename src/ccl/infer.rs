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

use crate::ccl::{
    fresh_infer_var_id, unify::UnificationTable, BinOpKind, Expr, InferVarId, Lit, RefinementKind,
    Type, TypedExprNode,
};
// TODO: once `BaseType` moves to `ccl`, this import goes away.
use crate::interpreter::BaseType;
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// TypeInferenceContext
// ---------------------------------------------------------------------------

/// Context for the CCL type-inference pass.
///
/// Combines a lexical scope stack (for lambda parameters and let bindings),
/// a registry of externally-registered data-source types, and a
/// [`UnificationTable`] that tracks solved and unified inference variables.
///
/// Scopes are entered and exited exclusively via [`enter_scope`](TypeInferenceContext::enter_scope);
/// each lambda body and let binding gets its own scope.
#[derive(Default)]
pub struct TypeInferenceContext {
    /// Lexical scopes mapping variable names to their types.
    scopes: ScopeStack<Type>,

    /// Types of known externally-registered data sources.
    source_types: HashMap<String, Type>,

    /// Union-Find table tracking solved and unified inference variables.
    ///
    /// Every inference variable allocated via [`fresh_infer_var`](Self::fresh_infer_var) is
    /// registered here. The post-inference [`resolve`](crate::ccl::unify::resolve)
    /// pass uses it to replace `Infer(id)` placeholders with concrete types.
    pub table: UnificationTable,
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

    /// Allocate a fresh inference variable, register it in the [`UnificationTable`],
    /// and return its ID.
    ///
    /// Use this instead of calling [`fresh_infer_var_id`] directly whenever you need
    /// a new variable during inference — the table entry is required for the
    /// post-inference resolution pass.
    pub fn fresh_infer_var(&mut self) -> InferVarId {
        let id = fresh_infer_var_id();
        self.table.register(id);
        id
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

    /// Constrain two types to be equal, recording the solution in the [`UnificationTable`].
    ///
    /// - Both `Infer`: union the two variables.
    /// - One `Infer`, one concrete: set the variable to the concrete type.
    /// - Both concrete and equal: no-op.
    /// - Both concrete and different: returns [`InferError::TypeMismatch`].
    fn constrain_equal(&mut self, a: &Type, b: &Type) -> Result<(), InferError> {
        match (a, b) {
            (Type::Infer(a_id), Type::Infer(b_id)) => {
                self.table
                    .unify(*a_id, *b_id)
                    .map_err(|(type_a, type_b)| InferError::TypeMismatch { type_a, type_b })?;
                Ok(())
            }
            (Type::Infer(id), concrete) | (concrete, Type::Infer(id)) => {
                // Ensure this is a actually a concrete type: guards against case reordering.
                debug_assert!(!matches!(concrete, Type::Infer(_)));
                self.table.set(*id, concrete.clone());
                Ok(())
            }
            (a, b) if a == b => Ok(()),
            (type_a, type_b) => Err(InferError::TypeMismatch {
                type_a: type_a.clone(),
                type_b: type_b.clone(),
            }),
        }
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
    /// A type mismatch was detected between two solved types.
    TypeMismatch { type_a: Type, type_b: Type },
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

/// Run type inference on `expr`, then resolve all inference variables.
///
/// Public entry point for the CCL type-inference pass. Calls [`infer_expr`]
/// to annotate every node, then calls [`crate::ccl::unify::resolve`] to
/// substitute solved inference-variable placeholders with their concrete types.
///
/// After this call returns `Ok`, the tree is fully annotated and contains no
/// `Type::Hole` or (ideally) `Type::Infer` placeholders.
pub fn infer(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    infer_expr(expr, ctx)?;
    crate::ccl::unify::resolve(expr, &mut ctx.table);
    // Return the type from expr.ty (post-resolve) rather than the pre-resolve return value
    // from infer_expr: the two can differ when infer_expr returns an Infer var that
    // constrain_equal subsequently solved (e.g. the left operand of a BinOp).
    Ok(expr.ty.clone())
}

/// Walk `expr` and fill in `ty` on every node. Does not call `resolve`.
///
/// Currently handled:
///
/// - Literals — type always known from the literal tag
/// - Variables — looked up in the scope stack ([`TypeInferenceContext`])
/// - Annotated lambdas — param type known; recurse into body
/// - `Apply(Lambda(x, Infer), arg)` — infers arg type, writes it onto `param.ty`
/// - Standalone unannotated lambdas — calls [`collect_param_constraint`] to
///   find a usage-site type constraint for the parameter
/// - Lists — derives `Fun(UIntRange(n), elem_ty)` from the first element
/// - Let bindings — infers value type, stores it in `bound_expr.ty`, binds name in scope
/// - `GroupBy` — infers the collection type; uses its codomain to annotate the
///   key lambda's parameter (mirrors how `Apply` annotates its lambda argument);
///   returns `Fun(KeyType, Fun(UInt, ValueType))`
///
/// Returns a fresh [`Type::Infer`] variable for unhandled cases or when component
/// types cannot be determined. BinOp type rules and full constraint solving are
/// deferred; see the TODOs throughout this module.
///
/// Errors propagate from sub-expressions: an [`InferError::UnboundVariable`]
/// anywhere in the tree aborts inference and returns the error.
fn infer_expr(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    // Register a fresh inference variable now so the table entry exists for the
    // solution recording step at the bottom of this function. If we skipped
    // this, the table would have no id to record the solution against and
    // resolve() would be unable to substitute the type back into the tree.
    if matches!(expr.ty, Type::Hole) {
        expr.ty = Type::Infer(ctx.fresh_infer_var());
    }

    let result_ty = match &mut expr.node {
        // ----- Literals -----
        TypedExprNode::Lit(lit) => Ok(lit_type(lit)),

        // ----- Variable reference -----
        TypedExprNode::Var(name) => ctx
            .lookup(name)
            .cloned()
            .ok_or_else(|| InferError::UnboundVariable(name.clone())),

        // ----- Lambda abstraction -----
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => infer_lambda(param, body, refinement, ctx),

        // ----- Aggregation -----
        TypedExprNode::Aggregate { input, kind } => {
            let input_type = infer_expr(input, ctx)?;
            let input_codomain = input_type
                .codomain()
                .ok_or_else(|| InferError::TypeMismatch {
                    type_a: Type::Fun(
                        Box::new(Type::Infer(ctx.fresh_infer_var())),
                        Box::new(Type::Infer(ctx.fresh_infer_var())),
                    ),
                    type_b: input_type,
                })?;
            kind.output_type(&input_codomain).ok_or_else(|| {
                InferError::Unsupported(format!("Cannot apply {kind:?} to {input_codomain}"))
            })
        }

        // ----- Function application -----
        TypedExprNode::Apply { function, argument } => infer_apply(function, argument, ctx),

        // ----- List literal -----
        TypedExprNode::List(elts) => infer_list(elts, ctx),

        // ----- Binary operation -----
        TypedExprNode::BinOp { left, right, op } => infer_binop(left, op, right, ctx),

        // ----- Unary operation -----
        //
        // Recurse into the operand for mutation side-effects.
        // TODO: add unary type rules.
        TypedExprNode::UnaryOp(_, inner) => {
            infer_expr(inner, ctx)?;
            Ok(Type::Infer(ctx.fresh_infer_var()))
        }

        // ----- Let binding -----
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => infer_let(binding, bound_expr, body, ctx),

        // ----- Case -----
        //
        // Recurse into the scrutinee and arms for mutation side-effects.
        // Pattern variable bindings are not pushed into scope; arms with
        // unbound variables silently produce Infer rather than aborting.
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            infer_expr(scrutinee, ctx)?;
            for (_, arm) in branches.iter_mut() {
                let _ = infer_expr(arm, ctx);
            }
            Ok(Type::Infer(ctx.fresh_infer_var()))
        }

        // ----- Tuple constructor -----
        //
        // Infer each element in order and return their types as a Tuple type.
        TypedExprNode::Tuple(elts) => {
            let types: Result<Vec<Type>, InferError> =
                elts.iter_mut().map(|e| infer_expr(e, ctx)).collect();
            Ok(Type::Tuple(types?))
        }

        // ----- Tuple index -----
        //
        // Infer the tuple expression, then return the element type at the given index.
        // Returns Unknown if the expression is not a known Tuple type or the index is out of bounds.
        TypedExprNode::TupleIndex(tuple, idx) => {
            let ty = infer_expr(tuple, ctx)?;
            let idx = *idx;
            Ok(match ty {
                Type::Tuple(types) => types
                    .into_iter()
                    .nth(idx)
                    .unwrap_or_else(|| Type::Infer(ctx.fresh_infer_var())),
                _ => Type::Infer(ctx.fresh_infer_var()),
            })
        }

        // ----- GroupBy -----
        TypedExprNode::GroupBy { collection, key } => infer_groupby(collection, key, ctx),

        // ----- Join / Jump / Record -----
        //
        // Not yet handled by this pass; sub-expressions are not visited.
        TypedExprNode::Join { .. } | TypedExprNode::Jump { .. } | TypedExprNode::Record(_) => {
            Ok(Type::Infer(ctx.fresh_infer_var()))
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
    // fields as Infer and miss lambda-param mutations at Apply/GroupBy sites.
    if let Some(ref annotation) = expr.user_annotation {
        ctx.constrain_equal(annotation, &result_ty)?;
        // Record the solution in the table if this node started with an Infer var.
        if let Type::Infer(id) = expr.ty {
            ctx.table.set(id, annotation.clone());
        }
        expr.ty = annotation.clone();
        return Ok(annotation.clone());
    }

    // Record the solved type in the unification table so the post-inference
    // resolution pass can substitute Infer placeholders in the tree.
    if let Type::Infer(id) = expr.ty {
        if !matches!(result_ty, Type::Infer(_)) {
            ctx.table.set(id, result_ty.clone());
        }
    }

    expr.ty = result_ty.clone();
    Ok(result_ty)
}

// ---------------------------------------------------------------------------
// Non-trivial match-arm helpers
// ---------------------------------------------------------------------------

/// Infer the type of a [`TypedExprNode::Lambda`] node.
///
/// Resolves the parameter type (either from a user annotation, a call-site
/// constraint collected by [`collect_param_constraint`], or a `Hole → Infer`
/// conversion), then infers the body type inside a fresh scope.
fn infer_lambda(
    param: &mut crate::ccl::TypedBinding,
    body: &mut Expr,
    refinement: &mut Option<crate::ccl::Refinement>,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    // Normalize Hole → fresh registered Infer before existing param-type logic.
    if matches!(param.ty, Type::Hole) {
        param.ty = Type::Infer(ctx.fresh_infer_var());
    }
    if matches!(param.ty, Type::Infer(_)) {
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
                match &param.user_annotation {
                    Some(annotation) => param.ty = annotation.clone(),
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
        infer_expr(body, &mut scoped)?
    };
    // Predicate is inferred in the outer scope (param not in scope).
    // This reflects that the refinement predicate is a constraint on the
    // *call site*, not an expression in the lambda body.
    if let Some(refinement) = refinement {
        if let RefinementKind::Predicate(def) = &refinement.kind {
            infer_expr(&mut def.borrow_mut(), ctx)?;
        }
        p = Type::Refinement(Box::new(p), refinement.clone())
    }
    Ok(Type::Fun(Box::new(p), Box::new(body_ty)))
}

/// Infer the type of a [`TypedExprNode::Apply`] node.
///
/// If the function is an unannotated lambda, annotates its parameter type from
/// the argument, then infers the function type and returns its codomain.
fn infer_apply(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    let arg_ty = infer_expr(argument, ctx)?;
    if let TypedExprNode::Lambda { param, .. } = &mut function.node {
        // Normalize Hole → fresh registered Infer before existing param-type logic.
        if matches!(param.ty, Type::Hole) {
            param.ty = Type::Infer(ctx.fresh_infer_var());
        }
        if matches!(param.ty, Type::Infer(_)) {
            // If the function is a lambda with unresolved type, infer it from the argument.
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
    match infer_expr(function, ctx)? {
        Type::Fun(domain, codomain) => {
            ctx.constrain_equal(&domain, &arg_ty)?;
            Ok(*codomain)
        }
        _ => Ok(Type::Infer(ctx.fresh_infer_var())),
    }
}

/// Infer the type of a [`TypedExprNode::Let`] node.
///
/// Infers the bound expression type, checks any user annotation on the binding
/// site, fills `binding.ty`, then infers the body in a fresh scope.
fn infer_let(
    binding: &mut crate::ccl::TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    let bound_ty = infer_expr(bound_expr, ctx)?;
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
    // Normalize Hole → fresh registered Infer before existing binding-type logic.
    if matches!(binding.ty, Type::Hole) {
        binding.ty = Type::Infer(ctx.fresh_infer_var());
    }
    // Move bound_ty into binding.ty when unresolved, avoiding a clone.
    // The scope bind then clones from binding.ty instead of from bound_ty.
    if matches!(binding.ty, Type::Infer(_)) {
        binding.ty = bound_ty;
    }
    let body_ty = {
        let mut scoped = ctx.enter_scope();
        scoped.bind(&binding.name, binding.ty.clone());
        infer_expr(body, &mut scoped)?
    };
    Ok(body_ty)
}

/// Infer the type of a [`TypedExprNode::List`] node.
///
/// Returns `Fun(UIntRange(n), elem_ty)` where `elem_ty` is derived from the
/// first element. Returns a fresh inference variable for empty lists or when
/// the first element's type is itself an unresolved inference variable.
fn infer_list(elts: &mut [Expr], ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    let Some(first) = elts.first_mut() else {
        return Ok(Type::Infer(ctx.fresh_infer_var()));
    };
    let elem_ty = match infer_expr(first, ctx)? {
        Type::Infer(_) => return Ok(Type::Infer(ctx.fresh_infer_var())),
        ty => ty,
    };
    // Visit remaining elements to eliminate Type::Hole placeholders and
    // propagate type information through sub-expressions. The list element
    // type is still derived from the first element only (all elements are
    // assumed homogeneous); errors from remaining elements are silently
    // dropped because the type has already been determined.
    for rest in elts.iter_mut().skip(1) {
        let _ = infer_expr(rest, ctx);
    }
    let n = elts.len();
    Ok(Type::Fun(Box::new(Type::UIntRange(n)), Box::new(elem_ty)))
}

/// Infer the type of a [`TypedExprNode::BinOp`] node.
/// Infer both operands then apply the operation's type rules via the
/// UnificationTable.  String + String → Concat rewriting is deferred to
/// compile time; this pass only propagates the type constraint.
fn infer_binop(
    left: &mut Expr,
    op: &mut BinOpKind,
    right: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    let left_ty = infer_expr(left, ctx)?;
    let right_ty = infer_expr(right, ctx)?;
    match op {
        BinOpKind::Arithmetic(_) => {
            // Both operands must have the same type; the result is that type.
            ctx.constrain_equal(&left_ty, &right_ty)?;
            Ok(left_ty)
        }
        BinOpKind::Concat => {
            // Explicit concat: both sides must be String.
            ctx.constrain_equal(&left_ty, &Type::Base(BaseType::String))?;
            ctx.constrain_equal(&right_ty, &Type::Base(BaseType::String))?;
            Ok(Type::Base(BaseType::String))
        }
        BinOpKind::Compare(_) => {
            // Operands must agree; result is Bool.
            ctx.constrain_equal(&left_ty, &right_ty)?;
            Ok(Type::Base(BaseType::Bool))
        }
        BinOpKind::BoolLogic(_) => {
            // Both operands must be Bool; result is Bool.
            ctx.constrain_equal(&left_ty, &Type::Base(BaseType::Bool))?;
            ctx.constrain_equal(&right_ty, &Type::Base(BaseType::Bool))?;
            Ok(Type::Base(BaseType::Bool))
        }
    }
}

/// Infer the type of a [`TypedExprNode::GroupBy`] node.
///
/// Infers the collection type, propagates the element type onto the key
/// lambda's parameter (mirroring the `Apply` rule), then returns
/// `Fun(KeyType, Fun(UInt, ValueType))`.
fn infer_groupby(
    collection: &mut Expr,
    key: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    let coll_ty = infer_expr(collection, ctx)?;
    let elem_ty = coll_ty.codomain();
    if let Some(ref et) = elem_ty {
        if let TypedExprNode::Lambda { param, .. } = &mut key.node {
            // Normalize Hole → fresh registered Infer before existing param-type logic.
            if matches!(param.ty, Type::Hole) {
                param.ty = Type::Infer(ctx.fresh_infer_var());
            }
            // If the key lambda's param type is unresolved, infer it from the collection element type.
            if matches!(param.ty, Type::Infer(_)) {
                param.ty = et.clone();
            }
        }
    }
    let key_fn_ty = infer_expr(key, ctx)?;
    let key_output_ty = key_fn_ty.codomain();
    match (key_output_ty, elem_ty) {
        (Some(k), Some(v)) => Ok(Type::Fun(
            Box::new(k),
            Box::new(Type::Fun(Box::new(Type::Base(BaseType::UInt)), Box::new(v))),
        )),
        _ => Ok(Type::Infer(ctx.fresh_infer_var())),
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

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
    // Log before consuming constraints so we avoid cloning the Vec for the trace.
    trace!("Collected constraints for {param}: {constraints:?}");
    let result = reconcile_constraints(constraints);
    trace!("Reconciled to {result:?}");
    result
}

/// Accumulate every type constraint for `param` found in `body` into `out`.
///
/// For each `Apply(func, Var(param))` encountered, calls [`infer_expr`] on
/// `func` and, if the result is a `Fun` type, pushes its domain onto `out`.
/// Does not short-circuit: all matching sites in the entire subtree are visited.
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
                    if let Ok(Type::Fun(domain, _)) = infer_expr(function, ctx) {
                        out.push(TypeConstraint::Type(*domain));
                        // Don't recurse: function was already inferred (possibly mutated),
                        // and argument = Var(param) has no sub-patterns to search.
                        return;
                    }
                }
                TypedExprNode::TupleIndex(tuple, idx) => {
                    let idx = *idx;
                    if matches!(&tuple.node, TypedExprNode::Var(v) if v == param) {
                        if let Ok(Type::Fun(domain, _)) = infer_expr(function, ctx) {
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
/// - Any differ → `Err(TypeMismatch { type_a: first, type_b: other })`
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
                            type_a: base.clone(),
                            type_b: ty,
                        });
                    }
                } else {
                    base_type = Some(ty);
                }
            }
            TypeConstraint::TupleField(idx, ty) => {
                let prev = tuple_type.insert(idx, ty.clone());
                if prev.as_ref().is_some_and(|p| p != &ty) {
                    return Err(InferError::TypeMismatch {
                        type_a: prev.unwrap(),
                        type_b: ty,
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
            Expr::lambda("x", Type::infer(), Expr::var("x")),
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
        assert!(
            matches!(ty, Type::Infer(_)),
            "empty list should return an inference variable"
        );
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
        let mut expr = Expr::lambda("x", Type::infer(), Expr::var("x"));
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(result, Err(InferError::CannotInferParam("x".into())));
    }

    /// Builds the unannotated list-comp CCL for `[elt for var in source]`.
    ///
    /// Produces:
    /// ```text
    /// λ __list_comp_var (?N) →
    ///   Apply(λ var (?M) → elt,
    ///         Apply(source, Var(__list_comp_var)))
    /// ```
    fn list_comp_unannotated(source: Expr, var: &str, elt: Expr) -> Expr {
        Expr::lambda(
            "__list_comp_var",
            Type::infer(),
            Expr::apply(
                Expr::apply(Expr::var("__list_comp_var"), source),
                Expr::lambda(var, Type::infer(), elt),
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
            Type::infer(),
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
        // (42 : String)  =>  TypeMismatch { type_a: String, type_b: Int }
        let mut expr = Expr::lit(Lit::Int(42)).with_user_annotation(Type::Base(BaseType::String));
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(
            result,
            Err(InferError::TypeMismatch {
                type_a: Type::Base(BaseType::String),
                type_b: Type::Base(BaseType::Int),
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
    fn test_infer_type_annotation_overrides_inferred() {
        let mut ctx = TypeInferenceContext::new();
        // (1 + 2 : Int)  =>  Int; annotation matches inferred type, accepted as-is.
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
                ty: Type::infer(),
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
            Type::infer(),
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
                type_a: Type::Base(BaseType::Int),
                type_b: Type::Base(BaseType::String),
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
    fn test_infer_string_add_infers_string() {
        let mut ctx = TypeInferenceContext::new();
        // "hello" + "world"  =>  String; Add is left as-is (Concat rewriting
        // happens at compile time, not inference time).
        let mut expr = Expr::binop(
            Expr::lit(Lit::String("hello".into())),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::String("world".into())),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::String));
        // The op is NOT rewritten at inference time.
        if let TypedExprNode::BinOp { op, .. } = &expr.node {
            assert_eq!(*op, BinOpKind::Arithmetic(ArithmeticKind::Add));
        } else {
            panic!("expected BinOp");
        }
    }

    // -----------------------------------------------------------------------
    // BinOp constraint propagation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_binop_int_add() {
        let mut ctx = TypeInferenceContext::new();
        // Int + Int → Int, left and right constrained equal.
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Int(2)),
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_binop_type_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // Int + Bool → TypeMismatch.
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Bool(true)),
        );
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(InferError::TypeMismatch {
                type_a: Type::Base(BaseType::Int),
                type_b: Type::Base(BaseType::Bool),
            })
        );
    }

    #[test]
    fn test_binop_constraint_propagation() {
        let mut ctx = TypeInferenceContext::new();
        // constrain_equal(Infer(id), Int) should solve the variable in the table.
        let fresh_id = ctx.fresh_infer_var();
        ctx.constrain_equal(&Type::Infer(fresh_id), &Type::Base(BaseType::Int))
            .unwrap();
        assert_eq!(ctx.table.probe(fresh_id), Some(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_binop_compare_bool_result() {
        let mut ctx = TypeInferenceContext::new();
        // 1 < 2 → Bool.
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Compare(CompareKind::Less),
            Expr::lit(Lit::Int(2)),
        );
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    /// Verify that `infer_binop` propagates type constraints to `Infer`-typed operands
    /// via [`TypeInferenceContext::constrain_equal`].
    ///
    /// A variable bound to a fresh `Infer` var in scope should be solved to `Int` after
    /// being used as the left operand of `x + 1`. This would fail if `infer_binop` never
    /// called `constrain_equal` — for example, if it was reverted to the pre-BinOp-rules
    /// stub. It also verifies that `infer()` returns the post-`resolve()` type from
    /// `expr.ty` rather than the pre-resolve return value of `infer_expr` (which would
    /// be `Infer(A)` since `constrain_equal` solves the variable in the table without
    /// updating the local binding).
    #[test]
    fn test_binop_constrains_infer_operand() {
        let mut ctx = TypeInferenceContext::new();
        let infer_id = ctx.fresh_infer_var();
        // Enter a scope so we can bind "x" to a fresh Infer type.
        let result_ty = {
            let mut scoped = ctx.enter_scope();
            scoped.bind("x", Type::Infer(infer_id));
            let mut expr = Expr::binop(
                Expr::var("x"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::lit(Lit::Int(1)),
            );
            infer(&mut expr, &mut scoped).unwrap()
        };
        // infer() must return the resolved type (Int), not the pre-resolve Infer var.
        assert_eq!(result_ty, Type::Base(BaseType::Int));
        // constrain_equal must have recorded Int as the solution for the Infer var.
        assert_eq!(ctx.table.probe(infer_id), Some(Type::Base(BaseType::Int)));
    }

    /// Verify that type information propagates inward through nested `BinOp` nodes.
    ///
    /// `(x + y) + (1 : Int)` — the outer `+` constrains its result to `Int`,
    /// which flows inward: `constrain_equal(Infer(id_x), Int)` solves `id_x`,
    /// and because the inner `+` had already unified `id_x` with `id_y` via
    /// `constrain_equal(Infer(id_x), Infer(id_y))`, `id_y` is also solved.
    #[test]
    fn test_binop_downward_propagation() {
        let mut ctx = TypeInferenceContext::new();
        let id_x = ctx.fresh_infer_var();
        let id_y = ctx.fresh_infer_var();
        let result_ty = {
            let mut scoped = ctx.enter_scope();
            scoped.bind("x", Type::Infer(id_x));
            scoped.bind("y", Type::Infer(id_y));
            let inner = Expr::binop(
                Expr::var("x"),
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::var("y"),
            );
            let mut outer = Expr::binop(
                inner,
                BinOpKind::Arithmetic(ArithmeticKind::Add),
                Expr::lit(Lit::Int(1)),
            );
            infer(&mut outer, &mut scoped).unwrap()
        };
        assert_eq!(result_ty, Type::Base(BaseType::Int));
        assert_eq!(ctx.table.probe(id_x), Some(Type::Base(BaseType::Int)));
        assert_eq!(ctx.table.probe(id_y), Some(Type::Base(BaseType::Int)));
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
            Expr::lambda("x", Type::infer(), Expr::var("x")),
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
            Expr::lambda("x", Type::infer(), Expr::var("x")),
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
            Expr::lambda("x", Type::infer(), Expr::var("x")),
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
            Type::infer(),
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
            Type::infer(),
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
                type_a: Type::Base(BaseType::Int),
                type_b: Type::Base(BaseType::String),
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
                ty: Type::infer(),
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
                    ty: Type::infer(),
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
                ty: Type::infer(),
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

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

use crate::ccl::symbolic::{symbolic, symbolic_typed};
use crate::ccl::BaseType;
use crate::ccl::{
    unify::UnificationTable, BinOpKind, Branch, Expr, InferVarId, Lit, ProjKey, RefinementKind,
    Type, TypedExprNode, UnaryOpKind,
};
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
        self.table.fresh_var()
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
    fn constrain_equal(&mut self, a: &Type, b: &Type) -> Result<(), InferError> {
        self.table.constrain_equal(a, b)
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
#[derive(Clone, PartialEq)]
pub enum InferError {
    /// A variable was referenced but not bound in the current scope.
    UnboundVariable(String),
    /// A lambda's parameter type could not be inferred from its body, any
    /// call-site constraints, or a user annotation. Emitted post-resolve by
    /// [`check_fully_typed`] when a `Type::Infer` remains in a param position.
    CannotInferParam(String),
    /// A type mismatch was detected between two solved types.
    TypeMismatch {
        type_a: Type,
        type_b: Type,
        ctx: String,
    },
    /// A [`Type::Fun`] was required — e.g. in a function-application or
    /// [`TypedExprNode::Compose`] position — but a non-function type was found.
    ///
    /// The inner [`Type`] is the actual type of the offending expression.
    ExpectedFunction(Type),
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
    /// A [`crate::ccl::TypedExprNode::Case`] with no branches was encountered.
    ///
    /// Lowering never produces a 0-branch `Case`; this indicates a malformed
    /// AST constructed outside the normal lowering path.
    EmptyCase,
    /// A [`Type::Hole`] placeholder survived past inference.
    /// The `String` is the symbolic representation of the offending expression.
    UnresolvedHole(String),
    /// An unresolved [`Type::Infer`] variable survived past resolution.
    /// The `String` is the symbolic representation of the offending expression.
    UnresolvedInfer(InferVarId, String),
}

impl std::fmt::Debug for InferError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferError::UnboundVariable(name) => write!(f, "Unbound variable: '{}'", name),
            InferError::CannotInferParam(name) => {
                write!(f, "Cannot infer type for parameter: '{}'", name)
            }
            InferError::TypeMismatch {
                ctx,
                type_a,
                type_b,
            } => {
                write!(
                    f,
                    "Type mismatch for {}: expected {}, found {}",
                    ctx, type_a, type_b
                )
            }
            InferError::ExpectedFunction(ty) => {
                write!(f, "Expected function type, found {}", ty)
            }
            InferError::AnnotationMismatch {
                annotation,
                inferred,
            } => {
                write!(
                    f,
                    "Annotation mismatch: annotated as {}, but inferred as {}",
                    annotation, inferred
                )
            }
            InferError::Unsupported(msg) => write!(f, "Unsupported: {}", msg),
            InferError::EmptyCase => write!(f, "Case expression must have at least one branch"),
            InferError::UnresolvedHole(sym) => {
                write!(f, "Unresolved type hole in expression: {}", sym)
            }
            InferError::UnresolvedInfer(id, sym) => {
                write!(
                    f,
                    "Unresolved inference variable {} in expression: {}",
                    id, sym
                )
            }
        }
    }
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
pub fn infer(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, Vec<InferError>> {
    infer_expr(expr, ctx).map_err(|e| vec![e])?;
    crate::ccl::unify::resolve(expr, &mut ctx.table);
    check_fully_typed(expr)?;
    // Return the type from expr.ty (post-resolve) rather than the pre-resolve return value
    // from infer_expr: the two can differ when infer_expr returns an Infer var that
    // constrain_equal subsequently solved (e.g. the left operand of a BinOp).
    Ok(expr.ty.clone())
}

/// Check that every [`crate::ccl::TypedExpr::ty`] and [`crate::ccl::TypedBinding::ty`]
/// in the tree is a fully concrete type — no [`Type::Hole`] or [`Type::Infer`] anywhere,
/// including nested inside compound types like `Fun` or `Tuple` and inside refinements.
///
/// Returns `Ok(())` if the tree is fully annotated, or all holes and unresolved
/// inference variables found in a depth-first walk.
///
/// TODO fold this into [`typecheck`]
pub fn check_fully_typed(expr: &Expr) -> Result<(), Vec<InferError>> {
    let mut errors = Vec::new();
    collect_expr_errors(expr, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Recursively collect all type errors from `expr` into `errors`.
fn collect_expr_errors(expr: &Expr, errors: &mut Vec<InferError>) {
    collect_type_errors(&expr.ty, &symbolic(expr), errors);
    match &expr.node {
        TypedExprNode::Lit(_) | TypedExprNode::Var(_) => {}
        TypedExprNode::Apply { function, argument } => {
            collect_expr_errors(function, errors);
            collect_expr_errors(argument, errors);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            collect_expr_errors(left, errors);
            collect_expr_errors(right, errors);
        }
        TypedExprNode::UnaryOp(_, operand) => {
            collect_expr_errors(operand, errors);
        }
        TypedExprNode::Lambda { param, body, .. } => {
            if type_has_infer(&param.ty) {
                // TODO: A future "errored table" tracking covered Infer IDs could suppress
                // derivative UnresolvedInfer errors for this ID in expr.ty and body uses
                // of this param.
                errors.push(InferError::CannotInferParam(param.name.clone()));
            } else {
                collect_type_errors(&param.ty, &param.name, errors);
            }
            collect_expr_errors(body, errors);
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_type_errors(&binding.ty, &binding.name, errors);
            collect_expr_errors(bound_expr, errors);
            collect_expr_errors(body, errors);
        }
        TypedExprNode::Tuple(elems) => {
            for elem in elems {
                collect_expr_errors(elem, errors);
            }
        }
        TypedExprNode::Record(fields) => {
            for (_, val) in fields {
                collect_expr_errors(val, errors);
            }
        }
        TypedExprNode::List(elems) => {
            for elem in elems {
                collect_expr_errors(elem, errors);
            }
        }
        TypedExprNode::Proj(_) => {}
        TypedExprNode::Case { branches } => {
            for branch in branches {
                collect_expr_errors(&branch.guard, errors);
                collect_expr_errors(&branch.body, errors);
            }
        }
        TypedExprNode::GroupBy { collection, key } => {
            collect_expr_errors(collection, errors);
            collect_expr_errors(key, errors);
        }
        TypedExprNode::Aggregate { input, .. } => {
            collect_expr_errors(input, errors);
        }
        TypedExprNode::Join {
            params,
            loop_body,
            outer_body,
            ..
        } => {
            for p in params {
                collect_type_errors(&p.ty, &p.name, errors);
            }
            collect_expr_errors(loop_body, errors);
            collect_expr_errors(outer_body, errors);
        }
        TypedExprNode::Jump { args, .. } => {
            for arg in args {
                collect_expr_errors(arg, errors);
            }
        }
        TypedExprNode::Source(_) => {}
        TypedExprNode::Compose(morphisms) => {
            for m in morphisms {
                collect_expr_errors(m, errors);
            }
        }
    }
}

/// Collect all holes and unresolved inference variables in `ty` into `errors`.
///
/// `context_sym` is the symbolic representation of the expression whose type
/// is being checked, used as the context string in any error pushed.
fn collect_type_errors(ty: &Type, context_sym: &str, errors: &mut Vec<InferError>) {
    match ty {
        Type::Hole => errors.push(InferError::UnresolvedHole(context_sym.to_string())),
        Type::Infer(id) => errors.push(InferError::UnresolvedInfer(*id, context_sym.to_string())),
        Type::Fun(domain, codomain) => {
            collect_type_errors(domain, context_sym, errors);
            collect_type_errors(codomain, context_sym, errors);
        }
        Type::Tuple(elems) => {
            for elem in elems {
                collect_type_errors(elem, context_sym, errors);
            }
        }
        Type::Record(fields) => {
            for (_, ty) in fields {
                collect_type_errors(ty, context_sym, errors);
            }
        }
        Type::Union(variants) => {
            for variant in variants {
                collect_type_errors(variant, context_sym, errors);
            }
        }
        Type::Refinement(inner, refinement) => {
            if let RefinementKind::Predicate(def) = &refinement.kind {
                collect_expr_errors(&def.borrow(), errors);
            }
            collect_type_errors(inner, context_sym, errors);
        }
        Type::PartialTuple(entries) => {
            for (_, ty) in entries {
                collect_type_errors(ty, context_sym, errors);
            }
        }
        Type::PartialRecord(entries) => {
            for (_, ty) in entries {
                collect_type_errors(ty, context_sym, errors);
            }
        }
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) => {}
    }
}

/// Check that the types in a fully-annotated expression tree are semantically
/// consistent.
///
/// Valid on both the lambda-bearing form produced by inference and the
/// lambda-free form produced by [`crate::ccl::lambda_elim`] and
/// [`crate::ccl::simplify`]. After lambda elimination, [`TypedExprNode::BinOp`]
/// and [`TypedExprNode::UnaryOp`] nodes are desugared away, so those rules
/// become vacuously satisfied; the rules for [`TypedExprNode::Apply`],
/// [`TypedExprNode::Compose`], [`TypedExprNode::Tuple`], and
/// [`TypedExprNode::Proj`] carry the full semantic load.
///
/// Recursively inspects every node and verifies that its annotated [`Type`]
/// is consistent with its sub-expression types and with the type rules of
/// the expression.
///
/// Assumes [`check_fully_typed`] has already passed (no [`Type::Hole`] or
/// [`Type::Infer`] placeholders remain). Returns `Ok(())` if no errors are
/// found, or all discovered errors as `Err(errs)`.
pub fn typecheck(expr: &Expr) -> Result<(), Vec<InferError>> {
    let mut errors = Vec::new();
    collect_typecheck_errors(expr, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// In debug mode only, typecheck the expression and panic if any errors are found.
pub fn debug_typecheck(expr: &Expr) {
    debug_assert_eq!(
        typecheck(expr),
        Ok(()),
        "Failed to typecheck result: {}",
        symbolic_typed(expr)
    );
}

// Helper to run typechecking inline when building an Expr
pub fn dbg_typecheck_mv(expr: Expr) -> Expr {
    debug_typecheck(&expr);
    expr
}

/// Recursively collect semantic type errors from `expr` into `errors`.
fn collect_typecheck_errors(expr: &Expr, errors: &mut Vec<InferError>) {
    match &expr.node {
        // Literal: node type must match the concrete base type of the literal.
        TypedExprNode::Lit(lit) => {
            let expected = lit_type(lit);
            if expr.ty != expected {
                errors.push(InferError::TypeMismatch {
                    ctx: symbolic(expr),
                    type_a: expected,
                    type_b: expr.ty.clone(),
                });
            }
        }

        // Variable references are resolved by the scope at inference time.
        TypedExprNode::Var(_) => {}

        TypedExprNode::BinOp { left, op, right } => {
            collect_typecheck_errors(left, errors);
            collect_typecheck_errors(right, errors);
            check_binop_types(&expr.ty, left, op, right, errors);
        }

        TypedExprNode::UnaryOp(op, inner) => {
            collect_typecheck_errors(inner, errors);
            check_unaryop_types(&expr.ty, op, inner, errors);
        }

        TypedExprNode::Apply { function, argument } => {
            collect_typecheck_errors(function, errors);
            collect_typecheck_errors(argument, errors);
            match &function.ty {
                Type::Fun(domain, codomain) => {
                    if !typecheck_equal(&argument.ty, domain) {
                        errors.push(InferError::TypeMismatch {
                            ctx: format!("domain of {}", symbolic(expr)),
                            type_a: (**domain).clone(),
                            type_b: argument.ty.clone(),
                        });
                    }
                    if !typecheck_equal(&expr.ty, codomain) {
                        errors.push(InferError::TypeMismatch {
                            ctx: format!("codomain of {}", symbolic(expr)),
                            type_a: (**codomain).clone(),
                            type_b: expr.ty.clone(),
                        });
                    }
                }
                _ => errors.push(InferError::ExpectedFunction(function.ty.clone())),
            }
        }

        TypedExprNode::Lambda { body, .. } => {
            collect_typecheck_errors(body, errors);
            // Node type must be Fun; its codomain must match the body type.
            // The domain may be a Refinement-wrapped version of param.ty — we
            // do not recheck that here; the inference pass already validates it.
            match &expr.ty {
                Type::Fun(_, codomain) => {
                    if !typecheck_equal(codomain, &body.ty) {
                        errors.push(InferError::TypeMismatch {
                            ctx: symbolic(body),
                            type_a: body.ty.clone(),
                            type_b: (**codomain).clone(),
                        });
                    }
                }
                _ => errors.push(InferError::ExpectedFunction(expr.ty.clone())),
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_typecheck_errors(bound_expr, errors);
            collect_typecheck_errors(body, errors);
            if !typecheck_equal(&binding.ty, &bound_expr.ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: symbolic(bound_expr),
                    type_a: binding.ty.clone(),
                    type_b: bound_expr.ty.clone(),
                });
            }
            if !typecheck_equal(&expr.ty, &body.ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: symbolic(body),
                    type_a: body.ty.clone(),
                    type_b: expr.ty.clone(),
                });
            }
        }

        TypedExprNode::Case { branches } => {
            let bool_ty = Type::Base(BaseType::Bool);
            for Branch { guard, body } in branches {
                collect_typecheck_errors(guard, errors);
                collect_typecheck_errors(body, errors);
                if !typecheck_equal(&guard.ty, &bool_ty) {
                    errors.push(InferError::TypeMismatch {
                        ctx: symbolic(expr),
                        type_a: bool_ty.clone(),
                        type_b: guard.ty.clone(),
                    });
                }
                if !typecheck_equal(&body.ty, &expr.ty) {
                    errors.push(InferError::TypeMismatch {
                        ctx: symbolic(expr),
                        type_a: expr.ty.clone(),
                        type_b: body.ty.clone(),
                    });
                }
            }
        }

        TypedExprNode::List(elts) => {
            for elt in elts.iter() {
                collect_typecheck_errors(elt, errors);
            }
            check_list_types(&expr.ty, elts, errors);
        }

        TypedExprNode::Tuple(elts) => {
            for elt in elts.iter() {
                collect_typecheck_errors(elt, errors);
            }
            let elem_tys: Vec<Type> = elts.iter().map(|e| e.ty.clone()).collect();
            let expected = Type::Tuple(elem_tys);
            if !typecheck_equal(&expr.ty, &expected) {
                errors.push(InferError::TypeMismatch {
                    ctx: symbolic(expr),
                    type_a: expected,
                    type_b: expr.ty.clone(),
                });
            }
        }

        TypedExprNode::Record(fields) => {
            for (_, val) in fields.iter() {
                collect_typecheck_errors(val, errors);
            }
            let field_tys: Vec<(String, Type)> = fields
                .iter()
                .map(|(n, e)| (n.clone(), e.ty.clone()))
                .collect();
            let expected = Type::Record(field_tys);
            if !typecheck_equal(&expr.ty, &expected) {
                errors.push(InferError::TypeMismatch {
                    ctx: symbolic(expr),
                    type_a: expected,
                    type_b: expr.ty.clone(),
                });
            }
        }

        // First-class projection morphisms: shape is determined by inference.
        TypedExprNode::Proj(_) => {}

        TypedExprNode::GroupBy { collection, key } => {
            collect_typecheck_errors(collection, errors);
            collect_typecheck_errors(key, errors);
            if !matches!(collection.ty, Type::Fun(..)) {
                errors.push(InferError::ExpectedFunction(collection.ty.clone()));
            }
            if !matches!(key.ty, Type::Fun(..)) {
                errors.push(InferError::ExpectedFunction(key.ty.clone()));
            }
        }

        TypedExprNode::Aggregate { input, .. } => {
            collect_typecheck_errors(input, errors);
            if !matches!(input.ty, Type::Fun(..)) {
                errors.push(InferError::ExpectedFunction(input.ty.clone()));
            }
        }

        // Join and Jump are not yet fully handled by inference; skip detailed checks.
        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => {
            collect_typecheck_errors(loop_body, errors);
            collect_typecheck_errors(outer_body, errors);
        }

        TypedExprNode::Jump { args, .. } => {
            for arg in args.iter() {
                collect_typecheck_errors(arg, errors);
            }
        }

        TypedExprNode::Source(_) => {}

        TypedExprNode::Compose(morphisms) => {
            for m in morphisms.iter() {
                collect_typecheck_errors(m, errors);
            }
            check_compose_types(&expr.ty, morphisms, errors);
        }
    }
}

// Checks if two types should be considered equal for the purposes of typechecking.
// Currently treats refinements as transparent
fn typecheck_equal(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Refinement(a, _), b) => typecheck_equal(a, b),
        (a, Type::Refinement(b, _)) => typecheck_equal(a, b),
        (Type::Fun(a_domain, a_codomain), Type::Fun(b_domain, b_codomain)) => {
            typecheck_equal(a_domain, b_domain) && typecheck_equal(a_codomain, b_codomain)
        }
        _ => a == b,
    }
}

/// Check [`BinOpKind`] type rules for a single binary-op node and push any
/// errors into `errors`.
///
/// Note: [`BinOpKind::Arithmetic`] permits non-numeric operands because
/// `String + String` is a valid pre-compile-time intermediate form that is
/// rewritten to [`BinOpKind::Concat`] by the compiler.
fn check_binop_types(
    node_ty: &Type,
    left: &Expr,
    op: &BinOpKind,
    right: &Expr,
    errors: &mut Vec<InferError>,
) {
    match op {
        BinOpKind::Arithmetic(_) => {
            // Operands must agree with each other.
            if !typecheck_equal(&left.ty, &right.ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                    type_a: left.ty.clone(),
                    type_b: right.ty.clone(),
                });
            }
            // Node type must match the operand type.
            if !typecheck_equal(node_ty, &left.ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                    type_a: left.ty.clone(),
                    type_b: node_ty.clone(),
                });
            }
        }
        BinOpKind::Concat => {
            let string_ty = Type::Base(BaseType::String);
            for ty in [&left.ty, &right.ty, node_ty] {
                if !typecheck_equal(ty, &string_ty) {
                    errors.push(InferError::TypeMismatch {
                        ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                        type_a: string_ty.clone(),
                        type_b: ty.clone(),
                    });
                }
            }
        }
        BinOpKind::Compare(_) => {
            // Operands must agree; result must be Bool.
            if !typecheck_equal(&left.ty, &right.ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                    type_a: left.ty.clone(),
                    type_b: right.ty.clone(),
                });
            }
            let bool_ty = Type::Base(BaseType::Bool);
            if !typecheck_equal(node_ty, &bool_ty) {
                errors.push(InferError::TypeMismatch {
                    ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                    type_a: bool_ty,
                    type_b: node_ty.clone(),
                });
            }
        }
        BinOpKind::BoolLogic(_) => {
            // All three (left operand, right operand, result) must be Bool.
            let bool_ty = Type::Base(BaseType::Bool);
            for ty in [&left.ty, &right.ty, node_ty] {
                if !typecheck_equal(ty, &bool_ty) {
                    errors.push(InferError::TypeMismatch {
                        ctx: format!("{} {} {}", symbolic(left), op.sym(), symbolic(right)),
                        type_a: bool_ty.clone(),
                        type_b: ty.clone(),
                    });
                }
            }
        }
    }
}

/// Check [`UnaryOpKind`] type rules for a single unary-op node and push any
/// errors into `errors`.
fn check_unaryop_types(
    node_ty: &Type,
    op: &UnaryOpKind,
    inner: &Expr,
    errors: &mut Vec<InferError>,
) {
    let expected = match op {
        UnaryOpKind::Neg => Type::Base(BaseType::Int),
        UnaryOpKind::Not => Type::Base(BaseType::Bool),
    };
    if !typecheck_equal(&inner.ty, &expected) {
        errors.push(InferError::TypeMismatch {
            ctx: format!("{:?} {}", op, symbolic(inner)),
            type_a: expected.clone(),
            type_b: inner.ty.clone(),
        });
    }
    if !typecheck_equal(node_ty, &expected) {
        errors.push(InferError::TypeMismatch {
            ctx: format!("{:?} {}", op, symbolic(inner)),
            type_a: expected,
            type_b: node_ty.clone(),
        });
    }
}

/// Check [`TypedExprNode::List`] type rules and push any errors into `errors`.
///
/// Verifies that all elements share the same type (inference silently drops
/// errors for elements after the first) and that the node type is
/// `Fun(UIntRange(n), elem_ty)`.
fn check_list_types(node_ty: &Type, elts: &[Expr], errors: &mut Vec<InferError>) {
    let Some(first) = elts.first() else {
        return;
    };
    let elem_ty = &first.ty;
    // All elements must share the type of the first element.
    for elt in elts.iter().skip(1) {
        if !typecheck_equal(&elt.ty, elem_ty) {
            errors.push(InferError::TypeMismatch {
                ctx: symbolic(elt),
                type_a: elem_ty.clone(),
                type_b: elt.ty.clone(),
            });
        }
    }
    // Node type must be Fun(UIntRange(n), elem_ty).
    let expected = Type::Fun(
        Box::new(Type::UIntRange(elts.len())),
        Box::new(elem_ty.clone()),
    );
    if !typecheck_equal(node_ty, &expected) {
        errors.push(InferError::TypeMismatch {
            ctx: "list".to_string(),
            type_a: expected,
            type_b: node_ty.clone(),
        });
    }
}

/// Check [`TypedExprNode::Compose`] type rules and push any errors into `errors`.
///
/// Every morphism must be a [`Type::Fun`]; adjacent pairs must have compatible
/// codomain/domain; the overall node type must be `Fun(first_domain, last_codomain)`.
fn check_compose_types(node_ty: &Type, morphisms: &[Expr], errors: &mut Vec<InferError>) {
    // Collect (domain, codomain) pairs, emitting ExpectedFunction for non-Fun morphisms.
    let mut fun_tys: Vec<Option<(Type, Type)>> = Vec::with_capacity(morphisms.len());
    for m in morphisms {
        match &m.ty {
            Type::Fun(d, c) => fun_tys.push(Some(((**d).clone(), (**c).clone()))),
            _ => {
                errors.push(InferError::ExpectedFunction(m.ty.clone()));
                fun_tys.push(None);
            }
        }
    }
    // Adjacent codomain/domain must agree.
    for i in 0..fun_tys.len().saturating_sub(1) {
        if let (Some((_, prev_cod)), Some((next_dom, _))) = (&fun_tys[i], &fun_tys[i + 1]) {
            if !typecheck_equal(prev_cod, next_dom) {
                errors.push(InferError::TypeMismatch {
                    ctx: format!(
                        "{} ≫ {}",
                        symbolic(&morphisms[i]),
                        symbolic(&morphisms[i + 1])
                    ),
                    type_a: prev_cod.clone(),
                    type_b: next_dom.clone(),
                });
            }
        }
    }
    // Overall node type must be Fun(first_domain, last_codomain).
    if let (Some(first), Some(last)) = (fun_tys.first(), fun_tys.last()) {
        if let (Some((first_dom, _)), Some((_, last_cod))) = (first, last) {
            let expected = Type::Fun(Box::new(first_dom.clone()), Box::new(last_cod.clone()));
            if !typecheck_equal(node_ty, &expected) {
                errors.push(InferError::TypeMismatch {
                    ctx: "compose".to_string(),
                    type_a: expected,
                    type_b: node_ty.clone(),
                });
            }
        }
    }
}

/// Walk `expr` and fill in `ty` on every node. Does not call `resolve`.
///
/// Currently handled:
///
/// - Literals — type always known from the literal tag
/// - Variables — looked up in the scope stack ([`TypeInferenceContext`])
/// - Annotated lambdas — param type known; recurse into body
/// - `Apply(Lambda(x, Infer), arg)` — infers arg type, writes it onto `param.ty`
/// - Standalone unannotated lambdas — binds param as an inference variable and
///   lets body inference constrain it at each usage site via the unification table
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
            let kind = kind.clone();
            let input_type = infer_expr(input, ctx)?;
            let input_codomain = input_type
                .codomain()
                .ok_or_else(|| InferError::TypeMismatch {
                    ctx: symbolic(expr),
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
        TypedExprNode::UnaryOp(op, inner) => {
            let inner_ty = infer_expr(inner, ctx)?;
            match op {
                UnaryOpKind::Neg => {
                    // Operand must be Int; result is Int.
                    ctx.constrain_equal(&inner_ty, &Type::Base(BaseType::Int))?;
                    Ok(Type::Base(BaseType::Int))
                }
                UnaryOpKind::Not => {
                    // Operand must be Bool; result is Bool.
                    ctx.constrain_equal(&inner_ty, &Type::Base(BaseType::Bool))?;
                    Ok(Type::Base(BaseType::Bool))
                }
            }
        }

        // ----- Let binding -----
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => infer_let(binding, bound_expr, body, ctx),

        // ----- Case -----
        //
        // For each branch: constrain the guard to Bool, infer the arm body type,
        // and unify all arm types via `constrain_equal`.
        //
        // Returns the unified arm type, or `InferError::EmptyCase` for 0-branch `Case`.
        TypedExprNode::Case { branches } => infer_case(branches, ctx),

        // ----- Tuple constructor -----
        //
        // Infer each element in order and return their types as a Tuple type.
        TypedExprNode::Tuple(elts) => {
            let types: Result<Vec<Type>, InferError> =
                elts.iter_mut().map(|e| infer_expr(e, ctx)).collect();
            Ok(Type::Tuple(types?))
        }

        // ----- Proj -----
        //
        // First-class projection morphism. A bare `Proj(Index(n))` gets type
        // `PartialTuple({n => ?a}) ⇒ ?a`; a bare `Proj(Field("x"))` gets type
        // `PartialRecord({x => ?a}) ⇒ ?a`.  These partial domain types unify
        // correctly with any concrete `Tuple`/`Record` during application.
        TypedExprNode::Proj(key) => {
            let domain_infer = Type::Infer(ctx.fresh_infer_var());
            let field_ty = Type::Infer(ctx.fresh_infer_var());
            let domain_ty = match key {
                ProjKey::Index(idx) => Type::PartialTuple(vec![(*idx, field_ty.clone())]),
                ProjKey::Field(name) => Type::PartialRecord(vec![(name.clone(), field_ty.clone())]),
            };
            ctx.constrain_equal(&domain_infer, &domain_ty)?;
            Ok(Type::fun(domain_infer, field_ty))
        }

        // ----- GroupBy -----
        TypedExprNode::GroupBy { collection, key } => infer_groupby(collection, key, ctx),

        // ----- Join / Jump -----
        //
        // Not yet handled by this pass; sub-expressions are not visited.
        TypedExprNode::Join { .. } | TypedExprNode::Jump { .. } => {
            Ok(Type::Infer(ctx.fresh_infer_var()))
        }

        // ----- Record constructor -----
        //
        // Infer each field expression and collect the field name–type pairs
        // into a `Type::Record`. This mirrors `Tuple` inference but preserves
        // field names.
        TypedExprNode::Record(fields) => {
            let field_types: Result<Vec<(String, Type)>, InferError> = fields
                .iter_mut()
                .map(|(name, expr)| Ok((name.clone(), infer_expr(expr, ctx)?)))
                .collect();
            Ok(Type::Record(field_types?))
        }

        // ----- External data source reference -----
        //
        // Look up the source's function type in the source registry.
        // Returns `InferError::UnboundVariable` if the source was not registered
        // before inference was run.
        TypedExprNode::Source(name) => ctx
            .source_type(name)
            .ok_or_else(|| InferError::UnboundVariable(name.clone())),

        // ----- N-ary compose -----
        //
        // Produced by simplify after type inference; should not appear here in
        // normal compilation. Infer the type chain: each morphism's codomain
        // must equal the next morphism's domain; the result is `domain(f₀) →
        // codomain(fₙ₋₁)`.
        TypedExprNode::Compose(elts) => infer_compose(elts, ctx),
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

/// Replace every [`Type::Hole`] in `ty` (recursively) with a fresh inference
/// variable, assigning one stable [`Type::Infer`] ID per structural position.
///
/// Any existing [`Type::Infer`] IDs are registered in the table if not already
/// present. This handles IDs created outside inference (e.g. via the
/// [`Type::infer`] test helper) so they participate in unification correctly.
fn replace_holes(ty: &mut Type, ctx: &mut TypeInferenceContext) {
    match ty {
        Type::Hole => *ty = Type::Infer(ctx.fresh_infer_var()),
        Type::Infer(id) => ctx.table.register(*id),
        Type::Fun(domain, codomain) => {
            replace_holes(domain, ctx);
            replace_holes(codomain, ctx);
        }
        Type::Tuple(elems) => elems.iter_mut().for_each(|t| replace_holes(t, ctx)),
        Type::Record(fields) => fields.iter_mut().for_each(|(_, t)| replace_holes(t, ctx)),
        Type::Union(variants) => variants.iter_mut().for_each(|t| replace_holes(t, ctx)),
        Type::Refinement(inner, _) => replace_holes(inner, ctx),
        Type::PartialTuple(entries) => entries.iter_mut().for_each(|(_, t)| replace_holes(t, ctx)),
        Type::PartialRecord(entries) => entries.iter_mut().for_each(|(_, t)| replace_holes(t, ctx)),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) => {}
    }
}

/// Return `true` if `ty` contains any [`Type::Infer`] node.
///
/// Used post-[`crate::ccl::unify::resolve`], where every solved inference
/// variable has already been substituted, so any remaining [`Type::Infer`] is
/// genuinely unresolved.
fn type_has_infer(ty: &Type) -> bool {
    match ty {
        Type::Infer(_) => true,
        Type::Fun(a, b) => type_has_infer(a) || type_has_infer(b),
        Type::Tuple(elems) => elems.iter().any(type_has_infer),
        Type::Record(fields) => fields.iter().any(|(_, t)| type_has_infer(t)),
        Type::Union(variants) => variants.iter().any(type_has_infer),
        Type::PartialTuple(entries) => entries.iter().any(|(_, t)| type_has_infer(t)),
        Type::PartialRecord(entries) => entries.iter().any(|(_, t)| type_has_infer(t)),
        Type::Refinement(inner, _) => type_has_infer(inner),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole => false,
    }
}

/// Infer the type of a [`TypedExprNode::Lambda`] node.
///
/// If the parameter type is unknown (`Hole` or `Infer`), it is left as an
/// inference variable and bound in scope. Body inference then constrains the
/// variable naturally at every usage site via the unification table.
///
/// After body inference, for a top-level `Infer` param:
/// - If body constrained the var and a user annotation is present, the annotation
///   is verified against the inferred type; a conflict returns
///   [`InferError::AnnotationMismatch`] rather than a raw [`InferError::TypeMismatch`].
/// - If no body constraint exists and an annotation is present, the annotation
///   is accepted as the param type.
/// - If neither body constraint nor annotation exists, `param.ty` is left as
///   `Infer(id)`. The constraint may still arrive from the call site or an
///   expression-level annotation. After full unification and
///   [`crate::ccl::unify::resolve`], any remaining unresolved param is caught
///   by [`check_fully_typed`], which emits [`InferError::CannotInferParam`].
///
/// Structured param types (e.g. `Tuple`) may contain a mix of resolved and
/// unresolved positions; unresolved positions are likewise deferred to
/// [`check_fully_typed`].
fn infer_lambda(
    param: &mut crate::ccl::TypedBinding,
    body: &mut Expr,
    refinement: &mut Option<crate::ccl::Refinement>,
    ctx: &mut TypeInferenceContext,
) -> Result<Type, InferError> {
    // Assign a stable Infer ID to every Hole in the param type before binding it
    // in scope. This must be a pre-pass rather than minting variables on-the-fly:
    // `param.ty` is cloned into the scope once and looked up once per usage site.
    // Replacing Holes at lookup time would give each usage a distinct Infer ID,
    // so constraints from different usage sites would never unify.
    // Annotation application is deferred to after body inference so that body
    // constraints are collected first and can be validated against the annotation.
    replace_holes(&mut param.ty, ctx);
    // Infer the body in a fresh scope with the param bound. All usage sites
    // constrain param.ty via the unification table automatically — no pre-scan needed.
    let param_name = param.name.clone();
    let body_ty = {
        let mut scoped = ctx.enter_scope();
        scoped.bind(&param_name, param.ty.clone());
        collect_constraints(&param_name, &param.ty, body, &mut scoped)?;
        infer_expr(body, &mut scoped)?
    };
    // Post-inference: for a bare Infer param, validate the annotation against body
    // constraints (or use it as a fallback when the body provides none). For
    // structured params, check recursively for any unresolved positions.
    if let Type::Infer(id) = param.ty {
        let probed = ctx.table.probe(id);
        let ann = param.user_annotation.clone();
        match (probed, ann) {
            (Some(inferred), Some(ann)) => {
                // Body constrained the param; verify the user annotation agrees.
                ctx.constrain_equal(&ann, &inferred).map_err(|_| {
                    InferError::AnnotationMismatch {
                        annotation: ann.clone(),
                        inferred: inferred.clone(),
                    }
                })?;
                param.ty = ann;
            }
            (Some(_), None) => {} // resolved by body; no annotation to check
            (None, Some(ann)) => param.ty = ann, // no body constraint; trust annotation
            (None, None) => {}    // unresolved; defer to post-resolve check_fully_typed
        }
    }
    // Build the domain type; refinement wraps it but is inferred in the outer
    // scope (param not in scope) because it is a constraint on the call site.
    let mut domain = param.ty.clone();
    if let Some(refinement) = refinement {
        if let RefinementKind::Predicate(def) = &refinement.kind {
            infer_expr(&mut def.borrow_mut(), ctx)?;
        }
        domain = Type::Refinement(Box::new(domain), refinement.clone());
    }
    Ok(Type::Fun(Box::new(domain), Box::new(body_ty)))
}

/// Constrain a lambda param equal to all of it's usages in the lambda body.
/// TODO: we probably shouldn't need this, but our handling of refinements is sketchy
/// right now and the order in which constraints are added to the unification table
/// affects whether or not refinements get dropped.  Once we have proper refinement
/// unification this should be unnecessary.
fn collect_constraints(
    param: &str,
    param_ty: &Type,
    body: &mut Expr,
    ctx: &mut TypeInferenceContext,
) -> Result<(), InferError> {
    match &mut body.node {
        TypedExprNode::Apply { function, argument } => {
            // If argument is Var(param), the domain of function's type is the constraint.
            match &argument.node {
                TypedExprNode::Var(v) if v == param => {
                    if let Ok(Type::Fun(domain, _)) = infer_expr(function, ctx) {
                        ctx.constrain_equal(param_ty, domain.as_ref())?;
                        // Don't recurse: function was already inferred (possibly mutated),
                        // and argument = Var(param) has no sub-patterns to search.
                        return Ok(());
                    }
                }
                // Apply(Proj(Index(n)), Var(param)) — tuple field projection.
                TypedExprNode::Apply {
                    function: proj_fn,
                    argument: proj_arg,
                } => {
                    if let TypedExprNode::Proj(ProjKey::Index(idx)) = &proj_fn.node {
                        if matches!(&proj_arg.node, TypedExprNode::Var(v) if v == param) {
                            if let Ok(Type::Fun(domain, _)) = infer_expr(function, ctx) {
                                ctx.constrain_equal(
                                    param_ty,
                                    &Type::PartialTuple(vec![(*idx, *domain.clone())]),
                                )?;
                                return Ok(());
                            }
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
            collect_constraints(param, param_ty, function, ctx)?;
            collect_constraints(param, param_ty, argument, ctx)?;
            Ok(())
        }

        // Don't recurse into a lambda that shadows param.
        TypedExprNode::Lambda {
            param: lam_param,
            body: lam_body,
            ..
        } => {
            if lam_param.name != param {
                collect_constraints(param, param_ty, lam_body, ctx)?;
            }
            Ok(())
        }

        TypedExprNode::Let {
            binding,
            bound_expr: value,
            body: let_body,
            ..
        } => {
            // Always search the value: it is evaluated in the outer scope, so
            // `param` is still in play even if `binding.name == param`.
            collect_constraints(param, param_ty, value, ctx)?;
            // Don't recurse into `body` when `binding.name == param`: the let-binding
            // shadows `param` there, mirroring the Lambda shadowing guard above.
            if binding.name != param {
                collect_constraints(param, param_ty, let_body, ctx)?;
            }
            Ok(())
        }

        TypedExprNode::BinOp { left, right, .. } => {
            collect_constraints(param, param_ty, left, ctx)?;
            collect_constraints(param, param_ty, right, ctx)?;
            Ok(())
        }

        TypedExprNode::UnaryOp(_, inner) => collect_constraints(param, param_ty, inner, ctx),

        TypedExprNode::Tuple(elts) => {
            for elt in elts {
                collect_constraints(param, param_ty, elt, ctx)?;
            }
            Ok(())
        }

        // Leaf nodes with no sub-expressions to search.
        _ => Ok(()),
    }
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
    let mut maybe_codomain_ty = None;
    match &mut function.node {
        TypedExprNode::Lambda { param, .. } => {
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
        // For projections, if the argument type is known (concrete or partial),
        // directly look up the projected element type to improve inference.
        TypedExprNode::Proj(key) => match (key, &arg_ty) {
            (ProjKey::Index(idx), Type::Tuple(types)) => {
                let proj_ty = types.get(*idx).cloned();
                if let Some(proj_ty) = proj_ty {
                    maybe_codomain_ty = Some(proj_ty);
                } else {
                    return Err(InferError::Unsupported(format!(
                        "Invalid tuple index {idx} for {arg_ty}"
                    )));
                }
            }
            (ProjKey::Index(idx), Type::PartialTuple(entries)) => {
                maybe_codomain_ty =
                    entries
                        .iter()
                        .find_map(|(i, t)| if i == idx { Some(t.clone()) } else { None });
            }
            (ProjKey::Field(field), Type::Record(types)) => {
                let proj_ty = types
                    .iter()
                    .find_map(|(name, typ)| if field == name { Some(typ) } else { None })
                    .cloned();
                if let Some(proj_ty) = proj_ty {
                    maybe_codomain_ty = Some(proj_ty);
                } else {
                    return Err(InferError::Unsupported(format!(
                        "Invalid record field {field} for {arg_ty}"
                    )));
                }
            }
            (ProjKey::Field(field), Type::PartialRecord(entries)) => {
                maybe_codomain_ty =
                    entries
                        .iter()
                        .find_map(|(n, t)| if n == field { Some(t.clone()) } else { None });
            }
            _ => {}
        },
        _ => {}
    }
    // Infer function type and return its codomain.
    match infer_expr(function, ctx)? {
        Type::Fun(domain, codomain) => {
            ctx.constrain_equal(&domain, &arg_ty)?;
            if let Some(codomain_ty) = maybe_codomain_ty {
                ctx.constrain_equal(&codomain, &codomain_ty)?;
            }
            Ok(*codomain)
        }
        ty => unreachable!("Apply function must have function type, got {ty}"),
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
    // Check user annotation on the binding site (e.g. `x: Int = expr`) via
    // constrain_equal so that partially-resolved Infer variables are handled
    // correctly (e.g. annotation=Int, bound_ty=Infer(id) → sets id→Int rather
    // than spuriously failing with !=).
    if let Some(ref annotation) = binding.user_annotation {
        ctx.constrain_equal(annotation, &bound_ty)
            .map_err(|_| InferError::AnnotationMismatch {
                annotation: annotation.clone(),
                inferred: bound_ty.clone(),
            })?;
    }
    // Always replace the pre-inference placeholder with the inferred type.
    // Expr::let_bind initialises binding.ty from bound_expr.ty *before*
    // inference runs, which can be a structured type containing Holes (e.g.
    // Fun(Infer(n), Hole) for a lambda whose body starts with ty=Hole).
    // Only checking for bare Hole or bare Infer misses those cases, leaving a
    // Hole embedded in binding.ty that panics resolve() later.
    binding.ty = bound_ty;
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
        return Ok(Type::Fun(
            Box::new(Type::UIntRange(0)),
            Box::new(Type::Base(BaseType::Unit)),
        ));
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

/// Destructure `ty` as a function type `(domain, codomain)`.
///
/// - If it is already `Fun(d, c)`, return `(d, c)` directly.
/// - If it is `Infer(id)`, constrain the variable to `Fun(fresh_d, fresh_c)` and
///   return the fresh pair.  This is sound in any context where a function type
///   is required (e.g. both sides of `≫`): the constraint will be resolved once
///   enough information flows into the surrounding expression.  Without this,
///   the post-composition morphism produced by the `curry_compose` simplification
///   rule (`curry(f ≫ g)  →  curry(f) ≫ map(g)`) fails inference because
///   `map(g)` has an unresolved codomain.
/// - Anything else is a hard type error.
fn require_fun(
    ty: Type,
    expr: &Expr,
    ctx: &mut TypeInferenceContext,
    side: &str,
) -> Result<(Type, Type), InferError> {
    match ty {
        Type::Fun(d, c) => Ok((*d, *c)),
        Type::Infer(id) => {
            let d = Type::Infer(ctx.fresh_infer_var());
            let c = Type::Infer(ctx.fresh_infer_var());
            ctx.constrain_equal(
                &Type::Infer(id),
                &Type::Fun(Box::new(d.clone()), Box::new(c.clone())),
            )?;
            Ok((d, c))
        }
        other => Err(InferError::Unsupported(format!(
            "Compose expects functions, got {side} {}: {other}",
            symbolic(expr),
        ))),
    }
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

/// Infer the type of a [`TypedExprNode::Compose`] node.
///
/// Each element must be a function. Adjacent elements are constrained so that
/// the codomain of element `i` equals the domain of element `i+1`. The result
/// type is `Fun(domain(f₀), codomain(fₙ₋₁))`.
fn infer_compose(elts: &mut [Expr], ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    assert!(elts.len() >= 2, "Compose requires at least two elements");
    // Infer all element types up front.
    let tys: Vec<Type> = elts
        .iter_mut()
        .map(|e| infer_expr(e, ctx))
        .collect::<Result<_, _>>()?;
    // Extract domain of the first and chain all adjacent pairs.
    let (overall_domain, mut prev_codomain) =
        require_fun(tys[0].clone(), &elts[0], ctx, "compose[0]")?;
    for (i, ty) in tys.into_iter().enumerate().skip(1) {
        let (d_i, c_i) = require_fun(ty, &elts[i], ctx, &format!("compose[{i}]"))?;
        ctx.constrain_equal(&prev_codomain, &d_i)?;
        prev_codomain = c_i;
    }
    Ok(Type::Fun(Box::new(overall_domain), Box::new(prev_codomain)))
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

/// Infer the type of a [`TypedExprNode::Case`] expression.
///
/// For each branch, the guard is constrained to [`Type::Base(BaseType::Bool)`]
/// and the body type is collected. All body types are unified via
/// [`constrain_equal`](TypeInferenceContext::constrain_equal); the unified
/// type is returned as the `Case` expression's type.
///
/// # Errors
///
/// - [`InferError::EmptyCase`] — `branches` is empty (malformed AST; lowering never produces this).
/// - [`InferError::TypeMismatch`] — two arms unify to distinct concrete types (e.g. `Int` vs
///   `String`). All arms must currently agree on one type; [`Type::Union`] is not yet produced.
fn infer_case(branches: &mut [Branch], ctx: &mut TypeInferenceContext) -> Result<Type, InferError> {
    let mut result_ty: Option<Type> = None;
    for Branch { guard, body } in branches.iter_mut() {
        // Guards must be boolean expressions.
        let guard_ty = infer_expr(guard, ctx)?;
        ctx.constrain_equal(&guard_ty, &Type::Base(BaseType::Bool))?;
        // Collect the arm body type and unify with the accumulated result type.
        let arm_ty = infer_expr(body, ctx)?;
        match result_ty.take() {
            None => result_ty = Some(arm_ty),
            Some(prev) => {
                ctx.constrain_equal(&prev, &arm_ty)?;
                // Keep `prev` unless `arm_ty` is concrete: stable accumulation
                // that only replaces when the new value is strictly more informative.
                result_ty = Some(if matches!(arm_ty, Type::Infer(_)) {
                    prev
                } else {
                    arm_ty
                });
            }
        }
    }
    result_ty.ok_or(InferError::EmptyCase)
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::symbolic::symbolic;
    use crate::ccl::BaseType;
    use crate::ccl::{
        AggregateKind, ArithmeticKind, BinOpKind, Branch, CompareKind, Expr, Lit, LogicKind, Type,
        TypedBinding, TypedExpr, TypedExprNode,
    };

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
        assert_eq!(
            ty,
            Type::fun(Type::UIntRange(0), Type::Base(BaseType::Unit))
        );
    }

    #[test]
    fn test_infer_unbound_var() {
        let mut ctx = TypeInferenceContext::new();
        let result = infer(&mut Expr::var("y"), &mut ctx);
        assert_eq!(result, Err(vec![InferError::UnboundVariable("y".into())]));
    }

    #[test]
    fn test_infer_cannot_infer_param() {
        let mut ctx = TypeInferenceContext::new();
        // λ x → x  — standalone; x is referenced but never used as an Apply argument.
        let mut expr = Expr::lambda("x", Type::infer(), Expr::var("x"));
        let errs = infer(&mut expr, &mut ctx).unwrap_err();
        assert!(errs.contains(&InferError::CannotInferParam("x".into())));
    }

    /// `λ p → p._0` where `p : Tuple([Hole, Hole])`.
    ///
    /// `replace_holes` converts the param type to `Tuple([Infer(a), Infer(b)])`.
    /// Body inference constrains `Infer(a)` via the index-0 projection but never
    /// touches `Infer(b)`. A shallow check (`if let Type::Infer(id) = param.ty`)
    /// would miss this because `param.ty` is a `Tuple`, not a top-level `Infer`.
    /// `type_has_infer` catches it recursively.
    #[test]
    fn test_cannot_infer_nested_tuple_param() {
        let mut ctx = TypeInferenceContext::new();
        // λ p → p._0  where p : (_, _)
        let body = Expr::apply(Expr::var("p"), Expr::proj_index(0));
        let mut expr = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "p".to_string(),
                ty: Type::Tuple(vec![Type::Hole, Type::Hole]),
                user_annotation: None,
            },
            body: Box::new(body),
            refinement: None,
        });
        let errs = infer(&mut expr, &mut ctx).unwrap_err();
        assert!(errs.contains(&InferError::CannotInferParam("p".into())));
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
            "λ __list_comp_var : [0, 1] → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x)"
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
            "λ __list_comp_var : [0, 1] → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → 42)"
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
            "λ __list_comp_var : [0, 1] → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x + 2)"
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
            "λ __list_comp_var : [0, 1] → __list_comp_var \
             ▷ (λ __list_comp_var : [0, 1] → __list_comp_var ▷ [10, 20] ▷ (λ x : Int → x)) \
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
            Err(vec![InferError::TypeMismatch {
                ctx: "unify".into(),
                type_a: Type::Base(BaseType::String),
                type_b: Type::Base(BaseType::Int),
            }])
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
            Err(vec![InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::String),
                inferred: Type::Base(BaseType::Int),
            }])
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
            Err(vec![InferError::UnboundVariable("unbound_var".into())])
        );
        // The scope stack must be empty: "x" should not be visible.
        assert_eq!(ctx.lookup("x"), None);
    }

    #[test]
    fn test_let_shadowing_no_constraint() {
        // λ x → let x = 42 in Apply(λ b:String → b, Var(x))
        //
        // `let x = 42` shadows the outer lambda param `x`. The scope stack
        // handles this correctly: the let-bound x (Int) shadows the lambda
        // param x. The body's Apply sees the inner x (Int), not the outer param.
        // Since `(λ b:String → b)(Int)` is a type error, inference returns
        // TypeMismatch. The outer lambda param is never constrained — but the
        // body type error surfaces first.
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
            Err(vec![InferError::TypeMismatch {
                ctx: "unify".into(),
                type_a: Type::Base(BaseType::String),
                type_b: Type::Base(BaseType::Int),
            }])
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
            Err(vec![InferError::TypeMismatch {
                ctx: "unify".into(),
                type_a: Type::Base(BaseType::Int),
                type_b: Type::Base(BaseType::String),
            }])
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
            Err(vec![InferError::TypeMismatch {
                ctx: "unify".into(),
                type_a: Type::Base(BaseType::Int),
                type_b: Type::Base(BaseType::Bool),
            }])
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
        assert_eq!(result, Err(vec![InferError::UnboundVariable("x".into())]));
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
            infer(&mut expr, &mut ctx)
                .is_err_and(|errs| errs.iter().any(|e| matches!(e, InferError::Unsupported(_)))),
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
            infer(&mut expr, &mut ctx).is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))),
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
            Err(vec![InferError::UnboundVariable("xs".into())])
        );
    }

    // -----------------------------------------------------------------------
    // PartialTuple inference via body-inference unification
    // -----------------------------------------------------------------------

    /// `λ p → f(p._0) + g(p._2)` where f : Int → Int and g : Bool → Bool.
    ///
    /// The pre-scan approach used to return `CannotInferParam` here because
    /// `reconcile_constraints` detected a gap at index 1. Now that body
    /// inference constrains `p` via the unification table, p is resolved to
    /// `PartialTuple([(0, Int), (2, Bool)])`. The body then fails with a
    /// type error from the `BoolLogic(And)` operator (Int vs Bool result).
    #[test]
    fn test_tuple_field_gap_now_infers_partial_tuple() {
        let f = Expr::lambda("a", Type::Base(BaseType::Int), Expr::var("a"));
        let g = Expr::lambda("b", Type::Base(BaseType::Bool), Expr::var("b"));
        let mut expr = Expr::lambda(
            "p",
            Type::infer(),
            Expr::binop(
                Expr::apply(Expr::apply(Expr::var("p"), Expr::proj_index(0)), f),
                BinOpKind::BoolLogic(LogicKind::And),
                Expr::apply(Expr::apply(Expr::var("p"), Expr::proj_index(2)), g),
            ),
        );
        let mut ctx = TypeInferenceContext::new();
        // Body inference constrains p, but the And of Int and Bool is a type error.
        assert!(infer(&mut expr, &mut ctx).is_err_and(|errs| errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. }))));
    }

    /// `λ p → f(p._0) + g(p._0)` where f : Int → Int and g : String → String.
    ///
    /// Both usages constrain p._0 via the unification table. The second usage
    /// constrains p._0 as String while the first established Int, causing a
    /// TypeMismatch.
    #[test]
    fn test_tuple_field_conflict_returns_mismatch() {
        let f = Expr::lambda("a", Type::Base(BaseType::Int), Expr::var("a"));
        let g = Expr::lambda("b", Type::Base(BaseType::String), Expr::var("b"));
        let mut expr = Expr::lambda(
            "p",
            Type::infer(),
            Expr::binop(
                Expr::apply(Expr::apply(Expr::var("p"), Expr::proj_index(0)), f),
                BinOpKind::BoolLogic(LogicKind::And),
                Expr::apply(Expr::apply(Expr::var("p"), Expr::proj_index(0)), g),
            ),
        );
        let mut ctx = TypeInferenceContext::new();
        assert!(infer(&mut expr, &mut ctx).is_err_and(|errs| errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. }))));
    }

    /// `λ p → p ► f` where f has domain `PartialTuple([(0, Int), (1, Bool)])`.
    ///
    /// Body inference constrains p against f's domain via the unification table.
    /// The resolution pass then promotes `PartialTuple([(0, Int), (1, Bool)])` to
    /// `Tuple([Int, Bool])` because indices 0 and 1 form a complete range `[0, 2)`.
    #[test]
    fn test_infer_lambda_partial_tuple_domain_promoted_to_tuple() {
        let mut ctx = TypeInferenceContext::new();
        let f_ty = Type::Fun(
            Box::new(Type::PartialTuple(vec![
                (0, Type::Base(BaseType::Int)),
                (1, Type::Base(BaseType::Bool)),
            ])),
            Box::new(Type::Base(BaseType::Int)),
        );
        let body = Expr::apply(Expr::var("p"), Expr::var("f"));
        let mut expr = Expr::lambda("p", Type::infer(), body);
        let mut scoped = ctx.enter_scope();
        scoped.bind("f", f_ty);
        let ty = infer(&mut expr, &mut scoped).unwrap();
        if let Type::Fun(domain, _) = ty {
            assert_eq!(
                *domain,
                Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Bool)]),
                "expected p : Tuple([Int, Bool]) after promotion, got {domain}"
            );
        } else {
            panic!("expected Fun type for lambda");
        }
    }

    // -----------------------------------------------------------------------
    // Deferred CannotInferParam: constraint comes from the call site
    // -----------------------------------------------------------------------

    /// `let g = λ x → x in let f = λ t → (t.0 ▸ g, t.2 ▸ g) in (0, 1, 2) ▸ f`
    ///
    /// `g`'s parameter type cannot be inferred from `g`'s own body, but usage
    /// inside `f` constrains it to Int (via `t.0` and `t.2` when `f` is applied
    /// to `(0, 1, 2)`). Unification should infer `g : Int ⇒ Int`,
    /// `f : {Int, Int, Int} ⇒ {Int, Int}`, and the whole expression `{Int, Int}`.
    #[test]
    fn test_lambda_type_inferred_from_call_site() {
        let mut ctx = TypeInferenceContext::new();
        let g_lambda = Expr::lambda("x", Type::infer(), Expr::var("x"));
        let t0g = Expr::apply(
            Expr::apply(Expr::var("t"), Expr::proj_index(0)),
            Expr::var("g"),
        );
        let t2g = Expr::apply(
            Expr::apply(Expr::var("t"), Expr::proj_index(2)),
            Expr::var("g"),
        );
        let f_lambda = Expr::lambda("t", Type::infer(), Expr::tuple(vec![t0g, t2g]));
        let tuple_012 = Expr::tuple(vec![
            Expr::lit(Lit::Int(0)),
            Expr::lit(Lit::Int(1)),
            Expr::lit(Lit::Int(2)),
        ]);
        let inner = Expr::let_bind("f", f_lambda, Expr::apply(tuple_012, Expr::var("f")));
        let mut expr = Expr::let_bind("g", g_lambda, inner);
        let ty = infer(&mut expr, &mut ctx).expect("should infer successfully");
        assert_eq!(
            ty,
            Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)])
        );
    }

    // -----------------------------------------------------------------------
    // AnnotationMismatch: user_annotation conflicts with inferred type
    // -----------------------------------------------------------------------

    /// Constructs a `Lambda` with `user_annotation: Some(Int)` but a body that
    /// constrains the param to `String`. Inference should return `AnnotationMismatch`.
    ///
    /// This path is not yet reachable from the pipeline (lowering always sets
    /// `user_annotation: None`), but the error variant must be exercised
    /// directly so it does not bitrot.
    #[test]
    fn test_infer_annotation_mismatch() {
        let mut ctx = TypeInferenceContext::new();
        // λ [x : annotated Int] → Apply(λ s : String → s, x)
        // x starts as Infer(id); body inference applies x as an arg to a
        // String-expecting function, constraining Infer(id) → String.
        // Post-body check: constrain_equal(Int, String) → AnnotationMismatch.
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
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(vec![InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::Int),
                inferred: Type::Base(BaseType::String),
            }])
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
            Err(vec![InferError::AnnotationMismatch {
                annotation: Type::Base(BaseType::String),
                inferred: Type::Base(BaseType::Int),
            }])
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
            Err(vec![InferError::UnboundVariable("ghost".into())])
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

    // -----------------------------------------------------------------------
    // UnaryOp type rule tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_unary_neg_int() {
        let mut ctx = TypeInferenceContext::new();
        use crate::ccl::UnaryOpKind;
        let mut expr = Expr::unary(UnaryOpKind::Neg, Expr::lit(Lit::Int(5)));
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    #[test]
    fn test_unary_not_bool() {
        let mut ctx = TypeInferenceContext::new();
        use crate::ccl::UnaryOpKind;
        let mut expr = Expr::unary(UnaryOpKind::Not, Expr::lit(Lit::Bool(true)));
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Bool)));
    }

    #[test]
    fn test_unary_neg_wrong_type() {
        let mut ctx = TypeInferenceContext::new();
        use crate::ccl::UnaryOpKind;
        // -true → TypeMismatch: constrain_equal(Bool, Int) errors with
        // expected=Bool (first arg / inner_ty), found=Int (second arg / constraint).
        let mut expr = Expr::unary(UnaryOpKind::Neg, Expr::lit(Lit::Bool(true)));
        assert_eq!(
            infer(&mut expr, &mut ctx),
            Err(vec![InferError::TypeMismatch {
                ctx: "unify".into(),
                type_a: Type::Base(BaseType::Bool),
                type_b: Type::Base(BaseType::Int),
            }])
        );
    }

    // -----------------------------------------------------------------------
    // Record inference tests
    // -----------------------------------------------------------------------

    /// A record literal `{x: 1, y: "hi"}` infers to `Record([("x", Int), ("y", String)])`.
    #[test]
    fn test_infer_record_literal() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::new(TypedExprNode::Record(vec![
            ("x".into(), Expr::lit(Lit::Int(1))),
            ("y".into(), Expr::lit(Lit::String("hi".into()))),
        ]));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(
            ty,
            Type::Record(vec![
                ("x".into(), Type::Base(BaseType::Int)),
                ("y".into(), Type::Base(BaseType::String)),
            ])
        );
    }

    /// An empty record infers to `Record([])`.
    #[test]
    fn test_infer_record_empty() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::new(TypedExprNode::Record(vec![]));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Record(vec![]));
    }

    // -----------------------------------------------------------------------
    // Case inference tests
    // -----------------------------------------------------------------------

    /// A `Case` arm that uses a `Let` binding in its body: variable `x` is
    /// bound via `Let` and used in arithmetic — the arm result is `Int`.
    #[test]
    fn test_infer_case_let_binding_in_arm() {
        let mut ctx = TypeInferenceContext::new();
        // { true → let x = 42 in x + 1 }
        let mut expr = Expr::new(TypedExprNode::Case {
            branches: vec![Branch {
                guard: Expr::lit(Lit::Bool(true)),
                body: Expr::let_bind(
                    "x",
                    Expr::lit(Lit::Int(42)),
                    Expr::binop(
                        Expr::var("x"),
                        BinOpKind::Arithmetic(ArithmeticKind::Add),
                        Expr::lit(Lit::Int(1)),
                    ),
                ),
            }],
        });
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    /// All `Case` branches must agree on the result type; unification of
    /// compatible types (both `Int`) succeeds and returns `Int`.
    #[test]
    fn test_infer_case_branches_unified() {
        let mut ctx = TypeInferenceContext::new();
        // { true → 1; true → 2 }
        let mut expr = Expr::new(TypedExprNode::Case {
            branches: vec![
                Branch {
                    guard: Expr::lit(Lit::Bool(true)),
                    body: Expr::lit(Lit::Int(1)),
                },
                Branch {
                    guard: Expr::lit(Lit::Bool(true)),
                    body: Expr::lit(Lit::Int(2)),
                },
            ],
        });
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    /// An empty `Case` (no branches) is a malformed AST; inference returns [`InferError::EmptyCase`].
    #[test]
    fn test_infer_case_no_branches() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::new(TypedExprNode::Case { branches: vec![] });
        assert_eq!(infer(&mut expr, &mut ctx), Err(vec![InferError::EmptyCase]));
    }

    // -----------------------------------------------------------------------
    // check_fully_typed unit tests
    // -----------------------------------------------------------------------

    /// A literal with a concrete type passes the fully-typed check.
    #[test]
    fn test_check_fully_typed_ok_literal() {
        let expr = Expr::lit(Lit::Int(42)).with_ty(Type::Base(BaseType::Int));
        assert_eq!(check_fully_typed(&expr), Ok(()));
    }

    /// A nested expression where every node has a concrete type passes.
    ///
    /// `Apply(λ x : Int → x, 42)` — all three nodes are given concrete types
    /// directly, simulating a fully-resolved tree.
    #[test]
    fn test_check_fully_typed_ok_nested() {
        let lambda = Expr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Base(BaseType::Int),
                user_annotation: None,
            },
            body: Box::new(Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int))),
            refinement: None,
        })
        .with_ty(Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        ));
        let expr = Expr::new(TypedExprNode::Apply {
            function: Box::new(lambda),
            argument: Box::new(Expr::lit(Lit::Int(42)).with_ty(Type::Base(BaseType::Int))),
        })
        .with_ty(Type::Base(BaseType::Int));
        assert_eq!(check_fully_typed(&expr), Ok(()));
    }

    /// A `Type::Hole` on the root node fails with `UnresolvedHole`.
    ///
    /// The context string is the symbolic representation of the offending expression,
    /// which for a literal `1` is just `"1"`.
    #[test]
    fn test_check_fully_typed_hole_on_root() {
        // TypedExpr::new sets ty: Type::Hole — don't call with_ty.
        let expr = Expr::lit(Lit::Int(1));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedHole("1".into())])
        );
    }

    /// A `Type::Hole` buried in a child node is caught by the depth-first walk.
    ///
    /// The context names the offending child (`"42"`), not the outer Apply node.
    #[test]
    fn test_check_fully_typed_hole_in_child() {
        // The Apply node itself has a concrete type, but the argument still has Hole.
        let arg = Expr::lit(Lit::Int(42)); // ty: Hole
        let func = Expr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int))),
            refinement: None,
        })
        .with_ty(Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        ));
        let expr = Expr::new(TypedExprNode::Apply {
            function: Box::new(func),
            argument: Box::new(arg),
        })
        .with_ty(Type::Base(BaseType::Int));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![
                InferError::UnresolvedHole("x".into()),
                InferError::UnresolvedHole("42".into())
            ])
        );
    }

    /// A `Type::Infer` on the root node fails with `UnresolvedInfer`.
    ///
    /// The context string is the symbolic representation of the offending expression
    /// (`"1"`), and the var ID matches the one used to build the type.
    #[test]
    fn test_check_fully_typed_infer_on_root() {
        let mut ctx = TypeInferenceContext::new();
        let id = ctx.fresh_infer_var();
        let expr = Expr::lit(Lit::Int(1)).with_ty(Type::Infer(id));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedInfer(id, "1".into())])
        );
    }

    /// A `Type::Infer` inside a lambda parameter binding is caught.
    ///
    /// The context string is the parameter name (`"x"`), not the whole lambda,
    /// because `check_fully_typed` passes `|| param.name.clone()` for param checks.
    #[test]
    fn test_check_fully_typed_infer_in_lambda_param() {
        let mut ctx = TypeInferenceContext::new();
        let id = ctx.fresh_infer_var();
        // The lambda's own type is concrete, but the param still holds an Infer var.
        let expr = Expr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Infer(id), // unsolved
                user_annotation: None,
            },
            body: Box::new(Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int))),
            refinement: None,
        })
        .with_ty(Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        ));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::CannotInferParam("x".into())])
        );
    }

    /// A `Type::Hole` nested inside a `Fun` type (not just at a node boundary)
    /// is caught by the recursive `check_type` walk.
    ///
    /// The context string is the symbolic form of the node whose type is malformed (`"1"`).
    #[test]
    fn test_check_fully_typed_hole_inside_fun_type() {
        // The node type is Fun(Hole, Int) — the Hole is inside the compound type.
        let expr = Expr::lit(Lit::Int(1)).with_ty(Type::Fun(
            Box::new(Type::Hole),
            Box::new(Type::Base(BaseType::Int)),
        ));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedHole("1".into())])
        );
    }

    // -----------------------------------------------------------------------
    // Proj / PartialTuple / PartialRecord inference tests
    // -----------------------------------------------------------------------

    /// `Proj(Index(2))` applied to a 3-tuple infers the third element type.
    ///
    /// This was the broken case before PartialTuple: the old fallback produced
    /// `Fun(?a, ?b)` for any index ≥ 2, losing all structural information.
    #[test]
    fn test_infer_proj_index_2_on_3_tuple() {
        let mut ctx = TypeInferenceContext::new();
        // Apply((1, "hello", true), .2)  =>  Bool
        let mut expr = Expr::apply(
            Expr::new(TypedExprNode::Tuple(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::String("hello".into())),
                Expr::lit(Lit::Bool(true)),
            ])),
            Expr::proj_index(2),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Bool));
    }

    /// `Proj(Field("x"))` applied to a record infers the field type.
    #[test]
    fn test_infer_proj_field_on_record() {
        let mut ctx = TypeInferenceContext::new();
        // Apply({x: 42, y: "hi"}, .x)  =>  Int
        let mut expr = Expr::apply(
            Expr::new(TypedExprNode::Record(vec![
                ("x".to_string(), Expr::lit(Lit::Int(42))),
                ("y".to_string(), Expr::lit(Lit::String("hi".into()))),
            ])),
            Expr::proj_field("x"),
        );
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    /// A bare `Proj(Index(n))` has domain type `PartialTuple({n => ?a})` after being resolved.
    #[test]
    fn test_bare_proj_index_has_partial_tuple_domain() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::proj_index(3);
        // Use infer_expr directly: a bare Proj has an unresolved codomain (?a), so
        // infer() would reject it via check_fully_typed. We only care about shape here.
        let ty = infer_expr(&mut expr, &mut ctx).unwrap();
        // Expect Fun(PartialTuple([...]), ?) — domain must be a PartialTuple with one entry at 3.
        match ty {
            Type::Fun(domain, _) => match domain.as_ref() {
                Type::Infer(id) => match ctx.table.probe(*id) {
                    Some(Type::PartialTuple(entries))
                        if entries.len() == 1 && entries[0].0 == 3 => {}
                    other => panic!("expected PartialTuple with index 3, got {other:?}"),
                },
                other => panic!("expected Infer type for Proj, got {other:?}"),
            },
            other => panic!("expected Fun, got {other}"),
        }
    }

    /// A bare `Proj(Field("z"))` has domain type `PartialRecord({"z" => ?a})` after being resolved.
    #[test]
    fn test_bare_proj_field_has_partial_record_domain() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::proj_field("z");
        // Use infer_expr directly: a bare Proj has an unresolved codomain (?a), so
        // infer() would reject it via check_fully_typed. We only care about shape here.
        let ty = infer_expr(&mut expr, &mut ctx).unwrap();
        match ty {
            Type::Fun(domain, _) => match domain.as_ref() {
                Type::Infer(id) => match ctx.table.probe(*id) {
                    Some(Type::PartialRecord(entries))
                        if entries.len() == 1 && entries[0].0 == "z" => {}
                    other => panic!("expected PartialTuple with index 3, got {other:?}"),
                },
                other => panic!("expected Infer type for Proj, got {other:?}"),
            },
            other => panic!("expected Fun, got {other}"),
        }
    }

    // -----------------------------------------------------------------------
    // typecheck tests
    // -----------------------------------------------------------------------

    /// A valid fully-inferred expression passes `typecheck` without errors.
    #[test]
    fn test_typecheck_valid_arithmetic() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Int(2)),
        );
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A valid boolean logic expression passes `typecheck`.
    #[test]
    fn test_typecheck_valid_bool_logic() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::binop(
            Expr::lit(Lit::Bool(true)),
            BinOpKind::BoolLogic(LogicKind::And),
            Expr::lit(Lit::Bool(false)),
        );
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A valid comparison expression passes `typecheck`.
    #[test]
    fn test_typecheck_valid_compare() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Compare(CompareKind::Less),
            Expr::lit(Lit::Int(2)),
        );
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A valid `not` expression passes `typecheck`.
    #[test]
    fn test_typecheck_valid_unary_not() {
        use crate::ccl::UnaryOpKind;
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::unary(UnaryOpKind::Not, Expr::lit(Lit::Bool(true)));
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A valid negation expression passes `typecheck`.
    #[test]
    fn test_typecheck_valid_unary_neg() {
        use crate::ccl::UnaryOpKind;
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::unary(UnaryOpKind::Neg, Expr::lit(Lit::Int(5)));
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A homogeneous list passes `typecheck`.
    #[test]
    fn test_typecheck_valid_list() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::list(vec![
            Expr::lit(Lit::Int(1)),
            Expr::lit(Lit::Int(2)),
            Expr::lit(Lit::Int(3)),
        ]);
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A function application with matching types passes `typecheck`.
    #[test]
    fn test_typecheck_valid_apply() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::apply(
            Expr::lit(Lit::Int(42)),
            Expr::lambda("x", Type::Base(BaseType::Int), Expr::var("x")),
        );
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// Corrupting a `BinOp::BoolLogic` operand type to `Int` is caught by `typecheck`.
    ///
    /// After inference `true and false` is correctly typed; forcibly setting one
    /// operand's type to `Int` creates a node whose types are inconsistent.
    #[test]
    fn test_typecheck_bool_logic_wrong_operand_type() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::binop(
            Expr::lit(Lit::Bool(true)),
            BinOpKind::BoolLogic(LogicKind::And),
            Expr::lit(Lit::Bool(false)),
        );
        infer(&mut expr, &mut ctx).unwrap();
        // Corrupt the left operand's type.
        if let TypedExprNode::BinOp { left, .. } = &mut expr.node {
            left.ty = Type::Base(BaseType::Int);
        }
        let result = typecheck(&expr);
        assert!(result.is_err(), "expected typecheck to report an error");
        let errs = result.unwrap_err();
        assert!(errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })));
    }

    /// Corrupting a `Compare` result type away from `Bool` is caught by `typecheck`.
    #[test]
    fn test_typecheck_compare_wrong_result_type() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Compare(CompareKind::Less),
            Expr::lit(Lit::Int(2)),
        );
        infer(&mut expr, &mut ctx).unwrap();
        // Corrupt the node type to Int instead of Bool.
        expr.ty = Type::Base(BaseType::Int);
        let result = typecheck(&expr);
        assert!(result.is_err());
        let errs = result.unwrap_err();
        assert!(errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })));
    }

    /// Corrupting the `Not` operand to a non-Bool type is caught by `typecheck`.
    #[test]
    fn test_typecheck_unary_not_wrong_operand_type() {
        use crate::ccl::UnaryOpKind;
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::unary(UnaryOpKind::Not, Expr::lit(Lit::Bool(true)));
        infer(&mut expr, &mut ctx).unwrap();
        if let TypedExprNode::UnaryOp(_, inner) = &mut expr.node {
            inner.ty = Type::Base(BaseType::Int);
        }
        let result = typecheck(&expr);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })));
    }

    /// A heterogeneous list — where element types differ — is caught by `typecheck`.
    ///
    /// Inference silently drops errors for elements after the first, so
    /// `[1, "hello"]` passes `infer` but `typecheck` detects the mismatch.
    #[test]
    fn test_typecheck_list_heterogeneous() {
        // Build a list whose elements have different concrete types by
        // constructing the node directly with pre-typed children.
        let int_elem = Expr::lit(Lit::Int(1)).with_ty(Type::Base(BaseType::Int));
        let str_elem = Expr::lit(Lit::String("hello".into())).with_ty(Type::Base(BaseType::String));
        let list_ty = Type::Fun(
            Box::new(Type::UIntRange(2)),
            Box::new(Type::Base(BaseType::Int)),
        );
        let expr = Expr::new(TypedExprNode::List(vec![int_elem, str_elem])).with_ty(list_ty);
        let result = typecheck(&expr);
        assert!(
            result.is_err(),
            "expected typecheck to catch heterogeneous list"
        );
        let errs = result.unwrap_err();
        assert!(errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })));
    }

    /// A function application where the argument type does not match the
    /// function domain is caught by `typecheck`.
    #[test]
    fn test_typecheck_apply_argument_domain_mismatch() {
        // Construct Apply((λ x : String → x) : Fun(String, String), 42 : Int)
        // with the Apply node given type String.  The argument is Int but the
        // domain is String — typecheck must detect this.
        let lambda = Expr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".to_string(),
                ty: Type::Base(BaseType::String),
                user_annotation: None,
            },
            body: Box::new(Expr::var("x").with_ty(Type::Base(BaseType::String))),
            refinement: None,
        })
        .with_ty(Type::Fun(
            Box::new(Type::Base(BaseType::String)),
            Box::new(Type::Base(BaseType::String)),
        ));
        let expr = Expr::new(TypedExprNode::Apply {
            function: Box::new(lambda),
            argument: Box::new(Expr::lit(Lit::Int(42)).with_ty(Type::Base(BaseType::Int))),
        })
        .with_ty(Type::Base(BaseType::String));
        let result = typecheck(&expr);
        assert!(
            result.is_err(),
            "expected typecheck to catch domain mismatch"
        );
        let errs = result.unwrap_err();
        assert!(errs
            .iter()
            .any(|e| matches!(e, InferError::TypeMismatch { .. })));
    }

    /// A valid lambda and application combination passes `typecheck` end-to-end.
    #[test]
    fn test_typecheck_lambda_and_apply_valid() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::apply(
            Expr::lit(Lit::String("hello".into())),
            Expr::lambda("s", Type::Base(BaseType::String), Expr::var("s")),
        );
        infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(typecheck(&expr), Ok(()));
    }

    /// A lambda that applies two different projections to the same parameter
    /// should infer a tuple-typed domain after `set()` merging and `TupleField`
    /// constraint accumulation in `collect_constraints_into`.
    #[test]
    #[ignore]
    fn test_infer_lambda_two_proj_on_same_param() {
        let mut ctx = TypeInferenceContext::new();
        // λ p → ((p ► .0) + 0, p ► .1)
        // p ► .0 feeds into Int addition → p[0] : Int
        // p ► .1 is unconstrained
        // Expected domain: (Int, ?b)
        let body = Expr::new(TypedExprNode::Tuple(vec![
            Expr::new(TypedExprNode::BinOp {
                op: BinOpKind::Arithmetic(ArithmeticKind::Add),
                left: Box::new(Expr::apply(Expr::var("p"), Expr::proj_index(0))),
                right: Box::new(Expr::lit(Lit::Int(0))),
            }),
            Expr::apply(Expr::var("p"), Expr::proj_index(1)),
        ]));
        let mut expr = Expr::lambda("p", Type::infer(), body);
        let ty = infer(&mut expr, &mut ctx).unwrap();
        if let Type::Fun(domain, _) = ty {
            match *domain {
                Type::Tuple(ref elts) if elts.len() == 2 => {
                    assert_eq!(
                        elts[0],
                        Type::Base(BaseType::Int),
                        "expected p[0] : Int, got {}",
                        elts[0]
                    );
                    // elts[1] remains as an unconstrained infer variable
                }
                ref other => panic!("expected 2-element Tuple domain for p, got {other}"),
            }
        } else {
            panic!("expected Fun type for lambda");
        }
    }
}

//! CCL type inference public API and post-inference validation.
//!
//! Sits between lowering (`ccl::lower`) and compilation (`interpreter::compile_ccl`):
//!
//! ```text
//! Python source
//!   → lower (ccl/lower.rs)            — structural, no type reasoning
//!   → infer  (ccl/infer.rs)           — type inference entry point
//!       → infer_simple_sub.rs         — simple-sub constraint-based inference
//!   → compile (interpreter/compile_ccl.rs)  — CCL → dataflow operators
//! ```
//!
//! # Type inference
//!
//! The public entry point is [`infer`], which delegates to
//! [`crate::ccl::infer_simple_sub`]. This module also provides post-inference
//! validation ([`check_fully_typed`], [`typecheck`]) and the
//! [`TypeInferenceContext`] that holds source-type registrations used by
//! both inference and compilation.
//!
//! The pass fills in [`crate::ccl::TypedExpr::ty`] on every node it visits. User-written
//! annotations are carried in [`crate::ccl::TypedExpr::user_annotation`]; they are checked for
//! compatibility with the inferred type at the end of each [`infer`] call.

use std::collections::{HashMap, HashSet};
use std::ops::{Deref, DerefMut};

use crate::ccl::symbolic::{symbolic, symbolic_typed};
use crate::ccl::{Expr, InferVarId, Type, TypedExprNode};
use crate::util::ScopeStack;

// ---------------------------------------------------------------------------
// InferArena
// ---------------------------------------------------------------------------

/// Owns every inference variable minted during one inference run and breaks
/// the `Rc` cycles their bounds form.
///
/// # Why this exists
///
/// The simple-sub solver records `α <: β` by pushing `Type::Infer(β)` into
/// `α`'s bounds and `Type::Infer(α)` into `β`'s bounds. Mutual constraints
/// (and self-recursive ones) therefore make each [`crate::ccl::InferVar`]
/// hold a strong `Rc` to the others through its `RefCell<InferBounds>`. Once
/// Pass 2 (coalesce) overwrites every `expr.ty` with a concrete,
/// variable-free type, those cells become unreachable from the final AST but
/// keep each other alive — reference counting alone never reclaims the
/// cycle, so the whole variable graph leaks after each `infer()` run.
///
/// The arena is a zero-field RAII guard over a thread-local capture buffer
/// (see [`crate::ccl::arena_enter`]). While it is alive, every
/// [`crate::ccl::InferVar::fresh`] registers its variable in that buffer, so
/// the buffer holds one strong handle to *every* variable minted during the
/// run. On drop the arena takes the buffer back and clears each variable's
/// lower and upper bound lists, severing all bound edges so every refcount
/// can reach zero. A single flat `Vec` suffices: variables are never looked
/// up by id (the `Type` carries the `Rc` directly); the arena only needs to
/// enumerate them once at teardown. Clearing bounds before the `Vec` drops
/// handles self-cycles and N-way cycles uniformly.
///
/// # Why clearing is always safe
///
/// Coalesce never reuses a bound-carrying solver variable in its output: it
/// builds a fresh `Type` and, for a position with no concrete contribution,
/// mints a brand-new *unconstrained* `Type::Infer`. So every variable the
/// arena clears is either orphaned from the result tree or has empty bounds
/// already — clearing can never corrupt a type that survives into the AST.
///
/// # Drop-time borrow rule
///
/// `Drop` calls `borrow_mut()` on each cell's bounds, so nothing may hold a
/// live `borrow_mut()` on any owned variable across the arena drop. This is
/// safe in practice: the solver's bound borrows are all transient
/// (taken and released within a single `constrain`/`coalesce` step), and the
/// arena drops only after inference has fully exited.
///
/// # Rejected alternative: `Weak` back-edges
///
/// We could instead make one direction of each bound edge a
/// `Weak<InferVar>`, so the cycle is never strong. Rejected: simple-sub
/// constraints are *symmetric* mutual references with no natural "back
/// edge" to demote, so we'd be upgrading `Weak`s and handling the `None`
/// case throughout the constraint/coalesce hot path. The arena instead pays
/// a single linear teardown and keeps every bound a plain, always-valid
/// strong `Type`.
pub struct InferArena {
    /// Zero-sized: the captured variables live in the thread-local buffer
    /// installed by [`crate::ccl::arena_enter`], not in the guard itself.
    /// The raw-pointer `PhantomData` suppresses the `Send`/`Sync` auto
    /// traits — the guard must drop on the thread whose buffer it opened
    /// (dropping elsewhere would tear down the wrong thread's slot). Also
    /// unconstructible outside this module's `new`.
    _not_send_sync: std::marker::PhantomData<*const ()>,
}

impl InferArena {
    /// Create an arena and begin capturing minted variables on this thread.
    /// Every [`crate::ccl::InferVar::fresh`] called before this arena is
    /// dropped registers its variable. Inference is non-reentrant: at most
    /// one arena is active per thread at a time, and constructing a second one
    /// while another is live trips a `debug_assert!` (see
    /// [`crate::ccl::arena_enter`]).
    pub fn new() -> Self {
        crate::ccl::arena_enter();
        InferArena {
            _not_send_sync: std::marker::PhantomData,
        }
    }
}

impl Default for InferArena {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for InferArena {
    fn drop(&mut self) {
        // Take back every variable minted during the run and sever its bound
        // edges, so the (otherwise cyclic) refcounts can all reach zero.
        for var in crate::ccl::arena_exit() {
            let mut bounds = var.bounds.borrow_mut();
            bounds.lower.clear();
            bounds.upper.clear();
        }
    }
}

// ---------------------------------------------------------------------------
// TypeInferenceContext
// ---------------------------------------------------------------------------

/// Context for the CCL type-inference pass.
///
/// Combines a lexical scope stack (for lambda parameters and let bindings)
/// and a registry of externally-registered data-source types. Type inference
/// is performed by the simple-sub pass ([`crate::ccl::infer_simple_sub`]).
///
/// Scopes are entered and exited exclusively via [`enter_scope`](TypeInferenceContext::enter_scope);
/// each lambda body and let binding gets its own scope.
#[derive(Default)]
pub struct TypeInferenceContext {
    /// Lexical scopes mapping variable names to their types.
    scopes: ScopeStack<Type>,

    /// Types of known externally-registered data sources.
    pub(crate) source_types: HashMap<String, Type>,
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
#[derive(Clone, PartialEq)]
pub enum InferError {
    /// A variable was referenced but not bound in the current scope.
    UnboundVariable(String),
    /// A type mismatch was detected between two solved types.
    TypeMismatch {
        type_a: Type,
        type_b: Type,
        ctx: String,
    },
    /// A [`Type::Fun`] was required — e.g. in a function-application or
    /// [`TypedExprNode::Compose`] position — but a non-function type was found.
    ExpectedFunction {
        /// The actual type of the non-function expression.
        found: Type,
        /// Symbolic label of the expression where the error occurred.
        at: String,
    },
    /// A user-written annotation on a binding site conflicts with the inferred type.
    ///
    /// Distinct from [`InferError::TypeMismatch`] so error messages can say
    /// "you annotated X as T but it has type U" vs. "expected T found U".
    AnnotationMismatch {
        /// The type the user wrote in the annotation.
        annotation: Type,
        /// The type that inference determined.
        inferred: Type,
    },
    /// The expression kind is not yet handled by this inference pass.
    Unsupported(String),
    /// A [`crate::ccl::TypedExprNode::Case`] with no branches was encountered.
    ///
    /// Lowering never produces a 0-branch `Case`; this indicates a malformed
    /// AST constructed outside the normal lowering path.
    EmptyCase {
        /// Symbolic label of the case expression.
        at: String,
    },
    /// A [`Type::Hole`] placeholder survived past inference.
    UnresolvedHole {
        /// Symbolic label of the expression whose type contains the hole.
        at: String,
    },
    /// An unresolved [`Type::Infer`] variable survived past inference.
    UnresolvedInfer {
        /// The unresolved variable's id.
        id: InferVarId,
        /// Symbolic label of the expression whose type contains the variable.
        at: String,
    },
    /// A partial tuple or partial record was not resolved to a concrete type.
    UnresolvedPartial {
        /// Display string of the partial type.
        kind: String,
        /// Symbolic label of the expression whose type is partial.
        at: String,
    },
    /// A node's coalesced type references a term binder that is not in scope
    /// at that node — a violation of the scope-validity invariant (design
    /// §6.2). Like [`InferError::UnresolvedHole`], treat as a compiler bug
    /// (a substitution that failed to discharge a binder), not a user-facing
    /// error: user scoping mistakes are rejected earlier with source context.
    ScopeViolation {
        /// Symbolic label of the expression whose type is ill-scoped.
        at: String,
        /// The ill-scoped type.
        ty: Type,
        /// The out-of-scope binder names free in the type's refinement
        /// predicates.
        unbound: Vec<String>,
    },
    /// An incompatible-bounds conflict from simple-sub coalescing.
    /// The solver rejects unions/intersections of distinct concrete types.
    IncompatibleBounds {
        /// `true` = positive polarity (lower-bound union); `false` = negative (upper-bound intersection).
        polarity: bool,
        /// Display string of the conflicting types, e.g. `"handle(0) | handle(1)"`.
        conflicting: String,
        /// UIDs of the simple-sub variables whose bounds conflicted.
        vars: Vec<InferVarId>,
        /// The innermost expression label where the conflict was first detected.
        origin: String,
        /// Enclosing expression labels, innermost-first.
        context: Vec<String>,
    },
}

impl std::fmt::Debug for InferError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferError::UnboundVariable(name) => write!(f, "Unbound variable: '{}'", name),
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
            InferError::ExpectedFunction { found, at } => {
                write!(f, "Expected function type at {at}, found {found}")
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
            InferError::EmptyCase { at } => {
                write!(f, "Case expression must have at least one branch (at {at})")
            }
            InferError::UnresolvedHole { at } => {
                write!(f, "Unresolved type hole in expression: {at}")
            }
            InferError::UnresolvedInfer { id, at } => {
                write!(f, "Unresolved inference variable {id} in expression: {at}")
            }
            InferError::UnresolvedPartial { kind, at } => {
                write!(f, "Unresolved partial {kind} in expression: {at}")
            }
            InferError::ScopeViolation { at, ty, unbound } => {
                write!(
                    f,
                    "Scope violation (compiler bug, design §6.2): type {ty} at {at} \
                     references out-of-scope binder(s) {unbound:?}"
                )
            }
            InferError::IncompatibleBounds {
                polarity,
                conflicting,
                vars,
                origin,
                context,
            } => {
                let bound_kind = if *polarity { "lower" } else { "upper" };
                let aligned_origin = origin.replace('\n', "\n  ");
                let var_ids: Vec<_> = vars.iter().map(|v| v.0).collect();
                write!(
                    f,
                    "Type Inference Error: Incompatible {bound_kind} bounds\nRejected by: structural inference (won't infer an untagged sum from a collision)\nConflicting Types: {conflicting}\nVariables: {var_ids:?}\n\nError originated at:\n  {aligned_origin}"
                )?;
                if !context.is_empty() {
                    write!(f, "\n\nIn context of:")?;
                    for (i, ctx) in context.iter().enumerate() {
                        // "  N. " prefix; continuation lines must align with the
                        // first character of content (i.e. same width of spaces).
                        let prefix = format!("  {}. ", i + 1);
                        let cont_indent = " ".repeat(prefix.len());
                        let aligned = ctx.replace('\n', &format!("\n{cont_indent}"));
                        write!(f, "\n{prefix}{aligned}")?;
                    }
                }
                Ok(())
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Run type inference on `expr` using the simple-sub algorithm.
///
/// Public entry point for the CCL type-inference pass. Delegates entirely to
/// [`crate::ccl::infer_simple_sub::infer`]. After this call returns `Ok`, the
/// tree is fully annotated and contains no `Type::Hole` or `Type::Infer`
/// placeholders.
pub fn infer(expr: &mut Expr, ctx: &mut TypeInferenceContext) -> Result<Type, Vec<InferError>> {
    // The arena owns every inference variable minted by the passes below
    // (captured through the thread-local mint sink). Its lifetime spans both
    // Pass 1 (constraint emission) and Pass 2 (coalesce); when it drops here
    // — on the `Ok` and the `?`/error paths alike — its `Drop` clears every
    // variable's bounds, breaking the `Rc` cycles that would otherwise leak
    // the whole variable graph. See [`InferArena`].
    let _arena = InferArena::new();
    crate::ccl::infer_simple_sub::infer(expr, &ctx.source_types)
}

/// Check that every [`crate::ccl::TypedExpr::ty`] and [`crate::ccl::TypedBinding::ty`]
/// in the tree is a fully concrete type — no [`Type::Hole`] or [`Type::Infer`] anywhere,
/// including nested inside compound types like `Fun` or `Tuple` and inside refinements.
///
/// Returns `Ok(())` if the tree is fully annotated, or all holes and unresolved
/// inference variables found in a depth-first walk.
///
/// Runs as the first phase of [`typecheck`]; callers that want the combined
/// hole-freeness + semantic check should call [`typecheck`] directly.
pub fn check_fully_typed(expr: &Expr) -> Result<(), Vec<InferError>> {
    let mut errors = Vec::new();
    let mut seen: HashSet<crate::ccl::PredicateCellId> = HashSet::new();
    collect_expr_errors(expr, &mut errors, &mut seen);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Recursively collect all type errors from `expr` into `errors`.
///
/// `seen_refinements` tracks already-visited predicate cells
/// ([`crate::ccl::PredicateCellId`]) to break cycles when a refinement's
/// predicate expression has a type slot containing the same refinement
/// (post-inference, this happens when a Lambda param's refinement embeds
/// a predicate that mentions the param — e.g. filter-feed inside a
/// defer-mediating UDF body).
fn collect_expr_errors(
    expr: &Expr,
    errors: &mut Vec<InferError>,
    seen_refinements: &mut HashSet<crate::ccl::PredicateCellId>,
) {
    collect_type_errors(&expr.ty, &symbolic(expr), errors, seen_refinements);
    // Binder-bearing variants emit per-binding type errors before descending
    // into their children; everything else just visits its direct children.
    match &expr.node {
        TypedExprNode::Lambda { param, body, .. } => {
            collect_type_errors(&param.ty, &param.name, errors, seen_refinements);
            collect_expr_errors(body, errors, seen_refinements);
        }
        TypedExprNode::Let { binding, .. } => {
            collect_type_errors(&binding.ty, &binding.name, errors, seen_refinements);
            expr.walk_children(|e| collect_expr_errors(e, errors, seen_refinements));
        }
        TypedExprNode::VariantCtor { payload, .. } => {
            collect_expr_errors(payload, errors, seen_refinements);
        }
        // `Case` carries per-branch pattern bindings on `TypedBinding`
        // (not reached by `walk_children`), so check their types here.
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_expr_errors(s, errors, seen_refinements);
            }
            for b in branches {
                if let Some(p) = &b.pattern {
                    collect_type_errors(&p.binding.ty, &p.binding.name, errors, seen_refinements);
                }
                collect_expr_errors(&b.guard, errors, seen_refinements);
                collect_expr_errors(&b.body, errors, seen_refinements);
            }
        }
        TypedExprNode::Loop { params, .. } => {
            for p in params {
                collect_type_errors(&p.ty, &p.name, errors, seen_refinements);
            }
            expr.walk_children(|e| collect_expr_errors(e, errors, seen_refinements));
        }
        TypedExprNode::Error => crate::unexpected_error_node!(),
        _ => expr.walk_children(|e| collect_expr_errors(e, errors, seen_refinements)),
    }
}

/// Collect all holes and unresolved inference variables in `ty` into `errors`.
///
/// `context_sym` is the symbolic representation of the expression whose type
/// is being checked, used as the context string in any error pushed.
///
/// `seen_refinements` breaks cycles through `Type::Refinement` predicates
/// whose expression type slots contain the same refinement.
fn collect_type_errors(
    ty: &Type,
    context_sym: &str,
    errors: &mut Vec<InferError>,
    seen_refinements: &mut HashSet<crate::ccl::PredicateCellId>,
) {
    match ty {
        Type::Hole => errors.push(InferError::UnresolvedHole {
            at: context_sym.to_string(),
        }),
        Type::Infer(var) => errors.push(InferError::UnresolvedInfer {
            id: var.uid,
            at: context_sym.to_string(),
        }),
        Type::Fun {
            domain, codomain, ..
        } => {
            collect_type_errors(domain, context_sym, errors, seen_refinements);
            collect_type_errors(codomain, context_sym, errors, seen_refinements);
        }
        Type::Tuple(elems) => {
            for elem in elems {
                collect_type_errors(elem, context_sym, errors, seen_refinements);
            }
        }
        Type::Record(fields) => {
            for (_, ty) in fields {
                collect_type_errors(ty, context_sym, errors, seen_refinements);
            }
        }
        Type::Variant(tags) => {
            for (_, payload) in tags {
                collect_type_errors(payload, context_sym, errors, seen_refinements);
            }
        }
        Type::Refinement(inner, refinement) => {
            // Walk each predicate cell only once to break cycles that
            // arise post-inference when the predicate's expressions
            // have type slots containing the same refinement.
            //
            // The same visited-set cycle-handling pattern lives in
            // [`crate::ccl::ccl_utils::count_free_in_type_with_visited`],
            // [`crate::ccl::lambda_elim::elim_lambdas_in_type`] (both
            // via [`crate::ccl::ccl_utils::walk_refined_predicates`]),
            // and a try_borrow_mut fallback variant in
            // [`crate::ccl::infer_simple_sub::coalesce_node`] and
            // [`crate::ccl::simplify::simplify_once`].  This site
            // doesn't share the helper because it mixes per-node
            // error checks with the refinement walk; if drift makes
            // the cycle logic important here, sync with those sites.
            if seen_refinements.insert(refinement.cell_id())
                && let Ok(def) = refinement.predicate.try_borrow()
            {
                // `try_borrow` (not `borrow`): this check can run *while* a
                // predicate is mid-substitution (e.g. `lambda_elim::substitute`
                // holds a predicate's `borrow_mut` and calls `debug_typecheck`,
                // which lands here). A predicate's own type slots may reference
                // this same refinement, so a panicking `borrow` would re-borrow
                // the held cell; skipping the in-flight predicate is correct —
                // the substitution that holds it checks it on its own.
                collect_expr_errors(&def, errors, seen_refinements);
            }
            collect_type_errors(inner, context_sym, errors, seen_refinements);
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
/// First enforces full annotation via [`check_fully_typed`] (no [`Type::Hole`]
/// or [`Type::Infer`] placeholders remain anywhere), then runs the semantic
/// rules — the latter assume hole-freeness, so checking it here makes that
/// precondition self-enforcing rather than an implicit caller obligation.
/// Returns `Ok(())` if no errors are found, or all discovered errors as
/// `Err(errs)`.
pub fn typecheck(expr: &Expr) -> Result<(), Vec<InferError>> {
    check_fully_typed(expr)?;
    crate::ccl::infer_simple_sub::check(expr)
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::BaseType;
    use crate::ccl::symbolic::symbolic;
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
            Type::Fun {
                name: None,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Int))
            }
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
            Type::Fun {
                name: None,
                domain: Box::new(Type::UIntRange(2)),
                codomain: Box::new(Type::Base(BaseType::Int))
            }
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
        // simple-sub permits unconstrained lambdas; returns Fun(Infer, Infer).
        let mut expr = Expr::lambda("x", Type::infer(), Expr::var("x"));
        let ty = infer(&mut expr, &mut ctx).expect("simple-sub allows unconstrained λ x → x");
        assert!(
            matches!(
                ty,
                Type::Fun {
                    domain: _,
                    codomain: _,
                    ..
                }
            ),
            "expected Fun type, got {ty:?}"
        );
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
        // simple-sub permits partially-inferred params; body constrains p._0 to Int
        // but leaves p._1 unconstrained — returns a Fun rather than erroring.
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
        let ty =
            infer(&mut expr, &mut ctx).expect("simple-sub allows partially-constrained params");
        assert!(
            matches!(
                ty,
                Type::Fun {
                    domain: _,
                    codomain: _,
                    ..
                }
            ),
            "expected Fun type, got {ty:?}"
        );
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
            Type::Fun {
                name: None,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Int))
            }
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
        // (42 : String)  =>  annotation conflict
        // simple-sub surfaces annotation conflicts as AnnotationMismatch
        let mut expr = Expr::lit(Lit::Int(42)).with_user_annotation(Type::Base(BaseType::String));
        let errs = infer(&mut expr, &mut ctx).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(
                e,
                InferError::AnnotationMismatch {
                    annotation: Type::Base(BaseType::String),
                    inferred: Type::Base(BaseType::Int),
                }
            )),
            "expected AnnotationMismatch String/Int, got {errs:?}"
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
        // simple-sub catches the mismatch at the Apply site.
        let errs = infer(&mut expr, &mut ctx)
            .expect_err("expected TypeMismatch Int/String under simple-sub");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                InferError::TypeMismatch {
                    type_a: Type::Base(BaseType::Int),
                    type_b: Type::Base(BaseType::String),
                    ..
                }
            )),
            "expected TypeMismatch Int/String, got {errs:?}"
        );
    }

    #[test]
    fn test_collect_multi_conflict() {
        // λ x → Apply(λ a:Int → a, Var(x)) + Apply(λ b:String → b, Var(x))
        // `x` is the argument to both an Int-domain and a String-domain function.
        // The sound one-way `arg <: domain` rule records `x <: Int` and
        // `x <: String` — two upper bounds, with no eager cross-constraint — so
        // the conflict surfaces structurally at coalesce when the bounds collide
        // (`IncompatibleBounds`, an untagged-sum rejection) rather than as an
        // eager `TypeMismatch` from the (retired) reverse `domain <: arg`. Both
        // correctly reject the program.
        let mut expr = double_apply_lambda(Type::Base(BaseType::Int), Type::Base(BaseType::String));
        let mut ctx = TypeInferenceContext::new();
        let errs = infer(&mut expr, &mut ctx).expect_err("expected an Int/String conflict");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                InferError::IncompatibleBounds { conflicting, .. }
                    if conflicting.contains("Int") && conflicting.contains("String")
            )),
            "expected IncompatibleBounds Int/String, got {errs:?}"
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
        // Int + Bool → type error; Int ⊔ Bool is inexpressible under simple-sub.
        let mut expr = Expr::binop(
            Expr::lit(Lit::Int(1)),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Expr::lit(Lit::Bool(true)),
        );
        assert!(
            infer(&mut expr, &mut ctx).is_err(),
            "expected error for Int + Bool"
        );
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

    // -----------------------------------------------------------------------
    // Predicate refinement tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_lambda_with_predicate_refinement() {
        // λ x : Int {True} → x
        // The predicate is a bare Bool over the implicit refinement binder; no
        // outer vars needed. Return type must be Fun(Refinement(Int, r), Int).
        let mut ctx = TypeInferenceContext::new();
        let predicate = Expr::lit(Lit::Bool(true));
        let mut expr =
            Expr::lambda_with_refinement("x", Type::Base(BaseType::Int), Expr::var("x"), predicate);
        let ty = infer(&mut expr, &mut ctx).unwrap();
        match ty {
            Type::Fun {
                domain, codomain, ..
            } => {
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
        let mut expr =
            Expr::lambda_with_refinement("x", Type::Base(BaseType::Int), Expr::var("x"), predicate);
        let result = infer(&mut expr, &mut ctx);
        assert_eq!(result, Err(vec![InferError::UnboundVariable("x".into())]));
    }

    // -----------------------------------------------------------------------
    // Aggregate type inference tests
    // -----------------------------------------------------------------------

    /// `Sum` over a list of ints: `sum([1, 2, 3])` → `Int`.
    ///
    /// The input list infers as `Fun(UIntRange(3), Int)`; the constraint
    /// `input = Fun(_, Int)` together with `Sum`'s fixed output type `Int`
    /// resolves the result to `Int`.
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
    /// `Max` has no fixed output type; the result equals the input element
    /// type (the codomain of the input function), which here is `Int`.
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

    /// `Sum` over a list of strings → type error.
    ///
    /// `Sum` has a fixed output type of `Int`; the constraint approach catches
    /// the mismatch as `TypeMismatch` (String ≠ Int) rather than `Unsupported`.
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
            infer(&mut expr, &mut ctx).is_err_and(|errs| errs
                .iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))),
            "Sum over String should be a type error"
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
        // HM produces TypeMismatch; simple-sub's map_constrain_err detects that the
        // rhs is a Fun and lhs is not, promoting it to ExpectedFunction.
        let errs = infer(&mut expr, &mut ctx).expect_err("expected error for non-function input");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                InferError::TypeMismatch { .. } | InferError::ExpectedFunction { .. }
            )),
            "expected TypeMismatch or ExpectedFunction, got {errs:?}"
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

    /// `let total = λ xs → sum(xs) in total([1, 2, 3])` — aggregate in a let-bound function.
    ///
    /// The lambda is bound in a `Let` rather than immediately applied, so
    /// `infer_apply`'s eager-annotation path (which sets `param.ty` from the
    /// argument before descending into the body) does not fire when the lambda
    /// body is first inferred. `xs` is therefore still an unresolved `Infer`
    /// variable when the `Aggregate` node is visited.
    ///
    /// The old `resolve_type` approach failed here: `resolve_type` on an unsolved
    /// `Infer` var is a no-op, leaving `Infer(_)`, whose `codomain()` is `None`,
    /// which produced a `TypeMismatch` error.
    ///
    /// The `constrain_equal` approach records `xs = Fun(_, output)` and lets
    /// unification fill in the concrete types when the call site `total([1,2,3])`
    /// constrains `xs = Fun(UIntRange(3), Int)`.
    #[test]
    fn test_infer_aggregate_input_type_inferred_from_call_site() {
        let mut ctx = TypeInferenceContext::new();
        // let total = λ xs → sum(xs) in total([1, 2, 3])
        let total_fn = Expr::lambda(
            "xs",
            Type::infer(),
            Expr::aggregate(Expr::var("xs"), AggregateKind::Sum),
        );
        let call = Expr::apply(
            Expr::list(vec![
                Expr::lit(Lit::Int(1)),
                Expr::lit(Lit::Int(2)),
                Expr::lit(Lit::Int(3)),
            ]),
            Expr::var("total"),
        );
        let mut expr = Expr::let_bind("total", total_fn, call);
        assert_eq!(infer(&mut expr, &mut ctx), Ok(Type::Base(BaseType::Int)));
    }

    // -----------------------------------------------------------------------
    // Open-record (projection) inference via body usage
    // -----------------------------------------------------------------------

    /// `λ p → f(p._0) + g(p._2)` where f : Int → Int and g : Bool → Bool.
    ///
    /// Body usage constrains `p` to an open record with `Int` at index 0 and
    /// `Bool` at index 2 (via the two projection sites). The body then fails
    /// with a type error from the `BoolLogic(And)` operator (Int vs Bool).
    #[test]
    fn test_tuple_field_gap_infers_from_projections() {
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
        assert!(infer(&mut expr, &mut ctx).is_err_and(|errs| {
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        }));
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
        assert!(infer(&mut expr, &mut ctx).is_err_and(|errs| {
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        }));
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
    ///
    /// HM: catches the conflict as `AnnotationMismatch` at the lambda-param annotation check.
    /// simple-sub: the annotation pins the param to String; the Apply then fails to constrain
    /// `Int ≤ String` and surfaces as `TypeMismatch{Apply, Int, String}`.
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
        // simple-sub: the annotation pins the param to String; the Apply then fails to
        // constrain Int ≤ String and surfaces as TypeMismatch.
        let errs = infer(&mut expr, &mut ctx).expect_err("expected error under simple-sub");
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. })),
            "expected TypeMismatch from annotation/arg conflict, got {errs:?}"
        );
    }

    // -----------------------------------------------------------------------
    // user_annotation used as fallback when body provides no constraint
    // -----------------------------------------------------------------------

    /// `λ [x : annotated Int] → unit` — body does not reference x, so
    /// inference has nothing to constrain. The annotation must be accepted
    /// as the param type.
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
            Type::Fun {
                name: None,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Unit))
            }
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
        let source_ty = Type::Fun {
            name: None,
            domain: Box::new(Type::DataSource("mystream".into())),
            codomain: Box::new(Type::Base(BaseType::String)),
        };
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
        let int_ty = Type::Fun {
            name: None,
            domain: Box::new(Type::DataSource("ints".into())),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let str_ty = Type::Fun {
            name: None,
            domain: Box::new(Type::DataSource("strs".into())),
            codomain: Box::new(Type::Base(BaseType::String)),
        };
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
        // -true → TypeMismatch(Bool, Int).
        let mut expr = Expr::unary(UnaryOpKind::Neg, Expr::lit(Lit::Bool(true)));
        let errs = infer(&mut expr, &mut ctx)
            .expect_err("expected TypeMismatch Bool/Int under simple-sub");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                InferError::TypeMismatch {
                    type_a: Type::Base(BaseType::Bool),
                    type_b: Type::Base(BaseType::Int),
                    ..
                }
            )),
            "expected TypeMismatch Bool/Int, got {errs:?}"
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

    /// An empty record: simple-sub cannot distinguish an empty `Record` from an empty
    /// `Tuple` at coalesce time (both compact to a `CompactType` with an empty field map)
    /// and produces `Tuple([])`.
    #[test]
    fn test_infer_record_empty() {
        let mut ctx = TypeInferenceContext::new();
        let mut expr = Expr::new(TypedExprNode::Record(vec![]));
        let ty = infer(&mut expr, &mut ctx).unwrap();
        assert_eq!(ty, Type::Tuple(vec![]));
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
            scrutinee: None,
            branches: vec![Branch {
                pattern: None,
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
            scrutinee: None,
            branches: vec![
                Branch {
                    pattern: None,
                    guard: Expr::lit(Lit::Bool(true)),
                    body: Expr::lit(Lit::Int(1)),
                },
                Branch {
                    pattern: None,
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
        let mut expr = Expr::new(TypedExprNode::Case {
            scrutinee: None,
            branches: vec![],
        });
        assert!(matches!(
            infer(&mut expr, &mut ctx),
            Err(ref errs) if errs.iter().any(|e| matches!(e, InferError::EmptyCase { .. }))
        ));
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
        .with_ty(Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        });
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
            Err(vec![InferError::UnresolvedHole { at: "1".into() }])
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
        .with_ty(Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        });
        let expr = Expr::new(TypedExprNode::Apply {
            function: Box::new(func),
            argument: Box::new(arg),
        })
        .with_ty(Type::Base(BaseType::Int));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![
                InferError::UnresolvedHole { at: "x".into() },
                InferError::UnresolvedHole { at: "42".into() }
            ])
        );
    }

    /// A `Type::Infer` on the root node fails with `UnresolvedInfer`.
    ///
    /// The context string is the symbolic representation of the offending expression
    /// (`"1"`), and the var ID matches the one used to build the type.
    #[test]
    fn test_check_fully_typed_infer_on_root() {
        let var = crate::ccl::InferVar::fresh(0);
        let id = var.uid;
        let expr = Expr::lit(Lit::Int(1)).with_ty(Type::Infer(var));
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedInfer { id, at: "1".into() }])
        );
    }

    /// A `Type::Infer` inside a lambda parameter binding is caught.
    ///
    /// The context string is the parameter name (`"x"`), not the whole lambda,
    /// because `check_fully_typed` passes `|| param.name.clone()` for param checks.
    #[test]
    fn test_check_fully_typed_infer_in_lambda_param() {
        let var = crate::ccl::InferVar::fresh(0);
        let id = var.uid;
        // The lambda's own type is concrete, but the param still holds an Infer var.
        // After removing CannotInferParam, collect_type_errors reports UnresolvedInfer.
        let expr = Expr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Infer(var), // unsolved
                user_annotation: None,
            },
            body: Box::new(Expr::lit(Lit::Int(0)).with_ty(Type::Base(BaseType::Int))),
            refinement: None,
        })
        .with_ty(Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        });
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedInfer { id, at: "x".into() }])
        );
    }

    /// A `Type::Hole` nested inside a `Fun` type (not just at a node boundary)
    /// is caught by the recursive `check_type` walk.
    ///
    /// The context string is the symbolic form of the node whose type is malformed (`"1"`).
    #[test]
    fn test_check_fully_typed_hole_inside_fun_type() {
        // The node type is Fun(Hole, Int) — the Hole is inside the compound type.
        let expr = Expr::lit(Lit::Int(1)).with_ty(Type::Fun {
            name: None,
            domain: Box::new(Type::Hole),
            codomain: Box::new(Type::Base(BaseType::Int)),
        });
        assert_eq!(
            check_fully_typed(&expr),
            Err(vec![InferError::UnresolvedHole { at: "1".into() }])
        );
    }

    // -----------------------------------------------------------------------
    // Proj inference tests
    // -----------------------------------------------------------------------

    /// `Proj(Index(2))` applied to a 3-tuple infers the third element type.
    ///
    /// This was the broken case under the old HM fallback, which produced
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
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        );
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
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        );
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
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        );
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
        let list_ty = Type::Fun {
            name: None,
            domain: Box::new(Type::UIntRange(2)),
            codomain: Box::new(Type::Base(BaseType::Int)),
        };
        let expr = Expr::new(TypedExprNode::List(vec![int_elem, str_elem])).with_ty(list_ty);
        let result = typecheck(&expr);
        assert!(
            result.is_err(),
            "expected typecheck to catch heterogeneous list"
        );
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        );
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
        .with_ty(Type::Fun {
            name: None,
            domain: Box::new(Type::Base(BaseType::String)),
            codomain: Box::new(Type::Base(BaseType::String)),
        });
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
        assert!(
            errs.iter()
                .any(|e| matches!(e, InferError::TypeMismatch { .. }))
        );
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
    /// constraint accumulation.
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
        if let Type::Fun {
            domain,
            codomain: _,
            ..
        } = ty
        {
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

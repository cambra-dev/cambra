//! Simple-sub-based type inference.
//!
//! The canonical type inference implementation, invoked via
//! [`crate::ccl::infer::infer`].
//!
//! # Design (monomorphic let)
//!
//! Two passes over the expression tree:
//!
//! 1. **Constraint emission**: walk the tree, emit `constrain_subtype` calls
//!    over [`Type`] (inference variables are [`Type::Infer`] with mutable
//!    bounds), writing each node's emitted `Type` straight onto `expr.ty`.
//!    Because the vars are shared `Rc<InferVar>`s, later constraints
//!    accumulate into bounds that are already visible through the stored
//!    `Type` — no side table is needed. Refinements stay on the AST node
//!    (`Expr::Lambda::refinement`) and are *not* part of the structural
//!    lattice (see plan R1); `type_saturate` and `lambda_elim` read them
//!    from the AST directly.
//! 2. **Coalesce + write-back**: walk the tree again and, for each node,
//!    run [`coalesce_compact`](crate::ccl::simple_sub::coalesce_compact) to
//!    resolve the inference variables in its `expr.ty` in place.
//!
//! # Polymorphism
//!
//! No let-generalization (`let` is monomorphic). The
//! [`OperatorSchemes`] registry contains [`PolyScheme`]s only for the
//! handful of operator/projection cases that are inherently polymorphic
//! (`Compare : ∀α. α → α → Bool`, `Max : ∀α γ. (α → γ) → γ`, etc.). Each scheme
//! is `instantiate`d at every use site, minting fresh vars per use.
//!
//! Most `Builtin` nodes are introduced post-inference by
//! `lambda_elim`/`planning` with their type pre-stamped on the node, and
//! inference just rubber-stamps them. The exceptions are polymorphic
//! builtins introduced pre-inference (e.g. `LastOrDefault` from
//! `lower_mutation_loop`); those have entries in [`OperatorSchemes`] and
//! are freshened at each use site like any other scheme.

use std::collections::{BTreeMap, HashMap};

use smol_str::SmolStr;

use crate::ccl::infer::InferError;
use crate::ccl::simple_sub::{
    CoalesceError, ConstrainCache, ConstrainError, FieldKey, PolyScheme, coalesce_compact,
    compact_type, constrain_subtype, fresh_var, fun, prim, simplify_type,
};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    AggregateKind, BaseType, BinOpKind, Branch, Builtin, Expr, Level, Lit, ProjKey, Refinement,
    RefinementKind, Type, TypedBinding, TypedExprNode, UnaryOpKind,
};
use crate::util::ScopeStack;

/// Build a structural product [`Type`] from a `FieldKey`-keyed field map:
/// all-`Name` keys → `Record`, otherwise a dense `Tuple` (the emitter only
/// builds dense `Index` products from 0). For a *sparse* / open index
/// position (an index projection's domain), the emitter pads to a dense
/// `Tuple` explicitly rather than going through here — see `emit_proj`.
fn product(fields: BTreeMap<FieldKey, Type>) -> Type {
    if fields.keys().all(|k| matches!(k, FieldKey::Name(_))) {
        Type::Record(
            fields
                .into_iter()
                .map(|(k, t)| match k {
                    FieldKey::Name(n) => (n.to_string(), t),
                    _ => unreachable!(),
                })
                .collect(),
        )
    } else {
        // BTreeMap iterates in key order, so dense `Index` keys come out
        // in position order.
        Type::Tuple(fields.into_values().collect())
    }
}

/// Build a [`Type::Variant`] from a `FieldKey`-keyed tag map.
fn variant_type(tags: BTreeMap<FieldKey, Type>) -> Type {
    Type::Variant(tags.into_iter().collect())
}

// ---------------------------------------------------------------------------
// Operator/projection scheme registry (Step 7b)
// ---------------------------------------------------------------------------

/// Schemes for operators that lift cleanly to fixed signatures.
///
/// Each scheme is built once per [`SimpleSubContext`]; `instantiate`
/// runs at every use site to mint fresh quantified variables. Operators
/// with structural result types (`BinOp::CollectionUnion`) and nodes
/// whose typing rules require AST-level reasoning (`Apply`, `Lambda`,
/// `Let`, `Case`, `List`, …) are handled by per-case rules in
/// [`emit_node`] rather than via this registry.
pub struct OperatorSchemes {
    /// `∀α. α → α → α` — both operands agree, result is the same type.
    /// Matches today's `infer_binop` Arithmetic rule which only enforces
    /// operand agreement, not numeric-ness (operator conversion catches
    /// non-numeric arithmetic later).
    arithmetic: PolyScheme,
    /// `∀α. α → α → Bool`.
    compare: PolyScheme,
    /// `Bool → Bool → Bool`.
    bool_logic: PolyScheme,
    /// `String → String → String`.
    concat: PolyScheme,
    /// `Int → Int`.
    neg: PolyScheme,
    /// `Bool → Bool`.
    not_op: PolyScheme,
    /// `∀α. (α → Int) → Int` — the full Sum operator type, applied
    /// directly to the input collection (function), folding its Int
    /// codomain to an Int.
    aggregate_sum: PolyScheme,
    /// `∀α γ. (α → γ) → γ` — the full Max operator type, applied directly
    /// to the input collection (function), folding its codomain γ to a
    /// result of the same type.
    aggregate_max: PolyScheme,
    /// `∀α β. ((α → β), β) → β` — extract the last value from a
    /// function-typed stream, falling back to the default scalar when the
    /// stream's domain is empty. Polymorphic in both the stream domain
    /// (`α`) and the shared codomain/default type (`β`); inline construction
    /// is required because both vars are shared across positions, which
    /// `normalize_annotation` (one fresh var per `Hole`) can't express.
    last_or_default: PolyScheme,
}

impl OperatorSchemes {
    /// Build the registry. Schemes are quantified at level 0; their
    /// internal fresh vars live at level 1 so `instantiate(0)` mints
    /// fresh copies at the active inference level.
    pub fn new() -> Self {
        const SCHEME_LEVEL: Level = 0;
        const BODY_LEVEL: Level = 1;

        // Arithmetic: ∀α. α → α → α
        let alpha = fresh_var(BODY_LEVEL);
        let arithmetic =
            PolyScheme::poly(SCHEME_LEVEL, fun(alpha.clone(), fun(alpha.clone(), alpha)));

        // Compare: ∀α. α → α → Bool
        let alpha = fresh_var(BODY_LEVEL);
        let compare = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(alpha.clone(), fun(alpha, prim(BaseType::Bool))),
        );

        // BoolLogic: Bool → Bool → Bool
        let bool_logic = PolyScheme::mono(fun(
            prim(BaseType::Bool),
            fun(prim(BaseType::Bool), prim(BaseType::Bool)),
        ));

        // Concat: String → String → String
        let concat = PolyScheme::mono(fun(
            prim(BaseType::String),
            fun(prim(BaseType::String), prim(BaseType::String)),
        ));

        // Neg: Int → Int
        let neg = PolyScheme::mono(fun(prim(BaseType::Int), prim(BaseType::Int)));

        // Not: Bool → Bool
        let not_op = PolyScheme::mono(fun(prim(BaseType::Bool), prim(BaseType::Bool)));

        // Sum: ∀α. (α → Int) → Int. The full operator type: consumes a
        // collection (a function whose domain α is unconstrained) and folds
        // its Int codomain to an Int. Inline-built so α gets its own fresh
        // var even though it's unconstrained.
        let alpha = fresh_var(BODY_LEVEL);
        let aggregate_sum = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(fun(alpha.clone(), prim(BaseType::Int)), prim(BaseType::Int)),
        );

        // Max: ∀α γ. (α → γ) → γ. Consumes a collection and folds its
        // codomain γ to a result of the same type.
        let alpha = fresh_var(BODY_LEVEL);
        let gamma = fresh_var(BODY_LEVEL);
        let aggregate_max = PolyScheme::poly(SCHEME_LEVEL, fun(fun(alpha, gamma.clone()), gamma));

        // LastOrDefault: ∀α β. ((α → β), β) → β
        // Inline-built (not via `normalize_annotation`) so the codomain of the
        // stream and the default share one variable `β`.
        let alpha = fresh_var(BODY_LEVEL);
        let beta = fresh_var(BODY_LEVEL);
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        tup.insert(FieldKey::Index(0), fun(alpha.clone(), beta.clone()));
        tup.insert(FieldKey::Index(1), beta.clone());
        let last_or_default = PolyScheme::poly(SCHEME_LEVEL, fun(product(tup), beta));

        Self {
            arithmetic,
            compare,
            bool_logic,
            concat,
            neg,
            not_op,
            aggregate_sum,
            aggregate_max,
            last_or_default,
        }
    }

    fn binop(&self, op: BinOpKind) -> &PolyScheme {
        match op {
            BinOpKind::Arithmetic(_) => &self.arithmetic,
            BinOpKind::Compare(_) => &self.compare,
            BinOpKind::BoolLogic(_) => &self.bool_logic,
            BinOpKind::Concat => &self.concat,
        }
    }

    fn unary(&self, op: UnaryOpKind) -> &PolyScheme {
        match op {
            UnaryOpKind::Neg => &self.neg,
            UnaryOpKind::Not => &self.not_op,
        }
    }

    fn aggregate(&self, kind: AggregateKind) -> &PolyScheme {
        match kind {
            AggregateKind::Sum => &self.aggregate_sum,
            AggregateKind::Max => &self.aggregate_max,
        }
    }

    /// Polymorphic-builtin lookup. Returns `Some` for builtins whose
    /// signature has shared type variables across positions (and so cannot
    /// be expressed via the generic `Hole → fresh_var` conversion); `None`
    /// for builtins whose pre-stamped `expr.ty` is already monomorphic
    /// (or polymorphic only in independent vars).
    fn builtin(&self, b: Builtin) -> Option<&PolyScheme> {
        match b {
            Builtin::LastOrDefault => Some(&self.last_or_default),
            _ => None,
        }
    }
}

impl Default for OperatorSchemes {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SimpleSubContext (Step 7c)
// ---------------------------------------------------------------------------

/// Inference state for the simple-sub path.
///
/// The solver works directly on [`Type`]: each node's inferred type (and
/// each binder's `.ty`) is written into the AST during emission and
/// resolved in place during coalesce — there is no side table.
struct SimpleSubContext {
    /// Lexical scope: name → `Type` for in-scope variables and let-bound
    /// names. We currently store monotypes; a future let-poly extension
    /// will widen this to `PolyScheme` schemes.
    scopes: ScopeStack<Type>,
    /// Externally-registered data sources (set by
    /// `TypeInferenceContext::register_source_type`).
    sources: HashMap<String, Type>,
    /// Constraint cycle cache, shared across one full inference pass.
    cache: ConstrainCache,
    /// Operator/projection scheme registry.
    schemes: OperatorSchemes,
    /// Current polymorphism level. Currently held at 0 (no `let` bumps);
    /// the field is threaded through so a future let-poly extension drops
    /// in without restructuring.
    level: Level,
}

impl SimpleSubContext {
    fn new(sources: HashMap<String, Type>) -> Self {
        Self {
            scopes: ScopeStack::default(),
            sources,
            cache: ConstrainCache::new(),
            schemes: OperatorSchemes::new(),
            level: 0,
        }
    }

    /// Normalize a user annotation / source type into a solver-ready
    /// `Type`: every `Hole` becomes a fresh inference variable at the
    /// current level. Everything else — including existing `Infer` vars,
    /// the structural variants the solver operates on, and `Refinement`
    /// wrappers (refinements now ride the lattice as restriction tags) — is
    /// kept, recursing to normalize nested holes.
    fn normalize_annotation(&self, ty: &Type) -> Type {
        match ty {
            // A `Hole` annotation means "infer this" → fresh variable.
            Type::Hole => fresh_var(self.level),
            // Refinements ride the lattice: keep the wrapper, normalize the
            // inner (so a `Refinement(Hole, r)` source annotation becomes
            // `Refinement(?fresh, r)` rather than losing the tag).
            Type::Refinement(inner, r) => {
                Type::Refinement(Box::new(self.normalize_annotation(inner)), r.clone())
            }
            // Structural types are already solver-ready; recurse to
            // normalize any nested holes/refinements.
            Type::Fun(d, c) => fun(self.normalize_annotation(d), self.normalize_annotation(c)),
            Type::Tuple(ts) => {
                Type::Tuple(ts.iter().map(|t| self.normalize_annotation(t)).collect())
            }
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), self.normalize_annotation(t)))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.normalize_annotation(t)))
                    .collect(),
            ),
            // Leaves and existing inference vars pass through unchanged.
            Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Infer(_) => ty.clone(),
        }
    }
}

/// Emit constraints for every refinement predicate embedded in an
/// annotation `Type`, so their expression sub-trees get inferred types.
/// Refinement predicates are `Expr`s that mention free variables of the
/// enclosing scope; this must run while those bindings are live (i.e.
/// during `emit_node` of the annotated node). `try_borrow_mut` skips a
/// predicate already being walked (the same `Rc` can recur through its own
/// type slot).
fn emit_annotation_predicates(ty: &Type, ctx: &mut SimpleSubContext) -> Result<(), InferError> {
    match ty {
        Type::Refinement(inner, r) => {
            let RefinementKind::Predicate(def) = &r.kind;
            if let Ok(mut pred) = def.try_borrow_mut() {
                emit_node(&mut pred, ctx)?;
            }
            emit_annotation_predicates(inner, ctx)
        }
        Type::Fun(d, c) => {
            emit_annotation_predicates(d, ctx)?;
            emit_annotation_predicates(c, ctx)
        }
        Type::Tuple(ts) => {
            for t in ts {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Record(fs) => {
            for (_, t) in fs {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Variant(tags) => {
            for (_, t) in tags {
                emit_annotation_predicates(t, ctx)?;
            }
            Ok(())
        }
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {
            Ok(())
        }
    }
}

/// Apply a binary scheme: instantiate, build the expected call shape,
/// constrain_subtype. Returns the fresh result variable.
fn apply_binary_scheme(
    ctx: &mut SimpleSubContext,
    scheme: &PolyScheme,
    left: &Type,
    right: &Type,
) -> Result<Type, ConstrainError> {
    let body = scheme.instantiate(ctx.level);
    let result = fresh_var(ctx.level);
    let expected = fun(left.clone(), fun(right.clone(), result.clone()));
    constrain_subtype(&body, &expected, &mut ctx.cache)?;
    Ok(result)
}

/// Apply a unary scheme. Used for UnaryOp and Aggregate. For an
/// aggregate the scheme is the full operator type `(α → γ) → γ`, so the
/// operand is the input collection (function) itself.
fn apply_unary_scheme(
    ctx: &mut SimpleSubContext,
    scheme: &PolyScheme,
    operand: &Type,
) -> Result<Type, ConstrainError> {
    let body = scheme.instantiate(ctx.level);
    let result = fresh_var(ctx.level);
    let expected = fun(operand.clone(), result.clone());
    constrain_subtype(&body, &expected, &mut ctx.cache)?;
    Ok(result)
}

/// Resolve a (possibly variable-laden) [`Type`] to a concrete type for use
/// in error messages. Falls back to [`Type::Hole`] if coalesce fails (which
/// can happen for types with incompatible bounds that triggered the error).
fn coalesce_for_error(ty: &Type) -> Type {
    resolve_var_type(ty).unwrap_or(Type::Hole)
}

/// Map a [`ConstrainError`] onto the public [`InferError`] enum.
fn map_constrain_err(err: ConstrainError, ctx_label: &str) -> InferError {
    match err {
        ConstrainError::Mismatch { lhs, rhs } => {
            let lhs_ty = coalesce_for_error(&lhs);
            let rhs_ty = coalesce_for_error(&rhs);
            // `constrain_subtype(lhs, rhs)` means `lhs <: rhs`. If rhs is a function
            // and lhs is not, the caller passed a non-function where a function
            // was expected (e.g. applying a non-function at an Apply site).
            if matches!(rhs, Type::Fun(..)) && !matches!(lhs, Type::Fun(..)) {
                InferError::ExpectedFunction {
                    found: lhs_ty,
                    at: ctx_label.to_string(),
                }
            } else {
                InferError::TypeMismatch {
                    ctx: ctx_label.to_string(),
                    type_a: lhs_ty,
                    type_b: rhs_ty,
                }
            }
        }
        ConstrainError::MissingField { key, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (missing field {key:?})"),
            type_a: coalesce_for_error(&in_type),
            type_b: Type::Hole,
        },
        ConstrainError::ExtraTag { tag, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (variant tag .{tag} not accepted)"),
            type_a: coalesce_for_error(&in_type),
            type_b: Type::Hole,
        },
    }
}

/// Map a [`CoalesceError`] onto the public [`InferError`] enum.
fn map_coalesce_err(err: CoalesceError, ctx_label: &str) -> InferError {
    match err {
        CoalesceError::IncompatibleBounds {
            polarity,
            vars,
            details,
        } => InferError::IncompatibleBounds {
            polarity,
            conflicting: details,
            vars,
            origin: ctx_label.to_string(),
            context: vec![],
        },
        CoalesceError::UnresolvedPartial { kind, details } => InferError::UnresolvedPartial {
            kind: format!("{:?} ({})", kind, details),
            at: ctx_label.to_string(),
        },
        CoalesceError::RecursiveType { details } => InferError::Unsupported(format!(
            "recursive type at {}: {} (residual μ-types are forbidden)",
            ctx_label, details
        )),
    }
}

// ---------------------------------------------------------------------------
// Public entry point + two-pass driver (Step 7e glue)
// ---------------------------------------------------------------------------

/// Run simple-sub type inference on `expr`.
///
/// Two-pass: emit constraints, then coalesce. Source types come from
/// the public [`crate::ccl::infer::TypeInferenceContext`] and are
/// normalized (holes → fresh vars) up front.
pub fn infer(expr: &mut Expr, sources: &HashMap<String, Type>) -> Result<Type, Vec<InferError>> {
    // Convert source registry once; reuse across all node emissions.
    let mut sub_ctx = {
        let pre = SimpleSubContext::new(HashMap::new());
        let translated: HashMap<String, Type> = sources
            .iter()
            .map(|(k, v)| (k.clone(), pre.normalize_annotation(v)))
            .collect();
        SimpleSubContext::new(translated)
    };

    // Pass 1: emit constraints.
    emit_node(expr, &mut sub_ctx).map_err(|e| vec![e])?;

    // Pass 2: resolve each node's inference variables in place into expr.ty.
    let errors = coalesce_pass(expr);
    if !errors.is_empty() {
        return Err(errors);
    }
    // Pass 3: saturate refinement/lexical-scope shapes the structural lattice cannot
    // carry, fixing up the four kinds of nodes affected (Refinement
    // Propagation, Let Binding Resolution, CollectionUnion direct-build).
    // See `type_saturate` for the rule set.
    crate::ccl::type_saturate::saturate(expr);
    Ok(expr.ty.clone())
}

// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

/// Walk one expression node, emit constraints for it, write its inferred
/// `Type` onto `expr.ty`, and return that `Type`. Sub-expressions recurse;
/// their `Type`s are stored on their own nodes the same way.
fn emit_node(expr: &mut Expr, ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
    // Compute the label before the mutable borrow so Case can pass it to emit_case.
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => lit_base(lit),

        TypedExprNode::Var(name) => match ctx.scopes.lookup(name) {
            Some(t) => t.clone(),
            None => return Err(InferError::UnboundVariable(name.clone())),
        },

        // Builtins with a polymorphic signature (shared type variables
        // across positions) live in the `OperatorSchemes` registry — at
        // each use site we freshen a copy. Currently only `LastOrDefault`
        // qualifies (`∀α β. ((α → β), β) → β`); the registry generalizes
        // as more polymorphic builtins land. All other builtins arrive
        // pre-stamped from lowering and just get converted in place.
        TypedExprNode::Builtin(b) => {
            if let Some(scheme) = ctx.schemes.builtin(*b) {
                scheme.instantiate(ctx.level)
            } else {
                ctx.normalize_annotation(&expr.ty)
            }
        }

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => emit_lambda(param, body, refinement, ctx)?,

        TypedExprNode::Apply { function, argument } => emit_apply(function, argument, ctx)?,

        TypedExprNode::BinOp { left, op, right } => emit_binop(left, *op, right, ctx)?,

        TypedExprNode::UnaryOp(op, inner) => {
            let inner_ty = emit_node(inner, ctx)?;
            // Clone the scheme out of the registry so we can pass `ctx`
            // mutably to apply_unary_scheme. Same pattern in emit_binop /
            // emit_aggregate.
            let scheme = ctx.schemes.unary(*op).clone();
            apply_unary_scheme(ctx, &scheme, &inner_ty)
                .map_err(|e| map_constrain_err(e, "UnaryOp"))?
        }

        TypedExprNode::Aggregate { input, kind } => emit_aggregate(input, *kind, ctx)?,

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::Tuple(elts) => {
            let mut fields = BTreeMap::new();
            for (i, e) in elts.iter_mut().enumerate() {
                fields.insert(FieldKey::Index(i), emit_node(e, ctx)?);
            }
            product(fields)
        }

        TypedExprNode::Record(fs) => {
            let mut fields = BTreeMap::new();
            for (n, e) in fs.iter_mut() {
                fields.insert(
                    FieldKey::Name(SmolStr::from(n.as_str())),
                    emit_node(e, ctx)?,
                );
            }
            product(fields)
        }

        TypedExprNode::Proj(key) => emit_proj(key, ctx)?,

        TypedExprNode::List(elts) => emit_list(elts, ctx)?,

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => emit_case(scrutinee.as_deref_mut(), branches, &label, ctx)?,

        TypedExprNode::VariantCtor { tag, payload } => emit_variant_ctor(tag, payload, ctx)?,

        TypedExprNode::Source(name) => match ctx.sources.get(name) {
            Some(t) => t.clone(),
            None => return Err(InferError::UnboundVariable(name.clone())),
        },

        TypedExprNode::Compose(elts) => emit_compose(elts, ctx)?,

        TypedExprNode::ExprStmt { expr: e, body } => {
            emit_node(e, ctx)?;
            emit_node(body, ctx)?
        }

        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so the type checker never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached inference: {:?}",
                expr.node
            )
        }

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => emit_loop(params, init_args, source, loop_body, ctx)?,

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // User-annotation check: constrain_subtype the inferred type to the user's
    // annotation. Annotation wins on success; on conflict we surface
    // AnnotationMismatch.
    if let Some(annotation) = expr.user_annotation.clone() {
        // The annotation may carry refinement predicates (e.g. a
        // filter-feed source annotation `Fun(Refinement(Hole, r), Hole)`
        // from `desugar_defers`). Now that refinements ride the lattice,
        // those predicates surface on the node's coalesced type and reach
        // the post-inference checks, so their expression trees must be
        // inferred in the current scope. (Lambda-node refinements are
        // handled in `emit_lambda`; this covers annotation-only ones.)
        emit_annotation_predicates(&annotation, ctx)?;
        let ann_simple = ctx.normalize_annotation(&annotation);
        // Snapshot the inferred type before the annotation bounds are added
        // so the error message shows what was actually inferred, not the
        // partially-modified state after a failed constrain_subtype.
        let inferred_ty = coalesce_for_error(&ty);
        if constrain_subtype(&ty, &ann_simple, &mut ctx.cache).is_err() {
            return Err(InferError::AnnotationMismatch {
                annotation: annotation.clone(),
                inferred: inferred_ty,
            });
        }
        // Annotation is the "canonical" type; record both directions
        // so coalesce produces the annotated shape.
        if constrain_subtype(&ann_simple, &ty, &mut ctx.cache).is_err() {
            return Err(InferError::AnnotationMismatch {
                annotation,
                inferred: inferred_ty,
            });
        }
    }

    // Write the emitted type straight into the node. It carries shared
    // `Infer` vars (via `Rc`), so constraints emitted by *later* nodes
    // accumulate into the same variables and are visible here at coalesce
    // time — no side table needed.
    expr.ty = ty.clone();
    Ok(ty)
}

fn lit_base(lit: &Lit) -> Type {
    match lit {
        Lit::Int(_) => prim(BaseType::Int),
        Lit::String(_) => prim(BaseType::String),
        Lit::Bool(_) => prim(BaseType::Bool),
        Lit::Unit => prim(BaseType::Unit),
    }
}

fn emit_lambda(
    param: &mut TypedBinding,
    body: &mut Expr,
    refinement: &mut Option<Refinement>,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    // Param type: convert any explicit annotation/Hole/Infer into a
    // the solver. A Hole turns into a fresh Var that will accumulate
    // bounds from body usage and call sites. Link `param.ty` to that
    // (shared) var so `coalesce_node` can resolve the binding slot in
    // place — the slot ends up carrying the body-usage restriction tags
    // but *not* the lambda's own refinement (that decorates only the
    // function-boundary domain in `expr.ty`).
    let param_simple = ctx.normalize_annotation(&param.ty);
    param.ty = param_simple.clone();
    let body_ty = {
        ctx.scopes.push_scope();
        ctx.scopes.bind(&param.name, param_simple.clone());
        let r = emit_node(body, ctx);
        ctx.scopes.pop_scope();
        r?
    };

    // Param user-annotation: two-way constrain_subtype == equality. This eagerly
    // detects conflicts (body constrains param to T, annotation says U ≠ T →
    // propagation fails immediately → AnnotationMismatch). One-way-only would
    // defer the conflict to coalesce as IncompatibleBounds/Unsupported.
    //
    // TODO (SOUNDNESS): two-way equality is unsound for annotations
    // containing union types (positive) or intersection types (negative) —
    // those should use one-way subtype constrain_subtype only. We avoid this
    // today because normalize_annotation converts Union → fresh_var, so union
    // annotations are unconstrained and equality degrades to trivially
    // satisfiable subtyping. Replace once let-polymorphism lands.
    if let Some(ann) = param.user_annotation.clone() {
        let ann_simple = ctx.normalize_annotation(&ann);
        let inferred_ty = coalesce_for_error(&param_simple);
        constrain_subtype(&param_simple, &ann_simple, &mut ctx.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty.clone(),
            }
        })?;
        constrain_subtype(&ann_simple, &param_simple, &mut ctx.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann,
                inferred: inferred_ty,
            }
        })?;
    }

    // Refinement: lift the lambda's *own* refinement into the inferred
    // domain so it rides the lattice as a restriction tag (replacing the
    // old `type_saturate` re-stitch). The AST node keeps its `refinement`
    // field — `lambda_elim` reads it from there, not from the type, so
    // there's no double-wrapping. We still walk the predicate so its inner
    // expressions get inferred types (otherwise downstream consumers see
    // `Hole`s inside the predicate body). The param is bound in scope under
    // the *unrefined* `param_simple`, so `Var(param)` body references stay
    // bare; restriction tags decorate only the function boundary.
    let domain_ty = match refinement {
        Some(r) => {
            let RefinementKind::Predicate(def) = &r.kind;
            // The predicate is compiled lazily inside an `Rc<RefCell<Expr>>`.
            emit_node(&mut def.borrow_mut(), ctx)?;
            Type::Refinement(Box::new(param_simple), r.clone())
        }
        None => param_simple,
    };

    Ok(fun(domain_ty, body_ty))
}

fn emit_apply(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    let arg_ty = emit_node(argument, ctx)?;
    let fn_ty = emit_node(function, ctx)?;
    let result = fresh_var(ctx.level);
    let expected = fun(arg_ty.clone(), result.clone());
    // Bidirectional Apply: constrain_subtype both directions so fn_ty's domain
    // and arg_ty share equality, matching HM's `constrain_equal` at
    // apply sites. Without this, a fresh Var on the function side (e.g.
    // a `Proj`'s synthesized `record_var`) only sees one polarity's
    // bounds and coalesces to a too-narrow type — closed `Tuple([α])`
    // instead of staying an open record `{0: α}` — even when the argument
    // is a richer record. This mirrors what HM achieves by unifying the
    // projection's domain with the argument's Infer var.
    //
    // TODO (SOUNDNESS): monomorphizing hack. Collapses polymorphism at
    // apply sites the same way HM does. The let-polymorphism work replaces
    // this with `Type::ForAll` + a monomorphization pass between `infer`
    // and `inline` (see
    // `docs/brainstorm/2026-05-06_simple_sub_prototype_status.md` §3.1).
    // Remove this line and the polarity fallback in
    // `simple_sub.rs::compact_go` together once the monomorphization pass
    // lands.
    constrain_subtype(&fn_ty, &expected, &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Apply"))?;
    constrain_subtype(&expected, &fn_ty, &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Apply"))?;
    Ok(result)
}

fn emit_binop(
    left: &mut Expr,
    op: BinOpKind,
    right: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    let left_ty = emit_node(left, ctx)?;
    let right_ty = emit_node(right, ctx)?;
    // Clone the scheme reference out of `ctx.schemes` so we can pass
    // `ctx` mutably to apply_binary_scheme. Schemes are PolyScheme
    // (Rc-shaped internals); cloning is cheap.
    let scheme = ctx.schemes.binop(op).clone();
    apply_binary_scheme(ctx, &scheme, &left_ty, &right_ty)
        .map_err(|e| map_constrain_err(e, "BinOp"))
}

fn emit_collection_union(
    exprs: &mut [Expr],
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    // CollectionUnion: the result is a collection (a function from index
    // to element) whose *domain* is tagged and whose *codomain* is the
    // join of branch codomains.
    //
    // The domain is a `Variant({_0: …, _1: …, …})` because the union
    // genuinely discriminates at runtime — `UnionOperator`
    // (`src/interpreter/operator_conversion.rs`) must know which operand
    // to dispatch to. Surface `a ++ b ++ c` flattens to a single N-ary
    // node at construction (see `TypedExpr::collection_union`), so we
    // emit one flat N-tag variant rather than the nested binary variants
    // of the pre-flattening design.
    //
    // The codomain is a single fresh var with every branch codomain as a
    // lower bound (a join), not a Variant. Once the union has dispatched
    // on the input tag, the runtime presents one combined output stream
    // regardless of which branch produced an element, so the codomain
    // carries no useful tag information. Encoding it as a join lets
    // `coalesce_compact` dedupe matching atoms (homogeneous unions like
    // `[1] ++ [2]` collapse to the common element type — consumers like
    // `Sum` then constrain the join `<: Int` directly) and surface
    // `IncompatibleBounds` on genuinely heterogeneous branches (the right
    // answer until traits / proper union elimination land).
    //
    // The domain tags are anonymous `FieldKey::Index` positions (the
    // dual of a tuple): operand `i` contributes tag `Index(i)`. These are
    // distinct from source-level `FieldKey::Name` tags, so a user variant
    // can never collide with a collection-union tag, and `Type::Display`
    // flattens all-`Index` variants back to a bare `A | B | C`.
    let cod_var = fresh_var(ctx.level);
    let mut tags = BTreeMap::new();
    for (i, e) in exprs.iter_mut().enumerate() {
        let ty = emit_node(e, ctx)?;
        let dom = fresh_var(ctx.level);
        let cod = fresh_var(ctx.level);
        constrain_subtype(&ty, &fun(dom.clone(), cod.clone()), &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "CollectionUnion element"))?;
        constrain_subtype(&cod, &cod_var, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "CollectionUnion codomain"))?;
        tags.insert(FieldKey::Index(i), dom);
    }
    let dom_variant = variant_type(tags);
    Ok(fun(dom_variant, cod_var))
}

fn emit_aggregate(
    input: &mut Expr,
    kind: AggregateKind,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    let input_ty = emit_node(input, ctx)?;
    // The scheme is the full operator type `(α → γ) → γ`, so apply it
    // directly to the input collection (function). The scheme's own domain
    // shape enforces that the input is a function and folds its codomain.
    let scheme = ctx.schemes.aggregate(kind).clone();
    apply_unary_scheme(ctx, &scheme, &input_ty).map_err(|e| map_constrain_err(e, "Aggregate"))
}

fn emit_let(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    let bound_ty = emit_node(bound_expr, ctx)?;
    // User annotation on binding site (e.g. `x: Int = expr`):
    if let Some(ann) = &binding.user_annotation {
        let ann_simple = ctx.normalize_annotation(ann);
        // Snapshot before adding annotation bounds for a clean inferred type in the error.
        let inferred_ty = coalesce_for_error(&bound_ty);
        constrain_subtype(&bound_ty, &ann_simple, &mut ctx.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty.clone(),
            }
        })?;
        constrain_subtype(&ann_simple, &bound_ty, &mut ctx.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty.clone(),
            }
        })?;
    }
    // Monomorphic let: bind name to bound_ty as-is. A future let-poly
    // extension will instead generalize bound_ty into a PolyScheme here.
    ctx.scopes.push_scope();
    ctx.scopes.bind(&binding.name, bound_ty.clone());
    let body_ty = emit_node(body, ctx);
    ctx.scopes.pop_scope();
    body_ty
}

fn emit_proj(key: &ProjKey, ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
    // Per-case rule: `Proj(k) : ∀α. {k: α, …} → α`. The input must have at
    // least field/position `k`; we record that as an upper bound on a fresh
    // domain var and rely on width-subtyping to admit any wider input.
    //
    // `ccl::Type` has no sparse-index product, so an *index* projection pads
    // to a dense `Tuple` of length `i+1` with fresh vars in positions `0..i`
    // and `α` at `i`; tuple width-subtyping (a longer tuple is a subtype)
    // then admits any tuple with at least `i+1` positions. A *named*
    // projection uses an open `Record{name: α}`; record width-subtyping
    // admits any record carrying that field.
    let alpha = fresh_var(ctx.level);
    let record_var = fresh_var(ctx.level);
    let requirement = match key {
        ProjKey::Index(i) => {
            let mut positions: Vec<Type> = (0..*i).map(|_| fresh_var(ctx.level)).collect();
            positions.push(alpha.clone());
            Type::Tuple(positions)
        }
        ProjKey::Field(name) => Type::Record(vec![(name.to_string(), alpha.clone())]),
    };
    constrain_subtype(&record_var, &requirement, &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Proj"))?;
    Ok(fun(record_var, alpha))
}

fn emit_list(elts: &mut [Expr], ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
    if elts.is_empty() {
        return Ok(fun(Type::UIntRange(0), prim(BaseType::Unit)));
    }
    // Element type: derive from the first; constrain_subtype remaining to it.
    let first_ty = emit_node(&mut elts[0], ctx)?;
    for rest in &mut elts[1..] {
        let r_ty = emit_node(rest, ctx)?;
        // Two-way constrain_subtype == equality. Mirrors the existing pass's
        // implicit assumption that list elements are homogeneous.
        constrain_subtype(&r_ty, &first_ty, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "List element"))?;
        constrain_subtype(&first_ty, &r_ty, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "List element"))?;
    }
    let n = elts.len();
    Ok(fun(Type::UIntRange(n), first_ty))
}

/// Emit constraints for a [`TypedExprNode::Case`] — the unified
/// logical/structural dispatch node.
///
/// When `scrutinee` is present, the branch patterns' tags form the expected
/// scrutinee `Variant({tag: αᵢ})`; width-subtyping enforces "scrutinee's
/// tags ⊆ branch tags", and each αᵢ (the per-tag narrowed payload) is
/// written straight into `Pattern::binding.ty` — coalesce resolves it in
/// place. Every branch's guard is constrained to `Bool` (a pattern-only
/// branch carries the literal-`true` guard), and all branch bodies are
/// mutually constrained to a single result type.
fn emit_case(
    scrutinee: Option<&mut Expr>,
    branches: &mut [Branch],
    label: &str,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    if branches.is_empty() {
        return Err(InferError::EmptyCase {
            at: label.to_string(),
        });
    }

    // Structural dispatch: constrain the scrutinee to the Variant of the
    // branch pattern tags, minting one payload var αᵢ per pattern branch and
    // writing it into the branch's binding slot (coalesce resolves it later).
    if let Some(scrut) = scrutinee {
        let scrut_ty = emit_node(scrut, ctx)?;
        let mut expected_tags: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for b in branches.iter_mut() {
            if let Some(p) = &mut b.pattern {
                let alpha = fresh_var(ctx.level);
                p.binding.ty = alpha.clone();
                expected_tags.insert(FieldKey::Name(SmolStr::from(p.tag.as_str())), alpha);
            }
        }
        let expected = variant_type(expected_tags);
        constrain_subtype(&scrut_ty, &expected, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Case scrutinee"))?;
    }

    let mut result_ty: Option<Type> = None;
    for b in branches.iter_mut() {
        // A pattern binds its payload (the var just written to `binding.ty`)
        // over the branch's guard and body.
        let pushed = b.pattern.is_some();
        if let Some(p) = &b.pattern {
            ctx.scopes.push_scope();
            ctx.scopes.bind(&p.binding.name, p.binding.ty.clone());
        }
        // Capture the body-emission result so we always pop the scope on
        // both the happy and error paths. Early-`?` would leak the scope.
        let branch_result: Result<Type, InferError> = (|| {
            let guard_ty = emit_node(&mut b.guard, ctx)?;
            let bool_ty = prim(BaseType::Bool);
            constrain_subtype(&guard_ty, &bool_ty, &mut ctx.cache)
                .map_err(|e| map_constrain_err(e, "Case guard"))?;
            constrain_subtype(&bool_ty, &guard_ty, &mut ctx.cache)
                .map_err(|e| map_constrain_err(e, "Case guard"))?;
            emit_node(&mut b.body, ctx)
        })();
        if pushed {
            ctx.scopes.pop_scope();
        }
        let body_ty = branch_result?;
        match &result_ty {
            None => result_ty = Some(body_ty),
            Some(prev) => {
                constrain_subtype(&body_ty, prev, &mut ctx.cache)
                    .map_err(|e| map_constrain_err(e, "Case arm"))?;
                constrain_subtype(prev, &body_ty, &mut ctx.cache)
                    .map_err(|e| map_constrain_err(e, "Case arm"))?;
            }
        }
    }
    Ok(result_ty.expect("non-empty branches"))
}

fn emit_variant_ctor(
    tag: &str,
    payload: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    let payload_ty = emit_node(payload, ctx)?;
    let mut tags = BTreeMap::new();
    tags.insert(FieldKey::Name(SmolStr::from(tag)), payload_ty);
    Ok(variant_type(tags))
}

fn emit_compose(elts: &mut [Expr], ctx: &mut SimpleSubContext) -> Result<Type, InferError> {
    assert!(elts.len() >= 2, "Compose requires at least two elements");
    let mut tys = Vec::with_capacity(elts.len());
    for e in elts.iter_mut() {
        tys.push(emit_node(e, ctx)?);
    }
    let first_dom = fresh_var(ctx.level);
    let mut prev_cod = fresh_var(ctx.level);
    constrain_subtype(
        &tys[0],
        &fun(first_dom.clone(), prev_cod.clone()),
        &mut ctx.cache,
    )
    .map_err(|e| map_constrain_err(e, "Compose[0]"))?;
    for (i, t) in tys.iter().enumerate().skip(1) {
        let d_i = fresh_var(ctx.level);
        let c_i = fresh_var(ctx.level);
        constrain_subtype(t, &fun(d_i.clone(), c_i.clone()), &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Compose[i]"))?;
        constrain_subtype(&prev_cod, &d_i, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, &format!("Compose[{i}]")))?;
        prev_cod = c_i;
    }
    Ok(fun(first_dom, prev_cod))
}

/// Emit Simple-sub constraints for a `Loop` node and return its outer type
/// `Fun(D, Record({step: σ, tap_k: τ_k}))`.
///
/// The Loop's typing rule (mirroring the paper's `App` shape — fresh
/// variables for each "guess" position, one-way `constrain_subtype` calls
/// throughout — see Parreaux 2020 Fig 9, p. 124:9):
///
/// - `source` is a stream `Fun(D, item)`; we mint fresh `D` and `item`
///   and constrain_subtype the inferred source type to fit.
/// - Each accumulator slot `params[i]` gets a fresh var `α_i`. The
///   `init_args[i]` value flows in as a lower bound: `init <: α_i`.
/// - `loop_body` is a Lambda whose input is `Tuple(α_0, …, α_{n-1}, item)`
///   and whose output is `Record({step: σ, tap_k: τ_k})`. We mint `σ`
///   and one `τ_k` per `body_taps` entry and constrain_subtype the inferred body
///   type against the expected shape.
/// - The recurrence wires the step output back to the accumulator slots:
///   single-acc → `σ <: α_0`; multi-acc → `σ <: Tuple(α_0, …, α_{n-1})`
///   (which depth-decomposes into `σ.i <: α_i`).
///
/// The accumulator vars are structurally shared across iterations by
/// construction — there's exactly one `α_i` per slot, and `init`, the
/// body's reads of `p.i`, and `σ` all flow into the same variable. No
/// separate "iterations agree" constraint is needed.
///
/// `params[i].name` is bound inside `loop_body` only via the body's own
/// let-chain (`let acc_i = p.i in …`), so we do not push the params
/// into `ctx.scopes` here.
fn emit_loop(
    params: &mut [TypedBinding],
    init_args: &mut [Expr],
    source: &mut Expr,
    loop_body: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Type, InferError> {
    debug_assert_eq!(
        params.len(),
        init_args.len(),
        "Loop: params and init_args must have equal length"
    );

    // Source: Fun(D, item).
    let d = fresh_var(ctx.level);
    let item = fresh_var(ctx.level);
    let s_ty = emit_node(source, ctx)?;
    constrain_subtype(&s_ty, &fun(d.clone(), item.clone()), &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Loop source"))?;

    // Accumulator slots: one fresh α per `params[i]`; `init_args[i] <: α_i`.
    let alphas: Vec<Type> = (0..params.len()).map(|_| fresh_var(ctx.level)).collect();
    for (i, init) in init_args.iter_mut().enumerate() {
        let init_ty = emit_node(init, ctx)?;
        constrain_subtype(&init_ty, &alphas[i], &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Loop init"))?;
    }

    // Body codomain: Record carrying at least `{step: σ}`.  Tap fields
    // (`to_<defer>`) are no longer named at this level — `desugar_defers`
    // runs before inference and folds them into the body's literal Record;
    // we let the actual body record flow into `actual_cod` as a lower
    // bound and use that as the Loop's outer codomain, so downstream
    // projections on `to_<defer>` still see the right fields.
    let sigma = fresh_var(ctx.level);
    let actual_cod = fresh_var(ctx.level);
    let mut cod_fields: BTreeMap<FieldKey, Type> = BTreeMap::new();
    cod_fields.insert(FieldKey::Name(SmolStr::from("step")), sigma.clone());
    let step_record = product(cod_fields);

    // Body domain: Tuple(α_0, …, α_{n-1}, item).
    let mut dom_fields: BTreeMap<FieldKey, Type> = BTreeMap::new();
    for (i, alpha) in alphas.iter().enumerate() {
        dom_fields.insert(FieldKey::Index(i), alpha.clone());
    }
    dom_fields.insert(FieldKey::Index(alphas.len()), item.clone());
    let body_dom = product(dom_fields);

    let body_ty = emit_node(loop_body, ctx)?;
    constrain_subtype(&body_ty, &fun(body_dom, actual_cod.clone()), &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Loop body"))?;
    // The body's codomain must at least carry `step: σ`.
    constrain_subtype(&actual_cod, &step_record, &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Loop body step"))?;

    // Recurrence: σ <: α_0 (single) or σ <: Tuple(α_0, …, α_{n-1}) (multi).
    if alphas.len() == 1 {
        constrain_subtype(&sigma, &alphas[0], &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Loop recurrence"))?;
    } else {
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for (i, alpha) in alphas.iter().enumerate() {
            tup.insert(FieldKey::Index(i), alpha.clone());
        }
        constrain_subtype(&sigma, &product(tup), &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Loop recurrence"))?;
    }

    // Write each accumulator var straight into `Loop::params[i].ty`;
    // coalesce resolves it in place. (The binding lives on `TypedBinding`,
    // not an `Expr`, so the tree walk wouldn't otherwise reach it.)
    for (binding, alpha) in params.iter_mut().zip(alphas) {
        binding.ty = alpha;
    }

    Ok(fun(d, actual_cod))
}

// ---------------------------------------------------------------------------
// Coalesce pass (Step 7e)
// ---------------------------------------------------------------------------
//
// lattice-blind stitching that used to live here (Refinement Propagation,
// Let Binding Resolution, the `dedup_union` helper, `propagate_var_ty`, and
// the CollectionUnion direct build) now lives in [`crate::ccl::type_saturate`],
// invoked by [`infer`] after `coalesce_pass`.

/// Returns `true` for expression labels that are structurally significant
/// (let bindings, lambdas, comprehensions) and worth showing as error context.
/// Filters out bare variable names and simple expressions that add noise.
///
/// TODO: revisit after the ariadne error-reporting changes land. Coalesce
/// error context is currently stringly-typed (we stringify the expression
/// via `symbolic` and then pattern-match on the string here); once errors
/// carry `Span`s and structured locations, contexts should be `&Expr`
/// (or a richer node-ref type) and this string-shaped filter goes away.
fn is_significant_context(label: &str) -> bool {
    label.contains("let ") || label.contains("λ ") || label.contains('\n')
}

/// Push `new_err` onto `errors`, deduplicating [`InferError::IncompatibleBounds`].
///
/// If an existing error has the same `(polarity, conflicting)` key, `label` is
/// appended to its context vec (when it passes [`is_significant_context`])
/// instead of pushing a duplicate.  All other error kinds are pushed as-is.
fn push_coalesce_err(errors: &mut Vec<InferError>, new_err: InferError, label: String) {
    if let InferError::IncompatibleBounds {
        polarity: p,
        conflicting: ref c,
        ..
    } = new_err
    {
        let key = (p, c.clone());
        let existing = errors.iter_mut().find_map(|e| {
            if let InferError::IncompatibleBounds {
                polarity,
                conflicting,
                context,
                ..
            } = e
                && *polarity == key.0
                && conflicting == &key.1
            {
                return Some(context);
            }
            None
        });
        if let Some(ctx_vec) = existing {
            if is_significant_context(&label) {
                ctx_vec.push(label);
            }
        } else {
            errors.push(new_err);
        }
    } else {
        errors.push(new_err);
    }
}

fn coalesce_pass(expr: &mut Expr) -> Vec<InferError> {
    let mut errors = Vec::new();
    coalesce_node(expr, &mut errors);
    errors
}

/// Resolve a type that may contain inference variables into a concrete
/// `Type`, via the compact → simplify → coalesce pipeline.
fn resolve_var_type(ty: &Type) -> Result<Type, CoalesceError> {
    coalesce_compact(&simplify_type(compact_type(ty)))
}

fn coalesce_node(expr: &mut Expr, errors: &mut Vec<InferError>) {
    // Recurse into sub-expressions first so child types are settled
    // before we coalesce this node's (which may reference them).
    match &mut expr.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            coalesce_node(function, errors);
            coalesce_node(argument, errors);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            coalesce_node(left, errors);
            coalesce_node(right, errors);
        }
        TypedExprNode::UnaryOp(_, inner) => coalesce_node(inner, errors),
        TypedExprNode::Lambda {
            param: _,
            body,
            refinement,
        } => {
            coalesce_node(body, errors);
            // Refinement predicate is itself an Expr that was inferred
            // by emit_lambda. Walk into it so its sub-trees get their
            // expr.ty slots filled — otherwise downstream code (and
            // structural equality for tests) sees a tree of Holes
            // inside the refinement's RefCell<Expr>.
            if let Some(r) = refinement {
                let RefinementKind::Predicate(def) = &r.kind;
                if let Ok(mut pred) = def.try_borrow_mut() {
                    coalesce_node(&mut pred, errors);
                }
            }
            // `param.ty` is resolved from the lambda's coalesced domain in
            // the end-of-function block (it can't be coalesced standalone:
            // body-usage restriction tags are negative-polarity upper-bound
            // facts that only materialize in the contravariant domain
            // position of `expr.ty`).
        }
        TypedExprNode::Aggregate { input, .. } => coalesce_node(input, errors),
        TypedExprNode::Let {
            binding: _,
            bound_expr,
            body,
        } => {
            coalesce_node(bound_expr, errors);
            coalesce_node(body, errors);
        }
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::Compose(elts)
        | TypedExprNode::CollectionUnion(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, errors);
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                coalesce_node(e, errors);
            }
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                coalesce_node(s, errors);
            }
            for b in branches.iter_mut() {
                coalesce_node(&mut b.guard, errors);
                coalesce_node(&mut b.body, errors);
            }
            // Resolve each pattern's payload-binding type in place.
            // `emit_case` wrote the per-tag narrowed var into
            // `Pattern::binding.ty`; run it through the same pipeline used
            // for `expr.ty` so it ends up concrete. `type_saturate` then has
            // a real type to bind when it pushes the branch scope.
            for b in branches.iter_mut() {
                let Some(p) = &mut b.pattern else { continue };
                match resolve_var_type(&p.binding.ty) {
                    Ok(ty) => p.binding.ty = ty,
                    Err(err) => {
                        let label = format!("Case pattern `.{}` payload", p.tag);
                        push_coalesce_err(errors, map_coalesce_err(err, &label), label);
                    }
                }
            }
        }
        TypedExprNode::VariantCtor { payload, .. } => {
            coalesce_node(payload, errors);
        }
        TypedExprNode::ExprStmt { expr: e, body } => {
            coalesce_node(e, errors);
            coalesce_node(body, errors);
        }
        // Defer/Feed/Define are eliminated by `desugar_defers` before
        // inference runs, so coalesce never sees them.
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached coalesce: {:?}",
                expr.node
            )
        }
        TypedExprNode::Loop {
            params,
            source,
            init_args,
            loop_body,
            ..
        } => {
            coalesce_node(source, errors);
            for a in init_args.iter_mut() {
                coalesce_node(a, errors);
            }
            coalesce_node(loop_body, errors);
            // Resolve each accumulator-slot type in place. `emit_loop`
            // wrote the slot var into `params[i].ty`; run it through the
            // same pipeline used for `expr.ty` so it ends up concrete.
            for binding in params.iter_mut() {
                match resolve_var_type(&binding.ty) {
                    Ok(ty) => binding.ty = ty,
                    Err(err) => {
                        let label = "Loop param".to_string();
                        push_coalesce_err(errors, map_coalesce_err(err, &label), label);
                    }
                }
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }

    // Resolve this node's type in place. `emit_node` wrote the emitted
    // type (carrying inference vars) into `expr.ty`; run it through the
    // compact → simplify → coalesce pipeline to materialize a concrete
    // `Type`.
    //
    // Refinements now ride the lattice as restriction tags, so a refined
    // domain coalesces straight onto `expr.ty` here (no `type_saturate`
    // re-stitch). `lambda_elim` still reads the lambda's own refinement
    // off the AST node — it is duplicated there deliberately, and the
    // tag's id-equality dedups any structural overlap downstream.
    let label = symbolic(expr);
    match resolve_var_type(&expr.ty) {
        Ok(ty) => expr.ty = ty,
        Err(err) => push_coalesce_err(errors, map_coalesce_err(err, &label), label),
    }

    // A lambda's param binding slot mirrors its coalesced domain, minus the
    // lambda's *own* refinement layer (that decorates only the function
    // boundary; `lambda_elim` re-wraps it from the AST node). Deriving it
    // from the resolved domain — rather than coalescing the slot var
    // standalone — is what preserves body-usage restriction tags, which are
    // negative-polarity facts visible only in the contravariant domain.
    if let TypedExprNode::Lambda {
        param, refinement, ..
    } = &mut expr.node
        && let Type::Fun(dom, _) = &expr.ty
    {
        let mut d = (**dom).clone();
        if let Some(r) = refinement {
            d = strip_refinement_id(d, r.id);
        }
        param.ty = d;
    }

    // Resolve any refinement predicates that ride on this node's type but
    // aren't reached through the main expression tree — e.g. a filter-feed
    // source annotation `Fun(Refinement(_, r), _)`. Their expression trees
    // were emitted (in `emit_annotation_predicates`); resolve their var
    // slots so the post-inference checks see concrete types. `try_borrow_mut`
    // breaks the cycle when a predicate's own type slot carries the same
    // refinement.
    coalesce_type_predicates(&expr.ty, errors);
}

/// Coalesce refinement predicates embedded anywhere in `ty` (see the call
/// site in `coalesce_node`). Idempotent for predicates already resolved by
/// the `Lambda` arm.
fn coalesce_type_predicates(ty: &Type, errors: &mut Vec<InferError>) {
    match ty {
        Type::Refinement(inner, r) => {
            let RefinementKind::Predicate(def) = &r.kind;
            if let Ok(mut pred) = def.try_borrow_mut() {
                coalesce_node(&mut pred, errors);
            }
            coalesce_type_predicates(inner, errors);
        }
        Type::Fun(d, c) => {
            coalesce_type_predicates(d, errors);
            coalesce_type_predicates(c, errors);
        }
        Type::Tuple(ts) => ts.iter().for_each(|t| coalesce_type_predicates(t, errors)),
        Type::Record(fs) => fs
            .iter()
            .for_each(|(_, t)| coalesce_type_predicates(t, errors)),
        Type::Variant(tags) => tags
            .iter()
            .for_each(|(_, t)| coalesce_type_predicates(t, errors)),
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {}
    }
}

/// Remove the single [`Type::Refinement`] layer whose tag id matches `id`
/// (if present), preserving the relative order of the other layers. Tags
/// may coalesce in any order, so we can't assume a fixed position.
fn strip_refinement_id(ty: Type, id: crate::ccl::RefinementId) -> Type {
    let mut layers = Vec::new();
    let mut cur = ty;
    while let Type::Refinement(inner, r) = cur {
        if r.id != id {
            layers.push(r);
        }
        cur = *inner;
    }
    layers
        .into_iter()
        .rev()
        .fold(cur, |acc, r| Type::Refinement(Box::new(acc), r))
}

// ---------------------------------------------------------------------------
// Smoke tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::TypedExpr;
    use crate::ccl::infer::TypeInferenceContext;

    fn lit_int(n: i64) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::Int(n)))
    }

    fn lit_string(s: &str) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::String(s.into())))
    }

    fn run_simple_sub(expr: &mut Expr) -> Result<Type, Vec<InferError>> {
        let mut ctx = TypeInferenceContext::new();
        crate::ccl::infer::infer(expr, &mut ctx)
    }

    #[test]
    fn smoke_lambda_identity_inferred_int() {
        // λx. x applied to 42 → Int
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".to_string(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".to_string()))),
            refinement: None,
        });
        let app = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(lam),
            argument: Box::new(lit_int(42)),
        });
        let mut e = app;
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    #[test]
    fn smoke_tuple_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Tuple(vec![lit_int(1), lit_string("x")]));
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    #[test]
    fn smoke_record_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Record(vec![
            ("a".to_string(), lit_int(1)),
            ("b".to_string(), lit_string("x")),
        ]));
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Record(vec![
                ("a".to_string(), Type::Base(BaseType::Int)),
                ("b".to_string(), Type::Base(BaseType::String)),
            ])
        );
    }

    #[test]
    fn smoke_let_monomorphic() {
        // let x = 42 in x → Int
        let mut e = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".to_string(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(lit_int(42)),
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".to_string()))),
        });
        let ty = run_simple_sub(&mut e).expect("inference succeeds");
        assert_eq!(ty, Type::Base(BaseType::Int));
    }

    /// TRIPWIRE — documents a known soundness gap, NOT desired behavior.
    ///
    /// `Max` has scheme `∀α γ. (α ⇒ γ) ⇒ γ` (see `aggregate_max`), so its
    /// codomain `γ` is wholly unconstrained and it type-checks over *any*
    /// codomain. But `Max` is only *defined* at eval for orderable base types
    /// (`Int`/`UInt`/`String` — see merge/identity in `ccl/mod.rs`). So `max`
    /// over a function with a tuple codomain type-checks and infers
    /// `Tuple([Int, Int])`, even though it has no defined runtime behavior.
    ///
    /// `Max` *should* require an orderable codomain. The correct long-term fix
    /// is a first-class comparability bound, which arrives with traits — there
    /// is no value in a stopgap validation now. When that lands, inference will
    /// start rejecting this program and this test will fail loudly; whoever
    /// lands traits should flip it to assert rejection.
    ///
    /// Tracked by `type-checker-traits-comparability` (P3) in the project vault.
    #[test]
    fn max_over_non_orderable_codomain_is_unsoundly_accepted() {
        // Aggregate { input: λx → (1, 2), kind: Max }
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".to_string(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Tuple(vec![
                lit_int(1),
                lit_int(2),
            ]))),
            refinement: None,
        });
        let mut e = TypedExpr::aggregate(lam, AggregateKind::Max);
        let ty = run_simple_sub(&mut e).expect("inference succeeds (the bug under test)");
        // Buggy current behavior: the non-orderable tuple codomain is accepted.
        assert_eq!(
            ty,
            Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)])
        );
    }
}

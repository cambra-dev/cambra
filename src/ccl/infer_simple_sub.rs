//! Simple-sub-based type inference.
//!
//! The canonical type inference implementation, invoked via
//! [`crate::ccl::infer::infer`].
//!
//! # Design (Stage 1, monomorphic let)
//!
//! Two passes over the expression tree:
//!
//! 1. **Constraint emission**: walk the tree, emit `constrain_subtype` calls
//!    against [`SimpleType`] graphs, record each node's `SimpleType` in
//!    a side table keyed by node pointer. Refinements stay on the AST
//!    node (`Expr::Lambda::refinement`) and are *not* part of the
//!    structural lattice (see plan R1); `type_saturate` and `lambda_elim`
//!    read them from the AST directly.
//! 2. **Coalesce + write-back**: walk the tree again, look up each
//!    node's `SimpleType`, run [`coalesce_compact`](crate::ccl::simple_sub::coalesce_compact),
//!    and write into `expr.ty`.
//!
//! # Polymorphism
//!
//! No let-generalization (`let` is monomorphic). The
//! [`OperatorSchemes`] registry contains [`PolyScheme`]s only for the
//! handful of operator/projection cases that are inherently polymorphic
//! (`Compare : ∀α. α → α → Bool`, `Max : ∀α. α → α`, etc.). Each scheme
//! is `instantiate`d at every use site, minting fresh vars per use.
//!
//! Most `Builtin` nodes are introduced post-inference by
//! `lambda_elim`/`join_plan` with their type pre-stamped on the node, and
//! inference just rubber-stamps them. The exceptions are polymorphic
//! builtins introduced pre-inference (e.g. `LastOrDefault` from
//! `lower_mutation_loop`); those have entries in [`OperatorSchemes`] and
//! are freshened at each use site like any other scheme.

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::infer::InferError;
use crate::ccl::simple_sub::{
    CoalesceError, ConstrainCache, ConstrainError, FieldKey, Level, PolyScheme, SimpleType,
    coalesce_compact, compact_type, constrain_subtype, fresh_var, fun, prim, simplify_type,
};
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    AggregateKind, BaseType, BinOpKind, Branch, Builtin, Expr, Lit, ProjKey, Refinement,
    RefinementKind, Type, TypedBinding, TypedExprNode, UnaryOpKind,
};
use crate::util::ScopeStack;

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
    /// `Int → Int` — applied to the codomain of the input function.
    aggregate_sum: PolyScheme,
    /// `∀α. α → α` — applied to the codomain of the input function.
    aggregate_max: PolyScheme,
    /// `∀α β. ((α → β), β) → β` — extract the last value from a
    /// function-typed stream, falling back to the default scalar when the
    /// stream's domain is empty. Polymorphic in both the stream domain
    /// (`α`) and the shared codomain/default type (`β`); inline construction
    /// is required because both vars are shared across positions, which
    /// `type_to_simple` (one fresh var per `Hole`) can't express.
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
        let arithmetic = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(Rc::clone(&alpha), fun(Rc::clone(&alpha), alpha)),
        );

        // Compare: ∀α. α → α → Bool
        let alpha = fresh_var(BODY_LEVEL);
        let compare = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(Rc::clone(&alpha), fun(alpha, prim(BaseType::Bool))),
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

        // Sum: Int → Int (codomain → result)
        let aggregate_sum = PolyScheme::mono(fun(prim(BaseType::Int), prim(BaseType::Int)));

        // Max: ∀α. α → α
        let alpha = fresh_var(BODY_LEVEL);
        let aggregate_max = PolyScheme::poly(SCHEME_LEVEL, fun(Rc::clone(&alpha), alpha));

        // LastOrDefault: ∀α β. ((α → β), β) → β
        // Inline-built (not via `type_to_simple`) so the codomain of the
        // stream and the default share one variable `β`.
        let alpha = fresh_var(BODY_LEVEL);
        let beta = fresh_var(BODY_LEVEL);
        let mut tup: BTreeMap<FieldKey, Rc<SimpleType>> = BTreeMap::new();
        tup.insert(FieldKey::Index(0), fun(Rc::clone(&alpha), Rc::clone(&beta)));
        tup.insert(FieldKey::Index(1), Rc::clone(&beta));
        let last_or_default =
            PolyScheme::poly(SCHEME_LEVEL, fun(Rc::new(SimpleType::Record(tup)), beta));

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
// SimpleSubContext + side table (Step 7c)
// ---------------------------------------------------------------------------

/// Pointer-keyed identifier for an AST node, used as the [`SideTable`] key.
///
/// Soundness invariant: the constraint emitter never moves nodes during
/// the walk (it only mutates `expr.ty` post-coalesce). The pointer
/// captured at recording time stays valid through the second pass.
/// If a future refactor starts replacing nodes mid-inference, this keying
/// silently breaks.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct NodeId(usize);

impl NodeId {
    fn of(e: &Expr) -> Self {
        NodeId(e as *const Expr as usize)
    }
}

/// Per-node SimpleType recorded during constraint emission and consumed
/// by the coalesce pass.
type SideTable = HashMap<NodeId, Rc<SimpleType>>;

/// Inference state for the simple-sub path.
///
/// Mirrors fields on [`crate::ccl::infer::TypeInferenceContext`] but
/// uses [`SimpleType`] internally instead of routing through the
/// HM-style unification table.
struct SimpleSubContext {
    /// Lexical scope: name → SimpleType for in-scope variables and
    /// let-bound names. Stage 1 stores monotypes; Stage 2's let-poly
    /// will widen this to `PolyScheme` schemes.
    scopes: ScopeStack<Rc<SimpleType>>,
    /// Externally-registered data sources (set by
    /// `TypeInferenceContext::register_source_type`). Stored as
    /// [`SimpleType`] for the simple-sub solver.
    sources: HashMap<String, Rc<SimpleType>>,
    /// Constraint cycle cache, shared across one full inference pass.
    cache: ConstrainCache,
    /// Side table: each node's inferred SimpleType, populated as the
    /// emitter walks down and consumed by the coalesce pass.
    side: SideTable,
    /// Per-Loop accumulator-slot SimpleTypes, in `params` order.
    ///
    /// `emit_loop` mints one α (type) per accumulator and constrains it
    /// via the init / recurrence / body-domain edges; the coalesce pass
    /// reads these out to fill in `Loop::params[i].ty`, which `lambda_elim`
    /// and `check_fully_typed` require be concrete (no `Type::Hole`).
    loop_param_tys: HashMap<NodeId, Vec<Rc<SimpleType>>>,
    /// Operator/projection scheme registry.
    schemes: OperatorSchemes,
    /// Current polymorphism level. Stage 1 holds it at 0 (no `let` bumps);
    /// the field is threaded through so Stage 2's let-poly extension drops
    /// in without restructuring.
    level: Level,
}

impl SimpleSubContext {
    fn new(sources: HashMap<String, Rc<SimpleType>>) -> Self {
        Self {
            scopes: ScopeStack::default(),
            sources,
            cache: ConstrainCache::new(),
            side: HashMap::new(),
            loop_param_tys: HashMap::new(),
            schemes: OperatorSchemes::new(),
            level: 0,
        }
    }

    /// Convert a public `ccl::Type` into a `SimpleType` for use as a
    /// constraint-graph type. Holes and Infer slots become fresh Vars
    /// at the current level (no shared identity across calls — good
    /// enough for Stage 1 since Builtin Infer-IDs are never depended on
    /// across nodes inside the simple-sub path).
    fn type_to_simple(&self, ty: &Type) -> Rc<SimpleType> {
        match ty {
            Type::Base(b) => prim(b.clone()),
            Type::UIntRange(n) => Rc::new(SimpleType::UIntRange(*n)),
            Type::DataSource(name) => Rc::new(SimpleType::Source(SmolStr::from(name))),
            Type::Fun(d, c) => fun(self.type_to_simple(d), self.type_to_simple(c)),
            Type::Tuple(ts) => {
                let mut m = BTreeMap::new();
                for (i, t) in ts.iter().enumerate() {
                    m.insert(FieldKey::Index(i), self.type_to_simple(t));
                }
                Rc::new(SimpleType::Record(m))
            }
            Type::Record(fs) => {
                let mut m = BTreeMap::new();
                for (n, t) in fs {
                    m.insert(FieldKey::Name(SmolStr::from(n)), self.type_to_simple(t));
                }
                Rc::new(SimpleType::Record(m))
            }
            Type::PartialTuple(es) => {
                // Partial tuples enter the solver as records with only
                // the listed Index keys. Width-subtyping then admits
                // any closed tuple with at least these positions.
                let mut m = BTreeMap::new();
                for (i, t) in es {
                    m.insert(FieldKey::Index(*i), self.type_to_simple(t));
                }
                Rc::new(SimpleType::Record(m))
            }
            Type::PartialRecord(es) => {
                let mut m = BTreeMap::new();
                for (n, t) in es {
                    m.insert(FieldKey::Name(SmolStr::from(n)), self.type_to_simple(t));
                }
                Rc::new(SimpleType::Record(m))
            }
            Type::Refinement(inner, _) => {
                // Refinements are sidecared, not lifted into SimpleType.
                // The wrapper is stripped here; coalesce wraps it back
                // on output if the corresponding node is in the
                // refinement context.
                self.type_to_simple(inner)
            }
            Type::Union(_) => {
                // Stage 1 rejects unions when emitted; an annotated
                // union still becomes a fresh var here so the constraint
                // emitter can continue past it (the unsupported error is
                // surfaced at coalesce time if the variable doesn't get
                // pinned to a single concrete type).
                fresh_var(self.level)
            }
            Type::Hole | Type::Infer(_) => fresh_var(self.level),
        }
    }
}

/// Apply a binary scheme: instantiate, build the expected call shape,
/// constrain_subtype. Returns the fresh result variable.
fn apply_binary_scheme(
    ctx: &mut SimpleSubContext,
    scheme: &PolyScheme,
    left: &Rc<SimpleType>,
    right: &Rc<SimpleType>,
) -> Result<Rc<SimpleType>, ConstrainError> {
    let body = scheme.instantiate(ctx.level);
    let result = fresh_var(ctx.level);
    let expected = fun(Rc::clone(left), fun(Rc::clone(right), Rc::clone(&result)));
    constrain_subtype(&body, &expected, &mut ctx.cache)?;
    Ok(result)
}

/// Apply a unary scheme. Used for UnaryOp and Aggregate (latter passes
/// the codomain of its function-typed input as the operand).
fn apply_unary_scheme(
    ctx: &mut SimpleSubContext,
    scheme: &PolyScheme,
    operand: &Rc<SimpleType>,
) -> Result<Rc<SimpleType>, ConstrainError> {
    let body = scheme.instantiate(ctx.level);
    let result = fresh_var(ctx.level);
    let expected = fun(Rc::clone(operand), Rc::clone(&result));
    constrain_subtype(&body, &expected, &mut ctx.cache)?;
    Ok(result)
}

/// Coalesce a [`SimpleType`] to its public [`Type`] representation for use in
/// error messages. Falls back to [`Type::Hole`] if coalesce fails (which can
/// happen for types with incompatible bounds that triggered the error).
fn simple_to_type(ty: &Rc<SimpleType>) -> Type {
    let graph = compact_type(ty);
    coalesce_compact(&graph).unwrap_or(Type::Hole)
}

/// Map a [`ConstrainError`] onto the public [`InferError`] enum.
fn map_constrain_err(err: ConstrainError, ctx_label: &str) -> InferError {
    match err {
        ConstrainError::Mismatch { lhs, rhs } => {
            let lhs_ty = simple_to_type(&lhs);
            let rhs_ty = simple_to_type(&rhs);
            // `constrain_subtype(lhs, rhs)` means `lhs <: rhs`. If rhs is a function
            // and lhs is not, the caller passed a non-function where a function
            // was expected (e.g. applying a non-function at an Apply site).
            if matches!(rhs.as_ref(), SimpleType::Fun(..))
                && !matches!(lhs.as_ref(), SimpleType::Fun(..))
            {
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
            type_a: simple_to_type(&in_type),
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
            "recursive type at {}: {} (Stage 1 forbids residual μ-types)",
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
/// converted into [`SimpleType`] up front.
pub fn infer(expr: &mut Expr, sources: &HashMap<String, Type>) -> Result<Type, Vec<InferError>> {
    // Convert source registry once; reuse across all node emissions.
    let mut sub_ctx = {
        let pre = SimpleSubContext::new(HashMap::new());
        let translated: HashMap<String, Rc<SimpleType>> = sources
            .iter()
            .map(|(k, v)| (k.clone(), pre.type_to_simple(v)))
            .collect();
        SimpleSubContext::new(translated)
    };

    // Pass 1: emit constraints.
    emit_node(expr, &mut sub_ctx).map_err(|e| vec![e])?;

    // Pass 2: coalesce SimpleType per node and write into expr.ty.
    let errors = coalesce_pass(expr, &sub_ctx);
    if !errors.is_empty() {
        return Err(errors);
    }
    // Pass 3: saturate refinement/Union shapes that `SimpleType` cannot
    // carry, fixing up the four kinds of nodes affected (Refinement
    // Propagation, Let Binding Resolution, CollectionUnion direct-build).
    // See `type_saturate` for the rule set.
    crate::ccl::type_saturate::saturate(expr);
    Ok(expr.ty.clone())
}

// ---------------------------------------------------------------------------
// Constraint emitter (Step 7d)
// ---------------------------------------------------------------------------

/// Walk one expression node, emit constraints for it, record its
/// SimpleType in `ctx.side`, and return the SimpleType. Sub-expressions
/// recurse; their SimpleTypes are recorded too.
fn emit_node(expr: &mut Expr, ctx: &mut SimpleSubContext) -> Result<Rc<SimpleType>, InferError> {
    let id = NodeId::of(expr);
    // Compute the label before the mutable borrow so Case can pass it to emit_case.
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => lit_simple(lit),

        TypedExprNode::Var(name) => match ctx.scopes.lookup(name) {
            Some(t) => Rc::clone(t),
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
                ctx.type_to_simple(&expr.ty)
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
            Rc::new(SimpleType::Record(fields))
        }

        TypedExprNode::Record(fs) => {
            let mut fields = BTreeMap::new();
            for (n, e) in fs.iter_mut() {
                fields.insert(
                    FieldKey::Name(SmolStr::from(n.as_str())),
                    emit_node(e, ctx)?,
                );
            }
            Rc::new(SimpleType::Record(fields))
        }

        TypedExprNode::Proj(key) => emit_proj(key, ctx)?,

        TypedExprNode::List(elts) => emit_list(elts, ctx)?,

        TypedExprNode::Case { branches } => emit_case(branches, &label, ctx)?,

        TypedExprNode::Source(name) => match ctx.sources.get(name) {
            Some(t) => Rc::clone(t),
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
        } => emit_loop(id, params, init_args, source, loop_body, ctx)?,

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // User-annotation check: constrain_subtype the inferred type to the user's
    // annotation. Annotation wins on success; on conflict we surface
    // AnnotationMismatch.
    if let Some(annotation) = expr.user_annotation.clone() {
        let ann_simple = ctx.type_to_simple(&annotation);
        // Snapshot the inferred type before the annotation bounds are added
        // so the error message shows what was actually inferred, not the
        // partially-modified state after a failed constrain_subtype.
        let inferred_ty = simple_to_type(&ty);
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

    ctx.side.insert(id, Rc::clone(&ty));
    Ok(ty)
}

fn lit_simple(lit: &Lit) -> Rc<SimpleType> {
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
) -> Result<Rc<SimpleType>, InferError> {
    // Param type: convert any explicit annotation/Hole/Infer into a
    // SimpleType. A Hole turns into a fresh Var that will accumulate
    // bounds from body usage and call sites.
    let param_simple = ctx.type_to_simple(&param.ty);
    let body_ty = {
        ctx.scopes.push_scope();
        ctx.scopes.bind(&param.name, Rc::clone(&param_simple));
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
    // those should use one-way subtype constrain_subtype only. Stage 1 avoids this
    // because type_to_simple converts Union → fresh_var, so union
    // annotations are unconstrained and equality degrades to trivially
    // satisfiable subtyping. Replace in Stage 2.
    if let Some(ann) = param.user_annotation.clone() {
        let ann_simple = ctx.type_to_simple(&ann);
        let inferred_ty = simple_to_type(&param_simple);
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

    // Refinement: not lifted into SimpleType and not into the inferred
    // function type. The refinement metadata lives on the AST node;
    // `type_saturate` and `lambda_elim` read it from there. We still
    // need to walk the refinement's predicate so its inner expressions
    // get inferred types (otherwise downstream consumers see `Hole`s
    // inside the predicate body).
    if let Some(r) = refinement {
        let RefinementKind::Predicate(def) = &r.kind;
        // The predicate is compiled lazily inside an `Rc<RefCell<Expr>>`.
        emit_node(&mut def.borrow_mut(), ctx)?;
    }

    Ok(fun(param_simple, body_ty))
}

fn emit_apply(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    let arg_ty = emit_node(argument, ctx)?;
    let fn_ty = emit_node(function, ctx)?;
    let result = fresh_var(ctx.level);
    let expected = fun(Rc::clone(&arg_ty), Rc::clone(&result));
    // Bidirectional Apply: constrain_subtype both directions so fn_ty's domain
    // and arg_ty share equality, matching HM's `constrain_equal` at
    // apply sites. Without this, a fresh Var on the function side (e.g.
    // a `Proj`'s synthesized `record_var`) only sees one polarity's
    // bounds and coalesces to a too-narrow type — closed `Tuple([α])`
    // instead of `PartialTuple([(0, α)])` — even when the argument is
    // a richer record. This mirrors what HM achieves by unifying the
    // projection's domain with the argument's Infer var.
    //
    // TODO (SOUNDNESS): monomorphizing hack. Collapses polymorphism at
    // apply sites the same way HM does. Stage 2 prep replaces this with
    // `Type::ForAll` + a monomorphization pass between `infer` and
    // `inline` (see
    // `docs/brainstorm/2026-05-06_simple_sub_prototype_status.md` §3.1
    // "Deferred to Stage 2 prep"). Remove this line and the polarity
    // fallback in `simple_sub.rs::compact_go` together once the
    // monomorphization pass lands.
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
) -> Result<Rc<SimpleType>, InferError> {
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
) -> Result<Rc<SimpleType>, InferError> {
    // CollectionUnion: structural, can't be a scheme. Compute domain
    // union and dedup-union of codomains directly. For Stage 1 we
    // approximate with fresh vars; full expressivity returns once
    // Stage 2's variants land.

    // Result domain: a fresh var that's a supertype of both — can't
    // express union directly (Stage 2 work), so we leave it open.
    let result_dom = fresh_var(ctx.level);

    // Result codomain: similarly open. Today's dedup logic doesn't
    // map cleanly without unions; leave it for Stage 2.
    let result_cod = fresh_var(ctx.level);

    for e in exprs.iter_mut() {
        let ty = emit_node(e, ctx)?;
        let dom = fresh_var(ctx.level);
        let cod = fresh_var(ctx.level);
        constrain_subtype(&ty, &fun(Rc::clone(&dom), Rc::clone(&cod)), &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "CollectionUnion element"))?;
        constrain_subtype(&dom, &result_dom, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "CollectionUnion domain"))?;
        constrain_subtype(&cod, &result_cod, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "CollectionUnion codomain"))?;
    }
    Ok(fun(result_dom, result_cod))
}

fn emit_aggregate(
    input: &mut Expr,
    kind: AggregateKind,
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    let input_ty = emit_node(input, ctx)?;
    // Input must be a function (collection) type.
    let domain = fresh_var(ctx.level);
    let codomain = fresh_var(ctx.level);
    constrain_subtype(
        &input_ty,
        &fun(Rc::clone(&domain), Rc::clone(&codomain)),
        &mut ctx.cache,
    )
    .map_err(|e| map_constrain_err(e, "Aggregate input"))?;
    let scheme = ctx.schemes.aggregate(kind).clone();
    apply_unary_scheme(ctx, &scheme, &codomain).map_err(|e| map_constrain_err(e, "Aggregate"))
}

fn emit_let(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    let bound_ty = emit_node(bound_expr, ctx)?;
    // User annotation on binding site (e.g. `x: Int = expr`):
    if let Some(ann) = &binding.user_annotation {
        let ann_simple = ctx.type_to_simple(ann);
        // Snapshot before adding annotation bounds for a clean inferred type in the error.
        let inferred_ty = simple_to_type(&bound_ty);
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
    // Stage 1 monomorphic let: bind name to bound_ty as-is. Stage 2
    // will instead generalize bound_ty into a PolyScheme here.
    ctx.scopes.push_scope();
    ctx.scopes.bind(&binding.name, Rc::clone(&bound_ty));
    let body_ty = emit_node(body, ctx);
    ctx.scopes.pop_scope();
    body_ty
}

fn emit_proj(key: &ProjKey, ctx: &mut SimpleSubContext) -> Result<Rc<SimpleType>, InferError> {
    // Per-case rule: `Proj(k) : ∀α. {k: α, …} → α`. We emit the
    // open-record constraint directly using simple-sub primitives —
    // can't pre-build as a scheme because the key is data-dependent.
    let alpha = fresh_var(ctx.level);
    let record_var = fresh_var(ctx.level);
    let mut field = BTreeMap::new();
    let field_key = match key {
        ProjKey::Index(i) => FieldKey::Index(*i),
        ProjKey::Field(name) => FieldKey::Name(SmolStr::from(name.as_str())),
    };
    field.insert(field_key, Rc::clone(&alpha));
    // record_var <: {k: α} — the input must have at least field k.
    constrain_subtype(
        &record_var,
        &Rc::new(SimpleType::Record(field)),
        &mut ctx.cache,
    )
    .map_err(|e| map_constrain_err(e, "Proj"))?;
    Ok(fun(record_var, alpha))
}

fn emit_list(elts: &mut [Expr], ctx: &mut SimpleSubContext) -> Result<Rc<SimpleType>, InferError> {
    if elts.is_empty() {
        return Ok(fun(Rc::new(SimpleType::UIntRange(0)), prim(BaseType::Unit)));
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
    Ok(fun(Rc::new(SimpleType::UIntRange(n)), first_ty))
}

fn emit_case(
    branches: &mut [Branch],
    label: &str,
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    if branches.is_empty() {
        return Err(InferError::EmptyCase {
            at: label.to_string(),
        });
    }
    let mut result_ty: Option<Rc<SimpleType>> = None;
    for Branch { guard, body } in branches.iter_mut() {
        let guard_ty = emit_node(guard, ctx)?;
        let bool_ty = prim(BaseType::Bool);
        constrain_subtype(&guard_ty, &bool_ty, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Case guard"))?;
        constrain_subtype(&bool_ty, &guard_ty, &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Case guard"))?;
        let arm_ty = emit_node(body, ctx)?;
        match &result_ty {
            None => result_ty = Some(arm_ty),
            Some(prev) => {
                constrain_subtype(&arm_ty, prev, &mut ctx.cache)
                    .map_err(|e| map_constrain_err(e, "Case arm"))?;
                constrain_subtype(prev, &arm_ty, &mut ctx.cache)
                    .map_err(|e| map_constrain_err(e, "Case arm"))?;
            }
        }
    }
    Ok(result_ty.expect("non-empty branches"))
}

fn emit_compose(
    elts: &mut [Expr],
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    assert!(elts.len() >= 2, "Compose requires at least two elements");
    let mut tys = Vec::with_capacity(elts.len());
    for e in elts.iter_mut() {
        tys.push(emit_node(e, ctx)?);
    }
    let first_dom = fresh_var(ctx.level);
    let mut prev_cod = fresh_var(ctx.level);
    constrain_subtype(
        &tys[0],
        &fun(Rc::clone(&first_dom), Rc::clone(&prev_cod)),
        &mut ctx.cache,
    )
    .map_err(|e| map_constrain_err(e, "Compose[0]"))?;
    for (i, t) in tys.iter().enumerate().skip(1) {
        let d_i = fresh_var(ctx.level);
        let c_i = fresh_var(ctx.level);
        constrain_subtype(t, &fun(Rc::clone(&d_i), Rc::clone(&c_i)), &mut ctx.cache)
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
    id: NodeId,
    params: &mut [TypedBinding],
    init_args: &mut [Expr],
    source: &mut Expr,
    loop_body: &mut Expr,
    ctx: &mut SimpleSubContext,
) -> Result<Rc<SimpleType>, InferError> {
    debug_assert_eq!(
        params.len(),
        init_args.len(),
        "Loop: params and init_args must have equal length"
    );

    // Source: Fun(D, item).
    let d = fresh_var(ctx.level);
    let item = fresh_var(ctx.level);
    let s_ty = emit_node(source, ctx)?;
    constrain_subtype(&s_ty, &fun(Rc::clone(&d), Rc::clone(&item)), &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Loop source"))?;

    // Accumulator slots: one fresh α per `params[i]`; `init_args[i] <: α_i`.
    let alphas: Vec<Rc<SimpleType>> = (0..params.len()).map(|_| fresh_var(ctx.level)).collect();
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
    let mut cod_fields: BTreeMap<FieldKey, Rc<SimpleType>> = BTreeMap::new();
    cod_fields.insert(FieldKey::Name(SmolStr::from("step")), Rc::clone(&sigma));
    let step_record = Rc::new(SimpleType::Record(cod_fields));

    // Body domain: Tuple(α_0, …, α_{n-1}, item).
    let mut dom_fields: BTreeMap<FieldKey, Rc<SimpleType>> = BTreeMap::new();
    for (i, alpha) in alphas.iter().enumerate() {
        dom_fields.insert(FieldKey::Index(i), Rc::clone(alpha));
    }
    dom_fields.insert(FieldKey::Index(alphas.len()), Rc::clone(&item));
    let body_dom = Rc::new(SimpleType::Record(dom_fields));

    let body_ty = emit_node(loop_body, ctx)?;
    constrain_subtype(
        &body_ty,
        &fun(body_dom, Rc::clone(&actual_cod)),
        &mut ctx.cache,
    )
    .map_err(|e| map_constrain_err(e, "Loop body"))?;
    // The body's codomain must at least carry `step: σ`.
    constrain_subtype(&actual_cod, &step_record, &mut ctx.cache)
        .map_err(|e| map_constrain_err(e, "Loop body step"))?;

    // Recurrence: σ <: α_0 (single) or σ <: Tuple(α_0, …, α_{n-1}) (multi).
    if alphas.len() == 1 {
        constrain_subtype(&sigma, &alphas[0], &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Loop recurrence"))?;
    } else {
        let mut tup: BTreeMap<FieldKey, Rc<SimpleType>> = BTreeMap::new();
        for (i, alpha) in alphas.iter().enumerate() {
            tup.insert(FieldKey::Index(i), Rc::clone(alpha));
        }
        constrain_subtype(&sigma, &Rc::new(SimpleType::Record(tup)), &mut ctx.cache)
            .map_err(|e| map_constrain_err(e, "Loop recurrence"))?;
    }

    // Stash the α vars so the coalesce pass can fill in
    // `Loop::params[i].ty` (a `TypedBinding` field not otherwise reached
    // by the side-table walk, which keys on `Expr` pointers).
    ctx.loop_param_tys.insert(id, alphas.clone());

    Ok(fun(d, actual_cod))
}

// ---------------------------------------------------------------------------
// Coalesce pass (Step 7e)
// ---------------------------------------------------------------------------
//
// `SimpleType`-blind stitching that used to live here (Refinement Propagation,
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

fn coalesce_pass(expr: &mut Expr, ctx: &SimpleSubContext) -> Vec<InferError> {
    let mut errors = Vec::new();
    coalesce_node(expr, ctx, &mut errors);
    errors
}

fn coalesce_node(expr: &mut Expr, ctx: &SimpleSubContext, errors: &mut Vec<InferError>) {
    let id = NodeId::of(expr);

    // Recurse into sub-expressions first so child types are settled
    // before we coalesce this node's (which may reference them).
    match &mut expr.node {
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Proj(_) => {}
        TypedExprNode::Apply { function, argument } => {
            coalesce_node(function, ctx, errors);
            coalesce_node(argument, ctx, errors);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            coalesce_node(left, ctx, errors);
            coalesce_node(right, ctx, errors);
        }
        TypedExprNode::UnaryOp(_, inner) => coalesce_node(inner, ctx, errors),
        TypedExprNode::Lambda {
            param: _,
            body,
            refinement,
        } => {
            coalesce_node(body, ctx, errors);
            // Refinement predicate is itself an Expr that was inferred
            // by emit_lambda. Walk into it so its sub-trees get their
            // expr.ty slots filled — otherwise downstream code (and
            // structural equality for tests) sees a tree of Holes
            // inside the refinement's RefCell<Expr>.
            if let Some(r) = refinement {
                let RefinementKind::Predicate(def) = &r.kind;
                if let Ok(mut pred) = def.try_borrow_mut() {
                    coalesce_node(&mut pred, ctx, errors);
                }
            }
        }
        TypedExprNode::Aggregate { input, .. } => coalesce_node(input, ctx, errors),
        TypedExprNode::Let {
            binding: _,
            bound_expr,
            body,
        } => {
            coalesce_node(bound_expr, ctx, errors);
            coalesce_node(body, ctx, errors);
        }
        TypedExprNode::List(elts)
        | TypedExprNode::Tuple(elts)
        | TypedExprNode::Compose(elts)
        | TypedExprNode::CollectionUnion(elts) => {
            for e in elts.iter_mut() {
                coalesce_node(e, ctx, errors);
            }
        }
        TypedExprNode::Record(fs) => {
            for (_, e) in fs.iter_mut() {
                coalesce_node(e, ctx, errors);
            }
        }
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches.iter_mut() {
                coalesce_node(guard, ctx, errors);
                coalesce_node(body, ctx, errors);
            }
        }
        TypedExprNode::ExprStmt { expr: e, body } => {
            coalesce_node(e, ctx, errors);
            coalesce_node(body, ctx, errors);
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
            coalesce_node(source, ctx, errors);
            for a in init_args.iter_mut() {
                coalesce_node(a, ctx, errors);
            }
            coalesce_node(loop_body, ctx, errors);
            // Materialize the accumulator-slot types onto `params[i].ty`.
            // `emit_loop` stored one α per slot in `loop_param_tys`; pass
            // each through the same compact + simplify + coalesce pipeline
            // used for `expr.ty` slots below.
            if let Some(alphas) = ctx.loop_param_tys.get(&id).cloned() {
                let coalesced: Vec<Result<Type, CoalesceError>> = alphas
                    .iter()
                    .map(|alpha| coalesce_compact(&simplify_type(compact_type(alpha))))
                    .collect();
                for (binding, result) in params.iter_mut().zip(coalesced) {
                    match result {
                        Ok(ty) => binding.ty = ty,
                        Err(err) => {
                            let label = "Loop param".to_string();
                            push_coalesce_err(errors, map_coalesce_err(err, &label), label);
                        }
                    }
                }
            }
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    }

    // Coalesce this node's recorded SimpleType into expr.ty. The
    // pipeline is `compact_type` (transitively expand bound graphs into
    // a per-position CompactType) → `coalesce_compact` (materialize
    // into ccl::Type).
    let label = symbolic(expr);
    if let Some(simple) = ctx.side.get(&id) {
        let graph = simplify_type(compact_type(simple));
        match coalesce_compact(&graph) {
            Ok(ty) => {
                // Refinements are AST-node metadata (on `Expr::Lambda`)
                // and are *not* lifted into the inferred function type.
                // `type_saturate` reads the refinement off the AST node;
                // `lambda_elim` wraps `Type::Refinement` around the
                // domain when it desugars a refined lambda. Round-tripping
                // the refinement through the inferred type also created a
                // false divergence between `lambda_elim`'s `original_ty`
                // and `result.ty` for any synthetic lambda with an
                // AST-level refinement (groupby, multi-gen comprehensions).
                expr.ty = ty;
            }
            Err(err) => push_coalesce_err(errors, map_coalesce_err(err, &label), label),
        }
    } else {
        // Not recorded in side table — usually means we never visited
        // this node (e.g. inside a Join/Jump body that Stage 1 doesn't
        // structurally walk). Leave expr.ty alone.
    }
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
}

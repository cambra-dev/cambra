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

use crate::ccl::ccl_utils::cast_target_refinement;
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
    /// wrappers (refinements ride the lattice as refinement tags) — is
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

// ---------------------------------------------------------------------------
// Typing: the structural typing-rule interface
// ---------------------------------------------------------------------------

/// The operations a typing rule needs from its surrounding pass.
///
/// Each per-node rule (`emit_apply`, `emit_let`, …) is written once against
/// this interface and run in two modes: **Emit** (type inference proper —
/// mints fresh inference vars and accumulates `constrain_subtype` bounds that
/// a later coalesce pass solves) and, in a later step, **Check** (a
/// post-inference structural re-validation over fully-resolved types). Sharing
/// the rule body keeps each node's typing rule in exactly one place rather
/// than duplicated across the two passes.
///
/// Implemented by [`SimpleSubContext`] (Emit) and [`CheckCtx`] (Check).
trait Typing {
    /// Obtain the type of a child sub-expression. In Emit mode this recurses
    /// via [`emit_node`], emitting the child's constraints and writing its
    /// inferred type onto the child node.
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError>;

    /// A fresh existential type variable at the current level.
    fn fresh(&mut self) -> Type;

    /// Instantiate a polymorphic operator scheme at the current level.
    fn instantiate(&mut self, scheme: &PolyScheme) -> Type;

    /// Normalize a user annotation / binder type into a solver-ready `Type`
    /// (holes → fresh vars; refinements kept). See
    /// [`SimpleSubContext::normalize_annotation`].
    fn normalize(&mut self, ann: &Type) -> Type;

    /// Require `sub <: sup`. `at` lazily produces an error-context label,
    /// invoked only on failure.
    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError>;

    /// Require `a` and `b` to be equal (subtyping in both directions).
    fn require_eq(
        &mut self,
        a: &Type,
        b: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        self.require_sub(a, b, at)?;
        self.require_sub(b, a, at)
    }

    /// Run `f` with `name: ty` bound in the lexical scope, restoring the
    /// scope afterward on both the success and error paths.
    fn scoped<R>(&mut self, name: &str, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R
    where
        Self: Sized;

    /// Reconcile a binder's inferred type with its user annotation. In Emit
    /// mode this two-way-constrains the two (eagerly surfacing
    /// [`InferError::AnnotationMismatch`]); the annotation is the canonical
    /// type, so both directions are recorded.
    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), InferError>;

    /// Obtain the type for a binder slot that lives on a [`TypedBinding`]
    /// rather than an [`Expr`] (a `Case` pattern payload, a `Loop`
    /// accumulator) — a place the tree walk wouldn't otherwise reach.
    ///
    /// Emit mints a fresh var and writes it into `slot` so coalesce resolves
    /// the binder in place. Check reads the slot's already-resolved type back,
    /// leaving it untouched.
    fn binding_slot(&mut self, slot: &mut Type) -> Type;

    /// Decompose `t` as a function, yielding `(domain, codomain)` and recording
    /// `t <: domain ⇒ codomain` — the "`t` is at least a function" requirement
    /// every eliminator makes.
    ///
    /// Emit mints fresh domain/codomain vars and constrains `t` to fit. Check
    /// destructures `t`'s already-resolved `Fun` shape directly (no inference
    /// vars), reporting [`InferError::ExpectedFunction`] if `t` isn't a
    /// function. Destructuring rather than constraining-a-throwaway is what
    /// lets the post-inference check compare concrete types directly.
    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError>;

    /// Like [`Typing::as_function`] but records equality (`t ⟺ domain ⇒
    /// codomain`). Used at `Apply`, where the argument and the function's
    /// domain are unified (the Stage-1 monomorphizing hack). In Check both
    /// directions hold once `t` is destructured, so it behaves identically to
    /// [`Typing::as_function`].
    fn as_function_eq(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError>;

    /// Relate an applied argument to the function's parameter domain.
    ///
    /// The sound rule is `arg <: domain` (the argument must fit the parameter,
    /// so a *refined* argument may flow into an unrefined parameter — dropping
    /// a restriction is admissible). Check records exactly that. Emit
    /// *additionally* records the reverse, unifying the two — the Stage-1
    /// monomorphizing hack (see `emit_apply`) that lets a function-side var
    /// (e.g. a `Proj`'s `record_var`) see both polarities and coalesce
    /// correctly. The reverse is unsound in general and only safe because Emit
    /// constrains a fresh var; in Check, where the argument may legitimately
    /// carry a restriction the parameter lacks, the one-way rule is the correct
    /// one.
    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError>;
}

/// Peel every outer [`Type::Refinement`] layer off `t`, returning the bare
/// structural type underneath. Non-allocating — only unwraps the outer tags a
/// node acquired during solving; nested refinements are left in place.
fn peel_refinements_outer(t: &Type) -> &Type {
    let mut cur = t;
    while let Type::Refinement(inner, _) = cur {
        cur = inner;
    }
    cur
}

impl Typing for SimpleSubContext {
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError> {
        emit_node(child, self)
    }

    fn fresh(&mut self) -> Type {
        fresh_var(self.level)
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        scheme.instantiate(self.level)
    }

    fn normalize(&mut self, ann: &Type) -> Type {
        self.normalize_annotation(ann)
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        constrain_subtype(sub, sup, &mut self.cache).map_err(|e| map_constrain_err(e, &at()))
    }

    fn scoped<R>(&mut self, name: &str, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push_scope();
        self.scopes.bind(name, ty.clone());
        let r = f(self);
        self.scopes.pop_scope();
        r
    }

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), InferError> {
        // Two-way constrain_subtype == equality. This eagerly detects
        // conflicts (a body constrains the binder to T, the annotation says
        // U ≠ T → propagation fails immediately → AnnotationMismatch).
        // One-way-only would defer the conflict to coalesce.
        //
        // TODO (SOUNDNESS): two-way equality is unsound for annotations
        // containing union types (positive) or intersection types (negative);
        // those should use one-way subtype only. Stage 1 avoids this because
        // `normalize_annotation` converts Union → fresh_var, so union
        // annotations degrade to trivially satisfiable subtyping. Replace in
        // Stage 2.
        let ann_simple = self.normalize_annotation(ann);
        // Snapshot the inferred type before the annotation bounds are added so
        // the error shows what was actually inferred, not the partially
        // modified state after a failed constrain_subtype.
        let inferred_ty = coalesce_for_error(inferred);
        constrain_subtype(inferred, &ann_simple, &mut self.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty.clone(),
            }
        })?;
        constrain_subtype(&ann_simple, inferred, &mut self.cache).map_err(|_| {
            InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty,
            }
        })?;
        Ok(())
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        let v = self.fresh();
        *slot = v.clone();
        v
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        let d = self.fresh();
        let c = self.fresh();
        self.require_sub(t, &fun(d.clone(), c.clone()), at)?;
        Ok((d, c))
    }

    fn as_function_eq(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        let d = self.fresh();
        let c = self.fresh();
        let f = fun(d.clone(), c.clone());
        // Two-way == equality, matching the Apply monomorphizing hack: see
        // `emit_apply`.
        self.require_sub(t, &f, at)?;
        self.require_sub(&f, t, at)?;
        Ok((d, c))
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // Two-way (the monomorphizing hack): unify the argument and domain.
        self.require_sub(arg, domain, at)?;
        self.require_sub(domain, arg, at)
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
                let pred_ty = emit_node(&mut pred, ctx)?;
                constrain_predicate_bool(&pred_ty, ctx)?;
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

/// Constrain a refinement predicate's inferred type to the closed-function
/// shape `D ⇒ Bool`. A predicate's body is the membership decision, so its
/// codomain must be a `Bool` (the current representation — see
/// `docs/refinement-types-design.md`). `if` filters in list comprehensions and
/// for-loops lower to such predicates, so this is where a non-Bool guard (e.g.
/// `[x for x in xs if x]`) is rejected. The domain is left as a fresh variable;
/// only the codomain is pinned.
fn constrain_predicate_bool<C: Typing>(pred_ty: &Type, ctx: &mut C) -> Result<(), InferError> {
    // One-way `pred_ty <: (_ ⇒ Bool)`: the covariant codomain forces the
    // predicate body to be a `Bool` directly (a non-Bool guard like `Int`
    // fails as a base-type `TypeMismatch`), while the contravariant domain is
    // left unconstrained as a fresh variable.
    let pred_domain = ctx.fresh();
    ctx.require_sub(pred_ty, &fun(pred_domain, prim(BaseType::Bool)), &|| {
        "refinement predicate".to_string()
    })
}

/// Apply a binary scheme: instantiate, build the expected call shape,
/// constrain_subtype. Returns the fresh result variable.
fn apply_binary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    left: &Type,
    right: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, InferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(left.clone(), fun(right.clone(), result.clone()));
    ctx.require_sub(&body, &expected, at)?;
    Ok(result)
}

/// Apply a unary scheme. Used for UnaryOp and Aggregate. For an
/// aggregate the scheme is the full operator type `(α → γ) → γ`, so the
/// operand is the input collection (function) itself.
fn apply_unary_scheme<C: Typing>(
    ctx: &mut C,
    scheme: &PolyScheme,
    operand: &Type,
    at: &dyn Fn() -> String,
) -> Result<Type, InferError> {
    let body = ctx.instantiate(scheme);
    let result = ctx.fresh();
    let expected = fun(operand.clone(), result.clone());
    ctx.require_sub(&body, &expected, at)?;
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

        // Cast: an upcast re-viewing `value` at the supertype `target`. See
        // [`emit_cast`] (shared with `check_node`).
        TypedExprNode::Cast { value, target } => emit_cast(value, target, ctx)?,

        TypedExprNode::Apply { function, argument } => emit_apply(function, argument, ctx)?,

        // Scheme-based rules: the registry lookup (which scheme for this op)
        // is Emit-specific, so the dispatcher resolves it and hands the
        // instantiable scheme to the shared rule. Cloning releases the `ctx`
        // borrow on the registry so the rule can take `ctx` mutably; schemes
        // are `Rc`-shaped, so the clone is cheap.
        TypedExprNode::BinOp { left, op, right } => {
            let scheme = ctx.schemes.binop(*op).clone();
            emit_binop(left, right, &scheme, ctx)?
        }

        TypedExprNode::UnaryOp(op, inner) => {
            let scheme = ctx.schemes.unary(*op).clone();
            emit_unary(inner, &scheme, ctx)?
        }

        TypedExprNode::Aggregate { input, kind } => {
            let scheme = ctx.schemes.aggregate(*kind).clone();
            emit_aggregate(input, &scheme, ctx)?
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::Tuple(elts) => emit_tuple(elts, ctx)?,

        TypedExprNode::Record(fs) => emit_record(fs, ctx)?,

        TypedExprNode::Proj(key) => {
            // The projection's function type is built here: seed it with a
            // fresh var that `emit_proj` ties to `domain ⇒ codomain`.
            let seed = ctx.fresh();
            emit_proj(key, &seed, ctx)?
        }

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

        TypedExprNode::ExprStmt { expr: e, body } => emit_expr_stmt(e, body, ctx)?,

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

fn emit_lambda<C: Typing>(
    param: &mut TypedBinding,
    body: &mut Expr,
    refinement: &mut Option<Refinement>,
    ctx: &mut C,
) -> Result<Type, InferError> {
    // Param type: convert any explicit annotation/Hole/Infer into a
    // the solver. A Hole turns into a fresh Var that will accumulate
    // bounds from body usage and call sites. Link `param.ty` to that
    // (shared) var so `coalesce_node` can resolve the binding slot in
    // place — the slot ends up carrying the body-usage refinement tags
    // but *not* the lambda's own refinement (that decorates only the
    // function-boundary domain in `expr.ty`).
    let param_simple = ctx.normalize(&param.ty);
    param.ty = param_simple.clone();
    // The param is bound in scope under the *unrefined* `param_simple`, so
    // `Var(param)` body references stay bare; restriction tags decorate only
    // the function boundary.
    let body_ty = ctx.scoped(&param.name, &param_simple, |ctx| ctx.subexpr(body))?;

    // Param user-annotation: reconcile the inferred param type with the
    // annotation (two-way; see `bind_annotation`).
    if let Some(ann) = param.user_annotation.clone() {
        ctx.bind_annotation(&param_simple, &ann)?;
    }

    // Refinement: lift the lambda's *own* refinement into the inferred
    // domain so it rides the lattice as a refinement tag (replacing the
    // old `type_saturate` re-stitch). The AST node keeps its `refinement`
    // field — `lambda_elim` reads it from there, not from the type, so
    // there's no double-wrapping. We still walk the predicate so its inner
    // expressions get inferred types (otherwise downstream consumers see
    // `Hole`s inside the predicate body).
    let domain_ty = match refinement {
        Some(r) => {
            let RefinementKind::Predicate(def) = &r.kind;
            // The predicate is compiled lazily inside an `Rc<RefCell<Expr>>`.
            let pred_ty = ctx.subexpr(&mut def.borrow_mut())?;
            constrain_predicate_bool(&pred_ty, ctx)?;
            Type::Refinement(Box::new(param_simple), r.clone())
        }
        None => param_simple,
    };

    Ok(fun(domain_ty, body_ty))
}

/// Type a [`TypedExprNode::Cast`]: `cast(value, target)` re-views `value` at
/// `target`, attaching `target`'s domain refinement `r` to `value`'s type.
///
/// The rule decomposes `value`'s type into `D ⇒ V` and re-wraps the domain
/// with `r`, yielding `{D | r} ⇒ V`. This is an upcast — the refined-domain
/// function is a *supertype* of `value` (`D ⇒ V <: {D | r} ⇒ V` by
/// contravariance, since `{D | r} <: D`) — but it is built *constructively*
/// rather than as a bare `value <: target` obligation, because the refinement
/// lattice is strict (`unrefined ⊀ refined`) so the value cannot flow *into*
/// the refined target by subtyping. Re-wrapping the domain stacks `r` over any
/// tags `value` already carries, so chained casts (nested list-comprehension
/// filters) compose.
///
/// `as_function_eq` is the mode-generic decompose: in Emit it pins fresh
/// `d`/`v` to `value_ty` (so coalesce resolves the result), in Check it peels
/// `value_ty`'s already-resolved `D`/`V`. `target`'s own holes are *not* used
/// for the result — Check's `normalize` is the identity, so they would survive
/// as unsolved vars; reconstructing from `value` keeps both modes honest. The
/// domain-refinement predicate is typed via `ctx.subexpr` and constrained to
/// the `D ⇒ Bool` shape exactly as [`emit_lambda`] handles a lambda's own
/// refinement; `coalesce_type_predicates(&expr.ty)` resolves it later (the
/// result shares `target`'s tag `r`).
///
/// Shared by [`emit_node`] (Emit) and [`check_node`] (Check) via [`Typing`].
fn emit_cast<C: Typing>(value: &mut Expr, target: &Type, ctx: &mut C) -> Result<Type, InferError> {
    let value_ty = ctx.subexpr(value)?;
    let refinement = cast_target_refinement(target);
    // Type the domain-refinement predicate and enforce `D ⇒ Bool`, mirroring
    // `emit_lambda`'s refinement arm.
    if let Some(r) = &refinement {
        let RefinementKind::Predicate(def) = &r.kind;
        let pred_ty = ctx.subexpr(&mut def.borrow_mut())?;
        constrain_predicate_bool(&pred_ty, ctx)?;
    }
    // Re-view `value : D ⇒ V` as `{D | r} ⇒ V` (the refinement on the domain).
    let (d, v) = ctx.as_function_eq(&value_ty, &|| "cast value".to_string())?;
    let domain = match refinement {
        Some(r) => Type::Refinement(Box::new(d), r),
        None => d,
    };
    Ok(fun(domain, v))
}

fn emit_apply<C: Typing>(
    function: &mut Expr,
    argument: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let arg_ty = ctx.subexpr(argument)?;
    let fn_ty = ctx.subexpr(function)?;
    // Decompose the function into (domain, codomain). `as_function_eq` records
    // `fn_ty ⟺ domain ⇒ codomain` in Emit; in Check it destructures the
    // resolved function type directly.
    let (domain, codomain) = ctx.as_function_eq(&fn_ty, &|| "Apply".to_string())?;
    // The argument flows into the parameter domain. Emit unifies them (the
    // bidirectional monomorphizing hack — matching HM's `constrain_equal` at
    // apply sites — so a fresh Var on the function side, e.g. a `Proj`'s
    // `record_var`, sees both polarities and doesn't coalesce too narrow);
    // Check uses the sound one-way `arg <: domain`, so a refined argument (a
    // filtered collection `{D | p}`) may flow into an unrefined parameter. See
    // `Typing::constrain_argument`.
    //
    // TODO (SOUNDNESS): the Emit-side equality is a monomorphizing hack. Stage
    // 2 prep replaces it with `Type::ForAll` + a monomorphization pass between
    // `infer` and `inline` (see
    // `docs/brainstorm/2026-05-06_simple_sub_prototype_status.md` §3.1). Make
    // `constrain_argument` one-way in Emit too, and drop the polarity fallback
    // in `simple_sub.rs::compact_go`, once that pass lands.
    ctx.constrain_argument(&arg_ty, &domain, &|| "Apply".to_string())?;
    Ok(codomain)
}

fn emit_binop<C: Typing>(
    left: &mut Expr,
    right: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let left_ty = ctx.subexpr(left)?;
    let right_ty = ctx.subexpr(right)?;
    apply_binary_scheme(ctx, scheme, &left_ty, &right_ty, &|| "BinOp".to_string())
}

fn emit_unary<C: Typing>(
    inner: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let inner_ty = ctx.subexpr(inner)?;
    apply_unary_scheme(ctx, scheme, &inner_ty, &|| "UnaryOp".to_string())
}

/// Tuple literal: each element type becomes a positional product field.
fn emit_tuple<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (i, e) in elts.iter_mut().enumerate() {
        fields.insert(FieldKey::Index(i), ctx.subexpr(e)?);
    }
    Ok(product(fields))
}

/// Record literal: each field value type becomes a named product field.
fn emit_record<C: Typing>(fs: &mut [(String, Expr)], ctx: &mut C) -> Result<Type, InferError> {
    let mut fields = BTreeMap::new();
    for (n, e) in fs.iter_mut() {
        fields.insert(FieldKey::Name(SmolStr::from(n.as_str())), ctx.subexpr(e)?);
    }
    Ok(product(fields))
}

/// `expr; body`: the statement's value is discarded (but still inferred for
/// its constraints/side-types); the node takes the body's type.
fn emit_expr_stmt<C: Typing>(
    e: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    ctx.subexpr(e)?;
    ctx.subexpr(body)
}

fn emit_collection_union<C: Typing>(exprs: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
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
    let cod_var = ctx.fresh();
    let mut tags = BTreeMap::new();
    for (i, e) in exprs.iter_mut().enumerate() {
        let ty = ctx.subexpr(e)?;
        // Each operand is a collection (function); its codomain joins into the
        // shared `cod_var`, its domain becomes the variant tag for operand `i`.
        let (dom, cod) = ctx.as_function(&ty, &|| "CollectionUnion element".to_string())?;
        ctx.require_sub(&cod, &cod_var, &|| "CollectionUnion codomain".to_string())?;
        tags.insert(FieldKey::Index(i), dom);
    }
    let dom_variant = variant_type(tags);
    Ok(fun(dom_variant, cod_var))
}

/// Aggregate (`Sum`, `Max`): the scheme is the full operator type
/// `(α → γ) → γ`, applied directly to the input collection (function). The
/// scheme's own domain shape enforces that the input is a function and folds
/// its codomain.
fn emit_aggregate<C: Typing>(
    input: &mut Expr,
    scheme: &PolyScheme,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let input_ty = ctx.subexpr(input)?;
    apply_unary_scheme(ctx, scheme, &input_ty, &|| "Aggregate".to_string())
}

fn emit_let<C: Typing>(
    binding: &mut TypedBinding,
    bound_expr: &mut Expr,
    body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let bound_ty = ctx.subexpr(bound_expr)?;
    // User annotation on binding site (e.g. `x: Int = expr`):
    if let Some(ann) = &binding.user_annotation {
        ctx.bind_annotation(&bound_ty, ann)?;
    }
    // Monomorphic let: bind name to bound_ty as-is. Later we
    // will instead generalize bound_ty into a PolyScheme here.
    ctx.scoped(&binding.name, &bound_ty, |ctx| ctx.subexpr(body))
}

/// Build the open-product shape a projection of `key` requires its input to
/// satisfy: the input must carry field/position `key` typed `field_ty`.
///
/// `ccl::Type` has no sparse-index product, so an *index* projection pads to a
/// dense `Tuple` of length `i+1` with fresh vars in positions `0..i` and
/// `field_ty` at `i`; tuple width-subtyping (a longer tuple is a subtype) then
/// admits any tuple with at least `i+1` positions. A *named* projection uses an
/// open `Record{name: field_ty}`; record width-subtyping admits any record
/// carrying that field.
fn proj_requirement<C: Typing>(key: &ProjKey, field_ty: Type, ctx: &mut C) -> Type {
    match key {
        ProjKey::Index(i) => {
            let mut positions: Vec<Type> = (0..*i).map(|_| ctx.fresh()).collect();
            positions.push(field_ty);
            Type::Tuple(positions)
        }
        ProjKey::Field(name) => Type::Record(vec![(name.to_string(), field_ty)]),
    }
}

/// `Proj(k) : ∀α. {k: α, …} ⇒ α`. The node's own type *is* that function, so
/// we decompose it into `(domain, codomain)` and require the domain to carry
/// field `k` typed at the codomain.
///
/// `node_ty` is the projection's function type: a fresh seed in Emit (which
/// `as_function_eq` ties to `domain ⇒ codomain`, so it coalesces to the built
/// function exactly as before) and the recorded type in Check (destructured
/// directly — no inference vars).
fn emit_proj<C: Typing>(key: &ProjKey, node_ty: &Type, ctx: &mut C) -> Result<Type, InferError> {
    let (domain, codomain) = ctx.as_function_eq(node_ty, &|| "Proj".to_string())?;
    let requirement = proj_requirement(key, codomain, ctx);
    ctx.require_sub(&domain, &requirement, &|| "Proj".to_string())?;
    Ok(node_ty.clone())
}

fn emit_list<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    if elts.is_empty() {
        return Ok(fun(Type::UIntRange(0), prim(BaseType::Unit)));
    }
    // Element type: derive from the first; constrain remaining to it.
    let first_ty = ctx.subexpr(&mut elts[0])?;
    for rest in &mut elts[1..] {
        let r_ty = ctx.subexpr(rest)?;
        // Two-way constrain == equality. Mirrors the existing pass's
        // implicit assumption that list elements are homogeneous.
        ctx.require_eq(&r_ty, &first_ty, &|| "List element".to_string())?;
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
fn emit_case<C: Typing>(
    scrutinee: Option<&mut Expr>,
    branches: &mut [Branch],
    label: &str,
    ctx: &mut C,
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
        let scrut_ty = ctx.subexpr(scrut)?;
        let mut expected_tags: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for b in branches.iter_mut() {
            if let Some(p) = &mut b.pattern {
                let alpha = ctx.binding_slot(&mut p.binding.ty);
                expected_tags.insert(FieldKey::Name(SmolStr::from(p.tag.as_str())), alpha);
            }
        }
        let expected = variant_type(expected_tags);
        ctx.require_sub(&scrut_ty, &expected, &|| "Case scrutinee".to_string())?;
    }

    let mut result_ty: Option<Type> = None;
    for b in branches.iter_mut() {
        // A pattern binds its payload (the var just written to `binding.ty`)
        // over the branch's guard and body. `scoped` restores the scope on
        // both the happy and error paths.
        let scope_info = b
            .pattern
            .as_ref()
            .map(|p| (p.binding.name.clone(), p.binding.ty.clone()));
        let body_ty = match scope_info {
            Some((name, ty)) => ctx.scoped(&name, &ty, |ctx| emit_case_branch(b, ctx))?,
            None => emit_case_branch(b, ctx)?,
        };
        match &result_ty {
            None => result_ty = Some(body_ty),
            Some(prev) => ctx.require_eq(&body_ty, prev, &|| "Case arm".to_string())?,
        }
    }
    Ok(result_ty.expect("non-empty branches"))
}

/// Emit a single Case branch: its guard must be `Bool`; the node takes the
/// body's type. The pattern binding (if any) is already in scope.
fn emit_case_branch<C: Typing>(b: &mut Branch, ctx: &mut C) -> Result<Type, InferError> {
    let guard_ty = ctx.subexpr(&mut b.guard)?;
    ctx.require_eq(&guard_ty, &prim(BaseType::Bool), &|| {
        "Case guard".to_string()
    })?;
    ctx.subexpr(&mut b.body)
}

fn emit_variant_ctor<C: Typing>(
    tag: &str,
    payload: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    let payload_ty = ctx.subexpr(payload)?;
    let mut tags = BTreeMap::new();
    tags.insert(FieldKey::Name(SmolStr::from(tag)), payload_ty);
    Ok(variant_type(tags))
}

fn emit_compose<C: Typing>(elts: &mut [Expr], ctx: &mut C) -> Result<Type, InferError> {
    assert!(elts.len() >= 2, "Compose requires at least two elements");
    let mut tys = Vec::with_capacity(elts.len());
    for e in elts.iter_mut() {
        tys.push(ctx.subexpr(e)?);
    }
    // Decompose each morphism into (domain, codomain); adjacent pairs must
    // compose (`prev_cod <: next_dom`). `as_function` destructures the resolved
    // function in Check and introduces-and-constrains in Emit.
    let (first_dom, mut prev_cod) = ctx.as_function(&tys[0], &|| "Compose[0]".to_string())?;
    for (i, t) in tys.iter().enumerate().skip(1) {
        let (d_i, c_i) = ctx.as_function(t, &|| "Compose[i]".to_string())?;
        // Strict refinement-aware adjacency: `prev_cod <: next_dom`, refinement
        // tags and all — no cast escape. A producer must already supply the
        // refinement its consumer demands. Join planning surfaces the
        // join-satisfying / iterated extent on each producing morphism's
        // codomain (`planning`'s `refine_codomain` / iteration-source
        // `set_codomain`), so a `… ≫ (id ≫ cast({D|r} ⇒ V))` chain composes
        // because the upstream genuinely carries `{D | r}` — matched
        // structurally even across the refinement ids planning re-mints.
        ctx.require_sub(&prev_cod, &d_i, &|| format!("Compose[{i}]"))?;
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
fn emit_loop<C: Typing>(
    params: &mut [TypedBinding],
    init_args: &mut [Expr],
    source: &mut Expr,
    loop_body: &mut Expr,
    ctx: &mut C,
) -> Result<Type, InferError> {
    debug_assert_eq!(
        params.len(),
        init_args.len(),
        "Loop: params and init_args must have equal length"
    );

    // Source: Fun(D, item).
    let s_ty = ctx.subexpr(source)?;
    let (d, item) = ctx.as_function(&s_ty, &|| "Loop source".to_string())?;

    // Accumulator slots: one var α per `params[i]` (Emit mints it and writes
    // it into the binder; Check reads the resolved accumulator type back);
    // `init_args[i] <: α_i`.
    let alphas: Vec<Type> = params
        .iter_mut()
        .map(|p| ctx.binding_slot(&mut p.ty))
        .collect();
    for (i, init) in init_args.iter_mut().enumerate() {
        let init_ty = ctx.subexpr(init)?;
        ctx.require_sub(&init_ty, &alphas[i], &|| "Loop init".to_string())?;
    }

    // Body codomain: Record carrying at least `{step: σ}`.  Tap fields
    // (`to_<defer>`) are no longer named at this level — `desugar_defers`
    // runs before inference and folds them into the body's literal Record;
    // we let the actual body record flow into `actual_cod` as a lower
    // bound and use that as the Loop's outer codomain, so downstream
    // projections on `to_<defer>` still see the right fields.
    let sigma = ctx.fresh();
    let actual_cod = ctx.fresh();
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

    let body_ty = ctx.subexpr(loop_body)?;
    ctx.require_sub(&body_ty, &fun(body_dom, actual_cod.clone()), &|| {
        "Loop body".to_string()
    })?;
    // The body's codomain must at least carry `step: σ`.
    ctx.require_sub(&actual_cod, &step_record, &|| "Loop body step".to_string())?;

    // Recurrence: σ <: α_0 (single) or σ <: Tuple(α_0, …, α_{n-1}) (multi).
    if alphas.len() == 1 {
        ctx.require_sub(&sigma, &alphas[0], &|| "Loop recurrence".to_string())?;
    } else {
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        for (i, alpha) in alphas.iter().enumerate() {
            tup.insert(FieldKey::Index(i), alpha.clone());
        }
        ctx.require_sub(&sigma, &product(tup), &|| "Loop recurrence".to_string())?;
    }

    Ok(fun(d, actual_cod))
}

// ---------------------------------------------------------------------------
// Check pass: post-inference structural re-validation
// ---------------------------------------------------------------------------

/// Post-inference structural type-check state.
///
/// Runs the *same* per-node rules as inference (the `emit_*` family) over a
/// tree whose `Type`s are already resolved, verifying that each node's typing
/// rule still holds. Where Emit ([`SimpleSubContext`]) mints fresh vars and
/// fails fast, Check reads the recorded `Type`s and *accumulates* every error:
/// [`Typing::require_sub`] records a mismatch and returns `Ok` (so a rule never
/// short-circuits), and [`Typing::subexpr`] recurses to collect a child's
/// errors then hands back the child's *recorded* type. Eliminators
/// *destructure* the resolved function/product directly ([`Typing::as_function`])
/// rather than constraining throwaway vars, so Check compares concrete types
/// and stays cheap.
///
/// Refinement handling: Check is refinement-*aware* — it constrains the real
/// (un-stripped) types via [`Typing::require_sub`], so the lattice's
/// restriction-tag subsetting (`unrefined ⊀ refined`) is enforced. The explicit
/// cast operator canonicalizes restriction *acquisition*, so the long-standing
/// deep strip is gone, and the check runs both after inference *and* after
/// join planning (`context.rs`).
///
/// There is no cast escape in the adjacency rule: a producer must already
/// carry the refinement its consumer demands. Join planning makes this hold by
/// surfacing each iterated/join-satisfying extent on the *producing* morphism's
/// codomain (`planning`'s `refine_codomain` / iteration-source `set_codomain`),
/// so a `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because the upstream
/// genuinely supplies `{D | r}`. Because planning re-mints a fresh refinement
/// id at every marker, the producer's `{D | r}` and the consumer's contract
/// rarely share an id; [`crate::ccl::simple_sub`]'s subset check matches them
/// by *structural predicate equality* (not just id) so the re-minted tags
/// still chain. (Previously this gap was papered over by a `contains_cast`
/// peel in `emit_compose` and by leaving planning output un-checked.)
struct CheckCtx {
    schemes: OperatorSchemes,
    level: Level,
    errors: Vec<InferError>,
}

impl CheckCtx {
    fn new() -> Self {
        // Level 0 matches inference (Stage 1 holds the level at 0) and the
        // scheme quantification level, so instantiated schemes mint vars at
        // the same level Check's `fresh` does.
        Self {
            schemes: OperatorSchemes::new(),
            level: 0,
            errors: Vec::new(),
        }
    }
}

impl Typing for CheckCtx {
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, InferError> {
        // Recurse to collect the child's own errors, then hand back its
        // *recorded* type (not the rule-derived, throwaway-laden one) so the
        // parent rule reasons about what was actually inferred. `check_node`
        // never returns `Err` in Check mode (errors accumulate in `self`).
        check_node(child, self)?;
        Ok(child.ty.clone())
    }

    fn fresh(&mut self) -> Type {
        fresh_var(self.level)
    }

    fn instantiate(&mut self, scheme: &PolyScheme) -> Type {
        scheme.instantiate(self.level)
    }

    fn normalize(&mut self, ann: &Type) -> Type {
        // A fully-typed tree carries no `Hole`s, so normalization is the
        // identity; refinements are kept (as everywhere else).
        ann.clone()
    }

    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // Delegate to the solver's `constrain_subtype` — the single source of
        // truth for width/variance and (since refinements ride the lattice as
        // restriction tags) tag subsetting. A failure is recorded (not
        // propagated) so the walk continues and reports every error.
        if let Err(e) = constrain_subtype(sub, sup, &mut ConstrainCache::new()) {
            self.errors.push(map_constrain_err(e, &at()));
        }
        Ok(())
    }

    fn scoped<R>(&mut self, _name: &str, _ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        // Check trusts each `Var`/binder node's recorded `Type` rather than
        // resolving names, so there is no scope to maintain.
        f(self)
    }

    fn bind_annotation(&mut self, _inferred: &Type, _ann: &Type) -> Result<(), InferError> {
        // The annotation was already folded into the binder's type during
        // inference; nothing to re-check here.
        Ok(())
    }

    fn binding_slot(&mut self, slot: &mut Type) -> Type {
        // Read the already-resolved binder type back, untouched.
        slot.clone()
    }

    fn as_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        // Destructure the resolved type directly (no inference vars). Peel any
        // outer refinement tags the function picked up during solving.
        match peel_refinements_outer(t) {
            Type::Fun(d, c) => Ok(((**d).clone(), (**c).clone())),
            _ => {
                self.errors.push(InferError::ExpectedFunction {
                    found: t.clone(),
                    at: at(),
                });
                // Continue with throwaways so the rest of the rule still runs
                // (Check accumulates every error rather than failing fast).
                Ok((self.fresh(), self.fresh()))
            }
        }
    }

    fn as_function_eq(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        // Destructuring already establishes both directions; identical to
        // `as_function` in Check.
        self.as_function(t, at)
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // Sound one-way only: a refined argument may flow into an unrefined
        // parameter (dropping a restriction is admissible). The Emit-side
        // monomorphizing hack's reverse direction does not apply here.
        self.require_sub(arg, domain, at)
    }
}

/// Run one node's typing rule in Check mode: dispatch to the shared rule,
/// then reconcile the rule-derived type against the node's recorded `Type`.
fn check_node(expr: &mut Expr, ctx: &mut CheckCtx) -> Result<Type, InferError> {
    let label = symbolic(expr);
    let ty = match &mut expr.node {
        TypedExprNode::Lit(lit) => lit_base(lit),

        // Leaves whose type carries the full load and was resolved during
        // inference — trust the recorded type (matching the old typecheck,
        // which left these unchecked).
        TypedExprNode::Var(_) | TypedExprNode::Builtin(_) | TypedExprNode::Source(_) => {
            expr.ty.clone()
        }

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => emit_lambda(param, body, refinement, ctx)?,

        TypedExprNode::Cast { value, target } => emit_cast(value, target, ctx)?,

        TypedExprNode::Apply { function, argument } => emit_apply(function, argument, ctx)?,

        TypedExprNode::BinOp { left, op, right } => {
            let scheme = ctx.schemes.binop(*op).clone();
            emit_binop(left, right, &scheme, ctx)?
        }

        TypedExprNode::UnaryOp(op, inner) => {
            let scheme = ctx.schemes.unary(*op).clone();
            emit_unary(inner, &scheme, ctx)?
        }

        TypedExprNode::Aggregate { input, kind } => {
            let scheme = ctx.schemes.aggregate(*kind).clone();
            emit_aggregate(input, &scheme, ctx)?
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => emit_let(binding, bound_expr, body, ctx)?,

        TypedExprNode::Tuple(elts) => emit_tuple(elts, ctx)?,

        TypedExprNode::Record(fs) => emit_record(fs, ctx)?,

        // The projection's function type is already recorded; decompose it.
        TypedExprNode::Proj(key) => emit_proj(key, &expr.ty, ctx)?,

        TypedExprNode::List(elts) => emit_list(elts, ctx)?,

        TypedExprNode::Case {
            scrutinee,
            branches,
        } => emit_case(scrutinee.as_deref_mut(), branches, &label, ctx)?,

        TypedExprNode::VariantCtor { tag, payload } => emit_variant_ctor(tag, payload, ctx)?,

        TypedExprNode::Compose(elts) => emit_compose(elts, ctx)?,

        TypedExprNode::ExprStmt { expr: e, body } => emit_expr_stmt(e, body, ctx)?,

        TypedExprNode::CollectionUnion(exprs) => emit_collection_union(exprs, ctx)?,

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => emit_loop(params, init_args, source, loop_body, ctx)?,

        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } | TypedExprNode::Defer => {
            unreachable!(
                "Defer/Feed/Define survived desugar_defers and reached typecheck: {:?}",
                expr.node
            )
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),
    };

    // Reconcile: the rule-derived type must agree with the node's recorded
    // type. In Emit this is the writeback `expr.ty = ty`; here it is the
    // subtype check `ty <: expr.ty` (the recorded type may be a width-wider
    // supertype — e.g. an annotation — exactly as the old typecheck allowed).
    //
    // Fast path: when the rule reproduced the recorded type exactly (the common
    // case — eliminators that destructure return the function's own codomain,
    // constructors rebuild the same product), the subtype check is reflexive
    // and trivially holds, so skip the (deeper, allocating) `constrain_subtype`.
    if ty != expr.ty {
        ctx.require_sub(&ty, &expr.ty, &|| format!("type of {label}"))?;
    }
    Ok(ty)
}

/// Run the post-inference structural type-check over `expr`.
///
/// Drives the shared per-node typing rules in Check mode over a throwaway
/// clone — the rules need `&mut Expr` for inference's in-place type writes, but
/// Check reads the recorded types and discards the clone, so callers keep their
/// `&Expr`. Returns every discovered error.
pub fn check(expr: &Expr) -> Result<(), Vec<InferError>> {
    let mut cloned = expr.clone();
    let mut ctx = CheckCtx::new();
    // `check_node` accumulates errors into `ctx` and never returns `Err` here.
    let _ = check_node(&mut cloned, &mut ctx);
    if ctx.errors.is_empty() {
        Ok(())
    } else {
        Err(ctx.errors)
    }
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
        // `target`'s refinement predicate is *not* coalesced here — it rides
        // `expr.ty` (the constructed `Fun({d | r}, v)` reuses `target`'s tag),
        // so the `coalesce_type_predicates(&expr.ty)` call at the end of this
        // function resolves it through the shared `Rc`.
        TypedExprNode::Cast { value, .. } => coalesce_node(value, errors),
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
            // body-usage refinement tags are negative-polarity upper-bound
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
    // Refinements ride the lattice as refinement tags, so a refined domain
    // coalesces straight onto `expr.ty` here. `lambda_elim` reads the
    // lambda's own refinement off the AST node — it is duplicated there
    // deliberately, and the tag's id-equality dedups any structural overlap
    // downstream.
    let label = symbolic(expr);
    match resolve_var_type(&expr.ty) {
        Ok(ty) => expr.ty = ty,
        Err(err) => push_coalesce_err(errors, map_coalesce_err(err, &label), label),
    }

    // A lambda's param binding slot mirrors its coalesced domain, minus the
    // lambda's *own* refinement layer (that decorates only the function
    // boundary; `lambda_elim` re-wraps it from the AST node). Deriving it
    // from the resolved domain — rather than coalescing the slot var
    // standalone — is what preserves body-usage refinement tags, which are
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

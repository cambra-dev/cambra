// ---------------------------------------------------------------------------
// Typing: the structural typing-rule interface
// ---------------------------------------------------------------------------

use crate::ccl::ccl_utils::TermMemo;
use crate::ccl::infer::solver::PolyScheme;
use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::provenance::NodeId;
use crate::ccl::{Expr, Name, Type};

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
/// Implemented by [`InferCtx`](super::context::InferCtx) (Emit)
/// and [`CheckCtx`](super::check::CheckCtx) (Check).
pub(super) trait Typing {
    /// The node whose typing rule is currently running — the blame for any error
    /// raised under it. Emit maintains it in
    /// [`emit_node`](super::emit::emit_node), Check in `check_node`; both set it
    /// on entry to a node's rule and restore it on exit, error path included.
    fn current_node(&self) -> NodeId;

    /// Raise `error`, blamed on the node whose rule is running.
    ///
    /// The **only** way to build a [`LocatedInferError`], which is why that type
    /// has no unlocated state to represent: an inference error cannot be
    /// constructed without the node it belongs to. Attribution happens at the
    /// raise site rather than on the unwind, so it does not depend on a pass
    /// being fail-fast — an accumulating pass gets the same per-error blame for
    /// free (this is how the coalesce walk and Check mode both get theirs).
    fn raise(&self, error: InferError) -> LocatedInferError {
        LocatedInferError {
            error,
            node_id: self.current_node(),
        }
    }

    /// Obtain the type of a child sub-expression. In Emit mode this recurses
    /// via [`emit_node`](super::emit::emit_node), emitting the child's
    /// constraints and writing its inferred type onto the child node.
    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, LocatedInferError>;

    /// A fresh existential type variable at the current level.
    fn fresh(&mut self) -> Type;

    /// The memo that keeps refinement-predicate `Rc` sharing across this whole
    /// emit/check walk. Both modes rebuild every predicate they type
    /// ([`emit_bare_predicate`](super::emit)), so both need it; it lives on the
    /// ctx because that is the only thing scoped to the pass rather than a node.
    fn pred_memo(&self) -> TermMemo;

    /// Instantiate a polymorphic operator scheme at the current level.
    fn instantiate(&mut self, scheme: &PolyScheme) -> Type;

    /// Normalize a user annotation / binder type into a solver-ready `Type`
    /// (holes → fresh vars; refinements kept). See
    /// [`InferCtx::normalize_annotation`](super::context::InferCtx::normalize_annotation).
    fn normalize(&mut self, ann: &Type) -> Type;

    /// Require `sub <: sup`. `at` lazily produces an error-context label,
    /// invoked only on failure.
    fn require_sub(
        &mut self,
        sub: &Type,
        sup: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError>;

    /// Run `f` with `name: ty` bound *monomorphically* in the lexical scope
    /// (lambda params, pattern/loop binders), restoring the scope afterward on
    /// both the success and error paths.
    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R
    where
        Self: Sized;

    /// Emit/check a `let` RHS. Emit bumps the polymorphism level so RHS-local
    /// variables become generalizable at the binding site; Check (which trusts
    /// recorded types) runs `f` unchanged.
    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R
    where
        Self: Sized;

    /// Whether generalizing a `let` bound to `def` would quantify anything —
    /// i.e. the binding is genuinely polymorphic (see
    /// [`should_generalize`](super::context::should_generalize)).
    /// Emit answers from the definition and level; Check always returns `false`
    /// (it never generalizes).
    fn is_generalizable(&self, def: &Expr) -> bool;

    /// Run `f` with a `let` name bound over the body. When `generalize` is set,
    /// Emit generalizes `bound_ty` at the current level into a polymorphic
    /// scheme (so each use site instantiates fresh quantified variables);
    /// otherwise it binds monomorphically (shared). Check ignores `generalize`
    /// and simply runs `f`.
    fn scoped_let<R>(
        &mut self,
        name: &Name,
        bound_ty: &Type,
        generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R
    where
        Self: Sized;

    /// Close a `let` body's type over its binder when lifting it to the `let`
    /// node: discharge `[name ↦ bound_expr]` into refinement predicates
    /// (design §6.2 move-site rule), so the lifted type stays well-formed
    /// outside the binder's scope.
    ///
    /// Emit returns `body_ty` unchanged: the body type is an unresolved var
    /// there, and the closing runs on the *resolved* type in `coalesce_node`'s
    /// Let arm — discharging here would rebuild refinement predicates out of
    /// any already-concrete body type (e.g. a lambda's `Fun`), and the rebuilt
    /// terms would escape coalesce unresolved. Check re-runs the discharge so its
    /// reconstruction matches the recorded (closed) node type under structural
    /// predicate equality.
    fn close_let_type(&self, name: &Name, bound_expr: &Expr, body_ty: Type) -> Type;

    /// Reconcile a binder's inferred type with its user annotation. In Emit
    /// mode this records the **one-way** obligation `inferred <: ann` —
    /// an annotation has to *admit* the value, not equal it — surfacing
    /// [`InferError::AnnotationMismatch`] on conflict. See the implementation
    /// for why the reverse direction is wrong, and
    /// `src/ccl/design/type-inference.md`, "Annotation kinds: exact and bounded"
    /// for the two forms this obligation serves.
    ///
    /// **Returns the normalized annotation**, because normalizing is not
    /// idempotent: a `Hole` or a [`Type::Below`] mints a fresh variable each time,
    /// so a caller that both reconciles against an annotation and binds at it must
    /// use one normalization for both or it relates two unrelated variables.
    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<Type, LocatedInferError>;

    /// Obtain the type for a binder slot that lives on a
    /// [`TypedBinding`](crate::ccl::TypedBinding) rather than an [`Expr`] (a
    /// `Case` pattern payload, a `Loop` accumulator) — a place the tree walk
    /// wouldn't otherwise reach.
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
    ) -> Result<(Type, Type), LocatedInferError>;

    /// Dual of [`Typing::as_function`], for a node that *provides* a function
    /// shape rather than being consumed at one. Emit records the one-way
    /// `domain ⇒ codomain <: t`, depositing the shape as a lower bound on the
    /// node's own type seed (positive-position coalesce then resolves the seed
    /// to that function). Used at `Proj`, whose `node_ty` is a fresh seed. In
    /// Check `t` is already resolved, so it destructures exactly like
    /// [`Typing::as_function`].
    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError>;

    /// Relate an applied argument to the function's parameter domain.
    ///
    /// One-way in both Emit and Check: the sound subtyping rule `arg <: domain`
    /// (the argument must fit the parameter, so a *refined* argument may flow
    /// into an unrefined parameter — dropping a restriction is admissible).
    ///
    /// This is half of the one-way Apply story; the other half is the shape
    /// edge `fn_ty <: domain ⇒ codomain` ([`Typing::as_function`]). Neither
    /// edge has an emit-time reverse, deliberately:
    ///
    /// - A reverse `domain <: arg` would pre-deposit the argument's shape on
    ///   the domain var's upper edge *and* eagerly propagate it across the
    ///   connected component — load-bearing but over-reaching, and not
    ///   replaceable by a general two-sided `Var <: Var` rule (that corrupts
    ///   mutually-bounded-but-distinct join vars).
    /// - A reverse `domain ⇒ codomain <: fn_ty` would turn every application's
    ///   function shape into an equality, creating var⇄var cycles linked
    ///   across call chains — the mesh that forces the constraint cache to
    ///   dedup on bare `(lhs, rhs)` pairs and blocks a fully one-way solver.
    ///
    /// The price of one-way edges is that a contravariant domain var only ever
    /// receives what the function's *body* demands, so it coalesces
    /// under-determined: a `Proj` constrains just the one field it touches; a
    /// lambda's record param narrows to the fields its body reads, sparsely
    /// touched tuples shorten, untouched params stay `Infer`. The full shape —
    /// the value actually flowing in — is recovered *structurally* in
    /// `coalesce_node` (its `Apply`/`Compose` arms) by monomorphizing the
    /// morphism to its input
    /// ([`specialize_projection_domain`](super::solve::specialize_projection_domain) /
    /// [`specialize_lambda_domain`](super::solve::specialize_lambda_domain)),
    /// the closed-form case of the same use-site specialization
    /// [`specialize_use`](super::solve::specialize_use) performs for generalized
    /// `let`s.
    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), LocatedInferError>;

    /// Type an application `function(argument)`.
    ///
    /// The result is the function's codomain with its Pi binder *discharged* to
    /// the argument — `codomain[binder ↦ argument]` — so a dependent refinement
    /// in the codomain reflects the actual argument (design §5). For an ordinary
    /// (non-dependent) function the discharge is vacuous and this is the plain
    /// codomain.
    ///
    /// Emit constrains `fn_ty <: (x: arg) ⇒ result` against a *named* expected
    /// Pi (whose codomain edge derives the binder correspondence) and returns
    /// `result` under a suspended discharge that fires at coalesce. Check
    /// destructures the already-resolved function and re-runs the discharge on
    /// its concrete codomain, so its reconstruction matches the recorded type.
    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        at: &dyn Fn() -> String,
    ) -> Result<Type, LocatedInferError>;
}

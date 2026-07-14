// ---------------------------------------------------------------------------
// InferCtx (Step 7c)
// ---------------------------------------------------------------------------

use std::collections::HashMap;

use crate::ccl::infer::InferError;
use crate::ccl::infer::solver::{
    ConstrainCache, PolyScheme, constrain_subtype, fresh_var, fun, type_level,
};
use crate::ccl::{Expr, Level, Name, Type, TypedExprNode};
use crate::util::ScopeStack;

use super::emit::emit_node;
use super::schemes::OperatorSchemes;
use super::typing::Typing;
use super::{coalesce_for_error, map_constrain_err};

/// A lexical-scope entry: the binder's polymorphic scheme.
///
/// The solver works directly on [`Type`]: each node's inferred type (and each
/// binder's `.ty`) is written into the AST during emission and resolved in
/// place during coalesce.
pub(super) struct Binding {
    /// The binder's scheme. Monomorphic binders quantify nothing (cutoff at
    /// their introduction level); a generalized `let` quantifies its RHS-local
    /// variables, so each `Var` use [`PolyScheme::instantiate`]s a fresh copy.
    /// Use-site *monomorphization* (turning each instantiation into concrete
    /// code) happens during the coalesce walk
    /// ([`specialize_use`](super::solve::specialize_use)).
    pub(super) scheme: PolyScheme,
}

/// Whether a `let` bound to `def` at `level` should be **generalized** —
/// typed polymorphically, with each use [`PolyScheme::instantiate`]ing a fresh
/// copy and the coalesce walk specializing per distinct resolved use type
/// ([`specialize_use`](super::solve::specialize_use)). Requires both of:
///
/// - **A function definition** (`def` is a `Lambda`). Let-polymorphism
///   generalizes function definitions; value bindings stay monomorphic and
///   *shared* — specializing a value would duplicate it, which breaks
///   structures that rely on sharing (e.g. a deferred-feed value used in
///   `y ++ y`).
/// - **A genuinely polymorphic type** — some variable deeper than `level` to
///   quantify. A function with no quantifiable variable is already monomorphic,
///   so generalizing it would be a no-op.
///
/// This is the single predicate emission
/// ([`emit_let`](super::emit::emit_let)), privatization, and the coalesce walk
/// all consult, so they agree on which `let`s are polymorphic. It deliberately
/// makes *no* use-count or generator distinction: a single-use function
/// generalizes to one specialization (later inlined like any monomorphic def),
/// and a generator/collection-producing UDF generalizes to one specialization
/// *per distinct element type*, which `inline` then leaves shared (cached)
/// rather than duplicated.
pub(super) fn should_generalize(def: &Expr, level: Level) -> bool {
    matches!(def.node, TypedExprNode::Lambda { .. }) && type_level(&def.ty) > level
}

/// Emission context for Cambra's inference algorithm (Pass 1).
///
/// The solver works directly on [`Type`]: each node's inferred type is written
/// into the AST during emission and resolved in place during coalesce — there
/// is no side table.
pub(super) struct InferCtx {
    /// Lexical scope: name → [`Binding`] for in-scope variables and let-bound
    /// names. Lambda params and `Case`/`Loop` binders bind monomorphically; a
    /// polymorphic `let` additionally stashes its typed definition subtree so
    /// each use site can splice a freshened, use-specialized copy (see
    /// `scoped_let` and the `Var` arm of `emit_node`).
    pub(super) scopes: ScopeStack<Name, Binding>,
    /// Externally-registered data sources (set by
    /// `TypeInferenceContext::register_source_type`).
    pub(super) sources: HashMap<String, Type>,
    /// Constraint cycle cache, shared across one full inference pass.
    cache: ConstrainCache,
    /// Operator/projection scheme registry.
    pub(super) schemes: OperatorSchemes,
    /// Current polymorphism level. Bumped while emitting a `let` RHS (see
    /// `in_let_rhs`) so RHS-local variables are minted deeper than the
    /// defining scope and become generalizable at the binding site.
    pub(super) level: Level,
}

impl InferCtx {
    pub(super) fn new(sources: HashMap<String, Type>) -> Self {
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
    /// wrappers (refinements ride the lattice as refinement witnesses) — is
    /// kept, recursing to normalize nested holes.
    pub(super) fn normalize_annotation(&self, ty: &Type) -> Type {
        match ty {
            // A `Hole` annotation means "infer this" → fresh variable.
            Type::Hole => fresh_var(self.level),
            // Refinements ride the lattice: keep the wrapper, normalize the
            // inner (so a `Refinement(Hole, r)` source annotation becomes
            // `Refinement(?fresh, r)` rather than losing the witness).
            Type::Refinement(inner, r) => {
                Type::Refinement(Box::new(self.normalize_annotation(inner)), r.clone())
            }
            // Structural types are already solver-ready; recurse to
            // normalize any nested holes/refinements.
            Type::Fun {
                name,
                kind,
                domain: d,
                codomain: c,
            } => Type::Fun {
                name: name.clone(),
                kind: *kind,
                domain: Box::new(self.normalize_annotation(d)),
                codomain: Box::new(self.normalize_annotation(c)),
            },
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
            // Structural recursion like `Fun` — normalizing each child turns a
            // nested `Hole` into a fresh var. (No `Mut`-specific `Hole` logic
            // here; that belongs to a later increment.)
            Type::History {
                value,
                domain,
                kind,
            } => Type::History {
                value: Box::new(self.normalize_annotation(value)),
                domain: Box::new(self.normalize_annotation(domain)),
                kind: *kind,
            },
            Type::Sigma(s) => Type::sigma(
                s.name.clone(),
                s.choices
                    .iter()
                    .map(|t| self.normalize_annotation(t))
                    .collect(),
                s.pi_name.clone(),
                self.normalize_annotation(&s.codomain),
            ),
            // Leaves and existing inference vars pass through unchanged.
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn
            | Type::Infer(_) => ty.clone(),
        }
    }
}

impl Typing for InferCtx {
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

    fn scoped<R>(&mut self, name: &Name, ty: &Type, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push_scope();
        // Monomorphic binder: lambda params and pattern/loop binders are not
        // generalized. The scheme's cutoff is the *current* level, not 0:
        // these binders' variables are minted at `self.level` (a `let` RHS may
        // have bumped it), and a cutoff below that would wrongly quantify them,
        // freshening the binder on every use and severing it from its body
        // constraints. `poly(self.level, ty)` quantifies nothing at this level,
        // so `instantiate` returns the binder's variables verbatim.
        self.scopes.bind(
            name,
            Binding {
                scheme: PolyScheme::poly(self.level, ty.clone()),
            },
        );
        let r = f(self);
        self.scopes.pop_scope();
        r
    }

    fn in_let_rhs<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // Mint RHS-local variables one level deeper than the defining scope,
        // so generalization at the binding site (the outer level) quantifies
        // exactly those variables. Restore the level on the way out.
        self.level += 1;
        let r = f(self);
        self.level -= 1;
        r
    }

    fn is_generalizable(&self, def: &Expr) -> bool {
        should_generalize(def, self.level)
    }

    fn scoped_let<R>(
        &mut self,
        name: &Name,
        bound_ty: &Type,
        generalize: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        // Generalize at the current (outer) level: any variable in `bound_ty`
        // whose level exceeds `self.level` was minted inside the RHS and is
        // universally quantified; `instantiate` freshens it per use site.
        // Variables that escaped to an outer scope were already lowered to
        // `self.level` (or below) by `extrude` during constraint solving, so
        // they stay fixed. (Sound to generalize unconditionally because CCL is
        // a pure value language — no value-restriction hazard.)
        let scheme = if generalize {
            // Polymorphic: generalize at the outer level. Each `Var` use
            // instantiates a fresh copy; the coalesce walk then specializes
            // the definition per distinct resolved use type
            // (`specialize_use`).
            PolyScheme::poly(self.level, bound_ty.clone())
        } else {
            // Monomorphic: bind verbatim with a cutoff above the RHS level so
            // `instantiate` freshens nothing — uses stay as `Var` references and
            // share the binding's variables (the pre-let-poly behavior). Handled
            // structurally / by the `inline` pass downstream.
            PolyScheme::poly(self.level + 1, bound_ty.clone())
        };
        self.scopes.push_scope();
        self.scopes.bind(name, Binding { scheme });
        let r = f(self);
        self.scopes.pop_scope();
        r
    }

    fn close_let_type(&self, _name: &Name, _bound_expr: &Expr, body_ty: Type) -> Type {
        // No-op: the closing discharge runs on the resolved type in
        // `coalesce_node`'s Let arm (see the trait doc).
        body_ty
    }

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), InferError> {
        // Shared by *binder* annotations (trait call sites in the emit rules)
        // and *node* annotations (`emit_node`'s `user_annotation` tail) — the
        // reconciliation is identical: annotation wins on success, conflict
        // surfaces as AnnotationMismatch.
        //
        // Two-way constrain_subtype == equality. This eagerly detects
        // conflicts (a body constrains the binder to T, the annotation says
        // U ≠ T → propagation fails immediately → AnnotationMismatch).
        // One-way-only would defer the conflict to coalesce.
        //
        // KNOWN OVER-RESTRICTION: an ascription `x: T = e` only *needs*
        // `inferred <: T` (the value is usable where T is expected). The
        // reverse direction (`T <: inferred`) additionally rejects a value
        // whose inferred type is a *strict subtype* of the annotation — e.g.
        // a variant inferred as `{A}` annotated at the wider `{A | B}`, which
        // is a sound widening. So the right rule for any annotation with a
        // non-trivial subtyping lattice (variants, `UIntRange`) is one-way
        // `inferred <: ann` in positive position.
        //
        // The over-restriction is currently unreachable, but NOT for the
        // reason the old comment here claimed (it referenced the long-removed
        // `Type::Union` and a `normalize_annotation` Union→fresh_var step that
        // no longer exists — `normalize_annotation` now recurses structurally
        // through `Type::Variant`). The actual reason: `lower_type_annotation`
        // (`lower.rs`) only lowers `int`/`str`/`bool`/`None` annotations from
        // source, all of which are `Type::Base` leaves where two-way ≡ one-way
        // (distinct bases are incomparable; equal bases compare reflexively).
        // The other annotation producer — `channelize`' filter-feed
        // `Fun(Refinement(Hole, r), Hole)` shapes — is Hole-based: normalized
        // Holes become fresh vars, where the two directions record symmetric
        // bounds (the intended "annotation wins" propagation) rather than
        // rejecting anything.
        //
        // Switching to one-way is a soundness-and-completeness change to the
        // inference core, untestable from source today; make it one-way, with
        // AST-level tests, when variant/range annotations become
        // source-reachable. (The `#[ignore]`d `variant_param_accepts_subtype`
        // in `tests/inference_variants.rs` exercises the widening at an apply
        // site; with the Apply edges now one-way it infers the widened variant
        // correctly and fails only on variant tag *ordering*.)
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

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), InferError> {
        let d = self.fresh();
        let c = self.fresh();
        // One-way `domain ⇒ codomain <: t`: the node supplies the function
        // shape as a lower bound on its own seed; nothing flows back into
        // `d`/`c` from `t`'s other bounds.
        self.require_sub(&fun(d.clone(), c.clone()), t, at)?;
        Ok((d, c))
    }

    fn constrain_argument(
        &mut self,
        arg: &Type,
        domain: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(), InferError> {
        // One-way: the sound subtyping rule `arg <: domain` (the argument must fit
        // the parameter). The contravariant domain var's shape — the record/tuple
        // actually flowing in — is recovered structurally in `coalesce_node` (its
        // `Apply` arm rebuilds a projection's domain from the resolved argument,
        // just as the `Compose` arm rebuilds a non-leading projection's domain from
        // the preceding morphism's codomain), rather than pre-deposited here by a
        // reverse `domain <: arg`. See the trait-method docs.
        self.require_sub(arg, domain, at)
    }

    fn apply(
        &mut self,
        fn_ty: &Type,
        arg_ty: &Type,
        argument: &Expr,
        at: &dyn Fn() -> String,
    ) -> Result<Type, InferError> {
        // Expect a *named* Pi `(x: d) ⇒ result`, so the codomain edge derives the
        // binder correspondence when `fn_ty`'s real Pi flows in (constrain's
        // Fun/Fun arm). The shape edge is one-way (`fn_ty <: (x: d) ⇒ result`),
        // matching `constrain_argument`'s one-way rule — the contravariant
        // domain a morphism loses under one-way edges is recovered structurally
        // at coalesce (see `Typing::constrain_argument`); only the expected
        // shape gained a binder.        //
        // No binder reuse: bounds are stored in their native two-sided form
        // (see `Bound`), so the discharge `[x ↦ arg]` composes through the
        // correspondence and reaches the predicate at *every* polarity and in
        // *every* constraint order — including the opaque/higher-order case
        // where `fn_ty` is still a variable here and its concrete Pi arrives
        // only later (design O3). The fresh binder also keeps the §3.6
        // global-freshness discipline (reusing a function's own binder as the
        // expected binder would violate it).
        let x = Name::solver_arg();
        let d = self.fresh();
        let result = self.fresh();
        let expected = Type::pi(&x, d.clone(), result.clone());
        self.require_sub(fn_ty, &expected, at)?;
        self.constrain_argument(arg_ty, &d, at)?;
        // The application's type is `result` with the binder discharged to the
        // argument. The discharge rides a fresh var's lower edge and fires at
        // coalesce, composing with the correspondence rename `[k ↦ x]` to the
        // effective `[k ↦ argument]` (design §5.2). For a non-dependent codomain
        // `result` does not mention `x`, so the discharge is vacuous.
        let applied = self.fresh();
        // `fresh()` always yields an `Infer` var; the discharge *must* be
        // recorded on its edge or the dependent application silently loses its
        // substitution, so state the invariant rather than guarding it away.
        let Type::Infer(v) = &applied else {
            unreachable!("fresh() yields a Type::Infer var");
        };
        v.bounds
            .borrow_mut()
            .lower
            .push(crate::ccl::Bound::with_subst(
                result,
                crate::ccl::subst::Subst::discharge(&x, argument.clone()),
            ));
        Ok(applied)
    }
}

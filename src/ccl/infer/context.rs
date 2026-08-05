// ---------------------------------------------------------------------------
// InferCtx (Step 7c)
// ---------------------------------------------------------------------------

use std::collections::HashMap;

use crate::ccl::ccl_utils::TermMemo;
use crate::ccl::infer::solver::{
    ConstrainCache, PolyScheme, constrain_subtype, fresh_var, fun, type_level,
};
use std::rc::Rc;

use crate::ccl::infer::{InferError, LocatedInferError};
use crate::ccl::provenance::NodeId;
use crate::ccl::{Expr, Level, Lit, Name, Refinement, Type, TypedExpr, TypedExprNode};
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
/// copy and the coalesce walk specializing per distinct use instantiation
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
    pred_memo: TermMemo,
    /// One predicate `Rc` per distinct literal *value*, for the singleton
    /// refinements `emit_node` stamps on `Lit` nodes.
    ///
    /// Without this every literal *occurrence* mints its own `{Int | __elem == 5}`,
    /// so a program's literals become a large family of structurally-equal but
    /// `Rc`-distinct predicates — exactly the shape that defeats planning's
    /// `Rc`-keyed compile memo and makes it compile one trivial predicate once per
    /// occurrence. Interning at birth is the cheapest place to prevent it: the
    /// term is ground (see [`singleton_predicate`](super::singleton_predicate)), so
    /// sharing it carries none of the context-dependence that makes sharing
    /// delicate elsewhere.
    lit_singletons: HashMap<Lit, Rc<TypedExpr>>,
    /// The node whose typing rule is currently running, maintained by the
    /// [`emit_node`](super::emit::emit_node) wrapper: set on entry and restored
    /// on exit, error path included. Read only through
    /// [`Typing::current_node`](super::typing::Typing::current_node), to stamp an
    /// error being raised — never after the walk unwinds, so it always names the
    /// node under emission and nothing else. Provenance metadata for
    /// diagnostics; it never influences inference.
    ///
    /// Not an `Option`: it is **seeded with the tree's root id** at construction,
    /// so a rule always has a node to blame. Nothing can raise before the root
    /// frame opens (the walk's first act is to enter it), but if the code ever
    /// grew such a path, the root is a truthful blame rather than an absent one —
    /// which is what lets `LocatedInferError` require a node instead of carrying
    /// an `Option` that every consumer must then interpret.
    current_node_id: NodeId,
    /// Obligations the solver could not decide during emission because one side
    /// was an unreduced [`Type::App`], each tagged with the node and label of the
    /// rule that raised it. Drained by
    /// [`check_parked_obligations`](Self::check_parked_obligations) once emission
    /// completes; see [`require_sub`](Self::require_sub).
    parked: Vec<ParkedObligation>,
}

/// A subtyping obligation deferred out of constraint emission, with the blame it
/// will need if it turns out to fail.
///
/// The types are held **by variable**, not by value: a `Type::Infer` clone shares
/// its `Rc<InferVar>`, so a parked obligation sees every bound recorded after it
/// was parked. That is the whole point — parking exists to read the graph once it
/// has stopped moving.
struct ParkedObligation {
    lhs: Type,
    rhs: Type,
    node: NodeId,
    label: String,
}

impl InferCtx {
    /// `root` seeds [`current_node_id`](Self::current_node_id) so the context is
    /// never in a state where an error has no node to blame.
    pub(super) fn new(sources: HashMap<String, Type>, root: NodeId) -> Self {
        Self {
            scopes: ScopeStack::default(),
            sources,
            cache: ConstrainCache::new(),
            schemes: OperatorSchemes::new(),
            level: 0,
            pred_memo: Default::default(),
            lit_singletons: HashMap::new(),
            current_node_id: root,
            parked: Vec::new(),
        }
    }

    /// Enter `node`'s rule, returning the previous node for the caller to
    /// restore. Only [`emit_node`](super::emit::emit_node) calls this.
    pub(super) fn enter_node(&mut self, node: NodeId) -> NodeId {
        std::mem::replace(&mut self.current_node_id, node)
    }

    /// Restore the node whose rule is running, on both exit paths.
    pub(super) fn leave_node(&mut self, prev: NodeId) {
        self.current_node_id = prev;
    }

    /// Normalize a user annotation / source type into a solver-ready
    /// `Type`: every `Hole` becomes a fresh inference variable at the
    /// current level. Everything else — including existing `Infer` vars,
    /// the structural variants the solver operates on, and `Refinement`
    /// wrappers (refinements ride the lattice as refinements) — is
    /// kept, recursing to normalize nested holes.
    pub(super) fn normalize_annotation(&self, ty: &Type) -> Type {
        match ty {
            // A `Hole` annotation means "infer this" → fresh variable.
            Type::Hole => fresh_var(self.level),
            // Refinements ride the lattice: keep the wrapper, normalize the
            // inner (so a `Refinement(Hole, r)` source annotation becomes
            // `Refinement(?fresh, r)` rather than losing the refinement).
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
                kind: kind.clone(),
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
            // Leaves and existing inference vars pass through unchanged.
            // A type function normalizes argumentwise; the function itself is data.
            Type::App { fun, args } => Type::App {
                fun: fun.clone(),
                args: args.iter().map(|a| self.normalize_annotation(a)).collect(),
            },
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn
            | Type::Infer(_) => ty.clone(),
        }
    }
}

impl InferCtx {
    /// `lit`'s singleton type, with its predicate shared across every occurrence
    /// of the same literal value in this pass (see [`Self::lit_singletons`]).
    pub(super) fn lit_singleton(&mut self, lit: &Lit) -> Type {
        let base = super::lit_base(lit);
        let Some(predicate) = self.lit_singletons.get(lit).cloned().or_else(|| {
            let p = super::singleton_predicate(lit)?;
            self.lit_singletons.insert(lit.clone(), Rc::clone(&p));
            Some(p)
        }) else {
            // `unit`: a singleton adds nothing to a one-inhabitant base.
            return base;
        };
        Type::Refinement(Box::new(base), Refinement::sharing(&predicate))
    }

    /// Record one emission-time subtyping obligation, claiming whatever the solver
    /// parks while doing so.
    ///
    /// **Every** emission-time `constrain_subtype` goes through here. A parked
    /// obligation is only ever retried if something tagged it with a node to blame,
    /// and the solver has no node cursor — so a call that bypassed this would
    /// silently drop its obligation, which is the exact defect parking exists to
    /// fix. [`check_parked_obligations`](Self::check_parked_obligations) asserts the
    /// solver's park list is empty on the way out, which is what makes a future
    /// bypass loud instead of silent.
    fn constrain_and_claim(
        &mut self,
        sub: &Type,
        sup: &Type,
        label: &dyn Fn() -> String,
    ) -> Result<(), crate::ccl::infer::solver::ConstrainError> {
        let mark = self.cache.parked_len();
        let result = constrain_subtype(sub, sup, &mut self.cache);
        let newly_parked = self.cache.take_parked_from(mark);
        if !newly_parked.is_empty() {
            let node = self.current_node_id;
            let label = label();
            self.parked
                .extend(newly_parked.into_iter().map(|(lhs, rhs)| ParkedObligation {
                    lhs,
                    rhs,
                    node,
                    label: label.clone(),
                }));
        }
        result
    }

    /// Discharge the obligations emission could not decide, now that the graph has
    /// stopped moving.
    ///
    /// Every entry has an unreduced [`Type::App`] on one side or the other, which
    /// `constrain_go` cannot see through *during* emission: reduction resolves the
    /// application's arguments off the bound graph, and reading that graph while it
    /// is still being built is the staleness the demand-driven design exists to rule
    /// out. Between emission and coalesce there is no such hazard — every edge the
    /// program implies has been recorded — so each side materializes to an
    /// `App`-free type and the obligation becomes an ordinary subtyping check.
    ///
    /// **Only fully-determined obligations are checked**, and that is what keeps
    /// this pass from perturbing the very graph it is reading. A side that still
    /// contains a variable after materialization is one the program never
    /// determined; re-constraining it would *record* a bound, which is a graph
    /// mutation after emission and would make a later resolution's answer depend on
    /// whether this pass ran. Skipping is not a hole in the check either — an
    /// undetermined operand is an ambiguous program, and coalesce reports it as
    /// `UnresolvedInfer`. With both sides variable-free the check cannot deposit
    /// anything: there is nothing left to bound.
    ///
    /// A side that fails to materialize is skipped for a different reason: the
    /// failure *is* the diagnostic (`NoCommonBase` for `1 + "a"`), and coalesce
    /// raises it on the node whose type it is, which is a better blame than this
    /// pass could give.
    pub(super) fn check_parked_obligations(&mut self) -> Vec<LocatedInferError> {
        use crate::ccl::infer::solver::ConstrainCache;
        use crate::ccl::subst::type_contains_infer;

        let mut errors = Vec::new();
        for ParkedObligation {
            lhs,
            rhs,
            node,
            label,
        } in std::mem::take(&mut self.parked)
        {
            let (Ok(lhs), Ok(rhs)) = (
                super::solve::resolve_var_type(&lhs),
                super::solve::resolve_var_type(&rhs),
            ) else {
                continue;
            };
            if type_contains_infer(&lhs) || type_contains_infer(&rhs) {
                continue;
            }
            // Kind-blind for the same reason the post-inference structural check is
            // (see `ConstrainCache`): both sides have been through coalesce, which
            // canonicalizes every reconstructed arrow's kind, so a kind edge here
            // would be re-deciding a question inference already settled on the
            // pre-coalesce types.
            if let Err(e) = constrain_subtype(&lhs, &rhs, &mut ConstrainCache::new_kind_blind()) {
                errors.push(LocatedInferError {
                    error: map_constrain_err(e, &label),
                    node_id: node,
                });
            }
        }
        debug_assert_eq!(
            self.cache.parked_len(),
            0,
            "an emission-time `constrain_subtype` bypassed `constrain_and_claim`: its \
             parked obligation has no node to blame and would be dropped unchecked"
        );
        errors
    }
}

impl Typing for InferCtx {
    fn pred_memo(&self) -> TermMemo {
        self.pred_memo.clone()
    }

    fn current_node(&self) -> NodeId {
        self.current_node_id
    }

    fn subexpr(&mut self, child: &mut Expr) -> Result<Type, LocatedInferError> {
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
    ) -> Result<(), LocatedInferError> {
        self.constrain_and_claim(sub, sup, at)
            .map_err(|e| self.raise(map_constrain_err(e, &at())))
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
            // the definition per distinct use instantiation
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

    fn bind_annotation(&mut self, inferred: &Type, ann: &Type) -> Result<(), LocatedInferError> {
        // Shared by *binder* annotations (trait call sites in the emit rules)
        // and *node* annotations (`emit_node`'s `user_annotation` tail) — the
        // reconciliation is identical: annotation wins on success, conflict
        // surfaces as AnnotationMismatch.
        //
        // **One-way**: `inferred <: ann`. An ascription `x: T = e` needs exactly
        // that — the value must be usable where `T` is expected — and nothing more.
        //
        // The reverse direction (`ann <: inferred`) additionally rejected a value
        // whose inferred type is a *strict subtype* of its annotation, which is a
        // sound widening, not an error: `x: Int = 1` with `1 : {Int | __elem == 1}`,
        // or a variant inferred as `{A}` annotated at the wider `{A | B}`. It was
        // kept for eager conflict detection, and was harmless only while every
        // source annotation was a `Type::Base` leaf, where the two directions
        // coincide. They no longer do.
        //
        // Information still flows *from* the annotation, so "annotation wins" is
        // preserved: against a `Hole`-based annotation (`channelize`'s filter-feed
        // `Fun(Refinement(Hole, r), Hole)`) the forward edge demands the
        // annotation's refinement of an inferred variable, and the refinement rule
        // flows that deficit onto it rather than rejecting. What changes is *when* a
        // genuine conflict surfaces: at coalesce rather than immediately.
        let ann_simple = self.normalize_annotation(ann);
        // Snapshot the inferred type before the annotation bounds are added so
        // the error shows what was actually inferred, not the partially
        // modified state after a failed constrain_subtype.
        let inferred_ty = coalesce_for_error(inferred);
        let ann_label = ann.to_string();
        self.constrain_and_claim(inferred, &ann_simple, &|| {
            format!("annotation `{ann_label}`")
        })
        .map_err(|_| {
            self.raise(InferError::AnnotationMismatch {
                annotation: ann.clone(),
                inferred: inferred_ty,
            })
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
    ) -> Result<(Type, Type), LocatedInferError> {
        let d = self.fresh();
        let c = self.fresh();
        self.require_sub(t, &fun(d.clone(), c.clone()), at)?;
        Ok((d, c))
    }

    fn provide_function(
        &mut self,
        t: &Type,
        at: &dyn Fn() -> String,
    ) -> Result<(Type, Type), LocatedInferError> {
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
    ) -> Result<(), LocatedInferError> {
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
    ) -> Result<Type, LocatedInferError> {
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
        v.bounds_mut().lower.push(crate::ccl::Bound::with_subst(
            result,
            crate::ccl::subst::Subst::discharge(&x, argument.clone()),
        ));
        Ok(applied)
    }
}

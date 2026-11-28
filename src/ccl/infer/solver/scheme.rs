//! Polymorphic schemes and freshening (instantiation).
//!
//! [`PolyScheme`] is the generalized-type representation; [`freshen_above`]
//! and its helpers mint a fresh copy of a scheme body (or a specialization
//! clone's whole subtree) at a use-site level, renaming quantified variables
//! uniformly across terms, types, refinement predicates, and the suspended
//! discharge payloads riding bound edges.

use super::transport::Side;
use crate::ccl::infer::solver::Solver;
use crate::ccl::infer::solver::held::{Held, HeldKey, HeldKind};
use crate::ccl::infer::solver::var::{Recorded, SolverVar};
use std::collections::HashMap;
use std::rc::Rc;

use super::traits::TraitObligation;
use crate::ccl::Duplicate;
use crate::ccl::capabilities::{Capabilities, Capability, CapabilityVar, CapabilityVarId, Repr};
use crate::ccl::infer_var::Telescope;
use crate::ccl::subst::Subst;
use crate::ccl::ty::TraitRequirement;
use crate::ccl::ty::{FunKind, FunKindVar};
use crate::ccl::{Bound, InferVar, InferVarId, Level, Type, TypedExpr};

// ---------------------------------------------------------------------------
// Polymorphic schemes
// ---------------------------------------------------------------------------

/// A polymorphic type scheme.
///
/// `body` may contain [`Type::Infer`] vars whose `level` exceeds `level`.
/// Those are the *quantified* variables — at each use site they are
/// replaced with fresh variables via [`PolyScheme::instantiate`]. Vars
/// whose level is ≤ `level` leaked in from an outer scope and stay fixed.
///
/// # Usage
///
/// Two sources of schemes: (1) operator/projection signatures that are
/// inherently polymorphic (`Max : ∀α γ. (α ⤇ γ) ⇒ γ`,
/// `Proj(Index n) : ∀α. {n: α, …} → α`, etc.), built once in
/// `OperatorSchemes`; and (2) let-generalization — a multi-use function
/// binding is generalized into a `PolyScheme` at its binding level
/// (`infer::context::scoped_let`) and `instantiate`d per use. See
/// `design/type-inference.md` for the rationale.
#[derive(Debug, Clone)]
pub struct PolyScheme {
    /// Quantification cutoff: vars in `body` at level > `self.level`
    /// are universally quantified.
    pub level: Level,
    /// Scheme body. May contain quantified vars (level > self.level)
    /// and free vars (level ≤ self.level).
    pub body: Type,
    /// The `requires` clause of a binding annotated with a polymorphic type, over
    /// its opened type parameters: what each use instantiates as trait obligations
    /// beside the body (`src/ccl/design/type-parameters.md`, "Instantiation"). Empty
    /// for every other scheme, whose obligations ride the body's variables.
    pub requires: Vec<Rc<TraitRequirement>>,
}

/// One use's copy of a [`PolyScheme`] ([`PolyScheme::instantiate_with_params`]).
pub struct Instance {
    /// The body, freshened.
    pub ty: Type,
    /// Each type parameter's instantiation with its bound, freshened through the
    /// same copy, and where the bound was written: the use records
    /// `instantiation <: bound`.
    pub bounds: Vec<(Type, Type, Option<chl_parser::ast::Span>)>,
    /// The scheme's `requires` clause, freshened through the same copy: the use
    /// mints an obligation for each.
    pub requires: Vec<TraitRequirement>,
    /// The copy of each capability variable the scheme reaches, by the original's id
    /// ([`FreshenCache::copies`]), which the specialization the use mints takes: a
    /// requirement's associated effect type is linked through it too.
    pub capability_copies: HashMap<CapabilityVarId, Rc<CapabilityVar>>,
    /// The use's copy of each trait obligation the scheme carries: the use answers each under
    /// what it assumes, and links each to the instance it selects
    /// ([`TraitObligation::effects`]).
    pub obligations: Vec<Rc<TraitObligation>>,
}

impl PolyScheme {
    /// A monotype scheme: no quantified variables. Convenience for
    /// scalar operator types like `Bool → Bool`.
    pub fn mono(body: Type) -> Self {
        Self::poly(0, body)
    }

    /// Construct a polytype with the given quantification cutoff.
    pub fn poly(level: Level, body: Type) -> Self {
        Self {
            level,
            body,
            requires: Vec::new(),
        }
    }

    /// This scheme stating `requires`, a polymorphic annotation's `requires` clause.
    pub fn with_requires(self, requires: Vec<Rc<TraitRequirement>>) -> Self {
        Self { requires, ..self }
    }

    /// Mint a fresh copy of `body` with quantified variables replaced
    /// by fresh variables at `current_level`.
    ///
    /// Called at every use site of the scheme to ensure each occurrence
    /// gets independent constraints (e.g. two uses of `Compare` can
    /// compare `Int`s and `String`s respectively without conflict).
    pub fn instantiate(&self, solver: &mut Solver, current_level: Level) -> Type {
        #[cfg(debug_assertions)]
        let before = Minted::now();
        let mut cache = FreshenCache::new();
        let ty = freshen_above(
            solver,
            self.level,
            &self.body,
            FreshenLevel::At(current_level),
            &mut cache,
        );
        #[cfg(debug_assertions)]
        assert_copied_apart(
            solver,
            self.level,
            std::slice::from_ref(&ty),
            &cache,
            before,
        );
        ty
    }

    /// [`instantiate`](Self::instantiate) for a scheme that may quantify **type
    /// parameters** and state a `requires` clause: the body, each parameter's
    /// bound, and each requirement, freshened through one copy, so a parameter is
    /// one variable across all three.
    ///
    /// The caller records `instantiation <: bound` for each bound and an obligation
    /// for each requirement: both are checked at every use, at the use's types
    /// (`src/ccl/design/type-parameters.md`, "Instantiation"). A variable minted for
    /// a parameter stands in `telescope`, the use site's, since a parameter has no
    /// variable a copy could inherit a scope from. Every other variable stands there too,
    /// under the binders its original stood under inside the definition
    /// ([`FreshenCache::use_telescope`]).
    pub fn instantiate_with_params(
        &self,
        solver: &mut Solver,
        current_level: Level,
        telescope: &Telescope,
        use_at: crate::ccl::provenance::NodeId,
        assumptions: &[Rc<TraitRequirement>],
    ) -> Instance {
        #[cfg(debug_assertions)]
        let before = Minted::now();
        let mut cache = FreshenCache::new();
        cache.use_at = Some(use_at);
        cache.use_assumptions = assumptions.to_vec();
        cache.param_telescope = Some(telescope.clone());
        cache.use_telescope = Some(telescope.clone());
        cache.definition_site = Some(telescope.clone());
        let at = FreshenLevel::At(current_level);
        let ty = freshen_above(solver, self.level, &self.body, at, &mut cache);
        let requires: Vec<TraitRequirement> = self
            .requires
            .iter()
            .map(|r| r.map_types(|t| freshen_above(solver, self.level, t, at, &mut cache)))
            .collect();
        // A bound can name a parameter nothing freshened yet, which the bound's own
        // freshening then maps, so the parameters are drained until none is new.
        let mut bounds = Vec::new();
        let mut done = std::collections::HashSet::new();
        loop {
            let mut pending: Vec<_> = cache
                .params
                .values()
                .filter(|(param, _)| !done.contains(&param.id))
                .cloned()
                .collect();
            if pending.is_empty() {
                break;
            }
            pending.sort_by(|a, b| a.0.cmp(&b.0));
            for (param, instantiation) in pending {
                done.insert(param.id);
                // A family parameter this freshening re-opens carries its bound on its own.
                if param.arity > 0 {
                    continue;
                }
                if let Some(bound) = &param.bound {
                    let bound = freshen_above(solver, self.level, bound, at, &mut cache);
                    bounds.push((instantiation, bound, param.bound_at));
                }
            }
        }
        // An instantiated family parameter's variable is below its bound at the variable's own
        // binders ([`FreshenCache::family_params`]).
        let mut families: Vec<_> = cache.family_params.values().cloned().collect();
        families.sort_by(|a, b| a.0.cmp(&b.0));
        for (param, names, var) in families {
            if let Some(bound) = &param.bound {
                let fresh = freshen_above(solver, self.level, bound, at, &mut cache);
                let bound = crate::ccl::subst::family_at_names(solver, &fresh, &names);
                bounds.push((var, bound, param.bound_at));
            }
        }
        let (ty, requires, bounds) = if cache.binders.is_empty() {
            (ty, requires, bounds)
        } else {
            rename_instance_binders(solver, &cache);
            let _f = crate::ccl::provenance::copy_frame("infer.instance_binders");
            let renames: crate::ccl::scope::Renames = cache.binders.clone().into_iter().collect();
            (
                instance_type(solver, &ty, &renames),
                requires
                    .iter()
                    .map(|r| instance_requirement(solver, r, &renames))
                    .collect(),
                bounds
                    .iter()
                    .map(|(v, b, at)| {
                        (
                            instance_type(solver, v, &renames),
                            instance_type(solver, b, &renames),
                            *at,
                        )
                    })
                    .collect(),
            )
        };
        // The instance is the body, each bound with its instantiation, and each requirement.
        #[cfg(debug_assertions)]
        assert_copied_apart_from(solver, self.level, &cache, before, &mut |visit| {
            visit(&ty);
            for (instantiation, bound, _) in &bounds {
                visit(instantiation);
                visit(bound);
            }
            for r in &requires {
                r.args.iter().for_each(&mut *visit);
                r.assoc.iter().for_each(|(_, t)| visit(t));
                r.binders.iter().for_each(|(_, t)| visit(t));
            }
        });
        Instance {
            ty,
            bounds,
            requires,
            capability_copies: cache
                .copies::<Rc<CapabilityVar>>()
                .filter_map(|(key, copy)| match key {
                    HeldKey::Capability(id) => Some((id, copy)),
                    _ => None,
                })
                .collect(),
            obligations: cache
                .copies::<Rc<TraitObligation>>()
                .map(|(_, copy)| copy)
                .collect(),
        }
    }

    /// [`instantiate`](Self::instantiate), stamping the *use site's* telescope
    /// on every variable the instantiation mints. For an operator scheme the
    /// template's variables stand nowhere — they were built outside any
    /// program scope, so inheriting their (empty) telescopes would leave the
    /// instantiation's variables scope-free at a position that has scope, and
    /// a dependent refinement flowing into an operand variable would be an open
    /// record. A *let*-generalized scheme instantiates through
    /// [`instantiate_with_params`](Self::instantiate_with_params), whose variables keep the
    /// binders the definition's own stood under, entered after the use site's
    /// ([`FreshenCache::use_telescope`]).
    pub fn instantiate_in(
        &self,
        solver: &mut Solver,
        current_level: Level,
        telescope: &Telescope,
    ) -> Type {
        #[cfg(debug_assertions)]
        let before = Minted::now();
        let mut cache = FreshenCache::new();
        cache.site_telescope = Some(telescope.clone());
        let ty = freshen_above(
            solver,
            self.level,
            &self.body,
            FreshenLevel::At(current_level),
            &mut cache,
        );
        #[cfg(debug_assertions)]
        assert_copied_apart(
            solver,
            self.level,
            std::slice::from_ref(&ty),
            &cache,
            before,
        );
        ty
    }
}

/// The first variable and funkind variable ids an instantiation could mint: whatever has a smaller
/// id stood before it, and whatever has a larger one the instantiation made.
#[cfg(debug_assertions)]
#[derive(Clone, Copy)]
pub(crate) struct Minted {
    var: InferVarId,
    funkind: crate::ccl::ty::FunKindVarId,
    capability: CapabilityVarId,
}

#[cfg(debug_assertions)]
impl Minted {
    pub(crate) fn now() -> Self {
        Minted {
            var: crate::ccl::infer_var::next_infer_var_id(),
            funkind: crate::ccl::ty::next_fun_kind_var_id(),
            capability: crate::ccl::capabilities::next_capability_var_id(),
        }
    }
}

/// Panic where an instantiation shares with its scheme something above the cutoff `lim`: a
/// variable, a funkind variable or a capability variable that stood before the instantiation (`before`), stands above
/// `lim`, and is reached from the instance, through its structure or a copy's bounds and funkind
/// edges. What stands at or below `lim` is an enclosing scope's and is shared by design; above it,
/// each use owns its own copy, and one shared with the scheme carries whatever a later use
/// records into every other (`src/ccl/design/type-inference.md`, "Funkind variables are copied by
/// level").
#[cfg(debug_assertions)]
fn assert_copied_apart(
    solver: &mut Solver,
    lim: Level,
    roots: &[Type],
    cache: &FreshenCache,
    before: Minted,
) {
    assert_copied_apart_from(solver, lim, cache, before, &mut |visit| {
        roots.iter().for_each(visit)
    });
}

/// A walk handing each root type of a copy to the visitor it is given.
#[cfg(debug_assertions)]
pub(crate) type Roots<'a> = dyn FnMut(&mut dyn FnMut(&Type)) + 'a;

/// [`assert_copied_apart`] over the roots `roots` hands its visitor: a specialization's are its
/// clone's type slots, walked in place.
#[cfg(debug_assertions)]
pub(crate) fn assert_copied_apart_from(
    solver: &mut Solver,
    lim: Level,
    cache: &FreshenCache,
    before: Minted,
    roots: &mut Roots<'_>,
) {
    struct Audit<'s> {
        solver: &'s mut Solver,
        lim: Level,
        before: Minted,
        vars: std::collections::HashSet<InferVarId>,
        kinds: std::collections::HashSet<crate::ccl::ty::FunKindVarId>,
        terms: std::collections::HashSet<crate::ccl::PredicateId>,
        /// The copies the cache holds, which a specialization may have taken from its use's
        /// instantiation before `before` (`UseCapabilities::copies`).
        capability_copies: std::collections::HashSet<CapabilityVarId>,
    }
    impl Audit<'_> {
        fn kind(&mut self, kind: &FunKind) {
            if let FunKind::Var(k) = kind {
                let level = k.level(self.solver);
                assert!(
                    k.uid >= self.before.funkind || level <= self.lim,
                    "an instantiation shares a funkind variable above the cutoff {} with its scheme: {k:?}",
                    self.lim
                );
                if level <= self.lim || !self.kinds.insert(k.uid) {
                    return;
                }
                let edges = k.lower_edges(self.solver);
                let upper = k.upper_edges(self.solver);
                for (edge, _) in edges.into_iter().chain(upper) {
                    self.kind(&edge);
                }
            }
            for witness in kind.witnesses() {
                for ty in witness.types() {
                    self.ty(ty);
                }
            }
        }
        fn term(&mut self, term: &Rc<TypedExpr>) {
            if !self.terms.insert(Rc::as_ptr(term)) {
                return;
            }
            self.expr(term);
        }
        fn expr(&mut self, expr: &TypedExpr) {
            expr.walk_type_slots(|ty| self.ty(ty));
            expr.walk_children(|child| self.expr(child));
        }
        fn ty(&mut self, ty: &Type) {
            if let Type::Infer(v) = ty {
                let level = v.level(self.solver);
                assert!(
                    v.uid >= self.before.var || level <= self.lim,
                    "an instantiation shares a variable above the cutoff {} with its scheme: {v:?}",
                    self.lim
                );
                if level <= self.lim || !self.vars.insert(v.uid) {
                    return;
                }
                self.kind(&FunKind::Var(Rc::clone(v.fun_kind())));
                let bounds = v.bounds(self.solver);
                let tys: Vec<Type> = bounds
                    .lower()
                    .iter()
                    .chain(bounds.upper().iter())
                    .map(|b| b.ty.clone())
                    .collect();
                for ty in &tys {
                    self.ty(ty);
                }
            }
            if let Type::Fun {
                fun_kind,
                capabilities,
                ..
            } = ty
            {
                self.kind(fun_kind);
                if let Repr::Var(c) = capabilities.repr() {
                    assert!(
                        c.uid >= self.before.capability
                            || c.level(self.solver) <= self.lim
                            || self.capability_copies.contains(&c.uid),
                        "an instantiation shares a capability variable above the cutoff {} with its scheme: {c:?}",
                        self.lim
                    );
                }
            }
            for r in ty.refinements() {
                self.term(&r.predicate);
            }
            ty.held_terms().for_each(|term| self.term(term));
            ty.walk_children(|child| self.ty(child));
        }
    }
    let mut audit = Audit {
        solver,
        lim,
        before,
        vars: Default::default(),
        kinds: Default::default(),
        terms: Default::default(),
        capability_copies: cache
            .copies::<Rc<CapabilityVar>>()
            .map(|(_, c)| c.uid)
            .collect(),
    };
    roots(&mut |root| audit.ty(root));
    for (_, copy) in cache.copies::<Rc<InferVar>>() {
        audit.ty(&Type::Infer(copy));
    }
    for (_, copy) in cache.copies::<Rc<FunKindVar>>() {
        audit.kind(&FunKind::Var(copy));
    }
}

/// Cache for [`freshen_above`]: each original quantified variable maps to its
/// single fresh replacement so multiple occurrences share the same fresh var,
/// and each quantified channel-domain name ([`Type::ChanDom`]) maps to its
/// single fresh (or pre-seeded — see [`seed_chan_dom_pairings`]) rename.
#[derive(Default)]
pub struct FreshenCache {
    /// The first variable this freshening can mint. Earlier variables keep their existing
    /// witness scopes when a function carrying them is copied.
    pub first_var: Option<InferVarId>,
    /// When set, every variable this freshening mints stands at *this* telescope instead
    /// of its original's — the operator-scheme instantiation mode
    /// ([`PolyScheme::instantiate_in`]). A template's own variables stand nowhere but under
    /// the template's own functions, so an original's telescope holds only those
    /// functions' binders, and the copy enters each after the site's as this
    /// instantiation names it ([`binders`](Self::binders)). Unset for specialization
    /// clones, which stand where their definition stood or under the binders their use
    /// entered ([`entered_binders`](Self::entered_binders)).
    pub site_telescope: Option<Telescope>,
    /// Each solver handle this freshening copied, by the original's key, with its copy: an
    /// inference, barrier, kind or capability variable, an ordering requirement, a trait
    /// obligation ([`HeldKey`]). Every kind is copied once per freshening and the same copy is
    /// read wherever the original is, so two uses of one generalized definition are
    /// constrained apart: a kind forced to `Data` at one use stays open at another, and a
    /// `String` use of `λ 𝑥 → 𝑥 + 1` does not narrow the `Int` use's obligation. A copy is
    /// recorded before the original's state is copied into it, so a cycle reaches the copy.
    pub copies: HashMap<HeldKey, Held>,
    /// Original quantified channel-domain name → its rename. Seeded by
    /// `specialize_use` with use-site pairings; unpaired names mint fresh.
    pub chan_doms: HashMap<crate::ccl::Name, crate::ccl::Name>,
    /// Original kind-variable binder → the copy's binder at the same position.
    ///
    /// A kind variable's binders are quantified with it: they are the scope its edges
    /// rename into (`src/ccl/design/type-inference.md`, "A consumer's binders are a scope,
    /// not a name"), and the references naming them live in the bounds this freshening
    /// copies. Carrying a reference across without the rename leaves the copy's bounds
    /// spelling the definition's binder, which nothing below the copy binds — the same
    /// α-conversion [`Type::alpha_convert_sum`] performs for a written sum and
    /// [`chan_doms`](Self::chan_doms) for a rigid channel name.
    pub witnesses: HashMap<crate::ccl::ty::WitnessId, crate::ccl::ty::WitnessId>,
    /// Original type parameter → what this copy stands it at
    /// (`src/ccl/design/type-parameters.md`, "Instantiation" and "Specialization").
    ///
    /// Instantiation maps each parameter above the cutoff to a fresh variable at the
    /// use's level, which the use then bounds. A specialization clone maps the
    /// specialized binding's own parameters, the ones at the cutoff's next level, to
    /// fresh variables its pin ties to the use's types; a parameter deeper than that
    /// belongs to a definition nested in the clone, which stays generic, so it is
    /// re-minted as a new parameter.
    pub params: HashMap<crate::ccl::ty::TypeParamId, (Rc<crate::ccl::ty::TypeParam>, Type)>,
    /// The scope a variable minted for a type parameter stands in: the use site's,
    /// at instantiation, and the clone's, in a specialization clone. A parameter has no
    /// variable of its own whose telescope a copy could inherit.
    pub param_telescope: Option<Telescope>,
    /// The scope a let-generalized binding's instantiation stands in: the use site's, which
    /// holds the definition site's and every binder entered between the two. Each variable
    /// minted stands there with the binders its original stood under inside the definition
    /// entered after it, so an argument whose type reads a binder of the use site flows into
    /// the instance ([`PolyScheme::instantiate_with_params`]).
    pub use_telescope: Option<Telescope>,
    /// The scope outside which a binder is the copied definition's own: the use site's for an
    /// instantiation, and the one the clone stands in for a specialization clone. Each binder a
    /// copy reads that this scope does not hold is the definition's, and the copy names it
    /// afresh ([`Self::binders`], [`is_definition_binder`]). `None` for a copy that keeps its
    /// original's names.
    pub definition_site: Option<Telescope>,
    /// The binders a specialization clone stands under besides its definition's: those
    /// between the definition and the use that the use's instance reads, which the clone is
    /// placed under (`infer::solve::specialize_use`). Each variable minted stands where its
    /// original did with these entered.
    pub entered_binders: Vec<crate::ccl::Name>,
    /// The obligation copies a specialization clone reset, having assumed one of the
    /// binding's own type parameters ([`Self::own_params`]): each resolves against its trait's
    /// instances once the pin delivers the use's types (`infer::solve::specialize_use`).
    pub reset_obligations: Vec<Rc<TraitObligation>>,
    /// For a specialization clone, the specialized binding's own type parameters:
    /// an obligation copy assuming one is reset
    /// ([`TraitObligation::reset_for_specialization`]), and the rest of its
    /// assumptions are freshened with the clone. `None` for an instantiation.
    pub own_params: Option<Rc<[crate::ccl::ty::TypeParamId]>>,
    /// The use an instantiation or a specialization clone is made for, where each copy of an
    /// ordering requirement is reported (`docs/chl-spec.md`, "Conditional ordering
    /// requirements"). `None` for a copy no use makes.
    pub use_at: Option<crate::ccl::provenance::NodeId>,
    /// The assumptions in scope at that use: each copy of a trait obligation or an ordering
    /// requirement made for the use is answered under them too, its instantiation's and its
    /// specialization's alike.
    pub use_assumptions: Vec<Rc<TraitRequirement>>,
    /// An operator scheme's Pi binder → the name this instantiation gives it.
    pub binders: HashMap<crate::ccl::Name, crate::ccl::Name>,
    /// The names in `binders`' values: each a name [`Self::binder_name`] minted.
    pub(crate) minted_binders: std::collections::HashSet<crate::ccl::Name>,
    /// Opened family parameter → what this instantiation stands it at: a variable that may
    /// read the binders beside it, one per term the parameter is applied to. An application
    /// is the variable with those binders discharged to its terms
    /// (`src/ccl/design/nominal-types.md`, "Family parameters").
    pub family_params: HashMap<
        crate::ccl::ty::TypeParamId,
        (Rc<crate::ccl::ty::TypeParam>, Vec<crate::ccl::Name>, Type),
    >,
    /// The funkind variables whose copies a copy's fixed part minted ahead of it
    /// ([`mint_ahead`]), in the order minted, each still to be recorded on.
    pub(crate) minted_ahead: Vec<Rc<FunKindVar>>,
    /// The ordering requirements whose copies are being built ([`copy_ordering`]): one is
    /// registered only once built, so a cycle back to it from its parts is not a copy.
    pub(crate) orderings_building: Vec<HeldKey>,
    /// Capabilities naming a requirement whose copy is being built, each recorded on its copy
    /// once that requirement is registered ([`WaitingCapability`]).
    pub(crate) waiting: Vec<WaitingCapability>,
}

impl FreshenCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// The scope a copy of a variable standing in `original` stands in.
    ///
    /// An operator scheme's template stands nowhere but under its own functions' binders, so the
    /// copy enters each, as this instantiation names it, after the site's
    /// ([`Self::site_telescope`]). A let-generalized binding's instance stands at the use with
    /// the binders its original stood under inside the definition entered after it, each of the
    /// definition's own under the instance's name ([`Self::binders`]);
    /// [`rename_instance_binders`] carries the renames into what the copies' bounds read. A
    /// specialization clone stands where its original did, each of the definition's own binders
    /// under the clone's name, with the binders its use entered ([`Self::entered_binders`]).
    pub(crate) fn copied_telescope(&mut self, original: &Telescope) -> Telescope {
        if let Some(site) = self.site_telescope.clone() {
            let mut template: Vec<_> = original.iter().cloned().collect();
            template.reverse();
            return template
                .into_iter()
                .fold(site, |t, n| t.extended(self.binder_name(&n)));
        }
        match self.use_telescope.clone() {
            Some(site) => site.entered_from_as(original, |n| {
                if is_definition_binder(&site, n) && !self.names_instance_binder(n) {
                    self.binder_name(n)
                } else {
                    n.clone()
                }
            }),
            None => {
                let renamed = match self.definition_site.clone() {
                    Some(site) => {
                        let mut entries: Vec<crate::ccl::Name> = original
                            .iter()
                            .map(|n| {
                                if is_definition_binder(&site, n) && !self.names_instance_binder(n)
                                {
                                    self.binder_name(n)
                                } else {
                                    n.clone()
                                }
                            })
                            .collect();
                        entries.reverse();
                        entries
                            .into_iter()
                            .fold(Telescope::empty(), |t, n| t.extended(n))
                    }
                    None => original.clone(),
                };
                renamed.entered(self.entered_binders.iter().cloned())
            }
        }
    }

    /// This freshening's copy of `original`, if it has made one.
    pub fn copy_of<K: HeldKind + Clone>(&self, original: &K) -> Option<K> {
        self.copies
            .get(&original.held_key())
            .and_then(K::from_held)
            .cloned()
    }

    /// Record `copy` as this freshening's copy of `original`.
    pub fn record_copy<K: HeldKind>(&mut self, original: &K, copy: K) {
        let previous = self.copies.insert(original.held_key(), copy.into_held());
        debug_assert!(
            previous.is_none(),
            "{:?} was copied twice by one freshening: a copy is registered before anything is \
             freshened from its original, so a cycle back to the original finds it",
            original.held_key(),
        );
    }

    /// Each copy of one kind of handle, by its original's key.
    pub fn copies<K: HeldKind + Clone>(&self) -> impl Iterator<Item = (HeldKey, K)> + '_ {
        self.copies
            .iter()
            .filter_map(|(key, held)| K::from_held(held).map(|k| (*key, k.clone())))
    }

    /// The name a copied function, dependent-tuple or family binder `n` takes in this copy. An
    /// operator scheme's template binds every binder it names, so each is named afresh. A
    /// definition's copy names afresh only the definition's own binders
    /// ([`is_definition_binder`]), as it does in telescopes and substitutions: a label naming a
    /// binder bound outside the definition stays the one variables and substitutions read.
    fn label_name(&mut self, n: &crate::ccl::Name) -> crate::ccl::Name {
        if self.site_telescope.is_some() {
            return self.binder_name(n);
        }
        match self.definition_site.clone() {
            Some(site) if is_definition_binder(&site, n) => self.binder_name(n),
            _ => n.clone(),
        }
    }

    /// The renames this instance owes `names`: each of the definition's binders among them, to
    /// the name this instance gives it ([`is_definition_binder`]). Empty for a freshening that
    /// keeps its definition's names.
    fn instance_renames(
        &mut self,
        names: impl IntoIterator<Item = crate::ccl::Name>,
    ) -> crate::ccl::scope::Renames {
        let Some(site) = self.definition_site.clone() else {
            return crate::ccl::scope::Renames::new();
        };
        let owed: Vec<crate::ccl::Name> = names
            .into_iter()
            .filter(|n| is_definition_binder(&site, n) && !self.names_instance_binder(n))
            .collect();
        owed.into_iter()
            .map(|n| {
                let to = self.binder_name(&n);
                (n, to)
            })
            .collect()
    }

    /// Whether `n` is a name this freshening gave one of the definition's binders: the
    /// instance's own, already renamed.
    fn names_instance_binder(&self, n: &crate::ccl::Name) -> bool {
        self.minted_binders.contains(n)
    }

    /// `item` with each of the copied definition's own binders it names under this copy's name
    /// for it ([`Self::instance_renames`]).
    fn renamed_capability(&mut self, item: &Capability) -> Capability {
        let names: Vec<crate::ccl::Name> = match item {
            Capability::Requires(r) => r.requirement().terms.clone(),
            Capability::Causes(e) => e.variable().cloned().into_iter().collect(),
            Capability::Param(_) | Capability::Every(_) => Vec::new(),
        };
        let renames = self.instance_renames(names);
        if renames.is_empty() {
            return item.clone();
        }
        item.renamed(&|n| renames.get(n).cloned().unwrap_or_else(|| n.clone()))
    }

    /// Name afresh each of `names` that is the copied definition's own binder
    /// ([`is_definition_binder`]): a clone's term binders, named before its types are copied so
    /// the two agree.
    pub fn name_definition_binders(&mut self, names: impl IntoIterator<Item = crate::ccl::Name>) {
        self.instance_renames(names);
    }

    /// The name this freshening gives the binder `n`, minted the first time it is asked. A name
    /// this freshening minted is already the instance's and is its own.
    fn binder_name(&mut self, n: &crate::ccl::Name) -> crate::ccl::Name {
        if self.names_instance_binder(n) {
            return n.clone();
        }
        let minted = &mut self.minted_binders;
        self.binders
            .entry(n.clone())
            .or_insert_with(|| {
                let to = crate::ccl::Name::fresh_like(n);
                minted.insert(to.clone());
                to
            })
            .clone()
    }
}

/// Whether `n`, read in a let-generalized binding's instantiation for a use standing in `site`, is
/// a binder the definition binds. Each binder is bound in one place, so one the use stands under
/// is bound outside the definition, and every other binder an instantiation reads is the
/// definition's own. An element reference is a refinement's and a de Bruijn reference a function
/// type's, not binders; a raw name is a builtin's or a fixture's and is not re-minted.
fn is_definition_binder(site: &Telescope, n: &crate::ccl::Name) -> bool {
    matches!(
        n,
        crate::ccl::Name::Unique { .. } | crate::ccl::Name::Synthetic { .. }
    ) && !site.contains(n)
}

/// The level [`freshen_above`] assigns to each fresh variable it mints.
#[derive(Clone, Copy)]
pub enum FreshenLevel {
    /// Mint every fresh variable at this one level. Use-site instantiation
    /// wants the copy to live at the *use's* level so it integrates with that
    /// site's constraints.
    At(Level),
    /// Mint each fresh variable at its *original* variable's level, preserving
    /// the relative level structure. Per-type specialization
    /// (`infer::solve::specialize_use`) wants this: a definition may
    /// contain nested generalized `let`s whose deeper levels must survive, or
    /// the inner generalization stops being recognized.
    Preserve,
    /// [`Preserve`](Self::Preserve), with every level raised by this much. A
    /// specialization made for a use inside a definition checked alone stands at
    /// least as deep as that definition's opaque type parameters, so they can flow
    /// into it (`src/ccl/design/type-parameters.md`, "Specialization").
    Raise(Level),
}

impl FreshenLevel {
    /// The level a fresh copy of something at `original` is minted at.
    pub fn level_of(self, original: Level) -> Level {
        match self {
            FreshenLevel::At(level) => level,
            FreshenLevel::Preserve => original,
            FreshenLevel::Raise(by) => original + by,
        }
    }
}

/// Freshen a function's kind at instantiation. A variable at or below `lim` belongs to the
/// enclosing scope and is shared. A variable above `lim` is copied through
/// [`copy_var`]. Concrete kinds keep their form, with a sum's candidate
/// types freshened through the same cache.
fn freshen_fun_kind(
    solver: &mut Solver,
    fun_kind: &FunKind,
    lim: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> FunKind {
    match fun_kind {
        FunKind::Compute | FunKind::Data(None) => fun_kind.clone(),
        FunKind::Data(Some(witnesses)) => FunKind::Data(Some(Rc::new(
            witnesses
                .iter()
                .map(|w| w.map_types(|t| freshen_above(solver, lim, t, target, cache)))
                .collect(),
        ))),
        FunKind::Var(kv) => FunKind::Var(freshen_handle(solver, lim, kv, target, cache)),
    }
}

/// `r` as this freshening copies it ([`super::transport::transport_requirement`]).
fn freshen_requirement(
    solver: &mut Solver,
    lim: Level,
    r: &crate::ccl::capabilities::Requirement,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> crate::ccl::capabilities::Requirement {
    super::transport::transport_requirement(solver, r, &mut Copying::new(lim, target, cache))
}

/// A new copy of `r`, an ordering requirement, over its positions, source and capabilities
/// as this freshening copies them ([`freshen_held`]).
fn copy_ordering(
    solver: &mut Solver,
    lim: Level,
    r: &crate::ccl::capabilities::Requirement,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> crate::ccl::capabilities::Requirement {
    let order = r
        .ordering()
        .expect("an ordering handle holds an ordering requirement");
    let iter = order
        .iter
        .as_ref()
        .map(|t| freshen_above(solver, lim, t, target, cache));
    let positions = freshen_above(solver, lim, &order.positions, target, cache);
    let capabilities = match order.capabilities.repr() {
        Repr::Var(v) => Capabilities::var(freshen_handle(solver, lim, v, target, cache)),
        _ => order.capabilities.clone(),
    };
    let assumptions = order
        .assumptions(solver)
        .iter()
        .map(|r| Rc::new(r.map_types(|t| freshen_above(solver, lim, t, target, cache))))
        .collect();
    let (node, source) = cache
        .use_at
        .map_or((order.node, order.source), |at| (at, at));
    let copy = crate::ccl::capabilities::Requirement::orderable_if_required_by(
        solver,
        positions,
        capabilities,
        node,
        source,
        iter,
        assumptions,
    );
    let copy = match cache.use_at {
        Some(_) => copy.at_use(),
        None => copy,
    };
    // What the original's run has decided of it, the copy holds too.
    if let Some(decision) = order.decision(solver) {
        copy.ordering()
            .expect("a copy of an ordering requirement is one")
            .decide(solver, decision);
    }
    // A copy made for a use is checked at the use, under what the use assumes, once the use's
    // run has typed the use (`InferCtx::check_loop_orders`).
    if cache.use_at.is_some() {
        copy.record(solver);
        copy.ordering()
            .expect("a copy of an ordering requirement is one")
            .assume_more(solver, cache.use_assumptions.iter().cloned());
    }
    cache.record_copy(r, copy.clone());
    copy
}

/// The level of what `capabilities` hold that freshening copies ([`freshen_level`]): a variable's
/// own, and within a known set the highest of its raised types', its requirements' and its
/// variables'. An ordering requirement is copied wherever freshening reaches it, so a set holding
/// one is above every cutoff.
fn capabilities_level(solver: &mut Solver, capabilities: &Capabilities) -> Level {
    let mut level = 0;
    capabilities.map_leaves(&mut |leaf| {
        level = level.max(match leaf.repr() {
            Repr::Var(v) => v.level(solver),
            Repr::Known(set) => {
                if set.requires.iter().any(|r| r.ordering().is_some()) {
                    Level::MAX
                } else {
                    let raised = set.causes.iter().map(|e| match e {
                        crate::ccl::capabilities::Effect::Raise(raised) => {
                            freshen_level(solver, &raised.ty)
                        }
                        _ => 0,
                    });
                    let raised = raised.collect::<Vec<_>>().into_iter().max().unwrap_or(0);
                    let vars = set
                        .vars
                        .values()
                        .map(|v| v.level(solver))
                        .max()
                        .unwrap_or(0);
                    raised.max(vars)
                }
            }
            Repr::Written(_) | Repr::Children(_) => 0,
        });
        leaf.clone()
    });
    level
}

/// `filter`, an edge of a copied capability variable's, as the copy's edge: a use's `try` catches
/// the use's instances of the types its clauses name, as its exceptions are the use's instances
/// of the types they are raised at, and the items a written clause states are the use's.
fn freshen_filter(
    solver: &mut Solver,
    lim: Level,
    mut filter: crate::ccl::capabilities::Filter,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> crate::ccl::capabilities::Filter {
    if let Some(catch) = &filter.catches {
        let clauses = catch
            .clauses()
            .iter()
            .map(|c| freshen_above(solver, lim, c, target, cache))
            .collect();
        filter.catches = Some(Rc::new(catch.instantiated(clauses)));
    }
    filter.stated = filter
        .stated
        .into_iter()
        .map(|item| match item {
            Capability::Requires(r) => {
                Capability::Requires(freshen_requirement(solver, lim, &r, target, cache))
            }
            item => cache.renamed_capability(&item),
        })
        .collect();
    filter
}

/// A copy of a capability variable carries its own capabilities, its edges and its bounds.
/// `chain` freshened step by step: each variable it leaves, and each edge's filter.
fn freshen_chain(
    solver: &mut Solver,
    lim: Level,
    chain: &crate::ccl::capabilities::Chain,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> crate::ccl::capabilities::Chain {
    let mut steps = Vec::new();
    for (source, filter) in crate::ccl::capabilities::chain_steps(chain) {
        let source = freshen_handle(solver, lim, &source, target, cache);
        let filter = freshen_filter(solver, lim, filter, target, cache);
        steps.push((source, filter));
    }
    crate::ccl::capabilities::chain_of(steps)
}

impl Copied for Capabilities {
    fn copy_fixed(
        _solver: &mut Solver,
        _lim: Level,
        _original: &Rc<CapabilityVar>,
        _level: Level,
        _telescope: &Telescope,
        _target: FreshenLevel,
        _cache: &mut FreshenCache,
    ) {
    }

    fn copy_recorded(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<CapabilityVar>,
        copy: &Rc<CapabilityVar>,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) {
        let open = original.open_input(solver);
        copy.set_open_input(solver, open);

        for capability in original.own(solver) {
            match copied_capability(solver, lim, capability, target, cache) {
                CopiedCapability::Ready(capability) => copy.record(solver, capability),
                CopiedCapability::Dropped => {}
                CopiedCapability::Waits(on, capability) => cache.waiting.push(WaitingCapability {
                    on,
                    copy: Rc::clone(copy),
                    capability,
                    guard: None,
                }),
            }
        }
        // Each use answers the bounds the definition states, recorded before any edge out of the
        // copy pushes what it holds past them: a use's arguments can add capabilities
        // its copy holds and the definition's variable never does. A part a parameter stands in
        // admits whatever the use passes there, and the definition was checked against it, less
        // what the clause takes from the parameter: the top of its direction less that.
        for mut upper in original.uppers(solver) {
            // The copy is noted by the use that makes it ([`CapabilityVar::note_use`]).
            if let crate::ccl::capabilities::Blame::NestedTransaction { used_at, .. } =
                &mut upper.blame
            {
                *used_at = None;
            }
            upper.set.requires = upper
                .set
                .requires
                .into_iter()
                .map(|r| freshen_requirement(solver, lim, &r, target, cache))
                .collect();
            for param in std::mem::take(&mut upper.set.params) {
                if !param.except.is_empty() {
                    let every = crate::ccl::capabilities::Every::of_direction(param.of_causes)
                        .less(solver, param.except.iter().cloned());
                    upper.set.add_every_in(solver, every);
                } else if param.of_causes {
                    upper.of_causes = false;
                } else {
                    upper.of_requires = false;
                }
            }
            if upper.of_requires || upper.of_causes || !upper.forbidden.is_empty() {
                copy.bound_above(solver, upper);
            }
        }
        // **The copy carries what the original stores, freshened**, as a type variable's copy
        // carries its bounds: each edge to the copy of the variable at its other end, or to that
        // variable where it stays, and what was pushed into the original. Nothing is pushed
        // again, and nothing is recorded on a variable that stays.
        //
        // Only a variable at the original's level or deeper pushes into it, so whatever was
        // pushed came from variables this freshening copies too: each pushed capability is
        // freshened as its variable's copy freshens it as its own, and what that copy would push
        // is what arrives. A copy is not a written hole ([`CapabilityVar::mark_hole`]), so no hole
        // reaching the original reaches the copy.
        let incoming: Vec<_> = original
            .incoming_chains(solver)
            .into_iter()
            .map(|(source, chain)| {
                (
                    freshen_handle(solver, lim, &source, target, cache),
                    freshen_chain(solver, lim, &chain, target, cache),
                )
            })
            .collect();
        let out: Vec<_> = original
            .out_edges(solver)
            .into_iter()
            .map(|(sink, chain)| {
                (
                    freshen_handle(solver, lim, &sink, target, cache),
                    freshen_chain(solver, lim, &chain, target, cache),
                )
            })
            .collect();
        let mut pushed = Vec::new();
        for entry in original.pushed(solver) {
            use crate::ccl::capabilities::Pushed;
            let entry = match entry {
                Pushed::Item(capability, guard) => {
                    match copied_capability(solver, lim, capability, target, cache) {
                        CopiedCapability::Ready(capability) => Pushed::Item(
                            capability,
                            freshen_chain(solver, lim, &guard, target, cache),
                        ),
                        CopiedCapability::Dropped => continue,
                        CopiedCapability::Waits(on, capability) => {
                            cache.waiting.push(WaitingCapability {
                                on,
                                copy: Rc::clone(copy),
                                capability,
                                guard: Some(guard),
                            });
                            continue;
                        }
                    }
                }
                Pushed::Open(v, guard) => Pushed::Open(
                    freshen_handle(solver, lim, &v, target, cache),
                    guard.map(|g| freshen_chain(solver, lim, &g, target, cache)),
                ),
                Pushed::Hole(..) => continue,
            };
            pushed.push(entry);
        }
        let pushed_from: Vec<_> = original
            .pushed_from(solver)
            .into_iter()
            .map(|source| freshen_handle(solver, lim, &source, target, cache))
            .collect();
        copy.carry_copied(solver, incoming, out, pushed_from, pushed);
    }
}

/// What a copy holds for `capability`, recorded on a variable this freshening copies: `None` for a
/// parameter's rigid stand-in, which the use's arguments replace.
fn copied_capability(
    solver: &mut Solver,
    lim: Level,
    capability: crate::ccl::capabilities::LocatedCapability,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> CopiedCapability {
    use crate::ccl::capabilities::{Effect, LocatedCapability};
    if let Capability::Requires(r) = &capability.item
        && r.ordering().is_some()
        && cache.orderings_building.contains(&r.held_key())
    {
        return CopiedCapability::Waits(r.held_key(), capability);
    }
    CopiedCapability::Ready(match &capability.item {
        // A capability naming a parameter that stands for a clause is the definition's rigid
        // stand-in for what each use passes (`InferCtx::open_poly`), as an opened type parameter
        // stands for itself. A copy above the cutoff is the use's variable for the parameter, as a
        // copied type parameter is a fresh variable, so it holds what the use's arguments bring
        // instead.
        Capability::Param(_) => return CopiedCapability::Dropped,
        // A use raises the exception at its own instance of the definition's types, and as an
        // exception of its own: two uses are two exceptions.
        Capability::Causes(Effect::Raise(raised)) => {
            let ty = freshen_above(solver, lim, &raised.ty, target, cache);
            let raised = raised.instantiated(ty, cache.use_at);
            LocatedCapability {
                item: Capability::Causes(Effect::Raise(raised)),
                ..capability.clone()
            }
        }
        Capability::Requires(r) if r.ordering().is_some() => {
            let requirement = freshen_requirement(solver, lim, r, target, cache);
            LocatedCapability {
                item: Capability::Requires(requirement),
                ..capability
            }
        }
        _ => {
            let item = cache.renamed_capability(&capability.item);
            LocatedCapability { item, ..capability }
        }
    })
}

/// What a copy holds for a capability its original holds ([`copied_capability`]).
enum CopiedCapability {
    /// The copy's capability.
    Ready(crate::ccl::capabilities::LocatedCapability),
    /// Nothing: a parameter's rigid stand-in, which the use's arguments replace.
    Dropped,
    /// The original's capability, naming the ordering requirement keyed here, whose copy is being
    /// built: recorded once that copy is registered ([`record_waiting`]).
    Waits(HeldKey, crate::ccl::capabilities::LocatedCapability),
}

/// A capability a copy holds once the ordering requirement it names is copied
/// ([`CopiedCapability::Waits`]).
pub(crate) struct WaitingCapability {
    on: HeldKey,
    copy: Rc<CapabilityVar>,
    capability: crate::ccl::capabilities::LocatedCapability,
    /// The guard it was pushed with, or `None` for the original's own.
    guard: Option<crate::ccl::capabilities::Guard>,
}

/// Record on its copy each capability waiting on the requirement keyed `on`, now registered.
fn record_waiting(
    solver: &mut Solver,
    lim: Level,
    on: &HeldKey,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) {
    let (ready, rest): (Vec<_>, Vec<_>) = std::mem::take(&mut cache.waiting)
        .into_iter()
        .partition(|w| w.on == *on);
    cache.waiting = rest;
    for w in ready {
        let CopiedCapability::Ready(capability) =
            copied_capability(solver, lim, w.capability, target, cache)
        else {
            unreachable!("a registered requirement's capability is copied")
        };
        match w.guard {
            None => w.copy.record(solver, capability),
            Some(guard) => {
                let guard = freshen_chain(solver, lim, &guard, target, cache);
                w.copy.carry_copied(
                    solver,
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    vec![crate::ccl::capabilities::Pushed::Item(capability, guard)],
                );
            }
        }
    }
}

/// A sort of solver variable a freshening copies ([`copy_var`]).
trait Copied: Recorded {
    /// What the copy of `original` carries besides what every variable has, made before the copy
    /// is minted at `level` in `telescope`.
    fn copy_fixed(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<SolverVar<Self>>,
        level: Level,
        telescope: &Telescope,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) -> Self::Fixed;

    /// Carry what the run recorded on `original` to `copy`, which is registered in `cache`.
    fn copy_recorded(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<SolverVar<Self>>,
        copy: &Rc<SolverVar<Self>>,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    );
}

/// A new copy of the solver variable `original` with what the definition recorded on it
/// ([`freshen_held`]). The copy stands at the target's level for the original's, in the copy of
/// its telescope. It is registered before anything is freshened from the original: what the
/// original records can reach it again, through a cycle of bounds or of edges, and the cache is
/// what makes that reach find this copy rather than mint a second one.
fn copy_var<V: Copied>(
    solver: &mut Solver,
    lim: Level,
    original: &Rc<SolverVar<V>>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Rc<SolverVar<V>>
where
    Rc<SolverVar<V>>: HeldKind,
{
    let ahead = cache.minted_ahead.len();
    let copy = mint_copy(solver, lim, original, target, cache);
    // The copies the fixed part minted ahead are recorded on first, in the order minted: the
    // original's own records name what they bind.
    for kind in cache.minted_ahead.split_off(ahead) {
        let kind_copy = cache
            .copy_of(&kind)
            .expect("a kind minted ahead is registered");
        FunKind::copy_recorded(solver, lim, &kind, &kind_copy, target, cache);
    }
    V::copy_recorded(solver, lim, original, &copy, target, cache);
    copy
}

/// The copy of `kind`, which the fixed part of another variable's copy holds: the copy this
/// freshening already made, `kind` itself where it stays, and otherwise a new one minted only.
/// What `kind` records can reach the variable whose copy is being minted, which is not
/// registered yet, so [`copy_var`] records on the new copy once it is.
fn mint_ahead(
    solver: &mut Solver,
    lim: Level,
    kind: &Rc<FunKindVar>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Rc<FunKindVar> {
    if let Some(existing) = cache.copy_of(kind) {
        return existing;
    }
    if kind.level(solver) <= lim {
        return Rc::clone(kind);
    }
    let copy = mint_copy(solver, lim, kind, target, cache);
    cache.minted_ahead.push(Rc::clone(kind));
    copy
}

/// The first half of [`copy_var`]: the copy of `original` minted and registered, with nothing
/// recorded on it yet. A variable whose fixed part holds another variable mints that one's copy
/// here and records on it once its own copy is registered.
fn mint_copy<V: Copied>(
    solver: &mut Solver,
    lim: Level,
    original: &Rc<SolverVar<V>>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Rc<SolverVar<V>>
where
    Rc<SolverVar<V>>: HeldKind,
{
    let level = target.level_of(original.level(solver));
    let telescope = cache.copied_telescope(&original.telescope);
    let fixed = V::copy_fixed(solver, lim, original, level, &telescope, target, cache);
    let copy = SolverVar::mint(solver, level, telescope, fixed, V::State::default());
    cache.record_copy(original, Rc::clone(&copy));
    copy
}

/// Freshening's one rule for a solver handle (`src/ccl/design/type-inference.md`, "Copying
/// solver state"): the copy this freshening already made; the handle itself where it stands at or
/// below the cutoff, an enclosing scope's; and otherwise a new copy carrying what is recorded on
/// the original, which records itself before copying that state, so a cycle reaches it.
fn freshen_held(
    solver: &mut Solver,
    lim: Level,
    held: &Held,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Held {
    if let Some(copy) = cache.copies.get(&held.key()) {
        return copy.clone();
    }
    if !held_above(solver, lim, held) {
        return held.clone();
    }
    // A copy freshens the variables at the other end of what it carries, each copied the same
    // way, so a chain of edges is a chain of frames: grow on demand as the other deep walks do.
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        copy_held(solver, lim, held, target, cache)
    })
}

/// [`freshen_held`] for a handle this freshening copies and has not copied yet.
fn copy_held(
    solver: &mut Solver,
    lim: Level,
    held: &Held,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Held {
    match held {
        Held::Infer(v) => Held::Infer(copy_var(solver, lim, v, target, cache)),
        Held::FunKind(k) => Held::FunKind(copy_var(solver, lim, k, target, cache)),
        Held::Capability(c) => Held::Capability(copy_var(solver, lim, c, target, cache)),
        Held::Ordering(r) => {
            cache.orderings_building.push(held.key());
            let copy = copy_ordering(solver, lim, r, target, cache);
            cache.orderings_building.retain(|k| *k != held.key());
            record_waiting(solver, lim, &held.key(), target, cache);
            Held::Ordering(copy)
        }
        Held::Obligation(o) => Held::Obligation(copy_obligation(solver, lim, o, target, cache)),
    }
}

/// [`freshen_held`] for a handle of a known kind.
fn freshen_handle<K: HeldKind + Clone>(
    solver: &mut Solver,
    lim: Level,
    handle: &K,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> K {
    let held = freshen_held(solver, lim, &handle.clone().into_held(), target, cache);
    K::from_held(&held)
        .expect("a handle freshens to a handle of its kind")
        .clone()
}

/// Whether freshening copies `held`: a solver variable is copied where its level is above the
/// cutoff, and an ordering requirement or an obligation, which has no level, wherever freshening
/// reaches it. A funkind variable lowering minted is the program's, not a run's: it stands at
/// level 0, so a copy keeps it.
fn held_above(solver: &mut Solver, lim: Level, held: &Held) -> bool {
    match held {
        Held::Infer(v) => v.level(solver) > lim,
        Held::FunKind(k) => k.level(solver) > lim,
        Held::Capability(c) => c.level(solver) > lim,
        Held::Ordering(_) | Held::Obligation(_) => true,
    }
}

/// A copy of a funkind variable carries its construction stamp, its binders renamed, every edge
/// and what it was built over, and records the original it copies.
impl Copied for FunKind {
    fn copy_fixed(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<FunKindVar>,
        _level: Level,
        _telescope: &Telescope,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) -> crate::ccl::ty::FunKindVarFixed {
        // An annotation's funkind hole is normalized away before inference, so no funkind
        // variable a freshening copies is one.
        debug_assert!(
            !original.is_hole(),
            "a run's funkind variable is never a hole"
        );
        let fixed = original.fixed.clone();
        // A proxy's copy binds the binders the copy of its original's owner binds, so the
        // copied function type it stands in names them, as the original names its owner's.
        match original.binders_of() {
            Some(owner) => fixed.binding_binders_of(mint_ahead(solver, lim, owner, target, cache)),
            None => fixed,
        }
    }

    fn copy_recorded(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<FunKindVar>,
        copy: &Rc<FunKindVar>,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) {
        // Each field of the original, and what the copy makes of it.
        let crate::ccl::ty::FunKindVarFields {
            // The copy's own.
            uid: (),
            // Not a hole, and stamped as the original was at construction (`copy_fixed`).
            hole: (),
            minted: (),
            // The copy of the original's owner, or the owner itself where it stays
            // (`copy_fixed`).
            binders_of: (),
            // Minted by this solver.
            home: (),
            // The target's level for the original's.
            level: (),
            // The stamp, the binders and every edge, below.
            bounds: (),
            // Memos of what the funkind variable resolved to, recomputed for the copy when it is
            // read.
            resolved_at: (),
        } = original.fields(solver);
        // **Everything the definition recorded comes across; the variable does not.** A pin the
        // definition site acquires later must not reach this instantiation, which a fresh `uid`
        // with copied state gives and a shared variable would not.
        //
        // All four, because all four are what the definition said: the construction stamp
        // (`fresh_data`'s `Data`, which no edge spells), the bounds on either side, and what the
        // collection was built over — a comprehension's instantiation binds one position per
        // position of its sources exactly as the definition does, and a copy that drops the
        // relation is a collection of unknown width that defaults to a compute function.
        if original.stamped(solver) == crate::ccl::ty::KindPin::Data {
            copy.stamp_data(solver);
        }
        // **The binders come across renamed, before the edges.** A position the original has
        // named is named in the bounds being copied, and the copy binds its own name there, so
        // the rename has to be in the cache when those bounds are freshened. Every binder the
        // original has named, arity known or not: a name is minted ahead of the arity
        // ([`FunKindVar::binder_id_at`]).
        let _ = original.binder_ids(solver);
        for (i, from) in original.named_binder_ids(solver).into_iter().enumerate() {
            cache.witnesses.insert(from, copy.binder_id_at(solver, i));
        }
        // Each edge's substitution comes across freshened, as a copied bound's does.
        for (lower, edges) in [
            (true, original.lower_edges(solver)),
            (false, original.upper_edges(solver)),
        ] {
            for (k, edge) in edges {
                let neighbor = freshen_fun_kind(solver, &k, lim, target, cache);
                let kept_neighbor = match (&k, &neighbor) {
                    (FunKind::Var(original), FunKind::Var(kept)) if Rc::ptr_eq(original, kept) => {
                        Some(Rc::clone(kept))
                    }
                    _ => None,
                };
                // The edge takes the neighbor's frame into `original`'s. A copied neighbor's frame
                // is renamed as `original`'s is, so the whole edge is; one left in place keeps its
                // names, so only what the edge maps into the copy's frame is renamed, and each of
                // the definition's binders the neighbor stands under is read under the copy's name
                // for it.
                let edge = match &kept_neighbor {
                    None => freshen_subst_payloads(solver, lim, &edge, target, cache),
                    Some(kept) => {
                        let edge = freshen_subst_payload_terms(solver, lim, &edge, target, cache);
                        let renames = cache.instance_renames(
                            edge.mentioned_names()
                                .into_iter()
                                .chain(kept.telescope.iter().cloned()),
                        );
                        let mut edge = edge.rename_images(&renames, crate::ccl::Ids::Fresh);
                        for n in kept.telescope.iter() {
                            if let Some(to) = renames.get(n)
                                && !edge.binders().any(|b| b == n)
                            {
                                edge = edge.extended_rename(n.clone(), to.clone());
                            }
                        }
                        edge
                    }
                };

                copy.record_under(solver, neighbor, lower, edge);
            }
        }
        for src in original.built_over(solver).into_iter().rev() {
            let kind = freshen_fun_kind(solver, &src, lim, target, cache);
            copy.contributes_first(solver, kind);
        }
        // **And recorded on the copy**, not only in this walk's cache. The cache rewrites the
        // references this instantiation carries and is then gone; a reference written in the
        // original's binder that arrives later has nothing to relate it to, since the copy's
        // relations are freshened and reach the original nowhere. Recorded as a copy rather than
        // as bounds: what the two share is which binder each position is, not what the kind
        // resolves to, and the decoupling above is the whole point of the fresh variable.
        copy.copied_from(solver, original);
    }
}

/// The highest level of any inference variable **reachable** in `ty` — including
/// the ones inside refinement predicates' own type slots.
///
/// This is deliberately *not* [`type_level`], and the difference is the whole
/// point. The two answer different questions:
///
/// * [`type_level`] asks "does this participate in the lattice above `lim`?", for
///   extrusion, bound-recording scope, and let-generalization. A refinement is
///   lattice-blind, so it defers to its base and the predicate is correctly
///   invisible; a `ChanDom` reports 0 so a rigid atom flows through bounds
///   unchanged. Both are load-bearing there.
/// * Freshening asks "does this contain a variable I must **copy**?" A predicate
///   carries real type slots holding real quantified variables, so for *this*
///   question they count.
///
/// Sharing one function between the two is what let an unfreshened predicate into
/// a specialization clone: `type_level` reports the base's level for a nested
/// refinement, so a type whose only above-`lim` content lives in a predicate
/// short-circuits and is returned verbatim — still pointing at the definition's
/// live inference variables, which `src/ccl/design/type-inference.md`
/// ("3.1 Let-Polymorphism is Freshening (Instantiation)") states it must not.
/// The symptom is a duplicate specialization: the clone reaches the same
/// generalized `let` twice, once through freshened variables and once through
/// the definition's own.
pub(crate) fn freshen_level(solver: &mut Solver, ty: &Type) -> Level {
    fn predicate_level(solver: &mut Solver, expr: &TypedExpr) -> Level {
        let mut lvl = 0;
        expr.walk_type_slots(|t| lvl = lvl.max(freshen_level(solver, t)));
        expr.walk_children(|c| lvl = lvl.max(predicate_level(solver, c)));
        lvl
    }
    // One walk, not `type_level` plus a second descent: `walk_children` already
    // reaches every structural position, so the only thing to add is the
    // predicate it documents itself as skipping. A `ChanDom` reports its stored
    // introduction level, where `type_level` reports 0: a channel minted inside the
    // definition is quantified, and [`freshen_above`] renames it. A history whose value
    // reads its key holds one in a predicate, as the key binder's type, beside
    // nothing else to freshen.
    let mut lvl = match ty {
        Type::Infer(v) => v.level(solver),
        // A declared parameter, in an annotation slot a clone copies, is a name the
        // solver never reads; normalization replaced it where the right-hand side was
        // emitted.
        Type::Param(param) => param.opened_at.unwrap_or(0),
        // An application of an opened family parameter is quantified with its parameter,
        // and its terms hold type slots as a predicate does.
        Type::FamilyApp(app) => app
            .args
            .iter()
            .map(|a| predicate_level(solver, &a.term))
            .fold(app.param.opened_at.unwrap_or(0), Level::max),
        Type::ChanDom(_, l) => l.0,
        // A function's capabilities and kind are copied like any state above the cutoff, so a
        // type whose only quantified content is either is not returned verbatim: each use would
        // add what its arguments bring to the definition's own variables.
        Type::Fun {
            capabilities,
            fun_kind,
            ..
        } => {
            let kind = match fun_kind {
                FunKind::Var(k) => k.level(solver),
                _ => 0,
            };
            capabilities_level(solver, capabilities).max(kind)
        }
        _ => 0,
    };
    for r in ty.refinements() {
        lvl = lvl.max(predicate_level(solver, &r.predicate));
    }
    if let Type::WitnessProjection(p) = ty {
        lvl = lvl.max(predicate_level(solver, &p.term));
    }
    ty.walk_children(|c| lvl = lvl.max(freshen_level(solver, c)));
    lvl
}

/// Whether `ty` holds an application of an opened family parameter.
fn holds_family_app(ty: &Type) -> bool {
    ty.holds_type(&|t| matches!(t, Type::FamilyApp(app) if app.param.opened_at.is_some()))
}

/// An application of the opened family parameter `app.param`, freshened: the variable this
/// instantiation stands the parameter at, its binders discharged to the application's terms
/// ([`FreshenCache::family_params`]). A parameter this freshening does not instantiate, one
/// deeper than the cutoff in a specialization clone, is re-minted as a parameter is.
fn freshen_family_app(
    solver: &mut Solver,
    lim: Level,
    app: &crate::ccl::ty::FamilyApp,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Type {
    let args: Vec<Rc<TypedExpr>> = app
        .args
        .iter()
        .map(|a| {
            let _f = crate::ccl::provenance::copy_frame("infer.freshen_family_arg");
            let mut term = (*a.term).duplicate();
            freshen_expr_type_slots(solver, &mut term, lim, target, cache);
            Rc::new(term)
        })
        .collect();
    let param = &app.param;
    let instantiated = matches!(target, FreshenLevel::At(_)) || param.level() == lim + 1;
    if !instantiated {
        let fresh = match cache.params.get(&param.id) {
            Some((_, Type::Param(p))) => Rc::clone(p),
            _ => {
                let bound = param
                    .bound
                    .as_ref()
                    .map(|b| freshen_above(solver, lim, b, target, cache));
                let p = crate::ccl::ty::TypeParam::opened_family(
                    param.spelling.clone(),
                    target.level_of(param.level()),
                    bound,
                    param.bound_at,
                    param.arity,
                );
                cache
                    .params
                    .insert(param.id, (Rc::clone(param), Type::Param(Rc::clone(&p))));
                p
            }
        };
        return Type::FamilyApp(crate::ccl::ty::FamilyApp::new(fresh, args));
    }
    if !cache.family_params.contains_key(&param.id) {
        let names: Vec<crate::ccl::Name> = (0..param.arity)
            .map(|_| crate::ccl::Name::fresh(format!("__{}_k", param.spelling.to_lowercase())))
            .collect();
        let telescope = names.iter().fold(
            cache
                .param_telescope
                .clone()
                .unwrap_or_else(Telescope::empty),
            |t, n| t.extended(n.clone()),
        );
        let level = match target {
            FreshenLevel::At(at) => at,
            _ => target.level_of(param.level()),
        };
        let var = Type::Infer(InferVar::fresh_in(solver, level, &telescope));
        cache
            .family_params
            .insert(param.id, (Rc::clone(param), names, var));
    }
    let (_, names, var) = &cache.family_params[&param.id];
    crate::ccl::subst::discharge_binders(solver, names, var, &args)
}

/// The copy freshening makes: each solver handle above `lim` copied with what is recorded on it
/// ([`freshen_held`]), the binders its definition binds renamed for the instance, and every type
/// this freshening reaches walked by the one structural walk extrusion uses too
/// ([`super::transport`]). Freshening copies structure, not constraints, so it reads no side.
pub(crate) struct Copying<'a> {
    lim: Level,
    target: FreshenLevel,
    cache: &'a mut FreshenCache,
    /// The first variable this freshening minted: a part placed under a function's kind is one of
    /// this instance's own.
    first_var: InferVarId,
    /// Whether a substitution's binders and terms take the instance's names: not where the edge
    /// it rides keeps a neighbour that stays ([`freshen_subst_payload_terms`]).
    rename_names: bool,
}

impl<'a> Copying<'a> {
    pub(crate) fn new(lim: Level, target: FreshenLevel, cache: &'a mut FreshenCache) -> Self {
        let first_var = *cache
            .first_var
            .get_or_insert_with(crate::ccl::infer_var::next_infer_var_id);
        Copying {
            lim,
            target,
            cache,
            first_var,
            rename_names: true,
        }
    }
}

impl super::transport::Transport for Copying<'_> {
    // The short-circuit asks [`freshen_level`], not `type_level`: a refinement's predicate holds
    // type slots whose quantified variables a low base hides, and freshening has to copy them. A
    // `WitnessRef` is exempt outright: it is a name holding no variable, so its level is 0 whether
    // or not its binder is quantified, and what decides that is the cache [`Self::witness`] reads.
    fn reaches(&mut self, solver: &mut Solver, ty: &Type) -> bool {
        matches!(ty, Type::WitnessRef(_)) || freshen_level(solver, ty) > self.lim
    }

    fn var(&mut self, solver: &mut Solver, v: &Rc<InferVar>, _side: Side) -> Type {
        Type::Infer(freshen_handle(solver, self.lim, v, self.target, self.cache))
    }

    fn kind(&mut self, solver: &mut Solver, k: &Rc<FunKindVar>, _side: Side) -> Rc<FunKindVar> {
        freshen_handle(solver, self.lim, k, self.target, self.cache)
    }

    fn capability_var(
        &mut self,
        solver: &mut Solver,
        v: &Rc<CapabilityVar>,
        _side: Side,
    ) -> Rc<CapabilityVar> {
        freshen_handle(solver, self.lim, v, self.target, self.cache)
    }

    // An ordering requirement is copied with its proof state, as a copied variable's is
    // ([`freshen_held`]).
    fn ordering(
        &mut self,
        solver: &mut Solver,
        r: &crate::ccl::capabilities::Requirement,
    ) -> crate::ccl::capabilities::Requirement {
        freshen_handle(solver, self.lim, r, self.target, self.cache)
    }

    // A use raises the exception at its own instance of the definition's types, and as an
    // exception of its own: two uses are two exceptions.
    fn raised(
        &mut self,
        raised: &crate::ccl::capabilities::Raised,
        ty: Type,
    ) -> crate::ccl::capabilities::Raised {
        raised.instantiated(ty, self.cache.use_at)
    }

    // An operator scheme's binder names are the template's, like its witnesses, so each
    // instantiation names its own: two `box`es binding one name would put one binder at two
    // scopes. Cache-consistent, so the functions a scheme names alike stay alike. A specialization
    // clone names each of them afresh too, standing where the definition stood
    // ([`FreshenCache::site_telescope`]); a definition's instantiation renames only the
    // definition's own ([`FreshenCache::label_name`]). `uncurry`'s scheme names its components as
    // a function names its binder, and the variables under them follow
    // ([`FreshenCache::binders`]).
    fn label(&mut self, name: &crate::ccl::Name) -> crate::ccl::Name {
        self.cache.label_name(name)
    }

    // A witness reference names a binder, not a variable, so what freshening owes it is the
    // α-conversion its binder got. A written sum's binder is re-minted by
    // [`Type::alpha_convert_sum`] on the way out of a function ([`Self::function`]); a kind
    // variable's is re-minted with the variable ([`copy_var`]), and the cache is what carries that
    // rename to the references, in this type and in the bounds copied with it.
    fn witness(&mut self, w: &crate::ccl::ty::WitnessId) -> crate::ccl::ty::WitnessId {
        self.cache.witnesses.get(w).copied().unwrap_or(*w)
    }

    // A channel domain minted inside the generalized definition (level > lim) is quantified
    // exactly like a variable: each instantiation is its own channel. A rigid name cannot be
    // identified through bounds the way a fresh var can, so instantiation renames it here,
    // cache-consistently ([`FreshenCache::chan_doms`], pre-seeded by `specialize_use` so the clone
    // agrees with the use site's pass-1 instantiation names). A free channel (level ≤ lim, a
    // captured outer defer) keeps its name: every instantiation's contributions union into the
    // one shared channel.
    fn chan_dom(&mut self, _solver: &mut Solver, ty: &Type) -> Type {
        let Type::ChanDom(name, lvl) = ty else {
            unreachable!("a channel domain")
        };
        let (lim, target, cache) = (self.lim, self.target, &mut *self.cache);
        if lvl.0 <= lim {
            return ty.clone();
        }
        let fresh = cache
            .chan_doms
            .entry(name.clone())
            .or_insert_with(|| crate::ccl::Name::fresh_like(name))
            .clone();
        Type::ChanDom(fresh, crate::ccl::ChanLevel(target.level_of(lvl.0)))
    }

    fn param(&mut self, solver: &mut Solver, ty: &Type) -> Type {
        let Type::Param(param) = ty else {
            unreachable!("a type parameter")
        };
        let (lim, target) = (self.lim, self.target);
        if let Some((_, existing)) = self.cache.params.get(&param.id) {
            return existing.clone();
        }
        let telescope = self
            .cache
            .param_telescope
            .clone()
            .unwrap_or_else(Telescope::empty);
        let mut for_param = |level| {
            let v = InferVar::fresh_in(solver, level, &telescope);
            v.mark_stands_for(
                solver,
                crate::ccl::infer_var::StandsFor::Param(param.spelling.clone()),
            );
            Type::Infer(v)
        };
        let out = match target {
            FreshenLevel::At(at) => for_param(at),
            _ if param.level() == lim + 1 => for_param(target.level_of(param.level())),
            _ => {
                let bound = param
                    .bound
                    .as_ref()
                    .map(|b| super::transport::transport(solver, b, Side::Both, self));
                Type::Param(crate::ccl::ty::TypeParam::opened(
                    param.spelling.clone(),
                    target.level_of(param.level()),
                    bound,
                    param.bound_at,
                ))
            }
        };
        self.cache
            .params
            .insert(param.id, (Rc::clone(param), out.clone()));
        out
    }

    fn family_app(&mut self, solver: &mut Solver, ty: &Type) -> Type {
        let Type::FamilyApp(app) = ty else {
            unreachable!("a family application")
        };
        freshen_family_app(solver, self.lim, app, self.target, self.cache)
    }

    // A `Poly` in a type slot is a definition's annotation, which `emit_let` opened in place,
    // copied with the term it annotates: in a specialization clone, or in a substitution payload
    // riding a copied bound. A parameter deeper than the cutoff is re-minted, as its occurrences
    // in the copied body are, through the same cache. One that freshens to a variable, the
    // specialized binding's own or an instantiated one in a payload, keeps its name in the
    // `Poly`, whose types are what freshening made of it; nothing opens or instantiates that copy.
    fn poly(&mut self, solver: &mut Solver, ty: &Type) -> Type {
        let Type::Poly(poly) = ty else {
            unreachable!("a polymorphic type")
        };
        let mut out = poly.map_types(|t| super::transport::transport(solver, t, Side::Both, self));
        for p in &mut out.params {
            if let Type::Param(param) = super::transport::transport(
                solver,
                &Type::Param(Rc::clone(&p.param)),
                Side::Both,
                self,
            ) {
                p.param = param;
            }
        }
        Type::Poly(Rc::new(out))
    }

    // Each binder renamed as a function's is, and the body freshened opened, so an application of
    // a family parameter in it discharges that parameter's binders to the terms by name.
    fn family(&mut self, solver: &mut Solver, ty: &Type, _side: Side) -> Type {
        let Type::Family { binders, body } = ty else {
            unreachable!("a family")
        };
        let renamed: Vec<crate::ccl::Name> = binders
            .iter()
            .map(|(n, _)| {
                let n = n
                    .clone()
                    .unwrap_or_else(|| crate::ccl::Name::fresh("__family_k"));
                self.cache.label_name(&n)
            })
            .collect();
        let opened = crate::ccl::subst::open_family_body(
            solver,
            binders,
            body,
            |j| crate::ccl::subst::Mapping::Rename(renamed[j].clone()),
            crate::ccl::Ids::Fresh,
        );
        let fresh_body = super::transport::transport(solver, &opened, Side::Both, self);
        let fresh_binders = renamed
            .into_iter()
            .zip(binders)
            .map(|(n, (_, t))| (n, super::transport::transport(solver, t, Side::Both, self)))
            .collect();
        Type::family(solver, fresh_binders, fresh_body)
    }

    // An application of a family parameter discharges that parameter's binders to its terms by
    // name, so a codomain holding one is freshened opened at the binder.
    fn codomain(
        &mut self,
        solver: &mut Solver,
        binder: &crate::ccl::FunBinder,
        domain: &Type,
        c: &Type,
        side: Side,
    ) -> Type {
        if binder.is_none() || !holds_family_app(c) {
            return super::transport::transport(solver, c, side, self);
        }
        let b = crate::ccl::subst::named_binder(binder);
        let opened =
            crate::ccl::subst::open_at_binder_in(solver, &b, domain, c, crate::ccl::Ids::Fresh);
        let freshened = super::transport::transport(solver, &opened, side, self);
        crate::ccl::subst::close_at_binder(solver, &b, &freshened, crate::ccl::Ids::Fresh)
    }

    fn function(&mut self, solver: &mut Solver, out: Type) -> Type {
        // The parts of a function whose kind may bind witnesses sit under those binders.
        if let Type::Fun {
            fun_kind,
            domain,
            codomain,
            ..
        } = &out
        {
            let first_var = self.first_var;
            let owned = |v: &InferVar| v.uid >= first_var;
            InferVar::place_parts_under_where(solver, domain, fun_kind, &owned);
            InferVar::place_parts_under_where(solver, codomain, fun_kind, &owned);
        }
        // A scheme binds its witnesses, so each instantiation owes itself its own: `box`'s scheme
        // is one sum, and sharing its binders would make every `box` in a program name the one
        // the scheme was written with, joining two independent conditional collections onto a
        // single witness.
        if out.sum().is_some() {
            out.alpha_convert_sum(solver)
        } else {
            out
        }
    }

    // The obligation of the call a term makes: the use's copy of it, as its types hold the use's
    // copies of their variables.
    fn obligation(
        &mut self,
        solver: &mut Solver,
        obligation: &Rc<TraitObligation>,
    ) -> Rc<TraitObligation> {
        freshen_obligation(solver, self.lim, obligation, self.target, self.cache)
    }

    fn rename_subst(&mut self, subst: Subst) -> Subst {
        if !self.rename_names {
            return subst;
        }
        let renames = self.cache.instance_renames(subst.mentioned_names());
        if renames.is_empty() {
            subst
        } else {
            subst.rename_names(&renames, crate::ccl::Ids::Fresh)
        }
    }
}

/// Copy `ty` with every variable introduced above `lim` replaced by a fresh one
/// at `target`, reusing `cache` so a variable reached twice freshens once.
///
/// A type wholly at or below `lim` is returned unchanged.
pub fn freshen_above(
    solver: &mut Solver,
    lim: Level,
    ty: &Type,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Type {
    super::transport::transport(
        solver,
        ty,
        Side::Both,
        &mut Copying::new(lim, target, cache),
    )
}

/// Rename, in every variable `cache` copied, each binder the definition binds to the name this
/// instance gives it ([`FreshenCache::binders`]): in each bound's type and substitutions, in each
/// kinding constraint and in each guarded bound.
///
/// A copy's telescope enters the instance's names as the copy is minted, but its bounds are
/// copied before every binder they read is known, so the renames run once the copy is complete.
/// Each binder is bound in one place, so every mention of a definition's binder is the
/// definition's, and the rename needs no scope (`src/ccl/design/type-inference.md`, "Every binder
/// is bound in one place").
pub(crate) fn rename_instance_binders(solver: &mut Solver, cache: &FreshenCache) {
    let _f = crate::ccl::provenance::copy_frame("infer.instance_binders");
    let renames: crate::ccl::scope::Renames = cache.binders.clone().into_iter().collect();
    let copies: Vec<Rc<InferVar>> = cache.copies::<Rc<InferVar>>().map(|(_, v)| v).collect();
    for v in copies {
        let (lows, ups, kinds, guarded) = {
            let s = v.bounds(solver);
            (
                Rc::clone(s.lower()),
                Rc::clone(s.upper()),
                s.type_kinds.clone(),
                s.guarded_upper.clone(),
            )
        };
        let lows = lows
            .iter()
            .map(|b| instance_bound(solver, b, &renames))
            .collect();
        let ups = ups
            .iter()
            .map(|b| instance_bound(solver, b, &renames))
            .collect();
        let kinds = kinds
            .iter()
            .map(|k| k.map_children(|t| instance_type(solver, t, &renames)))
            .collect();
        let guarded = guarded
            .iter()
            .map(|g| crate::ccl::infer_var::GuardedBound {
                guard: {
                    let refined = Type::refined(Type::Hole, g.guard.clone());
                    instance_type(solver, &refined, &renames)
                        .refinements()
                        .iter()
                        .cloned()
                        .collect()
                },
                bound: instance_bound(solver, &g.bound, &renames),
            })
            .collect();
        let s = v.bounds_mut(solver);
        s.set_lower(lows);
        s.set_upper(ups);
        s.type_kinds = kinds;
        s.guarded_upper = guarded;
    }
    // A funkind copy's candidates read the definition's binders as the bounds do.
    let kinds: Vec<Rc<FunKindVar>> = cache.copies::<Rc<FunKindVar>>().map(|(_, k)| k).collect();
    for k in kinds {
        k.map_edge_kinds(solver, |solver, kind| match kind {
            FunKind::Data(Some(ws)) => FunKind::Data(Some(Rc::new(
                ws.iter()
                    .map(|w| w.map_types(|t| instance_type(solver, t, &renames)))
                    .collect(),
            ))),
            other => other.clone(),
        });
    }
    // An obligation's copy builds what it deposits from its refinement operands and its
    // associated types, which read the definition's binders as the bounds do.
    let obligations: Vec<Rc<TraitObligation>> = cache
        .copies::<Rc<TraitObligation>>()
        .map(|(_, o)| o)
        .collect();
    for o in obligations {
        o.map_assumption_rows(|r| instance_requirement(solver, r, &renames));
        o.map_frames(|frame| frame.rename_names(&renames, crate::ccl::Ids::Fresh));
        o.map_held_apps(|app| {
            match instance_type(solver, &Type::FamilyApp(app.clone()), &renames) {
                Type::FamilyApp(renamed) => renamed,
                other => unreachable!("renaming names keeps a family application one: {other}"),
            }
        });
        let assoc = o
            .assoc_types()
            .iter()
            .map(|t| instance_type(solver, t, &renames))
            .collect();
        o.set_assoc_types(assoc);
        if let Some(operands) = o.refinement_operands() {
            o.set_refinement_operands(
                operands
                    .into_iter()
                    .map(|mut expr| {
                        crate::ccl::scope::rename_names_in_term(
                            &mut expr,
                            &renames,
                            crate::ccl::Ids::Fresh,
                        );
                        expr
                    })
                    .collect(),
            );
        }
    }
}

/// `r` as an instance reads it: its types as [`instance_type`] reads them, and the names it reads
/// and binds renamed.
fn instance_requirement(
    solver: &mut Solver,
    r: &TraitRequirement,
    renames: &crate::ccl::scope::Renames,
) -> TraitRequirement {
    r.map_types(|t| instance_type(solver, t, renames))
        .map_names(|n| renames.get(n).cloned().unwrap_or_else(|| n.clone()))
}

/// `b` as an instance reads it ([`instance_type`]), its substitutions' binders renamed.
fn instance_bound(solver: &mut Solver, b: &Bound, renames: &crate::ccl::scope::Renames) -> Bound {
    let ids = crate::ccl::Ids::Fresh;
    Bound {
        origin: b.origin,
        self_subst: b.self_subst.rename_names(renames, ids),
        ty: instance_type(solver, &b.ty, renames),
        ty_subst: b.ty_subst.rename_names(renames, ids),
        rendered: Default::default(),
    }
}

/// `ty` as an instance reads it: each binder of the definition renamed to the instance's, and
/// each variable the instance shares with the definition read under the renames of the binders
/// it stands under.
///
/// A variable at or below the cutoff is not copied, so it keeps the definition's binders in its
/// telescope and its bounds. The instance reads it as `𝑉‹ρ›`, the suspension of the renames on
/// it, so that what the instance relates it to is spelled in the instance's binders.
pub(crate) fn instance_type(
    solver: &mut Solver,
    ty: &Type,
    renames: &crate::ccl::scope::Renames,
) -> Type {
    let mut ty = ty.clone();
    crate::ccl::scope::rename_names_in_type(&mut ty, renames, crate::ccl::Ids::Fresh);
    read_shared_under(solver, &mut ty, renames);
    ty
}

/// Replace each variable in `ty` whose telescope holds a binder `renames` maps by its suspension
/// under those renames ([`instance_type`]).
fn read_shared_under(solver: &mut Solver, ty: &mut Type, renames: &crate::ccl::scope::Renames) {
    if let Type::Infer(v) = ty {
        let under = v
            .telescope
            .iter()
            .filter_map(|n| renames.get(n).map(|to| (n.clone(), to.clone())))
            .fold(Subst::id(), |s, (from, to)| s.extended_rename(from, to));
        if !under.is_id() {
            *ty = under.apply_type_in(solver, &Type::Infer(Rc::clone(v)));
        }
        return;
    }
    ty.walk_children_mut(|c| read_shared_under(solver, c, renames));
}

/// A copy of a type variable carries its funkind variable's copy, made before the copy is
/// minted, and its bounds, kinding constraints, watches and suspended memberships, copied once
/// it is registered.
impl Copied for Type {
    fn copy_fixed(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<InferVar>,
        _level: Level,
        telescope: &Telescope,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) -> crate::ccl::infer_var::TypeVarFixed {
        debug_assert!(
            original.fun_kind().level(solver) > lim,
            "a quantified type variable's own funkind is quantified at the same cutoff"
        );
        // Each field of the original, and what the copy makes of it.
        let crate::ccl::infer_var::InferVarFields {
            // The copy's own.
            uid: (),
            // The target's level for the original's.
            level: (),
            // Minted by this solver.
            home: (),
            // Rescoped to the use ([`FreshenCache::copied_telescope`]).
            telescope: (),
            // A barrier variable's copy is one, under the copies of its opaque binders, below.
            opaque: (),
            // Freshened in `copy_recorded`, lower, upper and type kinds.
            bounds: (),
            // A copy of the original's funkind variable, minted below and recorded on in
            // `copy_recorded`.
            fun_kind: (),
            // Freshened, each obligation's frames copied (`freshen_watches`).
            watches: (),
            // A memo of the variables reading this one under substitutions, minted afresh as
            // the copy is read; the memberships recorded on them come across in `copy_recorded`.
            suspensions: (),
            // `mark_named_domain`, in `copy_recorded`.
            named_domain: (),
            // `inherit_stands_for`, in `copy_recorded`.
            stands_for: (),
            // `inherit_witness_placement_renamed`, in `copy_recorded`.
            witness_scopes: (),
            // A barrier variable's checks: each upper bound's report comes across with it, in
            // `copy_recorded`, and the copy is checked afresh.
            barrier: (),
        } = original.fields(solver);
        // **The copy stands over a copy of the original's kind**, registered in the same cache
        // as the bounds. A variable's kind carries the edges to the kinds of the function types
        // that reached it; over a kind the cache does not know, the copied bounds arrive spelled
        // in *their* copies' binders with nothing relating those to the copy's own, and a Σ then
        // materializes declaring one name and referencing another.
        let fun_kind = mint_ahead(solver, lim, original.fun_kind(), target, cache);
        // A barrier variable's copy is one, standing under the copies of its opaque binders: an
        // instance binds its own copy of each binder its definition binds. The copied telescope
        // holds them, as the original's holds the originals.
        let opaque = original.opaque().map(|opaque| {
            let opaque: Rc<[crate::ccl::Name]> = opaque
                .iter()
                .map(|n| cache.binders.get(n).cloned().unwrap_or_else(|| n.clone()))
                .collect();
            debug_assert!(
                opaque.iter().all(|n| telescope.contains(n)),
                "a barrier variable's copy stands under the copies of its opaque binders"
            );
            opaque
        });
        crate::ccl::infer_var::TypeVarFixed::new(fun_kind, opaque)
    }

    fn copy_recorded(
        solver: &mut Solver,
        lim: Level,
        original: &Rc<InferVar>,
        copy: &Rc<InferVar>,
        target: FreshenLevel,
        cache: &mut FreshenCache,
    ) {
        // The kinds the original sits under are this copy's kinds, whichever this walk
        // reaches first: a variable copied before the function it is a part of would
        // otherwise sit under the definition's kind, which nothing at the use relates to.
        for k in original.witness_scope_kinds(solver) {
            freshen_handle(solver, lim, &k, target, cache);
        }
        copy.inherit_witness_placement_renamed(
            solver,
            original,
            |k| cache.copy_of(k).unwrap_or_else(|| Rc::clone(k)),
            |w| cache.witnesses.get(w).copied().unwrap_or(*w),
        );
        if original.names_domain(solver) {
            copy.mark_named_domain(solver);
        }
        copy.inherit_stands_for(solver, original);

        // Snapshot bounds before recursing — the recursion may touch
        // other variables but must not see partially-mutated state.
        let (lows, ups, kinds) = {
            let s = original.bounds(solver);
            (
                Rc::clone(s.lower()),
                Rc::clone(s.upper()),
                s.type_kinds.clone(),
            )
        };
        // Freshen the bound's type *and* its edge substitutions' discharge
        // payloads: a payload is a captured argument *term* whose type
        // slots still reference the source graph's variables, so it is
        // freshened through the same `cache` (the uniform term+type freshen
        // that subsumes the old separate `freshen_bound_substs` sweep).
        let new_lows: Vec<_> = lows
            .iter()
            .map(|b| Bound {
                origin: b.origin,
                self_subst: freshen_subst_payloads(solver, lim, &b.self_subst, target, cache),
                ty: freshen_above(solver, lim, &b.ty, target, cache),
                ty_subst: freshen_subst_payloads(solver, lim, &b.ty_subst, target, cache),
                rendered: Default::default(),
            })
            .collect();
        let new_ups: Vec<_> = ups
            .iter()
            .map(|b| Bound {
                origin: b.origin,
                self_subst: freshen_subst_payloads(solver, lim, &b.self_subst, target, cache),
                ty: freshen_above(solver, lim, &b.ty, target, cache),
                ty_subst: freshen_subst_payloads(solver, lim, &b.ty_subst, target, cache),
                rendered: Default::default(),
            })
            .collect();
        // Every instantiation gets its own copy of the kinding constraints. A
        // generalized definition's requirement is part of its scheme, so dropping
        // it here would make the requirement vanish at each use site — the
        // constraint would be checked on a variable nothing resolves and never on
        // the ones that do.
        let new_kinds: Vec<_> = kinds
            .iter()
            .map(|k| k.map_children(|t| freshen_above(solver, lim, t, target, cache)))
            .collect();
        // And of the guarded bounds, for the same reason: each instantiation's lower bounds
        // are checked under its own copy. The guard is freshened as the refinement it is, on
        // the copy of the variable it guards.
        let guarded = original.bounds(solver).guarded_upper.clone();
        let new_guarded: Vec<_> = guarded
            .iter()
            .map(|g| {
                let guarded_ty = freshen_above(
                    solver,
                    lim,
                    &Type::refined(Type::Infer(Rc::clone(original)), g.guard.clone()),
                    target,
                    cache,
                );
                crate::ccl::infer_var::GuardedBound {
                    guard: guarded_ty.refinements().iter().cloned().collect(),
                    bound: Bound {
                        origin: g.bound.origin,
                        self_subst: freshen_subst_payloads(
                            solver,
                            lim,
                            &g.bound.self_subst,
                            target,
                            cache,
                        ),
                        ty: freshen_above(solver, lim, &g.bound.ty, target, cache),
                        ty_subst: freshen_subst_payloads(
                            solver,
                            lim,
                            &g.bound.ty_subst,
                            target,
                            cache,
                        ),
                        rendered: Default::default(),
                    },
                }
            })
            .collect();
        let s = copy.bounds_mut(solver);
        s.set_lower(new_lows);
        s.set_upper(new_ups);
        s.type_kinds = new_kinds;
        s.guarded_upper = new_guarded;
        // A suspension's kinds are decided on it, and so on its copy
        // ([`crate::ccl::infer_var::SuspendedMembership`]).
        for m in crate::ccl::infer_var::suspended_memberships_of(solver, original) {
            let kind = m
                .kind
                .map_children(|t| freshen_above(solver, lim, t, target, cache));
            let witnesses = m
                .witnesses
                .map_types(|t| freshen_above(solver, lim, t, target, cache));
            crate::ccl::infer_var::record_suspended_membership(
                solver,
                crate::ccl::infer_var::SuspendedMembership {
                    var: Rc::clone(copy),
                    kind,
                    witnesses,
                    origin: m.origin,
                },
            );
        }
        // And a membership recorded on a reading of the original, which only the original's
        // suspensions reach: the copy reads the same way, and the kind is decided on that.
        let readings: Vec<Rc<InferVar>> = original
            .suspensions(solver)
            .iter()
            .map(|(_, held)| Rc::clone(held))
            .filter(|held| crate::ccl::infer_var::has_suspended_memberships(solver, held))
            .collect();
        for held in readings {
            freshen_above(solver, lim, &Type::Infer(held), target, cache);
        }
        let watches = original.watches(solver).to_vec();
        if original.is_barrier() {
            // An upper bound's report is the edge's that recorded it, the copy's too.
            for (i, upper) in original.barrier_uppers(solver).iter().enumerate() {
                if let Some(report) = &upper.report {
                    copy.report_upper(solver, i, Rc::clone(report));
                }
            }
            // A barrier variable is never an operand, so the copy records the watch
            // without `TraitObligation::watch`, which would make it one.
            freshen_watches(
                solver,
                lim,
                watches,
                &|solver, _, obligation, pos| {
                    copy.watches_mut(solver).push((Rc::clone(obligation), pos))
                },
                target,
                cache,
            );
        } else {
            freshen_watches(
                solver,
                lim,
                watches,
                &|solver, from, obligation, pos| {
                    obligation.copy_watch(solver, from, pos, original.uid, copy)
                },
                target,
                cache,
            );
        }
    }
}

/// How [`freshen_watches`] records a copy's watch on the freshened variable: given the original
/// obligation, its copy and the watched position.
type AttachWatch<'a> = dyn Fn(&mut Solver, &TraitObligation, &Rc<TraitObligation>, u8) + 'a;

/// Copy the trait obligations in `watches`, a variable's watch list, onto its freshened
/// counterpart: `attach` records the watch of each copy on it, given the original the copy
/// is of.
///
/// Runs *after* the bounds write-back, so an obligation reached through a bound has
/// already had its variables freshened into the cache and the copy's watches line up
/// with the copy's variables.
///
/// The clone is inserted into the cache **before** its associated positions are
/// freshened.
/// The obligation graph is cyclic — an obligation holds its output type, which holds
/// a variable, which watches the obligation — so freshening the output re-enters
/// here, and a clone that is not yet reachable would be minted twice: once per
/// operand, each watching a different copy, and neither ever narrowed by both
/// operands.
fn freshen_watches(
    solver: &mut Solver,
    lim: Level,
    watches: Vec<(Rc<TraitObligation>, u8)>,
    attach: &AttachWatch<'_>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) {
    for (obligation, pos) in watches {
        let copy = freshen_handle(solver, lim, &obligation, target, cache);
        attach(solver, &obligation, &copy, pos);
    }
}

/// A new copy of `obligation`: its candidates and state, and, once the copy is reachable, its
/// operands, associated types, effects and refinement inputs as this freshening copies them
/// ([`freshen_held`]).
fn copy_obligation(
    solver: &mut Solver,
    lim: Level,
    obligation: &Rc<TraitObligation>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Rc<TraitObligation> {
    {
        // Phase 1: a copy carrying the original's candidate set, with the output
        // position still pointing at the definition's — enough to be reachable.
        let copy = TraitObligation::new_from(solver, obligation);
        cache.record_copy(obligation, Rc::clone(&copy));
        // A specialization clone turns the binding's own type parameters, the ones
        // one level above the cutoff, into variables; an assumption about one of
        // them no longer describes the copy. The parameters are told apart by identity:
        // a sibling definition's parameters can sit at the same level.
        let mut reset = false;
        if let Some(own) = cache.own_params.clone() {
            reset = copy.reset_for_specialization(&own);
            if reset {
                cache.reset_obligations.push(Rc::clone(&copy));
            }
        }
        // What the copy assumes names enclosing definitions' parameters, which freshen to
        // themselves, and nested definitions' ones, which the copy re-mints through this cache.
        copy.map_assumptions(|t| freshen_above(solver, lim, t, target, cache));
        // A copy made for a use is answered under what the use assumes, where nothing the
        // definition assumed about its trait answers it: one assuming nothing, or one the reset
        // took the definition's own assumptions from.
        if reset || copy.assumptions().is_empty() {
            copy.assume_more(&cache.use_assumptions);
        }
        // Phase 2: now that re-entry finds the copy, freshen every operand, and the
        // output and the input expressions a refinement template builds from. An
        // operand the definition's operator minted is above the cutoff, and its copy
        // is reached here rather than only through the type being freshened: the
        // variable a literal flows into is reached through no type, and the copy
        // states its requirement whole only with it. An obligation the enclosing scope
        // minted has its operands at or below the cutoff; they freshen to themselves,
        // the copy watches none of them, and it states no requirement of the
        // definition's.
        for operand in obligation.operands().into_iter().flatten() {
            freshen_above(solver, lim, &operand, target, cache);
        }
        copy.set_assoc_types(
            obligation
                .assoc_types()
                .iter()
                .map(|ty| freshen_above(solver, lim, ty, target, cache))
                .collect(),
        );
        // What the copy selects is what its copies of the definition's associated effect types
        // hold.
        copy.set_effects(
            obligation
                .effects()
                .into_iter()
                .map(|(assoc, var)| (assoc, freshen_handle(solver, lim, &var, target, cache)))
                .collect(),
        );
        let _f = crate::ccl::provenance::copy_frame("infer.freshen_obligation_inputs");
        if let Some(operands) = copy.refinement_operands() {
            copy.set_refinement_operands(
                operands
                    .into_iter()
                    .map(|mut expr| {
                        freshen_expr_type_slots(solver, &mut expr, lim, target, cache);
                        expr
                    })
                    .collect(),
            );
        }
        copy
    }
}

/// Freshen every type slot reachable from an expression, through one shared
/// [`FreshenCache`], recursing into child terms. Slot coverage is
/// [`TypedExpr::walk_type_slots_mut`]'s — `expr.ty`, the user annotation, each
/// binder's declared type, a `Cast`'s target — rather than enumerated here, so a
/// new type-slot-bearing variant cannot leave a clone with a mix of fresh and
/// original variables. Used to freshen a
/// specialization clone's whole subtree (`infer::solve::specialize_use`).
///
/// Refinement predicates carried on those types are freshened by the same walk
/// ([`super::transport::transport_refinement`]), so this walk reaches every type
/// in the AST. A definition's interior carries variables (e.g. `Proj` seeds)
/// that never appear in its root type; missing them would leave a clone with a
/// mix of fresh and original variables and coalesce to an unresolved type.
pub fn freshen_expr_type_slots(
    solver: &mut Solver,
    expr: &mut TypedExpr,
    lim: Level,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) {
    super::transport::transport_term(solver, expr, &mut Copying::new(lim, target, cache));
}

/// The copy of `obligation` this freshening makes: one exists where a variable it watches is
/// above the cutoff, and freshening that variable copies the obligation with it
/// ([`freshen_watches`]). An obligation watching none, which the enclosing scope minted, is
/// its own.
fn freshen_obligation(
    solver: &mut Solver,
    lim: Level,
    obligation: &Rc<TraitObligation>,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Rc<TraitObligation> {
    freshen_handle(solver, lim, obligation, target, cache)
}

/// Structurally pair a use site's resolved instantiation type against the
/// definition's type, seeding `out` with def-name → use-name entries for each
/// *quantified* (level > `lim`) channel-domain name. Pass-1 instantiation
/// minted the use side's names ([`freshen_above`]'s `ChanDom` arm); the
/// specialization clone must reuse *those* names — a rigid name, unlike a
/// variable, cannot be identified with its instantiation through the pin's
/// bounds — so `specialize_use` seeds the clone's [`FreshenCache`] with these
/// pairings before freshening.
///
/// Positions are matched constructor-wise through refinements; a position
/// where the sides disagree structurally (an unexercised placeholder, a
/// collapsed union) is skipped — the clone then mints a fresh name there and
/// any stale consumer name surfaces at the post-channelize strict typecheck
/// rather than silently.
pub fn seed_chan_dom_pairings(
    solver: &mut Solver,
    use_ty: &Type,
    def_ty: &Type,
    lim: Level,
    out: &mut HashMap<crate::ccl::Name, crate::ccl::Name>,
) {
    let mut seen = std::collections::HashSet::new();
    seed_pairings_go(solver, use_ty, def_ty, lim, out, &mut seen);
}

/// A type holding bounds that [`seed_pairings_go`] descends through, once each.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum BoundHolder {
    InferVar(InferVarId),
}

fn seed_pairings_go(
    solver: &mut Solver,
    use_ty: &Type,
    def_ty: &Type,
    lim: Level,
    out: &mut HashMap<crate::ccl::Name, crate::ccl::Name>,
    seen: &mut std::collections::HashSet<BoundHolder>,
) {
    fn peel(ty: &Type) -> &Type {
        match ty {
            Type::Refinement(inner, _) => peel(inner),
            _ => ty,
        }
    }
    // The definition side is unresolved — a slot is often a *variable* whose
    // bounds carry the structure (a lambda definition's type is a var bounded
    // by its `Fun`). Descend through the bounds, once per var (`seen` guards
    // the cyclic bound graph). The use side is resolved; a placeholder var
    // there has no bounds and pairs nothing.
    // A barrier variable resolves to the join of its lower bounds, so those carry its
    // structure on either side; its upper bounds are checks against that join and add no
    // position to pair.
    if let Type::Infer(dv) = peel(def_ty) {
        if seen.insert(BoundHolder::InferVar(dv.uid)) {
            let (lows, ups) = {
                let s = dv.bounds(solver);
                let ups = if dv.is_barrier() {
                    Rc::new(Vec::new())
                } else {
                    Rc::clone(s.upper())
                };
                (Rc::clone(s.lower()), ups)
            };
            for b in lows.iter().chain(ups.iter()) {
                seed_pairings_go(solver, use_ty, &b.ty, lim, out, seen);
            }
        }
        return;
    }
    if let Type::Infer(uv) = peel(use_ty) {
        if seen.insert(BoundHolder::InferVar(uv.uid)) {
            let (lows, ups) = {
                let s = uv.bounds(solver);
                let ups = if uv.is_barrier() {
                    Rc::new(Vec::new())
                } else {
                    Rc::clone(s.upper())
                };
                (Rc::clone(s.lower()), ups)
            };
            for b in lows.iter().chain(ups.iter()) {
                seed_pairings_go(solver, &b.ty, def_ty, lim, out, seen);
            }
        }
        return;
    }
    match (peel(use_ty), peel(def_ty)) {
        (Type::ChanDom(u, _), Type::ChanDom(d, dlvl)) if dlvl.0 > lim && u != d => {
            let prev = out.insert(d.clone(), u.clone());
            debug_assert!(
                prev.is_none_or(|p| p == *u),
                "seed_chan_dom_pairings: definition channel `{d}` paired against two \
                 distinct use-site names"
            );
        }
        (Type::ChanDom(..), Type::ChanDom(..)) => {}
        (
            Type::Fun {
                domain: ud,
                codomain: uc,
                ..
            },
            Type::Fun {
                domain: dd,
                codomain: dc,
                ..
            },
        ) => {
            seed_pairings_go(solver, ud, dd, lim, out, seen);
            seed_pairings_go(solver, uc, dc, lim, out, seen);
        }
        (Type::Tuple(us), Type::Tuple(ds)) => {
            for (u, d) in us.iter().zip(ds) {
                seed_pairings_go(solver, u, d, lim, out, seen);
            }
        }
        (Type::Record(us), Type::Record(ds)) => {
            for ((un, u), (dn, d)) in us.iter().zip(ds) {
                if un == dn {
                    seed_pairings_go(solver, u, d, lim, out, seen);
                }
            }
        }
        // Openness plays no part in *pairing* payloads: this walks two structurally
        // corresponding types and matches arms by tag, which is the same work whether
        // either side commits to further arms.
        (Type::Variant(us, _), Type::Variant(ds, _)) => {
            for ((uk, u), (dk, d)) in us.iter().zip(ds) {
                if uk == dk {
                    seed_pairings_go(solver, u, d, lim, out, seen);
                }
            }
        }
        (Type::History { function: uv, .. }, Type::History { function: dv, .. }) => {
            seed_pairings_go(solver, uv, dv, lim, out, seen)
        }
        _ => {}
    }
}

/// Freshen the payloads of a bound edge's substitution: each captured *term* has its type
/// slots renamed through `cache`. Renames and an unkeyed join carry no term, so only
/// [`crate::ccl::subst::Mapping::Discharge`] and keyed [`crate::ccl::subst::Mapping::Join`]
/// entries are touched.
fn freshen_subst_payloads(
    solver: &mut Solver,
    lim: Level,
    subst: &Subst,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Subst {
    let mut copying = Copying::new(lim, target, cache);
    copying.rename_names = true;
    super::transport::transport_subst(solver, subst, &mut copying)
}

/// [`freshen_subst_payloads`] with no binder renamed: the payloads' type slots and the witness
/// half freshened through `cache`.
fn freshen_subst_payload_terms(
    solver: &mut Solver,
    lim: Level,
    subst: &Subst,
    target: FreshenLevel,
    cache: &mut FreshenCache,
) -> Subst {
    let mut copying = Copying::new(lim, target, cache);
    copying.rename_names = false;
    super::transport::transport_subst(solver, subst, &mut copying)
}

#[cfg(test)]
mod tests {
    use super::super::type_level;
    use super::*;
    use crate::ccl::Refinement;
    use crate::ccl::ty::{FunKind, FunKindVar, KindPin};
    use crate::ccl::{BaseType, InferVar};

    #[test]
    fn freshening_mints_a_distinct_kind_var_per_instantiation() {
        let solver = &mut Solver::new();
        // A generalized function's kind must be decided per use. Freshening
        // a Fun whose kind is an unpinned var must mint a *new* FunKindVar (the pin
        // copied), not share the original — otherwise pinning one instantiation's
        // kind contaminates the other into a spurious `DomainJoinConflict`.
        let kv = FunKindVar::fresh(solver, 5, &Telescope::empty());
        kv.stamp_data(solver); // a def-intrinsic answer to carry onto each instantiation
        // A quantified domain (level > lim) so the Fun is instantiated, not
        // early-returned as a captured/monomorphic shape.
        let f = Type::Fun {
            binder: crate::ccl::FunBinder::None,
            fun_kind: FunKind::Var(Rc::clone(&kv)),
            domain: Box::new(Type::Infer(InferVar::fresh(solver, 5))),
            codomain: Box::new(Type::Base(BaseType::Int)),
            capabilities: Capabilities::none(),
        };
        let mut cache = FreshenCache::new();
        let fresh = freshen_above(solver, 0, &f, FreshenLevel::At(1), &mut cache);
        let Type::Fun {
            fun_kind: FunKind::Var(kv2),
            ..
        } = fresh
        else {
            panic!("expected a kind var on the freshened function");
        };
        assert_ne!(
            kv.uid, kv2.uid,
            "instantiation must mint a distinct kind var"
        );
        assert_eq!(
            kv2.resolved_in(solver),
            KindPin::Data,
            "the definition's pin is copied to the fresh var"
        );
        // Pinning the fresh instantiation must not reach back to the original.
        kv2.record(solver, FunKind::Compute, true);
        assert_eq!(
            kv.resolved_in(solver),
            KindPin::Data,
            "the original var stays decoupled from this instantiation"
        );
    }

    /// A function whose funkind variable stands at the cutoff and whose only quantified content is
    /// a capability variable is still copied: each use collects its own capabilities.
    #[test]
    fn a_capability_variable_beside_a_shared_funkind_variable_is_copied() {
        let solver = &mut Solver::new();
        let kind = FunKindVar::fresh(solver, 0, &Telescope::empty());
        let quantified = CapabilityVar::fresh(solver, 1, &Telescope::empty());
        let ty = Type::Fun {
            binder: crate::ccl::FunBinder::None,
            fun_kind: FunKind::Var(Rc::clone(&kind)),
            domain: Box::new(Type::Base(BaseType::Int)),
            codomain: Box::new(Type::Base(BaseType::Int)),
            capabilities: Capabilities::var(Rc::clone(&quantified)),
        };
        let Type::Fun {
            fun_kind: FunKind::Var(copied_kind),
            capabilities,
            ..
        } = PolyScheme::poly(0, ty).instantiate(solver, 0)
        else {
            panic!("expected a function with a funkind variable");
        };
        assert_eq!(
            copied_kind.uid, kind.uid,
            "a funkind variable at the cutoff is shared"
        );
        let Repr::Var(copy) = capabilities.repr() else {
            panic!("expected a capability variable");
        };
        assert_ne!(
            copy.uid, quantified.uid,
            "the capability variable above the cutoff is copied"
        );
    }

    /// The function `domain => Int` whose capabilities are `capabilities`.
    fn function_over(domain: Type, capabilities: &Rc<CapabilityVar>) -> Type {
        Type::Fun {
            binder: crate::ccl::FunBinder::None,
            fun_kind: FunKind::Compute,
            domain: Box::new(domain),
            codomain: Box::new(Type::Base(BaseType::Int)),
            capabilities: Capabilities::var(Rc::clone(capabilities)),
        }
    }

    /// A variable a scheme's capabilities flow into, which an instantiation keeps, holds the
    /// exception each use raises: the definition's exception reaches it extruded, so its type is
    /// a variable at the kept level that each instance's copy of the exception's type flows into.
    #[test]
    fn a_kept_variable_holds_the_exception_each_use_raises() {
        use crate::ccl::capabilities::{Effect, Filter, LocatedCapability, Raised};
        let solver = &mut Solver::new();
        let kept = CapabilityVar::fresh(solver, 0, &Telescope::empty());
        let quantified = CapabilityVar::fresh(solver, 1, &Telescope::empty());
        let raised = InferVar::fresh(solver, 1);
        quantified.record(
            solver,
            LocatedCapability {
                item: Capability::Causes(Effect::Raise(Raised::at(
                    crate::ccl::provenance::NodeId::fresh(),
                    Type::Infer(Rc::clone(&raised)),
                ))),
                at: None,
            },
        );
        kept.flows_from(solver, &quantified, Filter::default());
        let ty = function_over(Type::Infer(Rc::clone(&raised)), &quantified);
        let Type::Fun { domain, .. } = PolyScheme::poly(0, ty).instantiate(solver, 0) else {
            panic!("expected a function");
        };
        // The use passes an `Int`, which its instance raises.
        super::super::constrain::constrain_subtype(
            solver,
            &Type::Base(BaseType::Int),
            &domain,
            &mut super::super::constrain::ConstrainCache::new(),
        )
        .expect("an Int argument");
        let types: Vec<_> = kept
            .resolved(solver)
            .iter()
            .filter_map(|c| match &c.item {
                Capability::Causes(Effect::Raise(r)) => Some(r.resolved(solver)),
                _ => None,
            })
            .collect();
        assert_eq!(types, vec![Some(Type::Base(BaseType::Int))]);
    }

    /// Lowering a capability variable lowers each deeper variable it pushes into, as lowering an
    /// inference variable lowers its bounds: an instantiation then keeps that variable, which
    /// holds what the lowered one comes to hold later.
    #[test]
    fn lowering_a_capability_variable_lowers_what_it_pushes_into() {
        use crate::ccl::capabilities::{Effect, Filter, LocatedCapability};
        let solver = &mut Solver::new();
        let source = CapabilityVar::fresh(solver, 1, &Telescope::empty());
        let downstream = CapabilityVar::fresh(solver, 1, &Telescope::empty());
        downstream.flows_from(solver, &source, Filter::default());
        let int = || Type::Base(BaseType::Int);
        super::super::constrain::lower_levels(solver, &function_over(int(), &source), 0);
        assert_eq!(downstream.level(solver), 0);
        let Type::Fun { capabilities, .. } =
            PolyScheme::poly(0, function_over(int(), &downstream)).instantiate(solver, 0)
        else {
            panic!("expected a function");
        };
        let Repr::Var(instance) = capabilities.repr() else {
            panic!("expected a capability variable");
        };
        assert_eq!(instance.uid, downstream.uid, "the instantiation keeps it");
        let affects_world = Capability::Causes(Effect::AffectWorld);
        source.record(
            solver,
            LocatedCapability {
                item: affects_world.clone(),
                at: None,
            },
        );
        assert!(
            instance
                .resolved(solver)
                .iter()
                .any(|c| c.item == affects_world)
        );
    }

    /// A quantified variable reachable *only* through a refinement predicate must
    /// still be freshened.
    ///
    /// The shape is the one a comprehension produces: a `Fun` whose every
    /// structural position is concrete (`[0,2] ⇒ Int`), carrying a refinement whose
    /// base is also concrete — so `type_level` reports 0 for the whole thing — while
    /// the predicate holds a level-5 variable. Short-circuiting on `type_level`
    /// returns the type verbatim and the clone keeps pointing at the definition's
    /// live variable, which shows up downstream as a *duplicate* specialization:
    /// the clone reaches one generalized `let` through both the freshened variable
    /// and the original.
    ///
    /// Guarding a top-level `Refinement` is not enough — one level of nesting is
    /// what the real shape has, and what this pins.
    #[test]
    fn a_variable_reachable_only_through_a_predicate_is_freshened() {
        let solver = &mut Solver::new();
        let quantified = InferVar::fresh(solver, 5);
        // A predicate term whose *type slot* holds the quantified variable.
        let predicate = Rc::new(
            TypedExpr::lit(crate::ccl::Lit::Bool(true))
                .with_ty(Type::Infer(Rc::clone(&quantified))),
        );
        let refined_domain = Type::refined_one(
            Type::UIntRange(3), // concrete base: hides the predicate's level
            Refinement::sharing(&predicate),
        );
        let ty = Type::Fun {
            binder: crate::ccl::FunBinder::None,
            fun_kind: FunKind::Compute,
            domain: Box::new(refined_domain),
            codomain: Box::new(Type::Base(BaseType::Int)),
            capabilities: Capabilities::none(),
        };
        assert_eq!(
            type_level(solver, &ty),
            0,
            "precondition: `type_level` cannot see the predicate's variable"
        );

        let mut cache = FreshenCache::new();
        let fresh = freshen_above(solver, 0, &ty, FreshenLevel::At(1), &mut cache);

        let Type::Fun { domain, .. } = &fresh else {
            panic!("expected a function type");
        };
        let [r] = domain.refinements() else {
            panic!("expected the refinement to survive freshening");
        };
        let Type::Infer(v) = &r.predicate.ty else {
            panic!("expected the predicate's type slot to stay a variable");
        };
        assert_ne!(
            v.uid, quantified.uid,
            "a quantified variable reachable only through a predicate must be \
             freshened — sharing it with the definition mints a duplicate \
             specialization"
        );
    }
}

#[cfg(all(test, debug_assertions))]
mod copy_audit_tests {
    use super::*;
    use crate::ccl::{BaseType, Expr, InferVar, Name, Refinement};

    #[test]
    fn the_copy_audit_enters_every_held_term() {
        let solver = &mut Solver::new();
        let variable = super::super::fresh_var(solver, 1);
        let held = Rc::new(Expr::var("condition").with_ty(variable));
        let roots = [
            Type::refined_one(
                Type::Base(BaseType::Int),
                Refinement::born(Rc::clone(&held)),
            ),
            Type::FamilyApp(crate::ccl::ty::FamilyApp::new(
                crate::ccl::TypeParam::declared_family("V", 1),
                vec![Rc::clone(&held)],
            )),
            Type::WitnessProjection(crate::ccl::ty::WitnessProjection::new(held, 0)),
        ];
        let before = Minted::now();
        for root in roots {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    assert_copied_apart(solver, 0, &[root], &FreshenCache::new(), before);
                }))
                .is_err(),
                "a held variable shared above the cutoff must be rejected"
            );
        }
    }

    #[test]
    fn settled_sum_kinds_on_copied_edges_freshen_their_candidates() {
        let solver = &mut Solver::new();
        let candidate = super::super::fresh_var(solver, 1);
        let sum = Type::sum_over(
            crate::ccl::TypeKind::Enumerated(vec![candidate.clone()]),
            None,
            Type::Base(BaseType::Int),
        );
        let kind = FunKind::fresh_var(solver, 1, &Telescope::empty());
        let FunKind::Var(k) = &kind else {
            unreachable!()
        };
        k.record_under(solver, sum.fun_kind().unwrap().clone(), true, Subst::id());
        let ty = Type::fun_over(
            Name::fresh("x"),
            Type::Base(BaseType::Int),
            Type::Base(BaseType::Int),
            kind,
        );
        let variable = InferVar::fresh(solver, 1);
        variable.fun_kind().record_under(
            solver,
            sum.fun_kind().unwrap().clone(),
            true,
            Subst::id(),
        );
        for source in [ty, Type::Infer(variable)] {
            let instance = PolyScheme::poly(0, source).instantiate(solver, 0);
            let copied = match &instance {
                Type::Infer(v) => Rc::clone(v.fun_kind()),
                ty => match ty.fun_kind().unwrap() {
                    FunKind::Var(k) => Rc::clone(k),
                    _ => unreachable!(),
                },
            };
            let edge = copied
                .lower_edges(solver)
                .into_iter()
                .find_map(|(kind, _)| match kind {
                    FunKind::Data(Some(witnesses)) => Some(witnesses),
                    _ => None,
                })
                .unwrap();
            let crate::ccl::TypeKind::Enumerated(types) = edge[0].type_kind() else {
                unreachable!()
            };
            assert_ne!(types[0], candidate);
        }
    }

    #[test]
    fn copying_a_function_places_only_its_fresh_variables_under_the_copy() {
        let solver = &mut Solver::new();
        let captured = InferVar::fresh(solver, 0);
        let quantified = InferVar::fresh(solver, 1);
        let ty = Type::Fun {
            binder: crate::ccl::FunBinder::None,
            fun_kind: FunKind::fresh_var(solver, 1, &Telescope::empty()),
            domain: Box::new(Type::Tuple(vec![
                Type::Infer(Rc::clone(&captured)),
                Type::Infer(quantified),
            ])),
            codomain: Box::new(Type::Base(BaseType::Int)),
            capabilities: Capabilities::none(),
        };
        let instance = PolyScheme::poly(0, ty).instantiate(solver, 0);
        let Type::Fun {
            fun_kind: FunKind::Var(kind),
            domain,
            ..
        } = instance
        else {
            unreachable!()
        };
        let Type::Tuple(parts) = *domain else {
            unreachable!()
        };
        let Type::Infer(fresh) = &parts[1] else {
            unreachable!()
        };
        assert!(captured.witness_scope_kinds(solver).is_empty());
        assert_eq!(parts[0], Type::Infer(captured));
        assert!(
            fresh
                .witness_scope_kinds(solver)
                .iter()
                .any(|k| k.uid == kind.uid)
        );
    }

    #[test]
    fn a_funkind_is_copied_even_when_its_function_has_no_type_variables() {
        let solver = &mut Solver::new();
        let kind = FunKind::fresh_var(solver, 1, &Telescope::empty());
        let int = Type::Base(BaseType::Int);
        let ty = Type::fun_over(Name::fresh("x"), int.clone(), int, kind.clone());
        let scheme = PolyScheme::poly(0, ty);
        let a = scheme.instantiate(solver, 0);
        let b = scheme.instantiate(solver, 0);
        let kind_id = |t: &Type| match t.fun_kind().unwrap() {
            FunKind::Var(k) => k.uid,
            _ => panic!("an unpinned funkind remains a variable"),
        };
        let FunKind::Var(original) = kind else {
            unreachable!()
        };
        assert_ne!(kind_id(&a), original.uid);
        assert_ne!(kind_id(&a), kind_id(&b));
    }
}

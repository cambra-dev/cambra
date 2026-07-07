//! Capture-avoiding substitutions over term binders — the context-morphism
//! machinery for dependent refinements (Pi types).
//!
//! This is the load-bearing distinction from the design proposal
//! (`brainstorm/2026-06-02-dependent-refinements-via-pi-types.md`, §3.5) and its
//! executable model
//! (`brainstorm/2026-06-02-dependent-refinements-substitution-prototype.rs`):
//!
//! * A **context** annotates a type or metavariable — the binders it may
//!   legitimately mention. It is a *checking* device only (free vars ⊆ context);
//!   it transforms nothing. See [`well_formed`].
//! * A **substitution** ([`Subst`]) is a context morphism `Γ_src → Γ_dst` that
//!   rides on a constraint edge and *rewrites* a term/type as it propagates.
//!   Two flavours:
//!     - a **rename** `[k ↦ x]` (a bijection on binders) is **invertible**;
//!     - a **discharge** `[x ↦ arg]` (plug an argument in for a binder) is
//!       **one-way** (no inverse).
//!
//! A [`Subst`] maps *term* binders — `TypedExprNode::Var(name)` references — to
//! replacement [`TypedExpr`]s. It is deliberately **not** a type-variable
//! substitution: it never relabels a [`Type::Infer`] (those belong to
//! freshening, a separate mechanism). Applying a substitution traverses terms
//! and types uniformly — refinement *predicates* are terms, and every node's
//! type slots are reached in the same pass — shadowing the binder of any
//! enclosing lambda / `let` / Pi it passes under. Under the Barendregt
//! convention capture cannot occur, and the engine asserts that rather than
//! α-renaming (see [`Subst::under_binder`]).
//!
//! Predicates are immutable (`Rc<TypedExpr>`), so a rewrite always *rebuilds* a
//! new predicate term — it never mutates one in place. The one engine drives
//! two modes that differ only in what *else* they touch:
//!
//! * **Transport** ([`Subst::apply_expr`] / [`Subst::apply_type`]) builds new
//!   terms/types, used where a substitution rides a constraint edge: a changed
//!   predicate gets a fresh `Rc` ([`Subst::force_refinement`]) while a vacuous
//!   one keeps sharing the source's `Rc` (pointer-equal, so the source context
//!   stays intact and the common case allocates nothing).
//! * **In-place rewrite** ([`Subst::rewrite_expr`]) mutates the *term tree* the
//!   caller owns (lambda elimination, inlining, defer desugaring, lowering's
//!   uncurrying), but still rebuilds each predicate as a fresh `Rc`. A `memo`
//!   keyed on the original predicate's identity re-points every occurrence
//!   that shared one predicate term in the tree at the *same* rebuilt term, so
//!   one rewrite is observed uniformly across the aliases.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ccl::ccl_utils::is_free;
use crate::ccl::{Branch, Name, PredicateId, Type, TypedExpr, TypedExprNode};

/// A term binder name.
pub type Binder = Name;

/// A single mapping target: a **rename** to another binder (invertible) or a
/// **discharge** to a term (one-way).
///
/// The variant is the morphism's *species*, assigned at construction —
/// provenance, not target shape reconstructed by inspecting terms. This is
/// what lets [`Subst::invert`] and [`Subst::split_renames`] be exact by
/// construction: inversion legality is type-enforced, and "the rename part"
/// means precisely the entries constructed as correspondences.
#[derive(Clone, Debug, PartialEq)]
pub enum Mapping {
    /// `binder ↦ other binder` — a correspondence between frames. Invertible.
    Rename(Binder),
    /// `binder ↦ term` — plug a term in for the binder. No inverse.
    /// (Boxed: a term is much larger than a binder name.)
    Discharge(Box<TypedExpr>),
}

impl Mapping {
    /// The mapping's replacement as a term (a `Rename` materializes as a bare
    /// variable reference).
    fn as_expr(&self) -> TypedExpr {
        match self {
            Mapping::Rename(to) => TypedExpr::var(to.clone()),
            Mapping::Discharge(t) => (**t).clone(),
        }
    }
}

/// A simultaneous substitution `{binder ↦ mapping, …}`. An absent binder maps
/// to itself (the identity). The empty map is [`Subst::id`].
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Subst(BTreeMap<Binder, Mapping>);

impl Subst {
    /// The identity substitution — a perfect no-op. `apply_*` on it returns the
    /// input structurally unchanged.
    pub fn id() -> Self {
        Subst(BTreeMap::new())
    }

    /// Is this the identity? Callers fast-path the common (non-dependent) case
    /// on this so that ordinary code paths are byte-identical to a world
    /// without substitutions.
    pub fn is_id(&self) -> bool {
        self.0.is_empty()
    }

    /// A rename `[from ↦ to]` — a bijection on binders, hence invertible.
    pub fn rename(from: impl Into<Name>, to: impl Into<Name>) -> Self {
        let mut m = BTreeMap::new();
        m.insert(from.into(), Mapping::Rename(to.into()));
        Subst(m)
    }

    /// A discharge `[binder ↦ term]` — plug `term` in for `binder`. One-way,
    /// **unconditionally**: the species is the caller's declared intent, even
    /// when `term` happens to be a bare variable reference. `[x ↦ k0]` from a
    /// dependent application `g(k0)` is fiber *selection* — inverting it
    /// would be fiber→family generalization, an overclaim in general. The one
    /// consumer permitted to read a Var-target discharge as a correspondence
    /// is the closure bridge, through the explicitly licensed
    /// [`Subst::licensed_correspondence_view`]; everywhere else the species
    /// is honest, and a caller that *means* a frame correspondence
    /// (relabeling, inversion-safe with no license) must say so with
    /// [`Subst::rename`].
    pub fn discharge(binder: impl Into<Name>, term: TypedExpr) -> Self {
        let mut m = BTreeMap::new();
        m.insert(binder.into(), Mapping::Discharge(Box::new(term)));
        Subst(m)
    }

    /// The binders this substitution acts on (its source domain).
    pub fn binders(&self) -> impl Iterator<Item = &Binder> {
        self.0.keys()
    }

    /// Visit each discharge mapping's captured term mutably (renames have no
    /// term). For specialization freshening: a suspended discharge's term was
    /// captured at emit with the definition's inference variables in its type
    /// slots, and a freshened clone must rename those alongside every other
    /// slot it copies — see `solver::scheme::freshen_subst_payloads`, called from
    /// `freshen_above`'s bound-copying arm.
    pub fn for_each_discharge_term_mut(&mut self, f: &mut impl FnMut(&mut TypedExpr)) {
        for m in self.0.values_mut() {
            if let Mapping::Discharge(t) = m {
                f(t);
            }
        }
    }

    /// Split into the rename entries and the discharge entries — a variant
    /// partition, exact by construction (see [`Mapping`]). The two act on
    /// disjoint binders, so the original is their parallel union; this is the
    /// factoring [`crate::ccl::infer::solver`]'s closure bridge uses to
    /// reconcile two composite holder-side morphisms that share their
    /// discharge part but differ in correspondence renames.
    pub fn split_renames(&self) -> (Subst, Subst) {
        let (ren, term): (BTreeMap<_, _>, BTreeMap<_, _>) = self
            .0
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .partition(|(_, v)| matches!(v, Mapping::Rename(_)));
        (Subst(ren), Subst(term))
    }

    /// Equality up to the terms' *type slots* — same binders, and each pair
    /// of replacement terms equal by the codebase's type-blind structural
    /// comparison (`eq_refinement_predicate`, the equality that backs
    /// [`crate::ccl::Refinement`]'s `PartialEq`).
    ///
    /// Why this exists: a discharge captures its argument expression **at emit
    /// time**, with whatever inference-variable slots emission minted — so two
    /// captures of the *same* argument (two syntactic occurrences, or one type
    /// reaching a variable along two propagation paths) carry distinct
    /// `Infer` uids and compare unequal under derived `==` even though they
    /// denote the same term. The closure bridge uses this as its last check
    /// before declaring two morphisms genuinely different: conflating two
    /// same-written, differently-slotted captures is sound wherever the
    /// alternative was refusing to bridge at all. (Caveat, accepted: two
    /// same-named binders from *different* scopes meeting at one variable
    /// would also compare equal here; predicates resolve names lexically at
    /// their introduction site, so this requires two distinct dependent
    /// functions with colliding argument spellings meeting at one position —
    /// the extent-join territory that O1/O4 owns anyway.)
    pub fn eq_modulo_ty_slots(&self, other: &Subst) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .zip(other.0.iter())
                .all(|((ka, va), (kb, vb))| {
                    ka == kb
                        && match (va, vb) {
                            (Mapping::Rename(a), Mapping::Rename(b)) => a == b,
                            (Mapping::Discharge(a), Mapping::Discharge(b)) => {
                                crate::ccl::eq_refinement_predicate(a, b)
                            }
                            _ => false,
                        }
                })
    }

    /// True if any binder of `self`'s *range* (the replacement terms) contains a
    /// free `name` — i.e. substituting under a binder `name` would capture.
    fn range_mentions(&self, name: &Name) -> bool {
        self.0.values().any(|m| match m {
            Mapping::Rename(to) => to == name,
            Mapping::Discharge(t) => is_free(name, t),
        })
    }

    /// Compose two morphisms: `then(a, b)` is "apply `a`, then `b`" — the
    /// function `(a;b)(t) = b(a(t))`. The composite records its action on every
    /// binder either map touches (so intermediate correspondence binders are
    /// faithfully carried; design §3.6 "force before combine").
    pub fn then(a: &Subst, b: &Subst) -> Subst {
        if a.is_id() {
            return b.clone();
        }
        if b.is_id() {
            return a.clone();
        }
        let mut keys: BTreeSet<Binder> = a.0.keys().cloned().collect();
        keys.extend(b.0.keys().cloned());
        let mut m = BTreeMap::new();
        for k in keys {
            // Species composes from the INPUT species, never from the shape
            // of the composed term — one-way-ness is contagious. Rename∘Rename
            // is a rename; a discharge anywhere in the chain (including a
            // rename whose target `b` discharges) makes the composite a
            // discharge, even if the composed term happens to be a bare
            // variable.
            let composed = match a.0.get(&k) {
                Some(Mapping::Rename(to)) => match b.0.get(to) {
                    Some(mb) => mb.clone(),
                    None => Mapping::Rename(to.clone()),
                },
                Some(Mapping::Discharge(t)) => Mapping::Discharge(Box::new(b.apply_expr(t))),
                None => match b.0.get(&k) {
                    Some(mb) => mb.clone(),
                    None => continue,
                },
            };
            // Drop entries that resolve back to the identity on `k` — for
            // either species: `[x ↦ x]` substitutes a variable for itself.
            let is_identity = match &composed {
                Mapping::Rename(to) => *to == k,
                Mapping::Discharge(t) => is_var_named(t, &k),
            };
            if !is_identity {
                m.insert(k, composed);
            }
        }
        Subst(m)
    }

    /// Extend this substitution with a fresh binder correspondence `k ↦ x`
    /// (the Pi-vs-Pi binder alignment derived in the codomain edge). `k` is a
    /// newly-scoped binder, so this is an insert, not a composition.
    pub fn extended_rename(&self, k: impl Into<Name>, x: impl Into<Name>) -> Subst {
        let mut m = self.0.clone();
        m.insert(k.into(), Mapping::Rename(x.into()));
        Subst(m)
    }

    /// The **licensed correspondence view** of this substitution: every
    /// `Rename` entry kept, and every discharge whose argument is a bare
    /// variable reference (`[x ↦ k0]`, the dependent application at a
    /// variable) *read as if* it were a correspondence into the outer scope.
    /// Non-variable discharges are unchanged.
    ///
    /// This view is the **only** place a discharge's species is overridden,
    /// and it exists for exactly one consumer: the closure bridge, when
    /// reconciling two holder views of one variable. The reading is a license
    /// with two terms, both currently held by **monomorphic determinism**
    /// (every inference variable inhabits one fiber) and both expiring at the
    /// polymorphism boundary (O1/O4/O2):
    /// 1. Inverting `[x ↦ k0]` is fiber→family *generalization* — re-stating
    ///    a fact about the fiber at `k0` over the open binder `x`. Sound only
    ///    while the family is inhabited at exactly one index.
    /// 2. `k0` is a program variable, not a globally fresh correspondence
    ///    binder, so the inverse rewrites *incidental* free occurrences of
    ///    `k0` along with fiber-index ones; the two roles coincide under the
    ///    same monomorphic license.
    ///
    /// When polymorphic fibers land, delete this view: the bridge then sees
    /// the honest `Discharge` species and its tripwire reports exactly the
    /// sites that demanded the no-longer-licensed transport. The retirement
    /// plan — observability probes first, then γ\[σ\] suspensions-on-uses for
    /// first-class dependent functions — is tracked in the vault issue
    /// `type-checker-first-class-dependent-functions`.
    pub fn licensed_correspondence_view(&self) -> Subst {
        let m = self
            .0
            .iter()
            .map(|(k, v)| {
                let v = match v {
                    Mapping::Discharge(t) => match &t.node {
                        TypedExprNode::Var(n) => Mapping::Rename(n.clone()),
                        _ => v.clone(),
                    },
                    Mapping::Rename(_) => v.clone(),
                };
                (k.clone(), v)
            })
            .collect();
        Subst(m)
    }

    /// Invert a **rename** (every entry a [`Mapping::Rename`], distinct
    /// targets). Returns `None` if any entry is a discharge or the map is not
    /// injective — the discipline that keeps only renames on bidirectional
    /// edges (§3.6). Exact by construction: the variant carries the species,
    /// so no target-shape inspection is involved.
    ///
    /// There is deliberately no invert-or-fall-back-to-identity convenience:
    /// the identity fallback is exact when *rendering* a bound's content in
    /// the holder's frame (post-discharge content cannot mention the
    /// discharged binder), but silently destroys the discharge when
    /// *transporting* bounds across an edge — and one lenient helper serving
    /// both roles cannot tell them apart. Rendering applies the fallback
    /// explicitly at its call sites ([`crate::ccl::Bound::render_subst`]);
    /// transport never inverts a discharge — the closure bridge panics on the
    /// unbridgeable corner instead.
    pub fn invert(&self) -> Option<Subst> {
        let mut m = BTreeMap::new();
        let mut seen = BTreeSet::new();
        for (k, v) in &self.0 {
            let Mapping::Rename(to) = v else {
                return None; // a discharge has no inverse
            };
            if !seen.insert(to.clone()) {
                return None; // not injective
            }
            m.insert(to.clone(), Mapping::Rename(k.clone()));
        }
        Some(Subst(m))
    }

    /// Apply this substitution to a **term**. Capture-avoiding: it shadows the
    /// binder of any lambda / `let` / loop / match-arm it descends under.
    /// The traversal is **uniform over terms and types**: each node's type
    /// slots (`expr.ty`, `user_annotation`, a `Cast`'s `target`) are rewritten
    /// by [`Self::apply_type`] in the same pass, so a substituted binder
    /// occurring inside a type-borne refinement predicate is discharged right
    /// here rather than left dangling for the §6.2 scope-validity check to
    /// catch. (That check accordingly demotes to a debug assert — see
    /// `check_scope_valid`.)
    pub fn apply_expr(&self, e: &TypedExpr) -> TypedExpr {
        if self.is_id() {
            return e.clone();
        }
        // No-op short-circuit: if none of the substituted binders occur free
        // in `e` — value or type slots — the substitution does nothing here.
        // The common case (a vacuous discharge `[x ↦ arg]` from a
        // non-dependent application, `x` not occurring in `e`) takes this
        // path, which is what keeps vacuous transport from copying terms or
        // rebuilding predicate terms into fresh `Rc`s.
        if !self.0.keys().any(|k| is_free(k, e)) {
            return e.clone();
        }
        self.apply_expr_inner(e)
    }

    fn apply_expr_inner(&self, e: &TypedExpr) -> TypedExpr {
        use TypedExprNode::*;
        let node = match &e.node {
            Var(n) => match self.0.get(n) {
                // The replacement carries its own type/annotation, so return it
                // wholesale rather than rebuilding `e`.
                Some(repl) => return repl.as_expr(),
                None => Var(n.clone()),
            },

            // The cast target is a type slot `map_children` cannot reach;
            // its refinement predicate is a primary anchor.
            Cast { value, target } => Cast {
                value: Box::new(self.apply_expr(value)),
                target: self.apply_type(target),
            },

            // The target name is a *use* of the defer-handle binder (these
            // nodes exist only pre-desugar; transport runs during inference,
            // but the uniform engine handles them for the pre-inference
            // ports). A var-shaped mapping renames the handle; a discharge
            // to a non-variable term has no Feed/Define shape to land in, so
            // the stale handle is kept for desugar's own
            // `UnboundDeferHandle` boundary to report (feeding a lambda
            // parameter is user-reachable: `lambda d, v: d << v`).
            Feed { name, value } => {
                let (name, value) = self.apply_handle_use(name, value);
                Feed { name, value }
            }
            Define { name, value } => {
                let (name, value) = self.apply_handle_use(name, value);
                Define { name, value }
            }
            // The write target is a use of the mutable variable's binding,
            // renamed exactly like a Feed target (a discharge to a
            // non-variable term keeps the stale name for the phase's own
            // residue checks to report).
            MutWrite { name, value } => {
                let (name, value) = self.apply_handle_use(name, value);
                MutWrite { name, value }
            }

            Lambda { param, body } => {
                // Domain refinements ride the param's *type* (a
                // `Type::Refinement`); those predicates are substituted by
                // `apply_type`, not here.
                let (param_name, inner) = self.under_binder(&param.name, body);
                let body = Box::new(inner.apply_expr(body));
                let mut param = param.clone();
                param.name = param_name;
                Lambda { param, body }
            }

            // The loop target binds only in the body; the source sees the
            // outer scope — same discipline as `Lambda`.
            For { target, iter, body } => {
                let iter = Box::new(self.apply_expr(iter));
                let (target_name, inner) = self.under_binder(&target.name, body);
                let body = Box::new(inner.apply_expr(body));
                let mut target = target.clone();
                target.name = target_name;
                For { target, iter, body }
            }

            Let {
                binding,
                bound_expr,
                body,
            } => {
                let bound_expr = Box::new(self.apply_expr(bound_expr));
                let (bind_name, inner) = self.under_binder(&binding.name, body);
                let body = Box::new(inner.apply_expr(body));
                let mut binding = binding.clone();
                binding.name = bind_name;
                Let {
                    binding,
                    bound_expr,
                    body,
                }
            }

            LetRec { bindings, body } => {
                // Mutual recursion: every group binder is in scope in every
                // binding body AND the letrec body, so all of them shadow the
                // substitution throughout the group.
                let inner = bindings
                    .iter()
                    .fold(self.clone(), |s, (b, _)| s.shadow(&b.name));
                LetRec {
                    bindings: bindings
                        .iter()
                        .map(|(b, def)| (b.clone(), inner.apply_expr(def)))
                        .collect(),
                    body: Box::new(inner.apply_expr(body)),
                }
            }

            Case {
                scrutinee,
                branches,
            } => {
                let scrutinee = scrutinee.as_ref().map(|s| Box::new(self.apply_expr(s)));
                let branches = branches
                    .iter()
                    .map(|b| {
                        // A structural pattern binds its payload name inside the
                        // branch's guard and body.
                        let inner = match &b.pattern {
                            Some(p) => self.shadow(&p.binding.name),
                            None => self.clone(),
                        };
                        Branch {
                            pattern: b.pattern.clone(),
                            guard: inner.apply_expr(&b.guard),
                            body: inner.apply_expr(&b.body),
                        }
                    })
                    .collect();
                Case {
                    scrutinee,
                    branches,
                }
            }

            // No binders introduced: recurse structurally into child terms.
            _ => {
                let mut child = e.clone();
                child.map_children(|c| self.apply_expr(&c));
                child.ty = self.apply_type(&e.ty);
                child.user_annotation = e.user_annotation.as_ref().map(|t| self.apply_type(t));
                return child;
            }
        };
        TypedExpr {
            node,
            ty: self.apply_type(&e.ty),
            user_annotation: e.user_annotation.as_ref().map(|t| self.apply_type(t)),
        }
    }

    /// Rewrite a `Feed`/`Define` handle use (see the `Feed` arm above for
    /// the non-variable-discharge rationale).
    fn apply_handle_use(&self, name: &Name, value: &TypedExpr) -> (Name, Box<TypedExpr>) {
        (self.handle_target(name), Box::new(self.apply_expr(value)))
    }

    /// The handle-rename half of [`Self::apply_handle_use`], shared with the
    /// in-place mode: rename through var-shaped mappings, keep the name on a
    /// non-variable discharge.
    fn handle_target(&self, name: &Name) -> Name {
        match self.0.get(name) {
            None => name.clone(),
            Some(Mapping::Rename(to)) => to.clone(),
            Some(Mapping::Discharge(t)) => match &t.node {
                TypedExprNode::Var(n) => n.clone(),
                _ => name.clone(),
            },
        }
    }

    /// Apply this substitution to a term **in place** — the pass-level mode
    /// (see module docs). Same traversal and shadowing rules as
    /// [`Self::apply_expr`], but refinement predicates are *rebuilt* (fresh
    /// `Rc`s) rather than mutated; `memo` re-points every occurrence that
    /// shared one predicate term at the same rebuilt term, so the rewrite is
    /// observed uniformly across the tree. `Compose` node types are recomputed from the
    /// rewritten elements (substituting a `Var` whose type was an unresolved
    /// placeholder can concretize the element types; the `Compose.ty ==
    /// Fun(first_domain, last_codomain)` invariant must follow).
    pub fn rewrite_expr(&self, e: &mut TypedExpr) {
        if self.is_id() {
            return;
        }
        self.rewrite_expr_go(e, &mut BTreeMap::new());
    }

    /// Discharge `binder ↦ term` over `e` **in place**, cloning `term` only
    /// when `binder` actually occurs free in `e`. A vacuous substitution
    /// costs one [`is_free`] walk and **no clone** — the pass-level callers
    /// (lambda elimination, defer desugaring, lowering's uncurrying)
    /// substitute into many subtrees that never mention the binder, so
    /// cloning `term` for those would be pure waste.
    pub fn discharge_in_place(e: &mut TypedExpr, binder: &Name, term: &TypedExpr) {
        if !is_free(binder, e) {
            return;
        }
        Subst::discharge(binder.clone(), term.clone()).rewrite_expr(e);
    }

    fn rewrite_expr_go(&self, e: &mut TypedExpr, memo: &mut BTreeMap<PredicateId, Rc<TypedExpr>>) {
        // Inert subtree (no substituted binder free in value or type slots):
        // leave it untouched — predicates in particular stay un-rebuilt,
        // mirroring the transport mode's `Rc`-sharing guarantee.
        if !self.0.keys().any(|k| is_free(k, e)) {
            return;
        }
        // A mapped `Var` is replaced wholesale (the replacement carries its
        // own type and annotation), so handle it before rewriting `e`'s own
        // slots. An *unmapped* `Var` falls through: its type slots may still
        // carry the substituted binder in a refinement predicate.
        if let TypedExprNode::Var(n) = &e.node
            && let Some(repl) = self.0.get(n)
        {
            *e = repl.as_expr();
            return;
        }
        self.rewrite_type_go(&mut e.ty, memo);
        if let Some(ann) = &mut e.user_annotation {
            self.rewrite_type_go(ann, memo);
        }
        match &mut e.node {
            TypedExprNode::Var(_) => {}

            TypedExprNode::Cast { value, target } => {
                self.rewrite_type_go(target, memo);
                self.rewrite_expr_go(value, memo);
            }

            TypedExprNode::Feed { name, value }
            | TypedExprNode::Define { name, value }
            | TypedExprNode::MutWrite { name, value } => {
                *name = self.handle_target(name);
                self.rewrite_expr_go(value, memo);
            }

            TypedExprNode::Lambda { param, body } => {
                // The param's domain refinement is reached through `e.ty`'s
                // `Fun` domain (rewritten above, rebuilding the predicate via
                // `memo`); only the body is under the binder here.
                self.under_binder_mut(&param.name, body, memo);
            }

            TypedExprNode::For { target, iter, body } => {
                self.rewrite_expr_go(iter, memo);
                self.under_binder_mut(&target.name, body, memo);
            }

            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                self.rewrite_expr_go(bound_expr, memo);
                self.under_binder_mut(&binding.name, body, memo);
            }

            TypedExprNode::LetRec { bindings, body } => {
                // Every group binder scopes every binding body and the letrec
                // body (mutual recursion) — shadow them all before descending
                // anywhere inside the group.
                let inner = bindings
                    .iter()
                    .fold(self.clone(), |s, (b, _)| s.shadow(&b.name));
                for (b, _) in bindings.iter() {
                    inner.assert_no_capture(&b.name);
                }
                for (_, def) in bindings.iter_mut() {
                    inner.rewrite_expr_go(def, memo);
                }
                inner.rewrite_expr_go(body, memo);
            }

            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(sc) = scrutinee {
                    self.rewrite_expr_go(sc, memo);
                }
                for b in branches.iter_mut() {
                    let inner = match &b.pattern {
                        Some(p) => self.shadow(&p.binding.name),
                        None => self.clone(),
                    };
                    if let Some(p) = &b.pattern {
                        inner.assert_no_capture(&p.binding.name);
                    }
                    inner.rewrite_expr_go(&mut b.guard, memo);
                    inner.rewrite_expr_go(&mut b.body, memo);
                }
            }

            TypedExprNode::Compose(elts) => {
                for el in elts.iter_mut() {
                    self.rewrite_expr_go(el, memo);
                }
                // Recompute the chain type from the rewritten ends, when both
                // are concrete enough to read.
                if let (Some(first), Some(last)) = (elts.first(), elts.last())
                    && let (Some(d), Some(c)) = (first.ty.domain(), last.ty.codomain())
                {
                    e.ty = Type::fun(d, c);
                }
            }

            // No binders introduced: recurse structurally into child terms.
            _ => e.walk_children_mut(|c| self.rewrite_expr_go(c, memo)),
        }
    }

    /// In-place analogue of [`Self::under_binder`]: shadow, assert
    /// no-capture, recurse into the binder's scope.
    fn under_binder_mut(
        &self,
        binder: &Name,
        body: &mut TypedExpr,
        memo: &mut BTreeMap<PredicateId, Rc<TypedExpr>>,
    ) {
        let restricted = self.shadow(binder);
        if !restricted.0.keys().any(|k| is_free(k, body)) {
            return;
        }
        restricted.assert_no_capture(binder);
        restricted.rewrite_expr_go(body, memo);
    }

    /// The Barendregt no-capture invariant at a binder crossing (see
    /// [`Self::under_binder`] for why capture is impossible by convention).
    fn assert_no_capture(&self, binder: &Name) {
        assert!(
            !self.range_mentions(binder),
            "Barendregt violation: substitution range mentions binder `{binder:?}` it passes \
             under — a fresh uid was minted outside lowering, or a copy broke uid preservation"
        );
    }

    /// In-place analogue of [`Self::apply_type`]: rewrite the term binders in
    /// `ty`'s refinement predicates by rebuilding each predicate as a fresh
    /// `Rc`. `memo` re-points every occurrence that shared one predicate term
    /// at the same rebuilt term (see [`Self::rewrite_expr`]).
    pub fn rewrite_type(&self, ty: &mut Type) {
        if self.is_id() {
            return;
        }
        self.rewrite_type_go(ty, &mut BTreeMap::new());
    }

    fn rewrite_type_go(&self, ty: &mut Type, memo: &mut BTreeMap<PredicateId, Rc<TypedExpr>>) {
        match ty {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Txn
            | Type::Hole
            | Type::Infer(_) => {}

            // A transient defer `Feed` (present only pre-desugar): rewrite into
            // its payload.
            Type::Feed(payload) => self.rewrite_type_go(payload, memo),

            // A transient `Mut` (present only pre-unified-phase): rewrite both
            // children in place, like `Feed`'s payload.
            Type::Mut { value, domain } => {
                self.rewrite_type_go(value, memo);
                self.rewrite_type_go(domain, memo);
            }

            Type::Fun {
                name: None,
                domain,
                codomain,
            } => {
                self.rewrite_type_go(domain, memo);
                self.rewrite_type_go(codomain, memo);
            }

            Type::Fun {
                name: Some(b),
                domain,
                codomain,
            } => {
                self.rewrite_type_go(domain, memo);
                let restricted = self.shadow(b);
                restricted.assert_no_capture(b);
                restricted.rewrite_type_go(codomain, memo);
            }

            Type::Refinement(base, r) => {
                let original = r.predicate_id();
                if let Some(rebuilt) = memo.get(&original) {
                    r.predicate = Rc::clone(rebuilt);
                } else {
                    // The refinement implicitly binds REFINEMENT_BINDER in
                    // its bare predicate, so rewrite under that binder.
                    let mut pred = (*r.predicate).clone();
                    self.shadow(&Name::elem()).rewrite_expr_go(&mut pred, memo);
                    let rebuilt = Rc::new(pred);
                    memo.insert(original, Rc::clone(&rebuilt));
                    r.predicate = rebuilt;
                }
                self.rewrite_type_go(base, memo);
            }

            Type::Tuple(ts) => ts.iter_mut().for_each(|t| self.rewrite_type_go(t, memo)),
            Type::Record(fs) => fs
                .iter_mut()
                .for_each(|(_, t)| self.rewrite_type_go(t, memo)),
            Type::Variant(tags) => tags
                .iter_mut()
                .for_each(|(_, t)| self.rewrite_type_go(t, memo)),
        }
    }

    /// Restrict this substitution so it does not act on `binder`. Returns the
    /// binder name to install and the substitution to use inside its scope.
    ///
    /// Capture cannot happen: under the Barendregt convention nothing free in
    /// a substitution's range can collide with a binder bound inside the
    /// target term (binder uids are minted once at lowering; copies preserve
    /// them, so a range name and an inner binder are the same `Name` only if
    /// they are the same binder — and a binder's scope cannot nest inside
    /// itself). The α-rename fallback is therefore asserted unreachable,
    /// which is also what deletes the same-discharge-twice determinism
    /// hazard: no fresh names are minted on any equality-mediated path.
    fn under_binder(&self, binder: &Name, body: &TypedExpr) -> (Binder, Subst) {
        let restricted = self.shadow(binder);
        // If no substituted binder occurs free in the body, the substitution
        // is inert there — return the identity so the body is left untouched.
        if !restricted.0.keys().any(|k| is_free(k, body)) {
            return (binder.clone(), Subst::id());
        }
        restricted.assert_no_capture(binder);
        (binder.clone(), restricted)
    }

    /// Rewrite a refinement's predicate by this substitution. A no-op clone
    /// under the identity.
    ///
    /// Refinements compare by *structural predicate equality*, so the same
    /// discharge applied in two places — the solver's coalesce walk and the
    /// post-inference check's reconstruction — rewrites the predicate to the
    /// same term and the resulting refinements compare equal, letting the
    /// check's reconcile pass. Two *different* discharges of one polymorphic
    /// refinement — `g(0)` vs `g(1)` — rewrite to structurally distinct
    /// predicates and stay distinguished for the same reason (O4).
    pub fn force_refinement(&self, r: &crate::ccl::Refinement) -> crate::ccl::Refinement {
        if self.is_id() {
            return r.clone();
        }
        // The refinement is a binding form for the implicit REFINEMENT_BINDER,
        // so the substitution acts *under* that binder: shadow it (drop it from
        // the domain) before rewriting the predicate. Unlike an ordinary binder
        // it is never α-renamed — every refinement shares the one global name,
        // and a predicate only ever references its *own* element through it, so
        // there is no capture to avoid.
        let restricted = self.shadow(&Name::elem());
        // Vacuous (no substituted binder occurs free anywhere in the
        // predicate — value or nested type slots): keep the original
        // refinement, *sharing its predicate `Rc`*. The shared `Rc` is what
        // keeps a vacuously-transported refinement pointer-equal to its
        // source, so the `PartialEq` fast path and any downstream identity
        // dedup still see one predicate.
        if !restricted.0.keys().any(|k| is_free(k, &r.predicate)) {
            return r.clone();
        }
        let new_pred = restricted.apply_expr(&r.predicate);
        // Scope-validity (design §6.2): a discharged binder must not survive
        // in the rewritten predicate — once `[x ↦ arg]` fires, no free `x`
        // may remain, or a downstream pass would observe a dangling
        // reference. (Only `Discharge` entries are checked: a rename
        // legitimately *introduces* its target.) In a correct implementation
        // this never fires; it is the per-rewrite regression guard for
        // substitution-descent bugs, backing the end-of-inference
        // `check_scope_valid` debug walk.
        #[cfg(debug_assertions)]
        for (b, m) in &self.0 {
            if matches!(m, Mapping::Discharge(_)) {
                debug_assert!(
                    !is_free(b, &new_pred),
                    "discharged binder `{b}` still free after substitution into predicate",
                );
            }
        }
        let mut r2 = r.clone();
        r2.predicate = Rc::new(new_pred);
        r2
    }

    /// This substitution with `binder` removed from its source domain (the
    /// binder shadows the outer mapping inside its scope).
    pub fn shadow(&self, binder: &Name) -> Subst {
        if !self.0.contains_key(binder) {
            return self.clone();
        }
        let mut m = self.0.clone();
        m.remove(binder);
        Subst(m)
    }

    /// Apply this substitution to a **type**, rewriting the term binders that
    /// appear inside refinement predicates. Descends into `Fun` codomains
    /// (shadowing the Pi binder) and refinement predicates. Leaves atoms and
    /// type *variables* untouched — a term substitution never relabels
    /// `Infer`/`Hole` slots; those belong to freshening.
    pub fn apply_type(&self, ty: &Type) -> Type {
        if self.is_id() {
            return ty.clone();
        }
        self.apply_type_inner(ty)
    }

    fn apply_type_inner(&self, ty: &Type) -> Type {
        match ty {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Txn
            | Type::Hole
            | Type::Infer(_) => ty.clone(),

            Type::Fun {
                name: None,
                domain,
                codomain,
            } => Type::Fun {
                name: None,
                domain: Box::new(self.apply_type(domain)),
                codomain: Box::new(self.apply_type(codomain)),
            },

            Type::Fun {
                name: Some(b),
                domain,
                codomain,
            } => {
                let domain = Box::new(self.apply_type(domain));
                let (b2, inner) = self.under_binder_ty(b, codomain);
                Type::Fun {
                    name: Some(b2),
                    domain,
                    codomain: Box::new(inner),
                }
            }

            Type::Refinement(base, r) => {
                // The refinement implicitly binds REFINEMENT_BINDER in its bare
                // predicate; `force_refinement` shadows it before rewriting.
                // Substituting the predicate changes its meaning, so it builds a
                // fresh predicate `Rc` rather than sharing the original's.
                Type::Refinement(Box::new(self.apply_type(base)), self.force_refinement(r))
            }

            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.apply_type(t)).collect()),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), self.apply_type(t)))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.apply_type(t)))
                    .collect(),
            ),
            Type::Feed(payload) => Type::Feed(Box::new(self.apply_type(payload))),
            Type::Mut { value, domain } => Type::Mut {
                value: Box::new(self.apply_type(value)),
                domain: Box::new(self.apply_type(domain)),
            },
        }
    }

    /// `Fun`-codomain analogue of [`under_binder`](Self::under_binder):
    /// shadow the Pi binder in `codomain`. Capture is asserted unreachable
    /// for the same reason (see `under_binder`); this is what retires the
    /// spurious α-renames PR #233 observed at this site.
    fn under_binder_ty(&self, binder: &Name, codomain: &Type) -> (Binder, Type) {
        let restricted = self.shadow(binder);
        restricted.assert_no_capture(binder);
        (binder.clone(), restricted.apply_type(codomain))
    }
}

/// Is `e` exactly the variable `name` (a bare `Var(name)`)?
fn is_var_named(e: &TypedExpr, name: &Name) -> bool {
    matches!(&e.node, TypedExprNode::Var(n) if n == name)
}

// ---- contexts: the *checking* device (free vars ⊆ context) ----

/// Collect the free term-variable names of `ty` — the term binders its
/// refinement predicates reference, minus any bound by an enclosing Pi binder
/// or by a binder inside the predicates themselves.
///
/// One scope-aware accumulating walk: it threads the set of in-scope binders
/// (so it subtracts shadowing binders as it descends) and a visited-set of
/// [`PredicateId`]s (so self-referential predicate type slots terminate),
/// gathering every free variable in a single pass. This is the accumulating
/// dual of [`crate::ccl::ccl_utils::count_free`]'s by-name query — O(n) in the
/// type/predicate size, where the old "collect every name, then re-run a
/// by-name occurrence walk per name" was O(n²).
pub fn type_free_vars(ty: &Type) -> BTreeSet<Binder> {
    let mut out = BTreeSet::new();
    let mut bound = BTreeSet::new();
    let mut visited = BTreeSet::new();
    collect_type_fv(ty, &mut bound, &mut visited, &mut out);
    out
}

/// Insert each of `names` into `bound` for the duration of `f`, restoring the
/// set afterward. Only names that were *newly* inserted are removed, so a
/// binder that shadows an already-in-scope name of the same spelling does not
/// spuriously un-bind the outer one on the way back up.
fn with_binders<R>(
    bound: &mut BTreeSet<Binder>,
    names: impl IntoIterator<Item = Binder>,
    f: impl FnOnce(&mut BTreeSet<Binder>) -> R,
) -> R {
    let added: Vec<Binder> = names
        .into_iter()
        .filter(|n| bound.insert(n.clone()))
        .collect();
    let r = f(bound);
    for n in added {
        bound.remove(&n);
    }
    r
}

fn collect_type_fv(
    ty: &Type,
    bound: &mut BTreeSet<Binder>,
    visited: &mut BTreeSet<PredicateId>,
    out: &mut BTreeSet<Binder>,
) {
    match ty {
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::Txn
        | Type::Hole
        | Type::Infer(_) => {}
        Type::Fun {
            name,
            domain,
            codomain,
        } => {
            collect_type_fv(domain, bound, visited, out);
            // A `Some` name is the Pi binder, bound in the codomain.
            with_binders(bound, name.clone(), |bnd| {
                collect_type_fv(codomain, bnd, visited, out)
            });
        }
        Type::Refinement(base, r) => {
            // Walk each predicate term at most once (a term shared by `Rc`
            // across occurrences is a DAG — dedup, not cycle-breaking). The
            // refinement binds the implicit REFINEMENT_BINDER over `base`, so it
            // is bound — not free — inside the predicate.
            if visited.insert(r.predicate_id()) {
                with_binders(bound, [Name::elem()], |bnd| {
                    collect_expr_fv(&r.predicate, bnd, visited, out)
                });
            }
            collect_type_fv(base, bound, visited, out);
        }
        Type::Tuple(ts) => ts
            .iter()
            .for_each(|t| collect_type_fv(t, bound, visited, out)),
        Type::Record(fs) => fs
            .iter()
            .for_each(|(_, t)| collect_type_fv(t, bound, visited, out)),
        Type::Variant(tags) => tags
            .iter()
            .for_each(|(_, t)| collect_type_fv(t, bound, visited, out)),
        Type::Feed(payload) => collect_type_fv(payload, bound, visited, out),
        Type::Mut { value, domain } => {
            collect_type_fv(value, bound, visited, out);
            collect_type_fv(domain, bound, visited, out);
        }
    }
}

/// Collect the free term-variable names of an expression, respecting the
/// binders introduced by lambdas / `let`s / loops / match arms (mirrors the
/// shadowing rules of [`crate::ccl::ccl_utils::count_free`]). Also descends
/// into each sub-expression's type slot, since predicate sub-terms may carry
/// further refinements.
fn collect_expr_fv(
    e: &TypedExpr,
    bound: &mut BTreeSet<Binder>,
    visited: &mut BTreeSet<PredicateId>,
    out: &mut BTreeSet<Binder>,
) {
    collect_type_fv(&e.ty, bound, visited, out);
    match &e.node {
        TypedExprNode::Var(n) => {
            if !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        TypedExprNode::Lambda { param, body } => {
            with_binders(bound, [param.name.clone()], |bnd| {
                collect_expr_fv(body, bnd, visited, out)
            });
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_expr_fv(bound_expr, bound, visited, out);
            with_binders(bound, [binding.name.clone()], |bnd| {
                collect_expr_fv(body, bnd, visited, out)
            });
        }
        // Mutual recursion: every group binder is bound in every binding
        // body and in the letrec body.
        TypedExprNode::LetRec { bindings, body } => {
            with_binders(bound, bindings.iter().map(|(b, _)| b.name.clone()), |bnd| {
                for (_, def) in bindings {
                    collect_expr_fv(def, bnd, visited, out);
                }
                collect_expr_fv(body, bnd, visited, out);
            });
        }
        // The `name` of Feed/Define/MutWrite is a *use* of the defer handle
        // / mutable variable.
        TypedExprNode::Feed { name, value }
        | TypedExprNode::Define { name, value }
        | TypedExprNode::MutWrite { name, value } => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
            collect_expr_fv(value, bound, visited, out);
        }
        // The loop target binds only in the body.
        TypedExprNode::For { target, iter, body } => {
            collect_expr_fv(iter, bound, visited, out);
            with_binders(bound, [target.name.clone()], |bnd| {
                collect_expr_fv(body, bnd, visited, out);
            });
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_expr_fv(s, bound, visited, out);
            }
            for b in branches {
                let payload = b.pattern.iter().map(|p| p.binding.name.clone());
                with_binders(bound, payload, |bnd| {
                    collect_expr_fv(&b.guard, bnd, visited, out);
                    collect_expr_fv(&b.body, bnd, visited, out);
                });
            }
        }
        // No binders introduced: recurse structurally into child terms.
        _ => e.walk_children(|c| collect_expr_fv(c, bound, visited, out)),
    }
}

/// A type is well-formed in context `ctx` iff every free term variable of its
/// refinement predicates is bound there. The scope-validity assertion of the
/// proposal (§6.2) is exactly this check.
pub fn well_formed(ty: &Type, ctx: &BTreeSet<Binder>) -> bool {
    type_free_vars(ty).is_subset(ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BinOpKind, CompareKind, Lit, Refinement};

    fn var(s: &str) -> TypedExpr {
        TypedExpr::var(s)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    /// `l > r`
    fn gt(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Compare(CompareKind::Greater), r)
    }

    // A — identity laws + associativity + action on the source context.
    #[test]
    fn scenario_a_laws() {
        let sigma = Subst::rename("k", "x");
        assert_eq!(Subst::then(&Subst::id(), &sigma), sigma);
        assert_eq!(Subst::then(&sigma, &Subst::id()), sigma);

        let a = Subst::rename("k", "x");
        let b = Subst::rename("x", "z");
        let c = Subst::discharge("z", int(5));
        let abc = Subst::then(&Subst::then(&a, &b), &c);
        let abc2 = Subst::then(&a, &Subst::then(&b, &c));
        assert_eq!(abc, abc2); // associative
        // [k↦x];[x↦z];[z↦5] sends k ↦ 5
        assert_eq!(abc.apply_expr(&var("k")), int(5));
    }

    // The identity substitution is a perfect structural no-op.
    #[test]
    fn identity_is_noop() {
        let id = Subst::id();
        let exprs = [var("k"), int(3), gt(var("y"), var("k"))];
        for e in &exprs {
            assert_eq!(&id.apply_expr(e), e);
        }
        let tys = [
            Type::fun(Type::infer(), Type::infer()),
            Type::pi("k", Type::infer(), Type::infer()),
        ];
        for t in &tys {
            assert_eq!(&id.apply_type(t), t);
        }
    }

    // B — invert a rename and round-trip on a source-context term.
    #[test]
    fn scenario_b_invert() {
        let sigma = Subst::rename("k", "x");
        let sinv = sigma.invert().expect("rename invertible");
        assert_eq!(sinv, Subst::rename("x", "k"));
        let pred = gt(var("y"), var("k"));
        let there = sigma.apply_expr(&pred);
        assert_eq!(sinv.apply_expr(&there), pred); // round-trip
    }

    // E — discharges (and composites containing one) are not invertible.
    #[test]
    fn scenario_e_discharge_not_invertible() {
        let dis = Subst::discharge("x", int(5));
        assert!(dis.invert().is_none());
        let sigma = Subst::rename("k", "x");
        assert!(Subst::then(&sigma, &dis).invert().is_none());
    }

    // The value-only contract is retired: a binder occurring only in a *type
    // slot's* refinement predicate is in contract — transport discharges it
    // and rebuilds the changed predicate as a fresh `Rc`, leaving no dangling
    // reference for the §6.2 walk to catch. A genuinely vacuous discharge still
    // shares the predicate term (same `Rc`).
    #[test]
    fn type_slot_occurrence_is_discharged() {
        use std::rc::Rc;
        // y : {_ | k > 0} — `k` appears only in the type slot's predicate.
        let slot_ref = Refinement {
            predicate: Rc::new(gt(var("k"), int(0))),
        };
        let e = var("y").with_ty(Type::Refinement(Box::new(Type::Hole), slot_ref.clone()));
        let dis = Subst::discharge("k", int(5));

        let out = dis.apply_expr(&e);
        let Type::Refinement(_, out_ref) = &out.ty else {
            panic!("type slot preserved");
        };
        assert_eq!(
            *out_ref.predicate,
            gt(int(5), int(0)),
            "the type-slot occurrence is discharged"
        );
        assert!(
            !Rc::ptr_eq(&out_ref.predicate, &slot_ref.predicate),
            "a changed predicate is rebuilt as a fresh `Rc`; the source context's original stays intact"
        );
        assert_eq!(*slot_ref.predicate, gt(var("k"), int(0)));

        // force_refinement on a predicate whose *sub-expression type*
        // mentions `k` is no longer vacuous: the nested slot is rewritten.
        let outer = Refinement {
            predicate: Rc::new(e),
        };
        let forced = dis.force_refinement(&outer);
        assert!(!Rc::ptr_eq(&forced.predicate, &outer.predicate));
        let forced_pred = &*forced.predicate;
        let Type::Refinement(_, nested) = &forced_pred.ty else {
            panic!("nested refinement preserved");
        };
        assert_eq!(*nested.predicate, gt(int(5), int(0)));

        // A vacuous discharge still shares the predicate term (same `Rc`).
        let vac = Subst::discharge("unrelated", int(7));
        let kept = vac.force_refinement(&outer);
        assert!(
            Rc::ptr_eq(&kept.predicate, &outer.predicate),
            "vacuous force_refinement must share the predicate term"
        );
    }

    // D — compose-into-then-apply equals apply-then-discharge.
    #[test]
    fn scenario_d_compose_equals_apply() {
        // predicate {y | y > k}, here just the bare body `y > k`.
        let pred = gt(var("y"), var("k"));
        let rename = Subst::rename("k", "x"); // [k↦x]: y>k ⇒ y>x
        let renamed = rename.apply_expr(&pred);
        assert_eq!(renamed, gt(var("y"), var("x")));
        let dis = Subst::discharge("x", int(5)); // [x↦5]: y>x ⇒ y>5
        let eager = dis.apply_expr(&renamed);
        let composed = Subst::then(&rename, &dis).apply_expr(&pred);
        assert_eq!(eager, gt(var("y"), int(5)));
        assert_eq!(eager, composed);
    }

    // F — the context check rejects a free `k` in [x], accepts it in [k].
    // The refinement's element binder `y` is bound by the predicate lambda
    // (as real refinement predicates are shaped), so only the outer `k` is
    // free.
    #[test]
    fn scenario_f_context_check() {
        let pred = TypedExpr::lambda("y", Type::Hole, gt(var("y"), var("k")));
        let bad = Type::Refinement(
            Box::new(Type::infer()),
            Refinement {
                predicate: Rc::new(pred),
            },
        );
        let only_x: BTreeSet<Binder> = [Name::raw("x")].into_iter().collect();
        let only_k: BTreeSet<Binder> = [Name::raw("k")].into_iter().collect();
        assert!(!well_formed(&bad, &only_x));
        assert!(well_formed(&bad, &only_k));
    }

    // G — capture is a Barendregt violation, not something to α-rename
    // around: [k↦x] passing under a binder `x` means a range name collides
    // with an inner binder, which the convention rules out (binder uids are
    // minted once at lowering; copies preserve them). The engine asserts
    // rather than minting a fresh name — minting on this path is the
    // same-discharge-twice determinism hazard.
    #[test]
    #[should_panic(expected = "Barendregt violation")]
    fn scenario_g_capture_panics() {
        // body: λ x → (x > k); apply [k ↦ x] — the raw names collide.
        let lam = TypedExpr::lambda("x", Type::Hole, gt(var("x"), var("k")));
        let _ = Subst::rename("k", "x").apply_expr(&lam);
    }

    // apply_type descends into a refinement predicate and discharges a free
    // outer binder — the dependent-application shape `g(5)`.
    #[test]
    fn apply_type_discharges_refinement_predicate() {
        let r = Refinement {
            predicate: Rc::new(gt(var("i"), var("k"))),
        };
        let ty = Type::fun(Type::Refinement(Box::new(Type::infer()), r), Type::infer());
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
        let Type::Fun { domain, .. } = &out else {
            panic!("expected fun");
        };
        let Type::Refinement(_, r2) = domain.as_ref() else {
            panic!("expected refinement domain");
        };
        assert_eq!(*r2.predicate, gt(var("i"), int(5)));
    }

    // apply_type shadows a Pi binder: [k↦5] does not touch a codomain that
    // rebinds k.
    #[test]
    fn apply_type_shadows_pi_binder() {
        let r = Refinement {
            predicate: Rc::new(gt(var("i"), var("k"))),
        };
        // (k: _) ⇒ {i | i > k} ⇒ _  — the inner k is bound by the Pi.
        let inner = Type::fun(Type::Refinement(Box::new(Type::infer()), r), Type::infer());
        let ty = Type::pi("k", Type::infer(), inner);
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
        // The Pi binder shadows the discharge: predicate is unchanged.
        let Type::Fun { codomain, .. } = &out else {
            panic!()
        };
        let Type::Fun { domain, .. } = codomain.as_ref() else {
            panic!()
        };
        let Type::Refinement(_, r2) = domain.as_ref() else {
            panic!()
        };
        assert_eq!(*r2.predicate, gt(var("i"), var("k")));
    }
}

#[cfg(test)]
mod rewrite_tests {
    use super::*;
    use crate::ccl::ccl_utils::is_free;
    use crate::ccl::{BinOpKind, CompareKind, Lit, Refinement};
    use std::rc::Rc;

    fn var(s: &str) -> TypedExpr {
        TypedExpr::var(s)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    fn gt(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Compare(CompareKind::Greater), r)
    }

    // In-place mode *rebuilds* each predicate as a fresh `Rc` (predicates are
    // immutable). A predicate term shared across two occurrences within the
    // rewritten tree is rebuilt once and both occurrences are re-pointed at the
    // same new term (the `memo`).
    #[test]
    fn rewrite_rebuilds_and_repoints_shared_predicates() {
        let shared = Rc::new(gt(var("k"), int(0)));
        // Two refinement occurrences sharing one predicate term, both inside a
        // single type (a function's domain and codomain).
        let dom = Type::Refinement(
            Box::new(Type::Hole),
            Refinement {
                predicate: Rc::clone(&shared),
            },
        );
        let cod = Type::Refinement(
            Box::new(Type::Hole),
            Refinement {
                predicate: Rc::clone(&shared),
            },
        );
        let mut e = var("y").with_ty(Type::fun(dom, cod));

        Subst::discharge("k", int(5)).rewrite_expr(&mut e);

        let Type::Fun {
            domain, codomain, ..
        } = &e.ty
        else {
            panic!("function type preserved");
        };
        let Type::Refinement(_, rd) = domain.as_ref() else {
            panic!("domain refinement preserved");
        };
        let Type::Refinement(_, rc) = codomain.as_ref() else {
            panic!("codomain refinement preserved");
        };
        assert_eq!(
            *rd.predicate,
            gt(int(5), int(0)),
            "the predicate is rebuilt with the discharge applied"
        );
        assert!(
            !Rc::ptr_eq(&rd.predicate, &shared),
            "a rewritten predicate is a fresh Rc, not the original"
        );
        assert!(
            Rc::ptr_eq(&rd.predicate, &rc.predicate),
            "both occurrences that shared one term are re-pointed at one rebuild"
        );
    }

    // The same binder bound again inside the tree (a copy — inlining
    // duplicates lambdas with their uids) shadows the substitution.
    #[test]
    fn rewrite_respects_shadowing_copies() {
        let a = Name::fresh("a");
        let inner = TypedExpr::lambda(a.clone(), Type::Hole, gt(var("x"), int(0)));
        let mut e = TypedExpr::apply(
            TypedExpr::var(a.clone()),
            TypedExpr::lambda("w", Type::Hole, inner),
        );
        Subst::discharge(a.clone(), int(3)).rewrite_expr(&mut e);
        let TypedExprNode::Apply { function, argument } = &e.node else {
            panic!("apply preserved");
        };
        assert_eq!(argument.node, TypedExprNode::Lit(Lit::Int(3)));
        let TypedExprNode::Lambda { body, .. } = &function.node else {
            panic!("outer lambda preserved");
        };
        let TypedExprNode::Lambda { param, .. } = &body.node else {
            panic!("inner lambda preserved");
        };
        assert_eq!(param.name, a, "the copied binding site is untouched");
        assert!(!is_free(&a, &e), "no free occurrence survives");
    }

    // A LetRec group binder shadows the substitution across *every* binding
    // body and the letrec body — a copied group re-binding the discharged
    // name (inlining duplicates subtrees with their uids) must keep all of
    // its internal references pointing at the group binder.
    #[test]
    fn rewrite_respects_letrec_group_shadowing() {
        use crate::ccl::TypedBinding;
        let x = Name::fresh("x");
        // letrec x = x + 1; y = x in x   (all references are the group's x)
        let letrec = TypedExpr::letrec(
            vec![
                (
                    TypedBinding::new_unannotated(x.clone()),
                    gt(TypedExpr::var(x.clone()), int(1)),
                ),
                (
                    TypedBinding::new_unannotated(Name::fresh("y")),
                    TypedExpr::var(x.clone()),
                ),
            ],
            TypedExpr::var(x.clone()),
        );
        let mut shadowed = letrec.clone();
        Subst::discharge(x.clone(), int(3)).rewrite_expr(&mut shadowed);
        assert_eq!(
            shadowed, letrec,
            "a group binder matching the discharged name blocks the \
             substitution throughout the group"
        );

        // Control: with no matching group binder, free occurrences in every
        // binding body and the letrec body are substituted.
        let z = Name::fresh("z");
        let mut open = TypedExpr::letrec(
            vec![(
                TypedBinding::new_unannotated(z.clone()),
                gt(TypedExpr::var(x.clone()), int(0)),
            )],
            TypedExpr::var(x.clone()),
        );
        Subst::discharge(x.clone(), int(3)).rewrite_expr(&mut open);
        assert!(!is_free(&x, &open), "free occurrences are discharged");
    }

    // Feed/Define handles rename through var-shaped mappings and survive a
    // non-variable discharge for desugar's own boundary to diagnose.
    #[test]
    fn rewrite_renames_feed_handles() {
        let mut e = TypedExpr::feed("d", var("d"));
        Subst::rename("d", "q").rewrite_expr(&mut e);
        let TypedExprNode::Feed { name, value } = &e.node else {
            panic!("feed preserved");
        };
        assert_eq!(name, &Name::raw("q"));
        assert_eq!(value.node, TypedExprNode::Var(Name::raw("q")));

        let mut stale = TypedExpr::feed("d", int(1));
        Subst::discharge("d", int(2)).rewrite_expr(&mut stale);
        let TypedExprNode::Feed { name, .. } = &stale.node else {
            panic!("feed preserved");
        };
        assert_eq!(
            name,
            &Name::raw("d"),
            "a non-variable discharge keeps the handle for UnboundDeferHandle to report"
        );
    }
}

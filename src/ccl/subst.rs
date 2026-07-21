//! Capture-avoiding substitutions over term binders — the context-morphism
//! machinery for dependent refinements (Pi types).
//!
//! This is the load-bearing distinction from the internal design proposal
//! for dependent refinements via Pi types (§3.5) and its executable
//! substitution-prototype model:
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
//!   uncurrying). A predicate the substitution actually touches is rebuilt as a
//!   fresh `Rc`; one it doesn't — no substituted binder free in it — keeps its
//!   `Rc`, exactly as transport mode does.
//!
//! Both modes share the same discipline: a
//! [`PredMemo`](crate::ccl::ccl_utils::PredMemo) re-points every occurrence that
//! shared one predicate term at the *same* result, so one rewrite is observed
//! uniformly across the aliases and occurrences that entered sharing one `Rc` leave
//! sharing one `Rc`. Its context (`C`) is **the active substitution**: an entry is
//! reused only for an occurrence under the same one, so a rebuild made outside a
//! scope that rebinds a substituted variable is never served to an occurrence
//! inside it. That is what makes threading a single memo across binder crossings
//! correct — acting differently in different scopes is the whole job of a
//! substitution, so scope cannot be left out of the key.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ccl::ccl_utils::{PredMemo, is_free, strip_iterate_markers};
use crate::ccl::provenance::NodeId;
use crate::ccl::scope::{
    ScopedItem, ScopedItemMut, for_each_scoped_item, for_each_scoped_item_mut,
};
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

/// A substitution must never leave a **typed** occurrence holding an untyped
/// replacement.
///
/// Every term a substitution fabricates goes through
/// [`Mapping::as_expr`]/[`as_expr_preserving`](Mapping::as_expr_preserving), so this is
/// the one boundary that owns the invariant. It is load-bearing rather than tidy: a
/// substitution fires *inside refinement predicates*, and a predicate's interior is
/// outside the walk that resolves node types — so an untyped node introduced here is
/// never typed by anything downstream, and surfaces at the post-inference wall as an
/// unresolved variable with no way to recover the type except a lexical-scope guess.
///
/// A hard `assert!`, not a `debug_assert!`: it is O(1) on a path that would otherwise
/// silently produce a type nothing can reconstruct. An *untyped* occurrence carries no
/// obligation — substitution runs before inference too (lowering's uncurry template
/// discharge, the chained-comparison operand freshens), where every slot is `Hole`.
#[track_caller]
fn assert_preserves_typedness(replacement: &TypedExpr, occurrence_ty: &Type) {
    assert!(
        matches!(occurrence_ty, Type::Hole) || !matches!(replacement.ty, Type::Hole),
        "substitution dropped the type of a replaced occurrence: `{}` had type `{occurrence_ty}`, \
         replacement `{}` is untyped",
        crate::ccl::symbolic::symbolic(replacement),
        crate::ccl::symbolic::symbolic(replacement),
    );
}

impl Mapping {
    /// The mapping's replacement as a term (a `Rename` materializes as a bare
    /// variable reference). The replacement carries a **new** identity: a fresh
    /// mint for a `Rename`, the discharged term's own ids for a `Discharge`.
    fn as_expr(&self, occurrence_ty: &Type) -> TypedExpr {
        let out = match self {
            // α-renaming cannot change a term's type: the occurrence's type is a
            // property of the *position*, not of the name, so the replacement
            // carries it. Building a bare `TypedExpr::var` here would leave the
            // node at `Type::Hole` — and a rename fires inside refinement
            // predicates, which no later pass types, so the hole would survive to
            // the post-inference check.
            Mapping::Rename(to) => TypedExpr::var(to.clone()).with_ty(occurrence_ty.clone()),
            Mapping::Discharge(t) => (**t).clone(),
        };
        assert_preserves_typedness(&out, occurrence_ty);
        out
    }

    /// [`as_expr`](Self::as_expr) at a **preserved** root identity: the
    /// replacement root takes `node_id` — the occurrence's own id — so it
    /// inherits the use-site's span and attribution.
    ///
    /// A `Rename` is built directly at `node_id` rather than minted and then
    /// overwritten: a mint fires `on_mint`, and an id no node ends up carrying is
    /// a phantom birth in the lineage log. A `Discharge` clones (which mints
    /// nothing) and re-roots that clone
    /// ([`re_root`](TypedExpr::re_root)) — the two shapes reach a preserved
    /// identity by different routes, and neither mints.
    fn as_expr_preserving(&self, node_id: NodeId, occurrence_ty: &Type) -> TypedExpr {
        let out = match self {
            // See [`as_expr`]: the rename keeps the occurrence's type.
            Mapping::Rename(to) => TypedExpr::preserve(node_id, TypedExprNode::Var(to.clone()))
                .with_ty(occurrence_ty.clone()),
            Mapping::Discharge(t) => (**t).clone().re_root(node_id),
        };
        assert_preserves_typedness(&out, occurrence_ty);
        out
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
    /// the domain-join territory that O1/O4 owns anyway.)
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
                Some(repl) => return repl.as_expr(&e.ty),
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
            // parameter is user-reachable: `\d, v -> d << v`).
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
                let inner = self.shadow_all(bindings.iter().map(|(b, _)| &b.name));
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
                        // branch's guard and body; a guard-only branch binds
                        // nothing, which `shadow_all` handles as the empty scope.
                        let inner = self.shadow_all(b.pattern.iter().map(|p| &p.binding.name));
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
        // Through `Expr::new`, so the mint is visible to the recorder — a raw
        // `node_id: NodeId::fresh()` would give the node an identity with no
        // recorded birth, which reads downstream as a node no step produced.
        //
        // TODO(preserve): this mints where the non-binder arm above *clones*
        // (keeping `e`'s id), so transport-mode substitution changes a
        // binder-introducing node's identity but not its children's. If the
        // rebuild should be a preserve, this is `Expr::preserve(e.node_id, node)`
        // — but that changes id semantics for every dependent-refinement
        // transport, so it wants its own change.
        let mut out = TypedExpr::new(node).with_ty(self.apply_type(&e.ty));
        out.user_annotation = e.user_annotation.as_ref().map(|t| self.apply_type(t));
        out
    }

    /// Rewrite a `Feed`/`Define` handle use (see the `Feed` arm above for
    /// the non-variable-discharge rationale).
    fn apply_handle_use(&self, name: &Name, value: &TypedExpr) -> (Name, Box<TypedExpr>) {
        (self.handle_target(name), Box::new(self.apply_expr(value)))
    }

    /// The name this substitution retargets a *name position* to, or `None` when
    /// it leaves the position alone: an unmapped name, or one mapped to a
    /// non-variable term (a handle or a channel domain can only hold a name, so
    /// a compound discharge has nothing to write there — see the `Feed` arm of
    /// [`Self::apply_expr_inner`]).
    ///
    /// Distinguishing "unchanged" from "changed to the same thing" is what lets
    /// the in-place mode visit every name occurrence in the tree without a
    /// [`Name`] clone per node.
    fn retarget(&self, name: &Name) -> Option<Name> {
        match self.0.get(name)? {
            Mapping::Rename(to) => Some(to.clone()),
            Mapping::Discharge(t) => match &t.node {
                TypedExprNode::Var(n) => Some(n.clone()),
                _ => None,
            },
        }
    }

    /// The handle-rename half of [`Self::apply_handle_use`], shared with the
    /// type-slot walks: [`Self::retarget`] with the unchanged case spelled out
    /// as the original name, for the rebuilding callers that need a value.
    fn handle_target(&self, name: &Name) -> Name {
        self.retarget(name).unwrap_or_else(|| name.clone())
    }

    /// Apply this substitution to a term **in place** — the pass-level mode
    /// (see module docs). Same traversal and shadowing rules as
    /// [`Self::apply_expr`], but refinement predicates are *rebuilt* (fresh
    /// `Rc`s) rather than mutated; `memo` re-points every occurrence that
    /// shared one predicate term at the same rebuilt term, so the rewrite is
    /// observed uniformly across the tree. `Compose` node types are recomputed from the
    /// rewritten elements (substituting a `Var` whose type was an unresolved
    /// placeholder can concretize the element types; the `Compose.ty ==
    /// `Fun(first_domain, last_codomain)` invariant must follow).
    ///
    /// There is no freshen observer: a compound replacement's interior is
    /// freshened by [`TypedExpr::freshen_interior_node_ids`], whose re-mints fire
    /// the ambient `lineage::on_copy` hook directly into any open lineage step, so
    /// the caller needs no callback.
    pub fn rewrite_expr(&self, e: &mut TypedExpr) {
        if self.is_id() {
            return;
        }
        self.rewrite_expr_go(e, &PredMemo::new());
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
        Subst::discharge(binder.clone(), term.clone()).rewrite_expr_go(e, &PredMemo::new());
    }

    fn rewrite_expr_go(&self, e: &mut TypedExpr, memo: &PredMemo<Subst>) {
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
            // Root-carry: the replacement ROOT is built at the occurrence's own
            // id — a *preserve*, so the root inherits the occurrence's
            // span/attribution (the use-site), unique per occurrence by
            // construction.
            let occurrence_ty = e.ty.clone();
            *e = repl.as_expr_preserving(e.node_id, &occurrence_ty);
            if !matches!(e.node, TypedExprNode::Var(_)) {
                // Compound replacement: `as_expr_preserving` bare-`clone()`s the
                // whole subtree, sharing the source's NodeIds. Freshen only the
                // INTERIOR (the children) — the root keeps the carried id. Each
                // interior re-mint fires the ambient `on_copy` lineage hook into
                // any open step. Type slots are out of the id domain, so the
                // predicate `Rc`s the clone shares with its source stay shared.
                //
                // Freshening the root as well would work, but it re-mints an id
                // the carry immediately overwrites, so the step records a `Copy`
                // whose produced id no node ends up holding. The node survives
                // either way — only its recorded identity would be one the tree
                // never keeps — so this is about not logging an operation that is
                // undone a line later, and about spending one fewer id.
                e.freshen_interior_node_ids();
            }
            return;
        }
        // *Every* type slot the node carries, not just `ty` and the annotation: a
        // `Cast`'s `target` and each binder's declared type hold their own
        // predicate `Rc`s, so rewriting only `ty` leaves those stale against it —
        // the same defect the retype walk had. A binder's own type is in the
        // *enclosing* scope (a binder does not bind in its own type), so the
        // unrestricted substitution is the right one for it, and the binder
        // crossings below still only guard the children.
        e.walk_type_slots_mut(|ty| self.rewrite_type_go(ty, memo));

        // Capture-avoiding descent, plus the node's own name occurrences. Which
        // children a binder scopes over, and which names a node mentions of its
        // own, are not decided here — `crate::ccl::scope` is the crate's one
        // statement of CCL's binding structure, and folding over it is what
        // keeps a newly-added node from silently escaping both.
        //
        // The restriction and its Barendregt check are per *scope*, not per
        // child: the walk opens a scope once for the whole run of children it
        // covers, so a `LetRec` group of n binders pays n checks rather than
        // n * (n + 1). Each check walks every `Discharge` replacement term, so
        // per-child would be quadratic in the group's width. An ambient scope
        // needs no special case: `shadow_all` borrows and the recursive call is
        // the unrestricted one.
        //
        // Inertness is *not* pre-tested here. The recursive call opens with the
        // same test against the same substitution, so testing it here would walk
        // every child subtree twice — and returning early on it would skip the
        // Barendregt assertion, which is the tripwire for a broken
        // uid-preservation invariant and should fire wherever the binder is
        // crossed, not only where the substitution happens to be live.
        let mut scoped: Cow<'_, Subst> = Cow::Borrowed(self);
        for_each_scoped_item_mut(e, &mut |item| match item {
            ScopedItemMut::Scope(binders) => {
                scoped = self.shadow_all(binders);
                for b in binders {
                    scoped.assert_no_capture(b);
                }
            }
            ScopedItemMut::Child(child) => scoped.rewrite_expr_go(child, memo),
            // A handle node's write target is a *use* of the binder that
            // introduced it, so a var-shaped mapping retargets it. (A `Var`
            // occurrence the substitution maps never reaches here — it was
            // replaced wholesale above — and `retarget` leaves an unmapped one
            // alone without so much as a clone.)
            ScopedItemMut::VarRef(name) => {
                if let Some(to) = self.retarget(name) {
                    *name = to;
                }
            }
            // A register key is a field label, not a variable occurrence:
            // nothing a term substitution acts on.
            ScopedItemMut::KeyRef(_) => {}
        });

        // `Compose`'s type is derived from its elements, so rewriting them can
        // concretize it (substituting a `Var` whose type was a placeholder).
        if let TypedExprNode::Compose(elts) = &e.node
            && let (Some(first), Some(last)) = (elts.first(), elts.last())
            && let (Some(d), Some(c)) = (first.ty.domain(), last.ty.codomain())
        {
            e.ty = Type::fun(d, c);
        }
    }

    /// The Barendregt no-capture invariant at a binder crossing (see
    /// [`Self::under_binder`] for why capture is impossible by convention).
    fn assert_no_capture(&self, binder: &Name) {
        #[cfg(test)]
        capture_assert_probe::bump();
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
        self.rewrite_type_go(ty, &PredMemo::new());
    }

    fn rewrite_type_go(&self, ty: &mut Type, memo: &PredMemo<Subst>) {
        match ty {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Txn
            | Type::Hole
            | Type::Infer(_) => {}

            // a nominal channel domain names its defer
            // binder, so a handle rename (`x ↦ y` on beta-reduction /
            // alias-inlining) must retarget it exactly like a `Feed` target —
            // otherwise the type slot would keep naming the dead binder.
            Type::ChanDom(name, _) => *name = self.handle_target(name),

            // A transient history handle (an `Overwrite` erased by the unified phase,
            // a `Feed` by `channelize`): rewrite both children in place. Renaming
            // does not cross the kind — the value and domain are ordinary types.
            Type::History { value, domain, .. } => {
                self.rewrite_type_go(value, memo);
                self.rewrite_type_go(domain, memo);
            }

            Type::Fun {
                name: None,
                domain,
                codomain,
                ..
            } => {
                self.rewrite_type_go(domain, memo);
                self.rewrite_type_go(codomain, memo);
            }

            Type::Fun {
                name: Some(b),
                domain,
                codomain,
                ..
            } => {
                self.rewrite_type_go(domain, memo);
                let restricted = self.shadow(b);
                restricted.assert_no_capture(b);
                restricted.rewrite_type_go(codomain, memo);
            }

            Type::Refinement(base, r) => {
                // The refinement implicitly binds REFINEMENT_BINDER in its bare
                // predicate, so the substitution acts *under* that binder.
                let restricted = self.shadow(&Name::elem());
                // `restricted` is the memo's context: an entry is reused only for
                // an occurrence under the *same* active substitution, so a rebuild
                // made outside a scope that shadows a substituted binder is never
                // served to an occurrence inside it (and a vacuous decision made
                // inside is never served outside). That is what makes threading one
                // memo across binder crossings correct — see `PredMemo`.
                memo.rebuild(r, &restricted, |pred| {
                    if !restricted.0.keys().any(|k| is_free(k, pred)) {
                        // Vacuous: no substituted binder occurs free here, so report
                        // no change and keep the origin `Rc` — a predicate this
                        // substitution merely walks past stays shared with its other
                        // occurrences (mirroring `force_refinement`'s transport
                        // path). Memoizing the decision also makes this `is_free`
                        // scan run once per distinct predicate, not per occurrence.
                        return false;
                    }
                    restricted.rewrite_expr_go(pred, memo);
                    // Keep the predicate marker-free: a substituted collection may
                    // carry a term-tree `iterate` marker that must not leak into a
                    // type (see `strip_iterate_markers` and the `force_refinement`
                    // twin). Only the rewritten path needs it — a marker arrives
                    // *through* the substitution, so the vacuous path above, which
                    // rewrites nothing and keeps the origin `Rc`, has none to strip.
                    *pred = strip_iterate_markers(pred);
                    true
                });
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
        // A refinement predicate is a *denotational* term, so a substituted
        // value must not drag a term-tree `iterate` planning marker into it
        // (the §6.2 move-site discharge of a `let`-bound, iterate-marked
        // collection into a refined domain). Strip the neutral marker so the
        // predicate stays marker-free — otherwise it churns under `simplify`
        // and diverges from inference's pre-marker copy.
        let new_pred = strip_iterate_markers(&restricted.apply_expr(&r.predicate));
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
        // A substituted predicate is a genuinely new term (the transport mode
        // builds rather than rewrites), so `born` is the right spelling; the
        // vacuous case returned above kept the source's `Rc` instead.
        crate::ccl::Refinement::born(Rc::new(new_pred))
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

    /// This substitution restricted so it acts on **none** of `binders` — the
    /// whole-scope form of [`Self::shadow`], for the nodes whose binders scope
    /// over a child as a group (a `LetRec`'s mutual-recursion group, a `Case`
    /// branch's payload, an empty list for a child in the node's own scope).
    ///
    /// Returns a borrow when the restriction is vacuous, which is the common
    /// case: a substitution's domain is usually a single binder and the scope
    /// being crossed usually does not name it. Folding [`Self::shadow`] over the
    /// group instead would clone the map once per binder even on a miss, since
    /// `shadow` returns an owned `Subst`.
    ///
    /// The `contains_key` guard is what makes that true and is therefore
    /// load-bearing, not a micro-optimization: `to_mut()` on a `Cow::Borrowed`
    /// clones unconditionally, so calling it before knowing there is something to
    /// remove would allocate on every crossing and the `Cow` would buy nothing.
    pub fn shadow_all<'a>(&self, binders: impl IntoIterator<Item = &'a Name>) -> Cow<'_, Subst> {
        let mut out = Cow::Borrowed(self);
        for b in binders {
            if out.0.contains_key(b) {
                out.to_mut().0.remove(b);
            }
        }
        out
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

            // rename the named defer binder, mirroring the
            // in-place mode (`rewrite_type_go`).
            Type::ChanDom(name, lvl) => Type::ChanDom(self.handle_target(name), *lvl),

            Type::Fun {
                name: None,
                domain,
                codomain,
                ..
            } => Type::fun_like(ty, self.apply_type(domain), self.apply_type(codomain)),

            Type::Fun {
                name: Some(b),
                kind,
                domain,
                codomain,
            } => {
                let domain = Box::new(self.apply_type(domain));
                let (b2, inner) = self.under_binder_ty(b, codomain);
                Type::Fun {
                    name: Some(b2),
                    kind: kind.clone(),
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
            Type::History {
                value,
                domain,
                kind,
            } => Type::History {
                value: Box::new(self.apply_type(value)),
                domain: Box::new(self.apply_type(domain)),
                kind: *kind,
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

/// Whether `ty`'s structural skeleton contains an unresolved [`Type::Infer`]
/// leaf. This is the per-type dual of `check_fully_typed`'s whole-program scan:
/// a cheap "is this type ground" predicate for invariant assertions at pass
/// boundaries. It walks the type skeleton only — a `Refinement`'s predicate is
/// a term, not a type, and is not descended into (an `Infer` embedded in a
/// predicate cast is out of scope and would need a term walk).
pub fn type_contains_infer(ty: &Type) -> bool {
    match ty {
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole => false,
        Type::Infer(_) => true,
        Type::Fun {
            domain, codomain, ..
        } => type_contains_infer(domain) || type_contains_infer(codomain),
        Type::History { value, domain, .. } => {
            type_contains_infer(value) || type_contains_infer(domain)
        }
        Type::Tuple(ts) => ts.iter().any(type_contains_infer),
        Type::Record(fs) => fs.iter().any(|(_, t)| type_contains_infer(t)),
        Type::Variant(tags) => tags.iter().any(|(_, t)| type_contains_infer(t)),
        Type::Refinement(base, _) => type_contains_infer(base),
    }
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
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole
        | Type::Infer(_) => {}
        Type::Fun {
            name,
            domain,
            codomain,
            ..
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
        Type::History { value, domain, .. } => {
            collect_type_fv(value, bound, visited, out);
            collect_type_fv(domain, bound, visited, out);
        }
    }
}

/// Collect the free term-variable names of an expression — the accumulating
/// dual of [`crate::ccl::ccl_utils::count_free`]'s by-name query, and the same
/// fold over [`crate::ccl::scope::for_each_scoped_item`], so the two cannot
/// disagree about what binds where. Also descends into each sub-expression's
/// type slot, since predicate sub-terms may carry further refinements.
fn collect_expr_fv(
    e: &TypedExpr,
    bound: &mut BTreeSet<Binder>,
    visited: &mut BTreeSet<PredicateId>,
    out: &mut BTreeSet<Binder>,
) {
    collect_type_fv(&e.ty, bound, visited, out);
    for_each_scoped_item(e, &mut |item| match item {
        ScopedItem::VarRef(n) => {
            if !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        // A register key is a field label, not a variable occurrence.
        ScopedItem::KeyRef(_) => {}
        ScopedItem::Child {
            expr: child,
            binders,
        } => {
            with_binders(bound, binders.iter().map(|b| b.name.clone()), |bnd| {
                collect_expr_fv(child, bnd, visited, out)
            });
        }
    });
}

/// A type is well-formed in context `ctx` iff every free term variable of its
/// refinement predicates is bound there. The scope-validity assertion of the
/// proposal (§6.2) is exactly this check.
pub fn well_formed(ty: &Type, ctx: &BTreeSet<Binder>) -> bool {
    type_free_vars(ty).is_subset(ctx)
}

/// Counts [`Subst::assert_no_capture`] calls, so a test can assert *how many
/// times* a descent pays for the Barendregt check rather than only that it
/// passes. The check is release-active and walks every replacement term, so
/// "once per scope crossed" is a cost invariant, not a detail — see
/// `letrec_pays_the_capture_check_once_per_binder_not_once_per_child`.
///
/// Thread-local, because `cargo test` runs tests concurrently in one process.
#[cfg(test)]
mod capture_assert_probe {
    use std::cell::Cell;

    thread_local! {
        static COUNT: Cell<usize> = const { Cell::new(0) };
    }

    pub fn bump() {
        COUNT.with(|c| c.set(c.get() + 1));
    }

    /// Run `body`, returning how many capture assertions it performed.
    pub fn count(body: impl FnOnce()) -> usize {
        COUNT.with(|c| c.set(0));
        body();
        COUNT.with(Cell::get)
    }
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
        let slot_ref = Refinement::born(Rc::new(gt(var("k"), int(0))));
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
        let outer = Refinement::born(Rc::new(e));
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
        let bad = Type::Refinement(Box::new(Type::infer()), Refinement::born(Rc::new(pred)));
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
    fn rename_preserves_the_occurrence_type() {
        // α-renaming cannot change a term's type. A rename materializes as a *fresh*
        // `Var` node, so the replacement has to take the type from the occurrence it
        // replaces — otherwise the node lands at `Type::Hole`. That matters most
        // inside a refinement predicate: nothing types a predicate's interior after
        // inference, so a hole introduced here survives to the post-inference check.
        let mut occurrence = var("k");
        occurrence.ty = Type::Base(crate::ccl::BaseType::Int);
        let out = Subst::rename("k", "j").apply_expr(&occurrence);
        assert_eq!(out.node, TypedExprNode::Var(Name::raw("j")));
        assert_eq!(
            out.ty,
            Type::Base(crate::ccl::BaseType::Int),
            "a renamed occurrence keeps its type"
        );
    }

    #[test]
    fn apply_type_discharges_refinement_predicate() {
        let r = Refinement::born(Rc::new(gt(var("i"), var("k"))));
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
        let r = Refinement::born(Rc::new(gt(var("i"), var("k"))));
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
    use crate::ccl::{BinOpKind, CompareKind, Lit, Refinement, TypedBinding};
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
        let dom = Type::Refinement(Box::new(Type::Hole), Refinement::sharing(&shared));
        let cod = Type::Refinement(Box::new(Type::Hole), Refinement::sharing(&shared));
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

    // ---- Barendregt-check cost at a binder crossing -------------------------
    //
    // `assert_no_capture` is a *release-active* `assert!` whose `range_mentions`
    // does a full `is_free` walk of every `Discharge` replacement term, so what
    // it is paid *per* is a cost invariant. The scoped walk opens a scope once
    // for the whole run of children it covers, and the descent restricts and
    // checks there; asserting inside a per-child callback instead is quadratic
    // in a scope's width, which is what these pin.

    /// A `LetRec` group of *n* binders opens **one** scope covering *n*+1
    /// children (each definition, plus the body), so the no-capture check is
    /// owed *n* times — once per binder of the one scope crossed.
    #[test]
    fn letrec_pays_the_capture_check_once_per_binder_not_once_per_child() {
        for n in [1usize, 4, 8] {
            let bindings: Vec<_> = (0..n)
                .map(|i| {
                    (
                        TypedBinding::new_unannotated(format!("f{i}")),
                        int(i as i64),
                    )
                })
                .collect();
            let mut e = TypedExpr::letrec(bindings, var("x"));
            let subst = Subst::discharge("x", int(0));

            let asserts = capture_assert_probe::count(|| subst.rewrite_expr(&mut e));

            assert_eq!(
                asserts,
                n,
                "a {n}-binder letrec crosses one scope, so it owes {n} capture checks; \
                 checking per child instead costs n*(n+1) = {}",
                n * (n + 1)
            );
        }
    }

    /// A `Case` branch's payload binder opens one scope covering the branch's
    /// guard *and* body — one scope, so one check, not one per child.
    #[test]
    fn case_pays_the_capture_check_once_per_branch_not_once_per_child() {
        let branch = |tag: &str, payload: &str| Branch {
            pattern: Some(crate::ccl::Pattern {
                tag: tag.into(),
                binding: TypedBinding::new_unannotated(payload),
            }),
            guard: int(1),
            body: int(2),
        };
        let mut e = TypedExpr::new(TypedExprNode::Case {
            scrutinee: Some(Box::new(var("x"))),
            branches: vec![branch("A", "pa"), branch("B", "pb")],
        });
        let subst = Subst::discharge("x", int(0));

        let asserts = capture_assert_probe::count(|| subst.rewrite_expr(&mut e));

        assert_eq!(
            asserts, 2,
            "two payload-binding branches cross two scopes, so two capture checks; \
             checking per child costs four (guard + body each)"
        );
    }

    /// The descent does not pre-test inertness before crossing a binder, so the
    /// crossing is checked wherever the binder is crossed and not only where the
    /// substitution is still live in the body. `for y in x do 1` is live at the
    /// node (`x` is in `iter`) and inert in the body, and the range mentions
    /// `y`, so the tripwire must fire.
    #[test]
    #[should_panic(expected = "Barendregt violation")]
    fn a_binder_crossing_is_checked_even_when_the_body_is_inert() {
        let mut e = TypedExpr::new(TypedExprNode::For {
            target: TypedBinding::new_unannotated("y"),
            iter: Box::new(var("x")),
            body: Box::new(int(1)),
        });
        Subst::discharge("x", var("y")).rewrite_expr(&mut e);
    }

    /// Substitution retargets every variable occurrence the scoped walk
    /// surfaces. `crate::ccl::scope`'s corpus test checks the two walks agree on
    /// what those occurrences *are*; this checks the descent acts on all of
    /// them — the end-to-end half, across `Var` and the three handle nodes.
    #[test]
    fn a_rename_retargets_every_varref_the_scoped_walk_surfaces() {
        use crate::ccl::scope::{ScopedItem, for_each_scoped_item};

        let handle_nodes = [
            TypedExpr::new(TypedExprNode::Feed {
                name: Name::raw("h"),
                value: Box::new(int(1)),
            }),
            TypedExpr::new(TypedExprNode::Define {
                name: Name::raw("h"),
                value: Box::new(int(1)),
            }),
            TypedExpr::new(TypedExprNode::MutWrite {
                name: Name::raw("h"),
                value: Box::new(int(1)),
            }),
            var("h"),
        ];

        for original in handle_nodes {
            let before: Vec<Name> = varrefs(&original);
            assert!(
                before.contains(&Name::raw("h")),
                "corpus node must surface `h` as a VarRef"
            );

            let mut renamed = original.clone();
            Subst::rename("h", "h2").rewrite_expr(&mut renamed);

            assert!(
                !varrefs(&renamed).contains(&Name::raw("h")),
                "a rename left an occurrence of `h` behind in `{:?}` — the scoped walk \
                 declares it a variable use, so substitution must retarget it",
                original.node
            );
        }

        fn varrefs(e: &TypedExpr) -> Vec<Name> {
            let mut out = Vec::new();
            for_each_scoped_item(e, &mut |item| {
                if let ScopedItem::VarRef(n) = item {
                    out.push(n.clone());
                }
            });
            out
        }
    }
}

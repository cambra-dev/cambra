//! Capture-avoiding substitutions over term binders — the context-morphism
//! machinery for dependent refinements (Pi types).
//!
//! This is the load-bearing distinction from the internal design proposal
//! for dependent refinements via Pi types (§3.5) and its executable
//! substitution-prototype model:
//!
//! * A **context** annotates a type or metavariable — the binders it may
//!   legitimately mention. It is a *checking* device only (free vars ⊆ context);
//!   it transforms nothing. See [`scope_gaps`], which reports what a context
//!   does not account for.
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
//!   caller owns (lambda elimination, inlining, channelization, lowering's
//!   uncurrying, and the mutability-elimination phases' read-your-writes
//!   environments — see [`Subst::discharge_env_in_place`]). A predicate the
//!   substitution actually touches is rebuilt as a
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
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use crate::ccl::ccl_utils::{PredMemo, free_among, is_free, strip_iterate_markers};
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
#[derive(Debug, PartialEq)]
pub enum Mapping {
    /// `binder ↦ other binder` — a correspondence between frames. Invertible.
    Rename(Binder),
    /// `binder ↦ term` — plug a term in for the binder. No inverse.
    /// (Boxed: a term is much larger than a binder name.)
    ///
    /// **Considered and deferred: `Rc<TypedExpr>`.** The payload is a template,
    /// never a tree node and cloned afresh at every read ([`Mapping::as_expr`]),
    /// so sharing it is sound. The solver copies substitutions constantly
    /// (`Bound::render_subst`, [`Subst::then`], `compact`, `constrain`): with a
    /// `Box` each of those ~28 sites deep-copies the payload tree, with an `Rc`
    /// they are refcount bumps.
    ///
    /// One trap if it is ever done: [`Subst::for_each_discharge_term_mut`] would
    /// become `Rc::make_mut`, which copies out through `TypedExpr`'s freshening
    /// `Clone`. `freshen_subst_payloads` clones the `Subst` while the source
    /// `Bound` is still alive, so the payload is **always** shared at that point
    /// and it would freshen every time. The fix is to stop mutating in place —
    /// map to a new `Rc` per payload instead. See the vault's
    /// `freshening-clone-report`.
    Discharge(Box<TypedExpr>),
}

/// Hand-written so that **copying a substitution does not duplicate its terms**
/// — the one place `TypedExpr`'s freshening `Clone` is deliberately opted out
/// of, and the reason it can be opted out of exactly here.
///
/// A `Discharge` payload is a **template**, not a tree node. It is cloned again
/// at every read ([`Mapping::as_expr`] / [`as_expr_preserving`]), and *that*
/// read is where the sibling gets minted, once per occurrence actually filled.
/// So copying the map itself must mint nothing: the template is never in a tree,
/// and no two nodes can end up sharing an id because of it.
///
/// Without this, every `Subst` copy inherits the freshening and re-mints its
/// payloads. The solver copies substitutions constantly — `Bound::render_subst`,
/// [`Subst::then`], `compact`, `constrain` — and a bound edge's payloads are **type-domain**
/// terms whose ids are outside the recorded id domain, so each such copy records
/// a `Copy` against an origin the table never saw and the pane fold reports it as
/// [`Leak::DanglingParent`](crate::ccl::provenance::Leak::DanglingParent). Measured on
/// `generator_pipeline`: 200 of them between the first two panes.
///
/// [`as_expr_preserving`]: Mapping::as_expr_preserving
impl Clone for Mapping {
    fn clone(&self) -> Self {
        match self {
            Mapping::Rename(b) => Mapping::Rename(b.clone()),
            Mapping::Discharge(t) => Mapping::Discharge(Box::new(t.clone_preserving_ids())),
        }
    }
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
    /// variable reference). The replacement carries a **new** identity
    /// throughout: a fresh mint for a `Rename`, and — since `Clone` freshens —
    /// a wholly fresh node-set for a `Discharge`, rather than the template's own
    /// ids duplicated into every occurrence it fills.
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

    /// [`as_expr`](Self::as_expr) at the **occurrence's own identity**: the
    /// replacement's root takes `node_id`, so attribution at that position stays
    /// the use site's rather than becoming the template's.
    ///
    /// A `Rename` is built directly at `node_id` rather than minted and then
    /// overwritten: a mint fires `on_mint`, and an id no node ends up carrying is
    /// a phantom birth in the provenance record.
    ///
    /// A `Discharge` copies through [`clone_at`](TypedExpr::clone_at), which
    /// builds the replacement's root directly at `node_id` and freshens the
    /// interior. Neither shape mints an id that no node ends up carrying.
    fn as_expr_preserving(&self, node_id: NodeId, occurrence_ty: &Type) -> TypedExpr {
        let out = match self {
            // See [`as_expr`]: the rename keeps the occurrence's type.
            Mapping::Rename(to) => TypedExpr::preserve(node_id, TypedExprNode::Var(to.clone()))
                .with_ty(occurrence_ty.clone()),
            Mapping::Discharge(t) => t.clone_at(node_id),
        };
        assert_preserves_typedness(&out, occurrence_ty);
        out
    }
}

/// A [`Subst`] domain is free names. A [`Name::PiBound`] is a *bound* reference
/// to an enclosing function, so nothing substitutes for one: the conversions in
/// this module remove it, at a binder crossing or at an application. The
/// invariant is stated in [`Name::PiBound`]'s docs and asserted here, at the two
/// constructors that build a domain.
fn debug_assert_no_pi_bound(binder: &Name) {
    debug_assert!(
        binder.pi_bound_index().is_none(),
        "a `PiBound` is never a substitution's domain binder: it is bound by a \
         function the type carries, and `open_pi_binder` is what removes it",
    );
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
        let from = from.into();
        debug_assert_no_pi_bound(&from);
        let mut m = BTreeMap::new();
        m.insert(from, Mapping::Rename(to.into()));
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
        let binder = binder.into();
        debug_assert_no_pi_bound(&binder);
        let mut m = BTreeMap::new();
        m.insert(binder, Mapping::Discharge(Box::new(term)));
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
        // Both early returns build a term the caller owns while `e` stays live in
        // whatever tree holds it, so the result is a genuinely new node even
        // though the substitution changed nothing. It freshens and is **recorded**
        // as a copy of `e`, rather than keeping `e`'s ids: preserving would put
        // one id-set on two live terms, which is the defect predicate rebuilding
        // just had to be fixed for.
        //
        // Recording rather than simply freshening is the load-bearing half —
        // with nothing recording, these produced 50 `DanglingParent` on `inner_join`.
        if self.is_id() {
            let _g = crate::ccl::provenance::enter(
                e.node_id(),
                "subst.vacuous",
                crate::ccl::provenance::Nature::Machinery,
            );
            return e.clone();
        }
        // No-op short-circuit: if none of the substituted binders occur free
        // in `e` — value or type slots — the substitution does nothing here.
        // The common case (a vacuous discharge `[x ↦ arg]` from a
        // non-dependent application, `x` not occurring in `e`) takes this
        // path, which is what keeps vacuous transport from copying terms or
        // rebuilding predicate terms into fresh `Rc`s.
        if !self.0.keys().any(|k| is_free(k, e)) {
            let _g = crate::ccl::provenance::enter(
                e.node_id(),
                "subst.vacuous",
                crate::ccl::provenance::Nature::Machinery,
            );
            return e.clone();
        }
        self.apply_expr_inner(e)
    }

    fn apply_expr_inner(&self, e: &TypedExpr) -> TypedExpr {
        use TypedExprNode::*;
        // Transport mode *builds*: it returns a new `TypedExpr` rather than
        // editing one already in the tree (that is `rewrite_expr_go`, which takes
        // `&mut` and installs the replacement at the occurrence's own id). So the
        // nodes below are genuinely new and want **recording**, not id-preserving
        // — and the node they are derived from is `e`. The recording opens at
        // function entry because the `Var` arm returns early.
        let _g = crate::ccl::provenance::enter(
            e.node_id(),
            "subst.transport",
            crate::ccl::provenance::Nature::Machinery,
        );
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
            // nodes exist only pre-channelize; transport runs during inference,
            // but the uniform engine handles them for the pre-inference
            // ports). A var-shaped mapping renames the handle; a discharge
            // to a non-variable term has no Feed/Define shape to land in, so
            // the stale handle is kept for channelize's own
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
    /// observed uniformly across the tree. `Compose` node types have their
    /// **ends** recomputed from the rewritten elements (substituting a `Var` whose
    /// type was an unresolved placeholder can concretize the element types; the
    /// `Compose.ty == Fun(first_domain, last_codomain)` invariant must follow) —
    /// the arrow's `FunKind` and Pi binder are preserved, since those belong to
    /// the composition and not to its elements.
    pub fn rewrite_expr(&self, e: &mut TypedExpr) {
        if self.is_id() {
            return;
        }
        self.rewrite_expr_go(e, &PredMemo::new());
    }

    /// Discharge `binder ↦ term` over `e` **in place**, cloning `term` only
    /// when `binder` actually occurs free in `e`. A vacuous substitution
    /// costs one [`is_free`] walk and **no clone** — the pass-level callers
    /// (lambda elimination, channelization, lowering's uncurrying)
    /// substitute into many subtrees that never mention the binder, so
    /// cloning `term` for those would be pure waste.
    pub fn discharge_in_place(e: &mut TypedExpr, binder: &Name, term: &TypedExpr) {
        if !is_free(binder, e) {
            return;
        }
        // `term` is a *template*: `as_expr` clones it afresh at every occurrence
        // it fills, and that read is where each sibling is minted. Copying it
        // into the map must therefore mint nothing — a freshening clone here
        // builds one whole extra tree per call that no occurrence ever uses.
        Subst::discharge(binder.clone(), term.clone_preserving_ids()).rewrite_expr(e);
    }

    /// Discharge a whole **environment** `{name ↦ term, …}` over `e` — every name
    /// at once, in one traversal.
    ///
    /// The env-shaped sibling of [`Self::discharge_in_place`], for the
    /// read-your-writes environments the mutability-elimination phases thread
    /// (`mut_elim`, `transact_phase`): a flat map with no binder structure,
    /// applied to a whole subtree.
    ///
    /// **Simultaneous, not a fold of single-name discharges.** [`Subst`] is
    /// already a simultaneous map, so this is a constructor over it rather than a
    /// second engine. A sequential fold would re-substitute into a replacement
    /// that mentions another env key, sending `{a ↦ b, b ↦ 0}`'s `a` to `0`
    /// instead of to `b`. A read-your-writes environment resolves each value
    /// against the environment before storing it, so caller ranges are key-free
    /// today — a property of the callers, not of the operation.
    ///
    /// Each replaced occurrence keeps its own `NodeId`, so N reads give N distinct
    /// roots; the contract is in [`Mapping::as_expr_preserving`] and
    /// [`Self::rewrite_expr_go`], and its rationale in
    /// `src/ccl/design/provenance.md`, "Duplication".
    ///
    /// Only the entries free in `e` are cloned into the substitution — the same
    /// "vacuous costs no clone" discipline as the single-name sibling, and it
    /// pays more here, since a writer's environment holds one fully-inlined value
    /// per register and most subtrees mention none of them. The selection is one
    /// traversal ([`free_among`], which carries the cost argument), not one per
    /// entry.
    ///
    /// Two hard `assert!`s ride this path, release-live rather than debug
    /// tripwires: [`assert_preserves_typedness`] fires if an environment value is
    /// untyped against a typed occurrence, and [`Self::assert_no_capture`] fires
    /// if the environment's range mentions a binder the walk passes under. The
    /// mutability phases satisfy both — they run post-inference over α-unique
    /// names — and the asserts make that an enforced precondition rather than a
    /// comment.
    pub fn discharge_env_in_place(mut e: TypedExpr, env: &HashMap<Name, TypedExpr>) -> TypedExpr {
        let live_names = free_among(env.keys(), &e);
        let live: BTreeMap<Binder, Mapping> = env
            .iter()
            .filter(|(name, _)| live_names.contains(*name))
            .map(|(name, term)| (name.clone(), Mapping::Discharge(Box::new(term.clone()))))
            .collect();
        Subst(live).rewrite_expr(&mut e);
        e
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
            // A mutable variable key is a field label, not a variable occurrence:
            // nothing a term substitution acts on.
            ScopedItemMut::KeyRef(_) => {}
        });

        // `Compose`'s type is derived from its elements, so rewriting them can
        // concretize it (substituting a `Var` whose type was a placeholder).
        //
        // `fun_like`, not `fun`: only the arrow's *ends* are derived from the
        // elements. Its `FunKind` and any Pi binder are properties of the
        // composition itself, and `Type::fun` answers `Compute`/`None` for both —
        // so rebuilding with it silently downgrades a data collection `⤇` to a
        // compute arrow `⇒` and drops a dependent binder, on every `Compose` a
        // live substitution happens to reach
        // (`src/ccl/design/type-inference.md`, "4.6 Data vs compute functions").
        if let TypedExprNode::Compose(elts) = &e.node
            && let (Some(first), Some(last)) = (elts.first(), elts.last())
            && let (Some(d), Some(c)) = (first.ty.domain(), last.ty.codomain())
        {
            e.ty = Type::fun_like(&e.ty, d, c);
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
            Type::BoundedHole(t) => self.rewrite_type_go(t, memo),
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Txn
            | Type::Hole
            | Type::SharedHole(_)
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
            Type::Variant(tags, _) => tags
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
        // **Recorded, not preserved.** `born` below installs a *new* `Rc` while
        // the source refinement stays alive behind `r`, so the two terms coexist
        // — this is a derivation, not the in-place replacement `PredMemo::rebuild`
        // performs. Preserving here put the same ids on two simultaneously-live
        // predicate terms, which nothing catches because predicate uniqueness is
        // not asserted; measured at 53 such collisions on `inner_join` alone.
        //
        // The recording names the source predicate's own root, so the rewritten term
        // rows as derived from the term it was substituted out of.
        let new_pred = {
            let _g = crate::ccl::provenance::enter(
                r.predicate.node_id(),
                "subst.force_refinement",
                crate::ccl::provenance::Nature::Machinery,
            );
            strip_iterate_markers(&restricted.apply_expr(&r.predicate))
        };
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
            Type::BoundedHole(t) => Type::BoundedHole(Box::new(self.apply_type_inner(t))),
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Txn
            | Type::Hole
            | Type::SharedHole(_)
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
            Type::Variant(tags, openness) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.apply_type(t)))
                    .collect(),
                *openness,
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
        | Type::Hole
        | Type::SharedHole(_) => false,
        Type::Infer(_) => true,
        Type::Fun {
            domain, codomain, ..
        } => type_contains_infer(domain) || type_contains_infer(codomain),
        Type::History { value, domain, .. } => {
            type_contains_infer(value) || type_contains_infer(domain)
        }
        Type::Tuple(ts) => ts.iter().any(type_contains_infer),
        Type::Record(fs) => fs.iter().any(|(_, t)| type_contains_infer(t)),
        Type::Variant(tags, _) => tags.iter().any(|(_, t)| type_contains_infer(t)),
        Type::Refinement(base, _) => type_contains_infer(base),
        // Annotation position only, and normalized away before solving. Answering
        // for the bounded type is the honest reading of the question; a `BoundedHole` that
        // reaches here at all is reported as `UnresolvedBoundedHole`, not by this test.
        Type::BoundedHole(t) => type_contains_infer(t),
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
        // A bounded annotation binds nothing, so its bound's free variables are
        // free in it — a name referenced only from inside an annotation is still
        // referenced.
        Type::BoundedHole(t) => collect_type_fv(t, bound, visited, out),
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_)
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
        Type::Variant(tags, _) => tags
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
            // A `PiBound` is a bound reference to a function of the enclosing
            // type, not a free name — it is never free and never in a context.
            if n.pi_bound_index().is_none() && !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        // A mutable variable key is a field label, not a variable occurrence.
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

/// Every stored dependent function in `ty` whose codomain still references its
/// own binder **by name** rather than as an index.
///
/// The construction boundary's invariant, from the outside: a `Fun` built through
/// `Type::pi`/`pi_kinded`/`fun_like` closes, while a field-wise literal does not,
/// and nothing in the type enforces which one a caller reached for. A stored type
/// carrying the name spelling is what the two opening tripwires only notice later,
/// once a reference has already escaped its binder.
///
/// Note this asks about the codomain alone: [`type_free_vars`] on the whole `Fun`
/// binds the Pi name over the codomain, which is the very reference in question.
#[cfg(debug_assertions)]
pub fn name_spelled_stored_binders(ty: &Type) -> Vec<Binder> {
    fn go(ty: &Type, out: &mut Vec<Binder>, visited: &mut BTreeSet<PredicateId>) {
        if let Type::Fun {
            name: Some(b),
            codomain,
            ..
        } = ty
            && type_free_vars(codomain).contains(b)
        {
            out.push(b.clone());
        }
        match ty {
            Type::Refinement(base, r) => {
                go(base, out, visited);
                if visited.insert(r.predicate_id()) {
                    expr_go(&r.predicate, out, visited);
                }
            }
            _ => ty.walk_children(|c| go(c, out, visited)),
        }
    }
    fn expr_go(e: &TypedExpr, out: &mut Vec<Binder>, visited: &mut BTreeSet<PredicateId>) {
        go(&e.ty, out, visited);
        e.walk_children(|c| expr_go(c, out, visited));
    }
    let mut out = Vec::new();
    go(ty, &mut out, &mut BTreeSet::new());
    out
}

/// The free term variables of `ty`'s refinement predicates that `in_scope` does
/// not account for. Empty iff `ty` is well-formed there.
///
/// One spelling for the whole family: the end-of-inference scope check
/// (`infer::solve`'s `check_scope_valid`) and the record-time closure check
/// (`infer_var`'s `bound_scope_gaps`) differ only in what they count as in scope, and both need the gap set rather than a yes/no — the first
/// to name the unbound variables in its diagnostic, the second because every
/// member is an error. `in_scope` is a predicate rather than a set so a caller
/// whose scope is not one (a telescope plus two substitution domains) needs no
/// set built to ask.
pub fn scope_gaps(ty: &Type, in_scope: impl Fn(&Binder) -> bool) -> BTreeSet<Binder> {
    let mut free = type_free_vars(ty);
    free.retain(|n| !in_scope(n));
    free
}

// ---- locally nameless: closing and opening a Pi binder ----

/// Close `binder`'s free references in `ty` into de Bruijn indices
/// ([`Name::PiBound`]) — the abstraction half of the locally-nameless
/// representation (see `src/ccl/design/type-inference.md`, "A binder reference
/// is stored in one of two forms"). An index counts the `Fun` codomains crossed
/// between the reference and the function that binds it, named and unnamed
/// alike (so it survives `Type::without_pi_names`): a reference in the
/// constructed function's immediate codomain closes at `#0`, one per crossed
/// codomain deeper.
///
/// Function construction owns closing: it runs over the codomain a dependent
/// function is built around, so a constructed `Type::Fun` never carries a free
/// name for its own binder. Indices already present are left alone — they
/// are bound by functions *inside* `ty`, strictly closer than the one being
/// created — so closing composes bottom-up across nested constructions and
/// is the identity on an already-closed type.
///
/// Predicate `Rc` sharing is preserved per call: occurrences sharing one
/// predicate term leave sharing one rewritten term, and a predicate the
/// closing does not touch keeps its original `Rc` (pointer-equal), exactly
/// as [`Subst::force_refinement`] transports a vacuous substitution.
pub fn close_pi_binder(binder: &Name, ty: &Type) -> Type {
    // A codomain with no free occurrence of the binder has nothing to close,
    // and every construction site runs this — including the rebuild helpers
    // (`Type::fun_like`, `emit_cast`) whose codomains come out of functions that
    // closed already. Answering from a borrowing scan keeps those off the
    // clone-and-walk path. The scan covers what the walk covers: predicates,
    // their interior type slots, and interior term binders' shadowing.
    debug_assert!(
        !binder.is_elem(),
        "a Pi binder is never the refinement element binder, which \
         `is_free_in_type` reports as never free",
    );
    debug_assert!(
        binder.pi_bound_index().is_none(),
        "a `PiBound` is a reference, never a binder, so nothing abstracts over \
         one: closing at one would rewrite references to an unrelated function",
    );
    if !crate::ccl::ccl_utils::is_free_in_type(binder, ty) {
        return ty.clone();
    }
    let enclosing = [Some(binder.clone())];
    let mut out = ty.clone();
    PiWalk::new(PiMode::Close(&enclosing)).ty(&mut out, 0);
    out
}

/// Open the function whose codomain `ty` was just extracted from
/// it: every [`Name::PiBound`] reference to it — index equal to the
/// codomains crossed to reach the reference — becomes `target`. The two
/// replacement species are the two opening sites (see
/// `src/ccl/design/type-inference.md`, "Where the conversions run"):
/// a [`Mapping::Rename`] opens at a name (descent under the binder — the
/// reference becomes a free `Var` closed against the reader's telescope),
/// a [`Mapping::Discharge`] opens at the argument (application — β). Indices
/// bound by functions inside `ty` are strictly smaller at their references and
/// stay untouched; no index shifts, because opening only ever removes the
/// enclosing function.
pub fn open_pi_binder(target: &Mapping, ty: &Type) -> Type {
    let mut out = ty.clone();
    PiWalk::new(PiMode::Open(target)).ty(&mut out, 0);
    out
}

/// A morphism's `codomain` in the form its *consumer* speaks: descent
/// under a dependent morphism's binder, where its own reference to that binder
/// is the free name rather than an index
/// (`src/ccl/design/type-inference.md`, "Where the conversions run").
///
/// The rebuild passes all reach for this at the same shape — a chain adjacency,
/// an application's transformer function, a recognizer matching a family's
/// predicate — each holding the morphism and the codomain it just read off it.
/// A non-dependent morphism and an index-free codomain pass through untouched,
/// so a caller with nothing to open pays a scan.
pub fn open_codomain(morphism: &Type, codomain: &Type) -> Type {
    match morphism.peel_refinements() {
        Type::Fun { name: Some(b), .. } if references_enclosing_function(codomain) => {
            open_pi_binder(&Mapping::Rename(b.clone()), codomain)
        }
        _ => {
            debug_assert!(
                !matches!(morphism.peel_refinements(), Type::Fun { name: None, .. })
                    || !references_enclosing_function(codomain),
                "an unnamed function's codomain references it: the index has no \
                 binder to open at, so nothing downstream can resolve it",
            );
            codomain.clone()
        }
    }
}

/// Which conversion a [`PiWalk`] performs.
enum PiMode<'a> {
    /// `Var(n)` where `n` names an enclosing function becomes `Var(PiBound(k))`,
    /// `k` the codomain crossings between the reference and it: that function's
    /// distance in the stack (innermost last, unnamed crossings as `None`)
    /// plus the crossings walked inside the converted structure itself.
    Close(&'a [Option<Name>]),
    /// `Var(PiBound(d))` at depth `d` becomes the target (a `Var` for a
    /// rename, the discharged term for an application).
    Open(&'a Mapping),
}

/// The shared engine under [`close_pi_binder`] and [`open_pi_binder`]: one
/// walk over the mixed type/term structure, threading the crossed-codomain
/// depth. Only a `Fun` codomain crossing deepens; a domain, a refinement
/// predicate, and a predicate's interior type slots stay at their enclosing
/// depth.
struct PiWalk<'a> {
    mode: PiMode<'a>,
    /// Rewrites performed, for change detection (an untouched predicate keeps
    /// its original `Rc`).
    changed: usize,
    /// Predicate terms already rewritten at a given depth, so occurrences
    /// that entered sharing one `Rc` leave sharing one `Rc`. Keyed by depth
    /// too: one term reachable at two depths is two different rewrites.
    /// Consulted only while [`shadowed`](Self::shadowed) is empty, since a
    /// shadow changes what the same term at the same depth converts to.
    memo: HashMap<(PredicateId, u32), Rc<TypedExpr>>,
    /// Term binders a predicate's interior introduces, innermost last. A
    /// reference to one of these is bound by the predicate's own lambda, not
    /// by an enclosing function, so closing leaves it alone
    /// (`src/ccl/design/type-inference.md`, "Interior term binders stay
    /// named, and compare by position").
    shadowed: Vec<Name>,
}

impl<'a> PiWalk<'a> {
    fn new(mode: PiMode<'a>) -> Self {
        PiWalk {
            mode,
            changed: 0,
            memo: HashMap::new(),
            shadowed: Vec::new(),
        }
    }

    fn ty(&mut self, ty: &mut Type, depth: u32) {
        match ty {
            // No structural children. An `Infer`'s bounds are the live
            // graph's, name-spelled — a construction-time
            // conversion must not reach through and rewrite them.
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_) => {}
            Type::BoundedHole(t) => self.ty(t, depth),
            Type::Fun {
                domain, codomain, ..
            } => {
                // A binder scopes over its codomain only: the domain stays at
                // the enclosing depth, the codomain is one crossing deeper.
                self.ty(domain, depth);
                self.ty(codomain, depth + 1);
            }
            Type::Refinement(base, r) => {
                self.ty(base, depth);
                self.refinement(r, depth);
            }
            Type::Tuple(ts) => ts.iter_mut().for_each(|t| self.ty(t, depth)),
            Type::Record(fs) => fs.iter_mut().for_each(|(_, t)| self.ty(t, depth)),
            Type::Variant(tags, _) => tags.iter_mut().for_each(|(_, t)| self.ty(t, depth)),
            Type::History { value, domain, .. } => {
                self.ty(value, depth);
                self.ty(domain, depth);
            }
        }
    }

    fn refinement(&mut self, r: &mut crate::ccl::Refinement, depth: u32) {
        // A shadow makes the conversion depend on more than the term and the
        // depth, so the memo is bypassed under one. It costs a re-walk of a
        // predicate a shadowing lambda encloses and keeps the key two fields.
        let key = (r.predicate_id(), depth);
        let memoizable = self.shadowed.is_empty();
        if memoizable && let Some(done) = self.memo.get(&key) {
            if !Rc::ptr_eq(done, &r.predicate) {
                *r = crate::ccl::Refinement::sharing(done);
            }
            return;
        }
        // A converted predicate is a **derived** term, not a replacement: the
        // stored closed form stays live on the type this view was read off, so
        // the two are two live terms and cannot share an id-set (the
        // `predicate-vs-predicate` half of `predicate_id_collisions`). The clone
        // therefore freshens, which makes this a rewrite like any other and puts
        // it under a recording named by the term it converts — the same shape
        // `PredMemo::rebuild` uses for its deriving branch. Without the guard the
        // fresh ids are minted with nothing recording, and surface as dangling
        // parents once a later recorded rewrite names the converted root.
        let (pred, before) = {
            let _g = crate::ccl::provenance::enter(
                r.predicate.node_id(),
                "predicate.coordinate",
                crate::ccl::provenance::Nature::Machinery,
            );
            let mut pred = (*r.predicate).clone();
            let before = self.changed;
            self.expr(&mut pred, depth);
            (pred, before)
        };
        let done = if self.changed > before {
            // Occurrences that shared the original re-share the conversion
            // through the memo.
            let done = Rc::new(pred);
            *r = crate::ccl::Refinement::sharing(&done);
            done
        } else {
            Rc::clone(&r.predicate)
        };
        if memoizable {
            self.memo.insert(key, done);
        }
    }

    fn expr(&mut self, e: &mut TypedExpr, depth: u32) {
        match &self.mode {
            PiMode::Close(enclosing) => {
                if let TypedExprNode::Var(n) = &e.node
                    && !self.shadowed.contains(n)
                    && let Some(dist) = enclosing.iter().rev().position(|f| f.as_ref() == Some(n))
                {
                    // The spelling rides along as the reference's display
                    // hint: a diagnostic that blames this refinement detached from
                    // its function has none to read a name off.
                    e.node = TypedExprNode::Var(Name::pi_bound(dist as u32 + depth, n));
                    self.changed += 1;
                    // Fall through: the occurrence's type slot may itself
                    // carry references to convert.
                }
            }
            PiMode::Open(target) => {
                if let TypedExprNode::Var(n) = &e.node
                    && n.pi_bound_index() == Some(depth)
                {
                    let occurrence_ty = e.ty.clone();
                    *e = target.as_expr_preserving(e.node_id, &occurrence_ty);
                    self.changed += 1;
                    // A `Discharge` replaces the occurrence with a foreign
                    // term, whose own indices are relative to wherever it was
                    // written and must not be read against this depth. A
                    // `Rename` keeps the occurrence's type slot, which is
                    // not yet opened, so that slot is
                    // converted and the term below it is a bare `Var`.
                    if matches!(target, Mapping::Rename(_)) {
                        self.ty(&mut e.ty, depth);
                    }
                    return;
                }
            }
        }
        e.walk_type_slots_mut(|t| self.ty(t, depth));
        // Children under the binders that scope over them: a term binder a
        // predicate introduces shadows an enclosing function that shares its name, and its
        // references are its own.
        let base = self.shadowed.len();
        for_each_scoped_item_mut(e, &mut |item| match item {
            ScopedItemMut::Scope(binders) => {
                self.shadowed.truncate(base);
                self.shadowed.extend(binders.iter().cloned());
            }
            ScopedItemMut::Child(child) => self.expr(child, depth),
            // A `VarRef` here is either this node's own `Var` — already
            // converted above, since `expr` is called on every child — or a
            // handle node's write target, which names a mutable variable. A
            // `KeyRef` names a record field. Neither of the latter two is a Pi
            // binder reference.
            ScopedItemMut::VarRef(_) | ScopedItemMut::KeyRef(_) => {}
        });
        self.shadowed.truncate(base);
    }
}

/// Does `ty` reference the function it was just extracted from — a
/// [`Name::PiBound`] whose index equals the codomain crossings to reach it?
/// This is the dependence test that drives **opening**: descent and
/// application convert exactly the references this finds. A site deciding
/// whether to *keep* a function's binder wants [`codomain_depends_on`], which
/// also admits a name-spelled codomain.
pub fn references_enclosing_function(ty: &Type) -> bool {
    fn ty_scan(ty: &Type, depth: u32, visited: &mut BTreeSet<(PredicateId, u32)>) -> bool {
        match ty {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::ChanDom(..)
            | Type::Txn
            | Type::Hole
            | Type::SharedHole(_)
            | Type::Infer(_) => false,
            Type::BoundedHole(t) => ty_scan(t, depth, visited),
            Type::Fun {
                domain, codomain, ..
            } => ty_scan(domain, depth, visited) || ty_scan(codomain, depth + 1, visited),
            // Keyed by depth as well as by predicate: the answer depends on
            // the crossings walked to reach the refinement, so one shared predicate
            // reached at two depths is two questions. Keying on identity alone
            // answers the second from the first and reports a dependent
            // codomain as independent — the index would then lose its binder.
            Type::Refinement(base, r) => {
                (visited.insert((r.predicate_id(), depth))
                    && expr_scan(&r.predicate, depth, visited))
                    || ty_scan(base, depth, visited)
            }
            Type::Tuple(ts) => ts.iter().any(|t| ty_scan(t, depth, visited)),
            Type::Record(fs) => fs.iter().any(|(_, t)| ty_scan(t, depth, visited)),
            Type::Variant(tags, _) => tags.iter().any(|(_, t)| ty_scan(t, depth, visited)),
            Type::History { value, domain, .. } => {
                ty_scan(value, depth, visited) || ty_scan(domain, depth, visited)
            }
        }
    }
    fn expr_scan(e: &TypedExpr, depth: u32, visited: &mut BTreeSet<(PredicateId, u32)>) -> bool {
        if matches!(&e.node, TypedExprNode::Var(n) if n.pi_bound_index() == Some(depth)) {
            return true;
        }
        let mut found = false;
        e.walk_type_slots(|t| found = found || ty_scan(t, depth, visited));
        if found {
            return true;
        }
        e.fold_children(false, |acc, c| acc || expr_scan(c, depth, visited))
    }
    ty_scan(ty, 0, &mut BTreeSet::new())
}

/// Does `codomain`, just extracted from a function binding `binder`, depend on
/// that function — closed or name-spelled? A closed codomain references it by
/// index ([`references_enclosing_function`]) and a name-spelled one
/// references `binder` by name; a site that keeps or drops the function's binder
/// slot has to admit both, because the slot is what a later descent or
/// application opens the function at and dropping it strands the reference.
///
/// The two callers are the two places a function is rebuilt around a codomain
/// computed elsewhere: `coalesce_compact_go` assembling a `Fun` from a compact
/// view, and `lambda_elim` re-attaching an eliminated lambda's Pi.
pub fn codomain_depends_on(binder: &Name, codomain: &Type) -> bool {
    references_enclosing_function(codomain) || type_free_vars(codomain).contains(binder)
}

/// The functions a refinement-closing walk is inside of, and the memo that closes
/// refinements against them (see `src/ccl/design/type-inference.md`, "Where the
/// conversions run").
///
/// One type, because two walks have to agree. `compact_go` and `key_go` each close
/// a refinement as it lands, and each must enter and leave the same crossings at the
/// same arms. Two walks that disagreed would spell one refinement two ways, and the
/// `SpecKey` would then split — or share — a specialization the compacted type does
/// not. Holding the stack and the memo in one type leaves them nothing to disagree
/// about.
#[derive(Default)]
pub(crate) struct RefinementScope {
    /// The binders of the `Fun`s the walk is inside of, innermost last (`None`
    /// for an unnamed one — it still counts as a crossing). Pushed entering a
    /// codomain, never a domain: a binder scopes over its codomain only.
    enclosing: Vec<Option<Name>>,
    /// Keyed on (predicate identity, enclosing binders) so occurrences that
    /// entered a view sharing one predicate `Rc` leave sharing one `Rc` — the
    /// planning-cost concern of [`crate::ccl::Refinement::predicate`].
    memo: HashMap<(PredicateId, Vec<Option<Name>>), crate::ccl::Refinement>,
}

impl RefinementScope {
    /// Enter the codomain of a `Fun` binding `name` — one crossing deeper.
    pub(crate) fn enter(&mut self, name: Option<Name>) {
        self.enclosing.push(name);
    }

    /// Leave the codomain [`enter`](Self::enter) entered.
    pub(crate) fn exit(&mut self) {
        self.enclosing.pop();
    }

    /// The entered binders, for a walk whose own memo is per-position too.
    pub(crate) fn enclosing(&self) -> &[Option<Name>] {
        &self.enclosing
    }

    /// Close `r` against the functions entered so far: its free references to
    /// them become indices. A refinement referencing none of them keeps its predicate
    /// `Rc` and costs no walk.
    pub(crate) fn close(&mut self, r: &crate::ccl::Refinement) -> crate::ccl::Refinement {
        if self.enclosing.iter().all(Option::is_none) {
            return r.clone();
        }
        let key = (r.predicate_id(), self.enclosing.clone());
        if let Some(done) = self.memo.get(&key) {
            return done.clone();
        }
        let mut walk = PiWalk::new(PiMode::Close(&self.enclosing));
        let mut out = r.clone();
        walk.refinement(&mut out, 0);
        self.memo.insert(key, out.clone());
        out
    }
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
        assert!(!scope_gaps(&bad, |n| only_x.contains(n)).is_empty());
        assert!(scope_gaps(&bad, |n| only_k.contains(n)).is_empty());
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

    // A binder's own references are out of a discharge's reach, by one of
    // two mechanisms, depending on how the function was built: a *constructed* one
    // (`Type::pi`) closed them into indices, which no name-keyed
    // substitution maps; a name-based one (the mid-solve form, built
    // field-wise) shadows the discharge under the binder instead.
    #[test]
    fn apply_type_shadows_pi_binder() {
        let refined = |pred: TypedExpr| {
            Type::fun(
                Type::Refinement(Box::new(Type::infer()), Refinement::born(Rc::new(pred))),
                Type::infer(),
            )
        };
        // Constructed: (k: _) ⇒ ({i | i > k} ⇒ _) closes k to #0 at
        // construction, and [k↦5] has nothing to touch.
        let ty = Type::pi("k", Type::infer(), refined(gt(var("i"), var("k"))));
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
        let Type::Fun { codomain, .. } = &out else {
            panic!()
        };
        let Type::Fun { domain, .. } = codomain.as_ref() else {
            panic!()
        };
        let Type::Refinement(_, r2) = domain.as_ref() else {
            panic!()
        };
        assert_eq!(
            *r2.predicate,
            gt(var("i"), TypedExpr::var(Name::pi_bound_bare(0)))
        );

        // Name-based: the same shape built field-wise keeps `k` a name, and
        // the shadow is what protects it.
        let ty = Type::Fun {
            name: Some(Name::raw("k")),
            kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(Type::infer()),
            codomain: Box::new(refined(gt(var("i"), var("k")))),
        };
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
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

    /// The identity property the mutability phases' read-your-writes environments
    /// depend on: a replaced occurrence keeps its own `NodeId`, and the value's
    /// interior arrives under fresh ids. N reads of one environment value therefore
    /// become N subtrees with disjoint ids — what lets a phase assemble them into a
    /// tree the pipeline's uniqueness invariant accepts — each inheriting its read
    /// site's span and attribution.
    ///
    /// This lives here rather than in `mut_elim` and `transact_phase` because it is
    /// a property of the *engine*: those phases each carried a copy of this test,
    /// which called the discharge directly and exercised no phase code, so one
    /// engine gets one test.
    #[test]
    fn discharge_env_root_carries_and_freshens_interiors() {
        let int_ty = Type::Base(crate::ccl::BaseType::Int);
        let acc = Name::fresh("acc");

        // A *compound* environment value, so there is an interior to freshen.
        let mut value = TypedExpr::tuple(vec![
            var("x").with_ty(int_ty.clone()),
            var("y").with_ty(int_ty.clone()),
        ]);
        value.ty = Type::Tuple(vec![int_ty.clone(), int_ty.clone()]);
        let TypedExprNode::Tuple(elts) = &value.node else {
            unreachable!("built as a tuple")
        };
        let value_interior: Vec<NodeId> = elts.iter().map(|e| e.node_id).collect();
        let env: HashMap<Name, TypedExpr> = HashMap::from([(acc.clone(), value)]);

        // Two reads of the accumulator, wrapped in the scaffolding a phase uses
        // to carry them into one decision record.
        let read0 = TypedExpr::var(acc.clone()).with_ty(int_ty.clone());
        let read1 = TypedExpr::var(acc.clone()).with_ty(int_ty.clone());
        let (id0, id1) = (read0.node_id, read1.node_id);
        let mut scaffold = TypedExpr::tuple(vec![read0, read1]);
        scaffold.ty = Type::Tuple(vec![int_ty.clone(), int_ty]);

        let out = Subst::discharge_env_in_place(scaffold, &env);

        let TypedExprNode::Tuple(replaced) = &out.node else {
            unreachable!("the scaffolding tuple survives")
        };
        assert_eq!(
            (replaced[0].node_id, replaced[1].node_id),
            (id0, id1),
            "a replaced read keeps its own id, so the inlined value \
             inherits the read site's span"
        );
        for copy in replaced {
            let TypedExprNode::Tuple(elts) = &copy.node else {
                unreachable!("the environment value is a tuple")
            };
            for e in elts {
                assert!(
                    !value_interior.contains(&e.node_id),
                    "the replacement's interior is freshened, not shared with the \
                     environment value"
                );
            }
        }
        // Assert through the real checker rather than a local copy of its walk:
        // uniqueness within a tree is one invariant with one implementation.
        crate::ccl::context::assert_unique_node_ids(&out, "discharge_env_in_place");
    }

    /// A `Compose`'s arrow *ends* are derived from its elements, so a
    /// substitution recomputes them — but its `FunKind` and Pi binder are not,
    /// and rebuilding with `Type::fun` would answer `Compute`/`None` for both.
    /// A data collection `⤇` must survive a discharge that reaches it, or
    /// op-conversion dispatches on a downgraded domain.
    #[test]
    fn a_compose_keeps_its_fun_kind_and_binder_across_a_discharge() {
        let int_ty = Type::Base(crate::ccl::BaseType::Int);
        let arrow = Type::data_fun(int_ty.clone(), int_ty.clone());

        // (f ≫ g) : Int ⤇ Int, with `f` the substituted occurrence.
        let mut compose = TypedExpr::compose(vec![
            var("f").with_ty(arrow.clone()),
            var("g").with_ty(arrow.clone()),
        ]);
        compose.ty = Type::pi("n", int_ty.clone(), int_ty.clone());
        // A Pi arrow whose ends the elements will recompute; the binder must stay.
        let replacement = var("h").with_ty(arrow);
        let env: HashMap<Name, TypedExpr> = HashMap::from([(Name::raw("f"), replacement)]);

        let out = Subst::discharge_env_in_place(compose, &env);

        let Type::Fun { name, kind, .. } = &out.ty else {
            panic!("a `Compose` over function elements types as a function")
        };
        assert_eq!(
            (name.as_ref().map(Name::base), kind),
            (Some("n"), &crate::ccl::FunKind::Compute),
            "the arrow's species and binder are the composition's, not its \
             elements' — `Type::fun` would have flattened both"
        );
    }

    /// The dual of the above on the data side: a `Compose` *typed* as a data
    /// collection stays one. This is the shape `mut_elim` discharges over when a
    /// mutating block binds a comprehension.
    #[test]
    fn a_data_compose_is_not_downgraded_to_a_compute_arrow() {
        let int_ty = Type::Base(crate::ccl::BaseType::Int);
        let arrow = Type::data_fun(int_ty.clone(), int_ty.clone());

        let mut compose = TypedExpr::compose(vec![
            var("f").with_ty(arrow.clone()),
            var("g").with_ty(arrow.clone()),
        ]);
        compose.ty = arrow.clone();
        let env: HashMap<Name, TypedExpr> =
            HashMap::from([(Name::raw("f"), var("h").with_ty(arrow))]);

        let out = Subst::discharge_env_in_place(compose, &env);

        assert!(
            matches!(
                &out.ty,
                Type::Fun {
                    kind: crate::ccl::FunKind::Data,
                    ..
                }
            ),
            "a discharge must not downgrade `⤇` to `⇒`; got `{}`",
            out.ty
        );
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
    // non-variable discharge for channelize's own boundary to diagnose.
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
                empty_payload: false,
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

#[cfg(test)]
mod locally_nameless_tests {
    use super::*;
    use crate::ccl::{BaseType, Lit, Refinement};

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }
    /// `{Int | <pred>}` — the predicate need not be `Bool`-typed for these
    /// structural tests.
    fn refined(pred: TypedExpr) -> Type {
        Type::Refinement(Box::new(int()), Refinement::born(Rc::new(pred)))
    }
    fn predicate_of(ty: &Type) -> &TypedExpr {
        let Type::Refinement(_, r) = ty else {
            panic!("expected a refinement, got {ty}");
        };
        &r.predicate
    }
    fn is_pi_bound(e: &TypedExpr, k: u32) -> bool {
        matches!(&e.node, TypedExprNode::Var(n) if n.pi_bound_index() == Some(k))
    }

    /// The worked example from `type-inference.md`, "Freshening and
    /// `SpecKey`": closing the outer binder of
    /// `(i: {Int | k}) ⇒ {Int | k}` assigns `#0` in the inner function's domain
    /// (only the outer binder is in scope there) and `#1` in its codomain
    /// (the inner function is crossed).
    #[test]
    fn closing_counts_codomain_crossings_only() {
        let k = Name::fresh("k");
        let inner = Type::pi(
            Name::fresh("i"),
            refined(TypedExpr::var(k.clone())),
            refined(TypedExpr::var(k.clone())),
        );
        let closed = close_pi_binder(&k, &inner);
        let Type::Fun {
            domain, codomain, ..
        } = &closed
        else {
            panic!("closing preserves the function");
        };
        assert!(is_pi_bound(predicate_of(domain), 0));
        assert!(is_pi_bound(predicate_of(codomain), 1));
    }

    /// Two α-variant codomains close to structurally identical types — the
    /// property the solver's identity sites key on.
    #[test]
    fn closing_is_alpha_canonical() {
        let shape = |binder: &Name| {
            Type::pi(
                Name::fresh("i"),
                refined(TypedExpr::var(binder.clone())),
                int(),
            )
        };
        let k = Name::fresh("k");
        let y = Name::fresh("y");
        // The `Fun` name slots (the closed binder is gone, but each shape's
        // *inner* binder is its own fresh mint) are display metadata the
        // identity sites strip; the refinements themselves are index-canonical.
        assert_eq!(
            close_pi_binder(&k, &shape(&k)).without_pi_names(),
            close_pi_binder(&y, &shape(&y)).without_pi_names()
        );
    }

    /// Distinct enclosing binders stay distinct: closing one binder leaves
    /// the other's references as free names.
    #[test]
    fn closing_leaves_other_free_names_alone() {
        let k = Name::fresh("k");
        let other = Name::fresh("outer");
        let ty = refined(TypedExpr::var(other.clone()));
        assert_eq!(close_pi_binder(&k, &ty), ty);
        assert!(type_free_vars(&close_pi_binder(&k, &ty)).contains(&other));
    }

    /// Opening at a name inverts closing (descent under the binder), and
    /// opening at a term is the application reading (β).
    #[test]
    fn opening_inverts_closing() {
        let k = Name::fresh("k");
        let inner = Type::pi(
            Name::fresh("i"),
            refined(TypedExpr::var(k.clone())),
            refined(TypedExpr::var(k.clone())),
        );
        let closed = close_pi_binder(&k, &inner);
        assert_eq!(open_pi_binder(&Mapping::Rename(k.clone()), &closed), inner);

        let applied = open_pi_binder(
            &Mapping::Discharge(Box::new(TypedExpr::lit(Lit::Int(5)))),
            &closed,
        );
        let Type::Fun { domain, .. } = &applied else {
            panic!("opening preserves the function");
        };
        assert_eq!(
            predicate_of(domain).node,
            TypedExprNode::Lit(Lit::Int(5)),
            "β replaces the reference with the argument term",
        );
    }

    /// Closing composes bottom-up: the inner construction's indices are
    /// strictly closer than the function the outer construction creates, so the
    /// outer close leaves them alone.
    #[test]
    fn nested_constructions_compose() {
        let k = Name::fresh("k");
        let i = Name::fresh("i");
        // Construction closes the codomain being wrapped: close `i`'s
        // references, then build the function around the result…
        let inner_closed = Type::pi(
            i.clone(),
            int(),
            close_pi_binder(&i, &refined(TypedExpr::var(i.clone()))),
        );
        // …then put a `k` reference beside the finished inner function and run
        // the outer construction's close over that codomain.
        let cod = Type::Tuple(vec![inner_closed, refined(TypedExpr::var(k.clone()))]);
        let closed = close_pi_binder(&k, &cod);
        let Type::Tuple(ts) = &closed else {
            panic!("closing preserves the tuple");
        };
        let Type::Fun { codomain, .. } = &ts[0] else {
            panic!("closing preserves the function");
        };
        assert!(
            is_pi_bound(predicate_of(codomain), 0),
            "the inner function's own index is untouched by the outer close",
        );
        assert!(is_pi_bound(predicate_of(&ts[1]), 0));
    }

    /// Occurrences sharing one predicate `Rc` leave sharing one `Rc`, and a
    /// predicate the conversion does not touch keeps its original `Rc`.
    #[test]
    fn closing_preserves_predicate_sharing() {
        let k = Name::fresh("k");
        let shared = Rc::new(TypedExpr::var(k.clone()));
        let untouched = Rc::new(TypedExpr::lit(Lit::Int(1)));
        let slot = |r: &Rc<TypedExpr>| Type::Refinement(Box::new(int()), Refinement::sharing(r));
        let ty = Type::Tuple(vec![slot(&shared), slot(&shared), slot(&untouched)]);
        let closed = close_pi_binder(&k, &ty);
        let Type::Tuple(ts) = &closed else {
            panic!("closing preserves the tuple");
        };
        let pred_rc = |t: &Type| {
            let Type::Refinement(_, r) = t else {
                panic!("expected refinement");
            };
            Rc::clone(&r.predicate)
        };
        assert!(
            Rc::ptr_eq(&pred_rc(&ts[0]), &pred_rc(&ts[1])),
            "rewritten occurrences re-share one term",
        );
        assert!(!Rc::ptr_eq(&pred_rc(&ts[0]), &shared));
        assert!(
            Rc::ptr_eq(&pred_rc(&ts[2]), &untouched),
            "an untouched predicate keeps its original Rc",
        );
    }

    /// A term binder inside a predicate shadows the function being closed: the
    /// references it binds stay names, because they are its and not the
    /// function's. Uniquification keeps the two spellings apart in a compiled
    /// program, so this is what makes closing correct without depending on
    /// that convention (`src/ccl/design/type-inference.md`, "Interior term
    /// binders stay named, and compare by position").
    #[test]
    fn closing_stops_at_a_shadowing_term_binder() {
        let k = Name::fresh("k");
        // {Int | (λ k → k) …} — the body's `k` is the lambda's parameter.
        let shadowing = refined(TypedExpr::lambda(
            k.clone(),
            int(),
            TypedExpr::var(k.clone()),
        ));
        assert_eq!(close_pi_binder(&k, &shadowing), shadowing);
        // The function's own reference beside it still closes, so the shadow is
        // scoped to the lambda rather than disabling the walk.
        let both = Type::Tuple(vec![shadowing, refined(TypedExpr::var(k.clone()))]);
        let Type::Tuple(ts) = close_pi_binder(&k, &both) else {
            panic!("closing preserves the tuple");
        };
        assert!(is_pi_bound(predicate_of(&ts[1]), 0));
    }

    /// The dependence test answers per position, not per predicate: one shared
    /// predicate reached at two depths is two questions, and the deeper
    /// position's answer must not settle the shallower one's. Reaching the
    /// non-referencing position first is what exposes a predicate-keyed guard.
    #[test]
    fn the_dependence_test_is_per_position_not_per_predicate() {
        let shared = Rc::new(TypedExpr::var(Name::pi_bound_bare(0)));
        let slot = || Type::Refinement(Box::new(int()), Refinement::sharing(&shared));
        // Under a function the index is one crossing short of the enclosing
        // one, so that position does not reference it; beside the function it
        // does.
        let under = Type::fun(int(), slot());
        assert!(!references_enclosing_function(&under));
        assert!(references_enclosing_function(&Type::Tuple(vec![
            under,
            slot()
        ])));
    }
}

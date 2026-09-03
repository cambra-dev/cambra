//! The constraint solver: `constrain_subtype` and its recursive engine.
//!
//! `constrain_subtype` records directional subtyping facts on inference
//! variables' bound lists, propagating transitively (`constrain_go`),
//! bridging two-sided edge substitutions (`bridge_holder_gap`), and recovering
//! from level mismatches by `extrude`. Refinement layers are peeled/wrapped
//! (`peel_refinements` / `wrap_refinements`) so a refinement deficit can flow onto
//! a variable base.

// The `constrain` cycle cache (`ConstrainCache`) keys on `(Type, Type)`. `Type`
// has interior mutability (an `Infer` var's `RefCell` bounds), but its
// `Hash`/`Eq` are identity-by-`uid` and never inspect the bounds — so mutating
// a variable's bounds during solving cannot change a key's hash. The lint's
// hazard therefore doesn't apply here.
#![allow(clippy::mutable_key_type)]

use std::collections::HashMap;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::subst::Subst;
use crate::ccl::ty::{FunKind, KindPin, TypeKind};
use crate::ccl::{
    BaseType, Bound, HistoryKind, InferVar, InferVarId, Level, Name, Refinement, RefinementSet,
    Type,
};

use super::traits::{Trait, link_watches, notify_lower};
use super::type_level;
use crate::ccl::FieldKey;

// ---------------------------------------------------------------------------
// Constraint solver
// ---------------------------------------------------------------------------

/// Errors raised by [`constrain_subtype`].
///
/// Mapped onto [`crate::ccl::infer::InferError`] by the constraint emitter
/// at use sites.
#[derive(Debug, Clone)]
pub enum ConstrainError {
    /// `lhs` and `rhs` cannot be related by the subtyping rules of
    /// [`Type`] — e.g. two distinct primitives, a function compared
    /// to a record, etc.
    Mismatch {
        /// The offending lhs type.
        lhs: Type,
        /// The offending rhs type.
        rhs: Type,
    },
    /// A record/tuple-on-record/tuple constraint required a field/position
    /// that lhs did not have. Width-subtyping says rhs's keys must be a
    /// subset of lhs's; this is the violation.
    MissingField {
        /// The key rhs demands and lhs does not carry. For a **positional** key
        /// this is the *widest* position demanded rather than the first absent one
        /// — see the tuple arm of [`constrain_go`] for why.
        key: FieldKey,
        /// The lhs record/tuple that should have contained the key.
        in_type: Type,
    },
    /// A variant-on-variant constraint had a tag in lhs that rhs did
    /// not accept. The dual of [`Self::MissingField`]: variant width-
    /// subtyping inverts records, so rhs's tag set must be a *super*set
    /// of lhs's, and the violation is an *extra* tag on lhs rather than a
    /// missing field.
    ExtraTag {
        /// The tag present in lhs but not accepted by rhs.
        tag: FieldKey,
        /// The rhs variant that should have accepted the tag.
        in_type: Type,
    },
    /// A non-feed type flowed into a [`Type::History`] requirement — e.g.
    /// a plain value passed to a function that feeds its parameter. The
    /// reverse direction is fine (a feed handle is transparently readable
    /// as its payload); only the write capability cannot be conjured from
    /// a plain value.
    NotAFeed {
        /// The non-feed type that was required to be a feed handle.
        found: Type,
        /// The feed type demanded.
        required: Type,
    },
    /// Two function types met whose kinds disagree: a compute function (a
    /// capability, `⇒`) where a data collection (`⤇`) is demanded, or the
    /// reverse. The kinds are incomparable, so neither direction is a legal
    /// coercion — a capability used as a collection would iterate a *declared*
    /// domain the value does not actually cover, and a collection used as a
    /// capability would lose the invariance its domain is typed under.
    KindMismatch {
        /// The supplied function.
        lhs: Type,
        /// The function demanded at the position.
        rhs: Type,
    },
    /// A type met a kind that does not admit it — the `𝑇 :: 𝐾` edge failing. Raised
    /// where the type side becomes known, which is the first moment the question has an
    /// answer: a `List(Int)` annotation demands `UIntRanges`, and a data source's domain
    /// is not a range.
    NotOfKind {
        /// The type that arrived.
        found: Type,
        /// The type kind the position requires it to inhabit.
        type_kind: TypeKind,
    },
    /// Two collections over domains that are not the same domain met at one
    /// position. A data domain is invariant (see
    /// `src/ccl/design/type-inference.md`, "Data domains are invariant"), so
    /// neither collection stands in for the other; their join is a Σ over the two
    /// candidate domains, which is not yet representable. The coalesce-time face
    /// of the same fact — reached when no edge forces the question earlier — is
    /// [`super::coalesce::CoalesceError::DomainJoinConflict`].
    DataDomainMismatch {
        /// The supplied collection's domain.
        lhs: Type,
        /// The domain demanded at the position.
        rhs: Type,
    },
    /// Collections over distinct domains met as **lower bounds** of one variable — the
    /// arms of a conditional flowing into one join.
    ///
    /// Distinct from [`DataDomainMismatch`](Self::DataDomainMismatch), which is a *demand*:
    /// there `rhs` is the domain a declaration or parameter requires and `lhs` is what was
    /// supplied, so "expected/found" is the sentence. Lower bounds are peers — no arm
    /// required anything of another — and reporting them as a demand picks one arbitrarily
    /// and calls it the requirement.
    ///
    /// The same fact reached at coalesce, when no edge forced the question first, is
    /// [`super::coalesce::CoalesceError::DomainJoinConflict`]. Both convert to one
    /// [`InferError`](crate::ccl::infer::InferError), so which phase noticed does not
    /// change what the user reads — it depends on an arm count and a domain shape, neither
    /// of which is visible in the source.
    DomainJoinConflict {
        /// The domains that have no common answer.
        domains: Vec<Type>,
    },
    /// An operand's type ruled out the last instance of a trait an operator
    /// requires — `1 > "a"`, or `\x -> x + 1` applied to a string.
    ///
    /// Raised from the bound-recording arm that delivered the offending type, so it
    /// fires the moment the program states the conflict rather than at a later phase
    /// that goes looking for it.
    NoTraitInstance {
        /// The trait with no instance left.
        trait_: Trait,
        /// The operand position whose type ruled the last one out.
        position: u8,
        /// The type that arrived there — a base no instance accepts, or a
        /// shape that is not a base at all.
        found: Type,
        /// What that position could still have accepted, given everything already
        /// known about the other operand.
        accepted: Vec<BaseType>,
    },
}

/// Cache of in-progress subtyping checks. Breaks cycles introduced through
/// variable bounds.
///
/// Keyed by the `(lhs, rhs)` pair *by value*. Identity at [`Type::Infer`] is
/// by `uid` (see [`InferVar`]), so this is cycle-safe (a recursive type's
/// graph re-enters through a shared `Infer`, whose hash/eq stop at the uid)
/// and de-dups structurally-equal constraints. Only var-involving pairs are
/// inserted; purely-structural constraints are finite trees that bottom out.
/// σ-aware: each visited `(lhs, rhs)` pair keeps the list of side-morphism
/// pairs it has been constrained under. The same pair under a *different*
/// morphism is a genuinely different constraint (e.g. two discharges of one
/// dependent codomain, `[k ↦ 0]` vs `[k ↦ 1]`) and must not be conflated;
/// the same pair under the *same* morphisms is the recursive/cyclic revisit
/// the cache exists to terminate. Termination: morphisms arising on cyclic
/// (var⇄var) edges are renames over the episode's finite binder set, whose
/// composites saturate; discharges ride acyclic content edges only (their
/// composites grow along lexical nesting depth, not around cycles).
pub struct ConstrainCache {
    edges: HashMap<(Type, Type), Vec<(Subst, Subst)>>,
    /// Which derivation this cache serves. The representation poses two questions
    /// and they do not have the same answer in all three
    /// (`src/ccl/design/type-inference.md`, "Where the conversions run").
    derivation: Derivation,
    /// **Γ for each side of the judgment** — what the witnesses in scope range over
    /// (`src/ccl/design/type-inference.md`, "The witness context").
    ///
    /// Two of them because the sides are two types with their own binders: a reference in
    /// `lhs` is classified by the Σs of `lhs`. Carried here rather than as parameters for the
    /// reason `compact_go` carries its refinement scope on the walk's state — the descent is
    /// already threading this, and every arm that does not bind pays nothing.
    ///
    /// **Swapped wherever the descent swaps the sides.** The domain edge relates `d1` to
    /// `d0`, so the contexts trade places with the substitutions.
    lctx: crate::ccl::ty::WitnessContext,
    rctx: crate::ccl::ty::WitnessContext,
}

/// The derivation a [`ConstrainCache`] serves: what the solver is doing when it
/// draws an edge, which is what those questions are answered against.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Derivation {
    /// Emission and its specialization pins — where a recorded bound becomes
    /// solved output.
    LiveSolve,
    /// A pass-boundary re-derivation over a whole tree: it reconciles types two
    /// passes spelled in different coordinates, but every binder the tree's
    /// refinements reference is a binder the walk itself can enter.
    PostPass,
    /// A probe over a sub-tree cut from its context: `debug_typecheck`'s
    /// per-operation check, its one caller. Its refinements reference binders the
    /// absent context holds, which no walk of the sub-tree can see, so the
    /// closure invariant is not a record-time error here. Planning's in-place
    /// checks of a morphism it has just built do not need the excuse: a
    /// morphism carries its own binder, so they take
    /// [`PostPass`](Self::PostPass), which enforces.
    SubTree,
}

impl Derivation {
    /// Whether every binder a reference in this derivation's types names is one the walk can
    /// enter — so a reference Γ does not classify is **free**.
    ///
    /// True over a self-contained tree, where free is a malformed type and the escape check
    /// reports it. A sub-tree probe cannot say it, and a refinement predicate is not the
    /// case that shows why: a predicate's type does bind the witnesses it names. **A
    /// Σ-typed lambda's parameter** is the case. Its type is a bare `WitnessRef`, and the
    /// sum that binds it rides the *lambda's* type rather than the parameter's
    /// (`crate::ccl::infer::debug_assert_no_free_witness`), so a cut anywhere inside the
    /// body leaves the index unclassifiable while the enclosing walk classifies it. The
    /// probe has no verdict to give there and gives none; the whole-tree walls decide. Same
    /// excuse, and the same reason, as [`enforces_closure`](Self::enforces_closure).
    pub(crate) fn sees_every_binder(self) -> bool {
        self != Derivation::SubTree
    }

    /// Whether bounds recorded through this derivation must close against the
    /// holder's telescope (`src/ccl/design/type-inference.md`, "The invariant").
    /// Every derivation over a self-contained tree does. Only a sub-tree probe
    /// is excused, because its absent context is what carries the binders.
    pub(crate) fn enforces_closure(self) -> bool {
        self != Derivation::SubTree
    }

    /// Whether a closed `Fun`/`Fun` codomain opens unconditionally rather than
    /// only toward a side carrying inference variables. A re-derivation is
    /// reconciling two passes' spellings of one type; the live solve is not, and
    /// opening a concrete pair at display names lets a free reference sharing a
    /// binder's spelling capture the reopened index.
    fn opens_unconditionally(self) -> bool {
        self != Derivation::LiveSolve
    }
}

impl ConstrainCache {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::for_derivation(Derivation::LiveSolve)
    }

    /// The cache for one of the re-derivations — see [`Derivation`] for what
    /// each one changes.
    pub fn for_derivation(derivation: Derivation) -> Self {
        Self {
            edges: HashMap::new(),
            derivation,
            lctx: crate::ccl::ty::WitnessContext::default(),
            rctx: crate::ccl::ty::WitnessContext::default(),
        }
    }

    /// The composite-substitution bridges recorded for a subtyping edge,
    /// inserting an empty list on first visit. This is the cycle breaker: a
    /// re-entry on the same `(lhs, rhs)` pair finds its in-progress entry rather
    /// than recursing forever.
    fn edge_bridges(&mut self, lhs: Type, rhs: Type) -> &mut Vec<(Subst, Subst)> {
        self.edges.entry((lhs, rhs)).or_default()
    }

    /// Start both sides' Γ from `ctx` — for a caller that knows what encloses the types it
    /// is relating, which an edge drawn between parts of a tree does and this cache cannot.
    pub fn seed_context(&mut self, ctx: &crate::ccl::ty::WitnessContext) {
        self.lctx = ctx.clone();
        self.rctx = ctx.clone();
    }

    /// Run `f` under each side's Γ extended by that side's binders — the judgment made
    /// inside a Σ is made under what the Σ binds.
    fn under<R>(
        &mut self,
        lhs: &[crate::ccl::ty::Witness],
        rhs: &[crate::ccl::ty::Witness],
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let (l, r) = (self.lctx.clone(), self.rctx.clone());
        self.lctx = l.extended(lhs);
        self.rctx = r.extended(rhs);
        let out = f(self);
        self.lctx = l;
        self.rctx = r;
        out
    }

    /// Run `f` with the two sides traded, for a descent that relates them the other way
    /// round — the contravariant domain edge, which already swaps the substitutions.
    fn swapped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        std::mem::swap(&mut self.lctx, &mut self.rctx);
        let out = f(self);
        std::mem::swap(&mut self.lctx, &mut self.rctx);
        out
    }
}

/// Cache for [`extrude`], keyed by the polar pair (variable uid, polarity).
///
/// Each polarity gets its own extruded copy so positive and negative
/// occurrences of the same variable can be approximated independently
/// (see Parreaux 2020 §3.4).
pub type ExtrudeCache = HashMap<(InferVarId, bool), Rc<InferVar>>;

/// Constrain `lhs <: rhs`, mutating variable bounds in place.
///
/// The cache argument breaks cycles; pass a fresh empty `HashSet` at
/// the top of each constraint emission and reuse it for the recursive
/// subtyping the rule fires.
pub fn constrain_subtype(
    lhs: &Type,
    rhs: &Type,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    constrain_go(lhs, rhs, &Subst::id(), &Subst::id(), cache)
}

/// [`constrain_subtype`], with both sides judged **under `binders`**.
///
/// For an edge drawn between parts of a type the caller has already taken apart: a function's
/// domain compared on its own is a reference stripped of the Σ that classifies it, so the
/// caller that still holds the function says what binds it
/// (`src/ccl/design/type-inference.md`, "The witness context").
pub fn constrain_subtype_under(
    lhs: &Type,
    rhs: &Type,
    lhs_binders: &[crate::ccl::ty::Witness],
    rhs_binders: &[crate::ccl::ty::Witness],
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // **The right side's binders are instantiated by the left.** A caller relating a value
    // to a shape written over binders — an application's argument against the domain it
    // lands in — is instantiating those binders, and the instance is the left side. Reading
    // the instantiation off the two types is what puts both sides in one spelling, so the
    // reference comparison below is name equality rather than two unrelated names.
    let instantiation = witness_instantiation(rhs, lhs, rhs_binders);
    cache.under(lhs_binders, rhs_binders, |cache| {
        constrain_go(lhs, rhs, &Subst::id(), &instantiation, cache)
    })
}

/// The renaming that instantiates `pattern`'s binders from `instance`, by walking the two
/// together: wherever the pattern names one of `binders`, the instance says what it is.
///
/// Structural and partial. A position the two do not share contributes nothing — the
/// comparison then reports the disagreement it is there to report — and a binder the pattern
/// never names is left alone, since nothing instantiated it.
fn witness_instantiation(
    pattern: &Type,
    instance: &Type,
    binders: &[crate::ccl::ty::Witness],
) -> Subst {
    fn go(pattern: &Type, instance: &Type, binders: &[crate::ccl::ty::WitnessId], out: &mut Subst) {
        if let Type::WitnessRef(p) = pattern {
            if binders.contains(p)
                && let Type::WitnessRef(i) = instance
                && p != i
            {
                *out = out.extended_witness_rename(p, i);
            }
            return;
        }
        // One frame per constructor pair, so only positions the two share are visited.
        match (pattern, instance) {
            (
                Type::Fun {
                    domain: pd,
                    codomain: pc,
                    ..
                },
                Type::Fun {
                    domain: id,
                    codomain: ic,
                    ..
                },
            ) => {
                go(pd, id, binders, out);
                go(pc, ic, binders, out);
            }
            (Type::Tuple(ps), Type::Tuple(is)) => {
                for (p, i) in ps.iter().zip(is) {
                    go(p, i, binders, out);
                }
            }
            (Type::Record(ps), Type::Record(is)) => {
                for (name, p) in ps {
                    if let Some((_, i)) = is.iter().find(|(n, _)| n == name) {
                        go(p, i, binders, out);
                    }
                }
            }
            (Type::Refinement(pb, _), _) => go(pb, instance, binders, out),
            (_, Type::Refinement(ib, _)) => go(pattern, ib, binders, out),
            _ => {}
        }
    }
    let ids: Vec<crate::ccl::ty::WitnessId> = binders.iter().map(|w| *w.id()).collect();
    let mut out = Subst::id();
    go(pattern, instance, &ids, &mut out);
    out
}

/// Relate two function kinds by **recording the edge**, and nothing else.
///
/// Whether the two are compatible, how many binders each is over, and what those binders
/// range over are all read off the bounds once the kind graph is closed — not decided here,
/// where a kind may not have been reached yet. The binder correspondence between them is
/// derived then too, for the same reason: its positions do not exist until an arity does.
///
/// A concrete pair is the one thing settled at the edge, since neither side can learn
/// anything later: two kinds that denote different points of the lattice have no common
/// function, whichever side is which.
fn constrain_fun_kind(
    k0: &FunKind,
    k1: &FunKind,
    lhs: &Type,
    rhs: &Type,
) -> Result<(), ConstrainError> {
    let mismatch = || ConstrainError::KindMismatch {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
    };
    match (k0, k1) {
        // **Two variables meeting are one kind**, so the edge is recorded on both: the
        // lattice is flat, an edge fixes a variable rather than bounding it, and which side
        // a fact arrived on says nothing about which variable it is about
        // (`src/ccl/design/type-inference.md`, "Consuming a sum: pinning the consumer's
        // kind"). Recording one side leaves the other reading nothing, so a pin that
        // reaches either end after the edge is drawn never crosses it.
        (FunKind::Var(v0), FunKind::Var(v1)) => {
            v0.record(k1.clone(), false);
            v1.record(k0.clone(), true);
        }
        (FunKind::Var(v), other) | (other, FunKind::Var(v)) => {
            v.record(other.clone(), matches!(k1, FunKind::Var(_)));
        }
        // Both concrete: a capability is not a collection, a plain collection is not a sum —
        // entering one is a term — and two sums of different width are two types. Nothing
        // arriving later can change any of that.
        _ if k0.resolved() == k1.resolved() => return Ok(()),
        _ => return Err(mismatch()),
    }
    // **A kind required to be two points is rejected at the edge that completed it.** A
    // consumer is minted pinned `Data` ([`FunKind::fresh_data`]), so a capability reaching
    // one is this rejection — the same one a concrete pair is, reported where both sides can
    // still be named rather than left for coalesce, which reaches a conflicted variable only
    // where some position happens to materialize from it.
    //
    // **However many variables lie between the two ends.** [`FunKindVar::resolved`] folds the
    // whole component, so one contribution settles nothing and a variable in the middle
    // hides nothing: the question this asks is the same question at every edge. What the
    // arms above must not do is *copy* one side's point onto the other — that answers from
    // the points that happen to have arrived and drops every one that arrives later, which
    // is why the edge is recorded and the join taken at the read.
    //
    // Reading it here is sound because `Conflict` **absorbs** in [`KindPin::join`] and
    // contributions are only ever appended, so a component that has reached it can never
    // leave, and the first edge to observe it is the one that completed it.
    if k0.resolved() == KindPin::Conflict || k1.resolved() == KindPin::Conflict {
        return Err(mismatch());
    }
    Ok(())
}

/// Bridge the holder gap when chaining two edges through one variable.
///
/// A lower entry `L‹σ_L› <: V‹lo›` and an upper entry `V‹hi› <: U‹σ_U›`
/// relate *different views* of `V` unless `lo == hi`. Transitivity needs the
/// two views reconciled; the returned bridge `(τ_L, τ_U)` is composed onto the
/// lower and upper **content** sides respectively, yielding the closure edge
/// `L‹τ_L∘σ_L› <: U‹τ_U∘σ_U›`.
///
/// The bridge moves whichever side is movable — substitution application is
/// monotone w.r.t. subtyping, so applying one morphism to *both* sides of an
/// edge preserves it:
/// - equal morphisms need no bridge (covers two entries that arrived under
///   the *same* discharge);
/// - an invertible `lo` (identity or rename) moves the lower into the upper's
///   frame: `τ_L = hi ∘ lo⁻¹` — the common case;
/// - otherwise an invertible `hi` moves the upper into the lower's frame:
///   `τ_U = lo ∘ hi⁻¹` (e.g. a discharge-bearing lower meeting an ordinary
///   upper — a discharge lands on a holder side at every contravariant edge
///   swap — where `V <: U` and `L <: V‹[x↦0]›` derive `L <: U‹[x↦0]›`);
/// - two *distinct non-invertible* morphisms meeting at one variable is the
///   unhandled domain-join corner (O1/O4) — `invert_rename` is its loud
///   tripwire.
fn bridge_holder_gap(lo: &Subst, hi: &Subst) -> (Subst, Subst) {
    if lo == hi {
        return (Subst::id(), Subst::id());
    }
    // Reconcile on the LICENSED CORRESPONDENCE VIEWS: Var-target discharges
    // read as correspondences into the outer scope, under the monomorphic
    // license documented at `Subst::licensed_correspondence_view` (the only
    // species override anywhere). Species elsewhere stay caller-declared, so
    // when the license expires with polymorphic fibers, deleting the view
    // re-arms the tripwire below for exactly the sites that depended on it.
    let lo = &lo.licensed_correspondence_view();
    let hi = &hi.licensed_correspondence_view();
    if let Some(lo_inv) = lo.invert() {
        return (Subst::then(&lo_inv, hi), Subst::id());
    }
    if let Some(hi_inv) = hi.invert() {
        return (Subst::id(), Subst::then(&hi_inv, lo));
    }
    // Both composites are non-invertible. Factor each into its rename part
    // and its term (discharge) part: when the term parts agree — the common
    // shape, two views of ONE instantiation reached through different routes —
    // the gap is purely a rename gap, bridged on whichever side inverts. The
    // routes arise without any dependent types in play: every application
    // mints its discharge edge unconditionally (vacuous when the codomain is
    // non-dependent), composition faithfully records its action on
    // intermediate binders (§3.6), and extrude's level-crossing proxies and
    // specialization clones copy bound lists — so one variable
    // receives the same content under composites that differ only in which
    // fresh expected binders and correspondences each route threaded. Such
    // entries are inert on all content (nothing references the minted
    // binders); reconciling them is bookkeeping, not semantics. The extra
    // composite entries the bridge result carries are likewise inert on
    // content that doesn't mention the intermediate binders free (the §3.6
    // freshness discipline).
    let (lo_ren, lo_term) = lo.split_renames();
    let (hi_ren, hi_term) = hi.split_renames();
    // Term parts compare modulo type slots: a discharge captures its argument
    // at emit time with freshly-minted inference-var slots, so two captures of
    // the SAME argument can differ in slots while denoting the same term
    // (`Subst::eq_modulo_ty_slots`). Strict `==` here would shunt a sound
    // same-fiber meeting into the tripwire below.
    if lo_term.eq_modulo_ty_slots(&hi_term) {
        if let Some(lo_ren_inv) = lo_ren.invert() {
            return (Subst::then(&lo_ren_inv, &hi_ren), Subst::id());
        }
        if let Some(hi_ren_inv) = hi_ren.invert() {
            return (Subst::id(), Subst::then(&hi_ren_inv, &lo_ren));
        }
    }
    // Last resort before declaring the morphisms genuinely different: equal
    // up to type slots as WHOLES (two captures of one fiber whose rename
    // parts also coincide) bridges as the same view.
    if lo.eq_modulo_ty_slots(hi) {
        return (Subst::id(), Subst::id());
    }
    // Two *distinct* non-invertible morphisms meeting at one variable: bounds
    // constraining different fibers (of one family — g(0) vs g(1) — or of two
    // unrelated families), between which no sound transport exists. This is the
    // domain-join corner (O1/O4): the two fibers are distinct domains of one data
    // family, which is exactly the join a `Data` kind refuses to narrow. No
    // reachable program produces this shape, so reaching it means a solver bug —
    // refuse loudly rather than corrupt the edge.
    panic!(
        "closure bridge: two distinct non-invertible morphisms met at one \
         variable (domain-join corner, O1/O4): lo={lo:?}, hi={hi:?}"
    );
}

/// The **uniquely-keyed** invariant the record and variant arms rest on, checked
/// where they rest on it.
///
/// Both arms look a key up with `iter().find(..)` — *first* match wins — so on a
/// duplicate-keyed product the answer depends on which copy comes first, and the
/// arm disagrees with `constrain_go`'s own trivial-equality short-circuit: the
/// short-circuit accepts `𝑡 <: 𝑡` while find-first demands cross-subtyping
/// between the duplicates and rejects it. Whether a type is a subtype of itself
/// would then depend on whether the two sides happened to be structurally
/// identical.
///
/// Nothing in `Type` enforces uniqueness — `Record(Vec<(String, Type)>)` admits
/// duplicates and the builders merely happen not to produce them — so this is a
/// real invariant that is not type-enforced, which is where a `debug_assert`
/// earns its keep. `dup_key_record_trips_the_uniquely_keyed_invariant` pins that
/// this assert fires, so the guard cannot rot into a no-op.
///
/// No program in the suite trips it, so the invariant does hold across the
/// pipeline today; what changes is that a builder which starts violating it fails
/// loudly instead of silently making subtyping depend on incidental structure.
///
/// Debug-only and shallow: it checks the type's own key list, not its payloads,
/// since recursion reaches every nested product on its own.
#[cfg(debug_assertions)]
fn debug_assert_unique_product_keys(t: &Type) {
    match t {
        Type::Record(fs) => debug_assert_unique_keys(fs.iter().map(|(n, _)| n), "record", t),
        Type::Variant(tags, _) => {
            debug_assert_unique_keys(tags.iter().map(|(k, _)| k), "variant", t)
        }
        _ => {}
    }
}

#[cfg(not(debug_assertions))]
fn debug_assert_unique_product_keys(_t: &Type) {}

#[cfg(debug_assertions)]
fn debug_assert_unique_keys<'a, K: Eq + std::fmt::Debug + 'a>(
    keys: impl Iterator<Item = &'a K>,
    what: &str,
    in_type: &Type,
) {
    let keys: Vec<&K> = keys.collect();
    for (i, k) in keys.iter().enumerate() {
        debug_assert!(
            !keys[..i].contains(k),
            "duplicate {what} key {k:?} in {in_type}: find-first lookup makes the \
             uniquely-keyed invariant load-bearing here, and the trivial-equality \
             short-circuit disagrees with it on `t <: t`"
        );
    }
}

/// Two lower bounds that are **collections over distinct domains**, if the set contains
/// any such pair.
///
/// Their join is a sum, and a sum is entered by a term — so with no subtyping edge into one, there
/// is no type above both, and the author has to say which arms are boxed. Reported here
/// rather than left to the pointwise fallback because that fallback relates each
/// collection to the consumer separately, which is the silent narrowing a lossless data
/// join rules out, and which does not terminate.
fn distinct_data_domains(lows: &[Bound]) -> Option<(Type, Type)> {
    let mut seen: Vec<Type> = Vec::new();
    for low in lows {
        let Type::Fun {
            fun_kind: FunKind::Data(..),
            domain,
            ..
        } = &low.ty
        else {
            continue;
        };
        // A **witness-indexed** collection joins losslessly — its sum keeps every
        // domain — so it is not a party to this conflict. A domain that is not yet a
        // concrete type is not one either: invariance between variable-involving
        // domains is decided at materialization, in the compact domain lattice
        // (`src/ccl/design/type-inference.md`, "Materialization").
        if low.ty.sum().is_some() {
            continue;
        }
        let d = low.ty_subst.apply_type(domain);
        if matches!(d, Type::WitnessRef(_) | Type::Infer(_)) {
            continue;
        }
        if let Some(prev) = seen.iter().find(|p| **p != d) {
            return Some((prev.clone(), d));
        }
        if !seen.contains(&d) {
            seen.push(d);
        }
    }
    None
}

/// Answer each type kind recorded on `𝛼` against everything recorded below it.
///
/// A kinding edge is answerable the moment its *type* side is known, and a variable's lower
/// bounds are where a type arrives at it. So this runs where a lower is recorded and where a
/// kind is, and asks the same question from both — whichever arrives second is the one that
/// completes the pair.
///
/// A lower that is itself a variable **inherits** the edge rather than answering it. The
/// constraint is a conjunction with no polarity of its own (`src/ccl/design/type-inference.md`,
/// "An unresolved candidate becomes a kinding edge"), so it travels down every path a type
/// could arrive by, and is answered wherever one does.
///
/// **The peel finds the variable; the kind reads the type whole.** Refinements come off to see
/// whether a lower is a variable, because a kind recorded on `{𝛼 | 𝑝}` is a demand on `𝛼`. The
/// membership question is a different one and gets the unpeeled type, since a refined type is
/// not the type it refines (`candidate_in_kind` says the same of a candidate) — one scrutinee
/// answering both is how a refined range came to pass here and be refused at coalesce.
pub(super) fn answer_type_kinds(v: &Rc<InferVar>) -> Result<(), ConstrainError> {
    let (lows, kinds) = {
        let b = v.bounds.borrow();
        (Rc::clone(b.lower()), b.type_kinds.clone())
    };
    if kinds.is_empty() || lows.is_empty() {
        return Ok(());
    }
    for k in &kinds {
        for low in lows.iter() {
            match low.ty.peel_refinements() {
                Type::Infer(w) => {
                    let mut b = w.bounds.borrow_mut();
                    if !b.type_kinds.contains(k) {
                        b.type_kinds.push(k.clone());
                    }
                }
                // Only a *certain* non-member is an error: the kind abstains wherever the
                // type is still open, and this runs while types are arriving.
                _ if k.refuses(&low.ty) => {
                    return Err(ConstrainError::NotOfKind {
                        found: low.ty.clone(),
                        type_kind: k.clone(),
                    });
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// The **kind premise** of the Σ rule: is every type `sub` admits also admitted by `sup`?
///
/// A type kind is a type of types, and containment holds when every type `sub` classifies
/// `sup` classifies too — no variance, and no case per pair. What differs between the four is
/// only how each *states* which types it classifies, and that is
/// what decides whether a membership question is answered here or drawn as an edge
/// ([`candidate_in_kind`]).
///
/// **Both sides' fun kinds must state a type kind**, which is why the caller asks
/// [`FunKind::sum_binders`] rather than reading one off a variable. A fun kind variable states
/// none, and deriving one from what has reached the variable so far gives an answer that moves
/// as the solve proceeds — it widens as arms arrive, and narrows the moment the first arm
/// displaces a demand from above. A verdict against it would depend on when the edge was
/// drawn. This is the same reason [`constrain_fun_kind`] records against a variable instead of
/// deciding.
fn constrain_type_kinds(
    sub: &TypeKind,
    sup: &TypeKind,
    sl: &Subst,
    sr: &Subst,
    lhs: &Type,
    rhs: &Type,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    let mismatch = || ConstrainError::Mismatch {
        lhs: lhs.clone(),
        rhs: rhs.clone(),
    };
    match (sub, sup) {
        // The universe admits every domain, so nothing is left to ask.
        (_, TypeKind::Type) => Ok(()),
        // Candidates are members, so containment is membership, once per member.
        (TypeKind::Enumerated(subs), _) => {
            for d in subs {
                candidate_in_kind(d, sup, sl, sr, lhs, rhs, cache)?;
            }
            Ok(())
        }
        // **Two bounds are ordered by their bounds.** Every domain below `a` is below `b`
        // exactly when `a <: b`, which is one ordinary covariant edge — and the edge is
        // what determines an unannotated `b`.
        (TypeKind::SubtypesOf(a), TypeKind::SubtypesOf(b)) => constrain_go(a, b, sl, sr, cache),
        (TypeKind::UIntRanges, TypeKind::UIntRanges) => Ok(()),
        // A kind that names no members offers none to place in the kind above it, so nothing
        // relates it upward: the universe, every `UIntRange`, and every type below a key
        // type name three incomparable sets, and none of them sits inside a set of named
        // candidates.
        (TypeKind::Type | TypeKind::UIntRanges | TypeKind::SubtypesOf(_), _) => Err(mismatch()),
    }
}

/// Is `d` — one candidate of `sub` — a member of `sup`?
///
/// One answer per type kind, because how each states which types it classifies is what the
/// question turns on:
///
/// * [`TypeKind::Enumerated`] names its members, so membership is type equality. A candidate
///   *is* a domain and data domains are invariant ([Data domains are
///   invariant](`src/ccl/design/type-inference.md`)), so a refined range is a different
///   candidate from the range it refines, in either direction.
/// * [`TypeKind::SubtypesOf`] names its members by a type, so membership is an ordinary
///   subtyping edge — and the parameter is the one place information can flow *in*, which is
///   what lets `Map(_, 𝑉)` take its key from the domains that reach it. Deciding this
///   structurally instead would answer "an undecided bound admits anything" and the key
///   would be determined by nothing.
/// * [`TypeKind::UIntRanges`] and [`TypeKind::Type`] state a property of their members and
///   name none, so membership is structural — [`TypeKind::refuses`], asked on `d` whole,
///   since a refined type is not the type it refines.
///
/// A candidate that is still a **variable** has no shape to read a property off, so it takes
/// the kinding edge `𝛼 :: 𝐾` and is answered wherever a type reaches it
/// ([`answer_type_kinds`]).
#[allow(clippy::too_many_arguments)]
fn candidate_in_kind(
    d: &Type,
    sup: &TypeKind,
    sl: &Subst,
    sr: &Subst,
    lhs: &Type,
    rhs: &Type,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    match sup {
        TypeKind::SubtypesOf(b) => constrain_go(d, b, sl, sr, cache),
        TypeKind::Enumerated(sups) if sups.contains(d) => Ok(()),
        TypeKind::Enumerated(_) => Err(ConstrainError::Mismatch {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }),
        TypeKind::UIntRanges | TypeKind::Type => match d {
            Type::Infer(v) => {
                {
                    let mut b = v.bounds.borrow_mut();
                    if !b.type_kinds.contains(sup) {
                        b.type_kinds.push(sup.clone());
                    }
                }
                answer_type_kinds(v)
            }
            _ if sup.refuses(d) => Err(ConstrainError::NotOfKind {
                found: d.clone(),
                type_kind: sup.clone(),
            }),
            _ => Ok(()),
        },
    }
}

fn constrain_go(
    lhs: &Type,
    rhs: &Type,
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // Checked *before* the short-circuit, deliberately: the case the two
    // disagree on is `𝑡 <: 𝑡` itself, which the short-circuit would answer and
    // return before any arm looked at the keys.
    debug_assert_unique_product_keys(lhs);
    debug_assert_unique_product_keys(rhs);

    // Structural descent over two types at once, one frame per constructor pair;
    // grow on demand as the other deep walks do.
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        constrain_go_impl(lhs, rhs, sl, sr, cache)
    })
}

fn constrain_go_impl(
    lhs: &Type,
    rhs: &Type,
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // The trivial-equality short-circuit is only sound when the edge carries
    // no transformation — under non-identity morphisms `lhs` and `rhs` live
    // in different contexts even when structurally equal.
    if sl.is_id() && sr.is_id() && lhs == rhs {
        return Ok(());
    }

    // Cycle-break: only constraints involving variables can recur.
    // Non-variable structural types are regular trees; their constraints
    // bottom out without revisiting themselves. Key by value — identity at
    // `Infer` is by `uid`, so this is cycle-safe. The side morphisms ARE part
    // of the visited state: the same pair under different morphisms is a
    // different constraint (see `ConstrainCache`).
    let either_var = matches!(lhs, Type::Infer(_)) || matches!(rhs, Type::Infer(_));
    if either_var {
        let seen = cache.edge_bridges(lhs.clone(), rhs.clone());
        // Morphisms compare modulo emit-time type slots — the SAME notion of
        // constraint identity the closure bridge uses (`eq_modulo_ty_slots`).
        // Strict `==` here would admit a near-duplicate edge (two captures of
        // one fiber differing only in minted slots) that the bridge would then
        // immediately reconcile as same-fiber: wasted edges and traversal, and
        // two components disagreeing about what "the same constraint" means.
        if seen
            .iter()
            .any(|(a, b)| a.eq_modulo_ty_slots(sl) && b.eq_modulo_ty_slots(sr))
        {
            return Ok(());
        }
        seen.push((sl.clone(), sr.clone()));
    }

    match (lhs, rhs) {
        // Leaf types match by structural equality.
        (Type::Base(a), Type::Base(b)) if a == b => Ok(()),
        (Type::UIntRange(a), Type::UIntRange(b)) if a == b => Ok(()),
        (Type::DataSource(a), Type::DataSource(b)) if a == b => Ok(()),
        // a channel's nominal domain is reflexively equal to
        // itself (the common read-vs-read case short-circuits here).
        (Type::ChanDom(a, _), Type::ChanDom(b, _)) if a == b => Ok(()),
        // `Txn` is a nullary leaf: reflexively equal to itself, incomparable
        // to every other type (the catch-all `Mismatch` below).
        (Type::Txn, Type::Txn) => Ok(()),

        // Function: contravariant on domain, covariant on codomain. The
        // codomain edge *derives* the binder correspondence — aligning the two
        // Pi binders `k ↦ x` — and carries it onward (design §3.6); the domain
        // edge flips with the polarity by **swapping the two sides'
        // morphisms** — no inversion, so a discharge crosses a domain edge
        // intact. When neither side is a Pi (both names `None`) the
        // correspondence is unchanged, so this is exactly the ordinary
        // contravariant/covariant rule.
        (
            Type::Fun {
                name: n0,
                fun_kind: k0,
                domain: d0,
                codomain: c0,
            },
            Type::Fun {
                name: n1,
                fun_kind: k1,
                domain: d1,
                codomain: c1,
            },
        ) => {
            // The kind edge (see [`constrain_fun_kind`]): recorded, not answered. What the two
            // kinds turn out to be, and how their binders correspond, is read once the kind
            // graph is closed.
            constrain_fun_kind(k0, k1, lhs, rhs)?;
            // **Binders correspond by position across this edge.** A sum's binders are its
            // kind's positions, so position `i` of one side is position `i` of the other,
            // and the edge carries that correspondence in its own substitution — the Σ
            // analog of the Pi binder rename below. Unlike a Pi binder a Σ binder scopes
            // over the *domain* as well, so it is in hand before the domain edge, not only
            // the codomain one.
            //
            // [`FunKind::named_binders`], not `bound_witnesses`: every bound this edge goes
            // on to record carries the rename, and a bound outlives the walk that drew it.
            // A position answers with the one name it settles to, so what lands in the
            // graph is an ordinary binder — nothing that has to be reconciled later, and
            // nothing naming a kind variable a freshening could copy out from under it.
            //
            // What each side's fun kind states, so one that has not resolved to a sum
            // states nothing and the edge is the ordinary function rule.
            // **The kind premise**, per binder position, at every derivation. Asked of the
            // type kinds the two fun kinds *state* — a variable states none, and a verdict
            // against a derived type kind would depend on when the edge was drawn
            // ([`constrain_type_kinds`]).
            //
            // A check runs the same rule as the solve, because a check that asks a weaker
            // question is not checking. Containment needs nothing recorded to answer
            // between two settled kinds: the arms that would record take a variable, and a
            // settled tree has none. What a check must not do is *decide* a kind, and this
            // does not — it reads what each side states.
            if let (Some(w0), Some(w1)) = (k0.sum_binders(), k1.sum_binders()) {
                for (a, b) in w0.iter().zip(w1.iter()) {
                    constrain_type_kinds(&a.type_kind(), &b.type_kind(), sl, sr, lhs, rhs, cache)?;
                }
            }
            let corresponding;
            let sl = {
                // **Identities, so a variable-kinded consumer gets a correspondence too.**
                // The consumer of a sum is a sum ("Consuming a sum: pinning the consumer's
                // kind"), but its kind is a variable that states no *range* until compaction
                // derives one — while its binder identities exist from the moment its arity
                // does. Asking for stated binders here leaves a variable contributing none,
                // no rename is drawn, and the domain premise then compares an arm's witness
                // against the consumer's raw domain as though the two were one domain rather
                // than corresponding binders of two sums.
                let (b0, b1) = (k0.binder_ids(), k1.binder_ids());
                if b0.is_empty() || b1.is_empty() {
                    sl
                } else {
                    corresponding = b0
                        .iter()
                        .zip(b1.iter())
                        .fold(sl.clone(), |acc, (a, b)| acc.extended_witness_rename(a, b));
                    &corresponding
                }
            };
            // **Invariance is a property of the data-domain position**, so it is asked of
            // the position. A kind nothing has reached yet is not known to be a collection,
            // and the reverse obligation a variable's domain owes is discharged where every
            // contribution to it meets.
            let invariant_domains = k0.resolved().is_data() || k1.resolved().is_data();
            let cod_sl = match (n0, n1) {
                (Some(k), Some(x)) => sl.extended_rename(k, x),
                _ => sl.clone(),
            };
            // Descent opens (`src/ccl/design/type-inference.md`, "Where the
            // conversions run"): a *closed* codomain — one whose refinements
            // reference this function's binder as indices — opens at its own
            // binder name before the edge decomposes it, so the bounds
            // recorded on inner variables are name-spelled against their
            // telescopes and the correspondence above applies to them.
            //
            // On the live solve, opening is gated on the **opposite** side
            // carrying inference variables: only a live side records
            // bounds, so only there would a dangling index land. A concrete
            // closed-closed pair compares index-to-index instead — opening it
            // at display names would let an unrelated *free* reference that
            // happens to share the binder's spelling capture the reopened
            // index (found by the differential oracle; with uniquified
            // binders the collision needs the same uid, which *is* the same
            // binder, but the concrete relation must not depend on that
            // convention). A post-pass re-derivation opens unconditionally: it
            // reconciles types that different passes spelled in different
            // forms (a closed function's codomain against a rebuilt,
            // discharged one). Which derivation this is
            // ([`Derivation`]) answers both this and the record sites'
            // question, so the two read one field rather than two flags.
            // The pre-scan keeps the common codomain that does not reference
            // this function untouched — the same dependence test descent and
            // application ask everywhere else.
            let open = |n: &Option<Name>, c: &Type, other: &Type| -> Option<Type> {
                // An unnamed function whose codomain references it by index has no
                // binder to open at, so the reference reaches the codomain edge and
                // compares against the other side's name — a mismatch reported as a
                // type error rather than as the malformed input it is. The same
                // tripwire guards `subst::open_codomain`, the rebuild passes' entry
                // to this conversion. A binder dropped off a closed function arms it:
                // `Type::without_pi_names`, or a pass rebuilding a `Fun` and filtering
                // the name slot.
                debug_assert!(
                    n.is_some() || !crate::ccl::subst::references_enclosing_function(c),
                    "an unnamed function's codomain references it: the index has no \
                     binder to open at, so the codomain edge compares an index \
                     against a name",
                );
                match n {
                    Some(b)
                        if crate::ccl::subst::references_enclosing_function(c)
                            && (cache.derivation.opens_unconditionally()
                                || crate::ccl::subst::type_contains_infer(other)) =>
                    {
                        Some(crate::ccl::subst::open_pi_binder(
                            &crate::ccl::subst::Mapping::Rename(b.clone()),
                            c,
                        ))
                    }
                    _ => None,
                }
            };
            let c0_opened = open(n0, c0, c1);
            let c1_opened = open(n1, c1, c0);
            // The domain edge. A *compute* domain is contravariant: it is a
            // parameter, nothing can enumerate it, and accepting more inputs than
            // demanded only under-promises. A **data** domain is *invariant* — it is
            // the loop bound op-conversion emits and it reappears in every
            // consumer's result, so narrowing or widening it changes which rows the
            // consumer reads (`src/ccl/design/type-inference.md`, "Data domains are
            // invariant").
            //
            // Between concrete domains the invariance is an equation — both edges. A
            // domain edge with a variable on either side records its bound in the
            // native direction and asserts no equation: n arm domains reaching one
            // consumer's domain variable satisfy the invariant without being equal
            // to each other, and the reverse obligation is discharged at
            // materialization, where every contribution to the variable meets in
            // the compact domain lattice (`src/ccl/design/type-inference.md`,
            // "Materialization"). Whether a side is a variable is a property of the
            // edge, not of when it fires, so both spellings stay order-independent.
            //
            // The kind edge above reports which rule its two sides call for, so
            // this asks one question rather than inspecting both spellings — a var
            // it just pinned to `Data` counts as a collection here like any other.
            // **The body is judged under what this function binds.** Both the domain and the
            // codomain sit inside a Σ's binders, so Γ gains them for the descent and loses
            // them on the way out (`src/ccl/design/type-inference.md`, "The witness
            // context").
            let (b0, b1) = (k0.named_binders(), k1.named_binders());
            cache.under(&b0, &b1, |cache| {
                if invariant_domains {
                    // Swapped with the substitutions: this edge relates the sides the other
                    // way round, and a reference in `d1` is classified by `d1`'s binders.
                    let ok = cache.swapped(|cache| constrain_go(d1, d0, sr, sl, cache).is_ok())
                        && (matches!(**d0, Type::Infer(_))
                            || matches!(**d1, Type::Infer(_))
                            || constrain_go(d0, d1, sl, sr, cache).is_ok());
                    if !ok {
                        return Err(ConstrainError::DataDomainMismatch {
                            lhs: (**d0).clone(),
                            rhs: (**d1).clone(),
                        });
                    }
                } else {
                    cache.swapped(|cache| constrain_go(d1, d0, sr, sl, cache))?;
                }
                constrain_go(
                    c0_opened.as_ref().map_or(&**c0, |c| c),
                    c1_opened.as_ref().map_or(&**c1, |c| c),
                    &cod_sl,
                    sr,
                    cache,
                )
            })
        }

        // (Two sums are related by the function arm above and nothing else: the width
        // premise rides it as [`constrain_type_kinds`], and there is no arm that enters a
        // sum (a sum is introduced by `box`, a term) or eliminates one (a sum reaches a
        // consumer by pinning its kind variable, never by subsumption) —
        // `src/ccl/design/type-inference.md`, "Subtyping for sums". No arm here dispatches
        // on the kind, which is why a new kind needs no new arm: containment is the only
        // kind-dependent question, and it is asked in one place.)

        // Tuple: positional width-subtyping. A longer/equal tuple is a
        // subtype, so every position rhs requires must exist in lhs.
        (Type::Tuple(a), Type::Tuple(b)) => {
            for (i, t1) in b.iter().enumerate() {
                match a.get(i) {
                    Some(t0) => constrain_go(t0, t1, sl, sr, cache)?,
                    None => {
                        // A `Tuple` is **dense**, so the failure here is one of *width*
                        // and the widest position rhs demands is its sharpest witness —
                        // report that rather than the first absent one, which is just
                        // `lhs`'s own width restated. This is what makes a positional
                        // projection diagnosable: `t.99` requires a 100-wide tuple, so
                        // the demand a 3-tuple fails is `.99`, not `.3`.
                        return Err(ConstrainError::MissingField {
                            key: FieldKey::Index(b.len() - 1),
                            in_type: lhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // Record: named width-subtyping. rhs's fields must all appear in lhs.
        (Type::Record(a), Type::Record(b)) => {
            for (name, t1) in b {
                match a.iter().find(|(n, _)| n == name) {
                    Some((_, t0)) => constrain_go(t0, t1, sl, sr, cache)?,
                    None => {
                        return Err(ConstrainError::MissingField {
                            key: FieldKey::Name(SmolStr::from(name.as_str())),
                            in_type: lhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // **A reference denotes a runtime choice, so two of them relate by identity.**
        // `σ` means "whichever domain `σ` turned out to be", and two binders are two
        // independent choices — so one is below the other only when they are the same
        // binder. Comparing their *kinds* instead would make two collections over the same
        // candidates interchangeable when the program picked differently.
        //
        // Two sums therefore have *corresponding* binders, never identical ones, and the
        // correspondence rides this edge's substitutions ([`Subst::apply_witnesses`])
        // exactly as a Pi binder's does. Reaching here uncorresponded is two domains where
        // one was demanded.
        //
        // **One rule for the solve and the check**
        // (`src/ccl/design/type-inference.md`, "One rule for the solve and the check").
        // Two derivations of one consumption need not have
        // agreed on a name — a comprehension's result binds its own index and the collection
        // it iterates binds that collection's, and the two are one index — so the
        // correspondence is what brings them into one spelling, and the comparison is
        // identity either side of inference.
        (Type::WitnessRef(a), Type::WitnessRef(b)) => {
            let (a, b) = (
                sl.apply_witnesses(&Type::WitnessRef(*a)),
                sr.apply_witnesses(&Type::WitnessRef(*b)),
            );
            let (Type::WitnessRef(a), Type::WitnessRef(b)) = (&a, &b) else {
                unreachable!("a witness renaming maps a reference to a reference")
            };
            // **Each side's own Γ classifies its own reference.** A reference is a name, so
            // what it ranges over is read where it is bound.
            // **Two references are one index when they are one name**, at every derivation.
            // The comparison runs under the correspondence its caller established — the
            // Fun/Fun arm's rename between two Σs, [`witness_instantiation`]'s where a value
            // meets a shape written over binders — so both sides arrive in one spelling and
            // nothing is left for this to reconcile.
            //
            // A **sub-tree** probe is the one abstention: a binder its refinements reference
            // may be held by the context the cut removed, so Γ classifies neither reference
            // and the probe has no verdict to give ([`Derivation::sees_every_binder`]).
            let same = a == b
                || (!cache.derivation.sees_every_binder()
                    && (cache.lctx.type_kind_of(a).is_none()
                        || cache.rctx.type_kind_of(b).is_none()));
            if same {
                Ok(())
            } else {
                Err(ConstrainError::Mismatch {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })
            }
        }

        // **A concrete type meeting a witness constrains every candidate.** The witness
        // is one of its kind's domains and the choice is not the demand's to make, so the
        // demand must hold whichever it is: one invariant edge per candidate. Invariance
        // is what rejects the silent narrowing — two distinct candidates cannot both equal
        // the demand — and a sole candidate is the ordinary edge to its domain, with no
        // cardinality read anywhere. A kind naming no candidate offers nothing to
        // instantiate at and is a mismatch. A variable is not a concrete
        // type: it falls through to the variable arms below, and the reference lands in
        // its bounds like any other leaf.
        (Type::WitnessRef(w), other) | (other, Type::WitnessRef(w))
            if !matches!(other, Type::Infer(_)) =>
        {
            // Whichever side the reference came from is the Γ that classifies it.
            let gamma = if matches!(lhs, Type::WitnessRef(_)) {
                &cache.lctx
            } else {
                &cache.rctx
            };
            // **A candidate that has not resolved carries the demand itself.** It is an
            // ordinary inference variable sitting among the candidates (`[?25]`), so the edges
            // below record against it like any other bound, and what the position ends up
            // ranging over has to admit this type. There is nothing to defer and nowhere
            // separate to defer it to.
            let Some(TypeKind::Enumerated(candidates)) = gamma.type_kind_of(w) else {
                return Err(ConstrainError::Mismatch {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                });
            };
            for c in &candidates {
                constrain_go(c, other, sl, sr, cache)?;
                constrain_go(other, c, sr, sl, cache)?;
            }
            Ok(())
        }

        // Variant: width-subtyping is the dual. lhs's tags must all appear
        // in rhs (with a payload subtype check). Payload depth is covariant.
        // Variant: width-subtyping is the dual of records — lhs's tags must all
        // appear in rhs, each with a payload subtype check. Payload depth is
        // covariant.
        //
        // The loop does **two** jobs, and they are separable only by rhs's
        // [`Openness`]. Recursing into a shared tag is what carries the payload
        // *into* rhs's slot — how a `match` arm's binder learns its type from the
        // scrutinee. Rejecting an lhs tag that rhs lacks is the exhaustiveness
        // check. An **open** rhs keeps the first and drops the second: it commits
        // to the arms it lists and says nothing about the rest, which is what a
        // `case _:` needs (the default arm handles the tags no arm names, so the
        // scrutinee must stay free to carry them).
        //
        // Skipping — rather than returning early — is the whole point: `Ok(())` on
        // a missing tag would abandon every *shared* tag ordered after it, so the
        // payloads that do need constraining would be lost by tag order.
        (Type::Variant(a, lhs_openness), Type::Variant(b, openness)) => {
            debug_assert!(
                !lhs_openness.permits_extra_tags(),
                "an open arm set reached the left of a subtyping edge: openness is a \
                 property of a demand, so only the right-hand side may be open"
            );
            for (k, t0) in a {
                match b.iter().find(|(bk, _)| bk == k) {
                    Some((_, t1)) => constrain_go(t0, t1, sl, sr, cache)?,
                    None if openness.permits_extra_tags() => continue,
                    None => {
                        return Err(ConstrainError::ExtraTag {
                            tag: k.clone(),
                            in_type: rhs.clone(),
                        });
                    }
                }
            }
            Ok(())
        }

        // A mutable handle is invariant in BOTH value and domain: a `Mut`
        // parameter both reads its value (covariant) and writes it
        // (contravariant), so the values equate; and the domain must equate so a
        // `Mut` param's fresh per-call domain resolves to the argument mutable variable's
        // domain (pass-by-reference — the two-way edge is what carries the
        // resolution back to the caller). Value/domain edges run under *identity*
        // like a `Feed` payload: a `Mut`'s value and domain are plain types, not
        // content in a Pi binder's scope, so discharges accumulated on the way to
        // the handle do not transport in.
        // Two histories of the **same kind** equate invariantly in both value
        // and domain (a mutable param reads *and* writes; a feed handle both feeds
        // and is read). A cross-kind pair (a mutable variable demanded as a feed, or vice
        // versa) is *not* matched here: it falls through to the `(_, Append)` arm below,
        // which accepts any left-hand shape, so a mutable variable demanded as a feed
        // lands in `NotAFeed` — the type-level guardrail that `<<` targets a `defer`
        // channel, not a `:=` mutable variable.
        (
            Type::History {
                value: v0,
                domain: d0,
                history_kind: k0,
            },
            Type::History {
                value: v1,
                domain: d1,
                history_kind: k1,
            },
        ) if k0 == k1 => {
            constrain_go(v0, v1, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(v1, v0, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(d0, d1, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(d1, d0, &Subst::id(), &Subst::id(), cache)
        }
        // There is deliberately **no deref arm here.** A mutable variable mention that denotes
        // its value is dereffed by the rule that emits it (`emit::emit_value_read`), so a
        // handle reaching this relation is a handle: the only edges that carry one are
        // a pass-by-reference argument against its parameter, which the invariance arm
        // above relates, and a write's target.
        //
        // As a subtyping rule the deref was a coercion in disguise — it made `Mut(V)`
        // sit *below* `V` while `Mut` is invariant in `V`, and it fired against a fresh
        // inference variable, so nothing downstream could tell a read from a handle
        // being passed along. That is precisely why passing a mutable variable to a `Mut(V)`
        // parameter needed a separate compensating contribution: the handle was gone
        // before the invariance rule could see it.

        // Variable on lhs, rhs has compatible level: record the upper edge in
        // native form (`V‹sl› <: rhs‹sr›`, no inversion), then close each
        // existing lower (`low.ty‹low.ty_subst› <: V‹low.self_subst›`) against
        // the new upper by bridging the holder gap and composing **forward**
        // onto the two content sides.
        (Type::Infer(lv), _) if type_level(rhs) <= lv.level => {
            let lows = {
                let bound = Bound::edge(sl.clone(), rhs.clone(), sr.clone());
                crate::ccl::infer_var::observe_bound_scope(lv, "upper", &bound, cache.derivation);
                let mut s = lv.bounds.borrow_mut();
                s.upper_mut().push(bound);
                let lows = Rc::clone(s.lower());
                drop(s);
                // **A function-shaped bound carries a kind, so it lands on this variable's.**
                // Unconditional: a variable no function reaches keeps an unpinned kind
                // nobody consults, so nothing here dispatches on what the variable will turn
                // out to be.
                if let Some(k) = rhs.fun_kind_of() {
                    // **Both ends, because the relation is symmetric.** A kind related to
                    // this one is reachable from either side or from neither: recording only
                    // here leaves a walk that arrives at the far end unable to get back, and
                    // two kinds at one position then rename onto their own binders with
                    // nothing composing the two.
                    if let FunKind::Var(other) = &k {
                        other.record(FunKind::Var(Rc::clone(&lv.fun_kind)), true);
                    }
                    lv.fun_kind.record(k, false);
                }
                lows
            };
            // **No join here.** A variable's lower bounds are joined where every other
            // join is: at compaction, off these same bounds. Assembling one here as well
            // would compute it twice, by two rules, and — because this arm runs again on
            // every arriving upper edge — recompute it, which is what made the joined
            // sum's binder need an identity stable under recomputation.
            // A declined join over **collection** lower bounds is a type error, not a
            // reason to fall back. Relating two collections over distinct domains to one
            // consumer pointwise is exactly what the join exists to prevent — the
            // consumer's domain would have to lie below both — and the transitive closure
            // does not terminate on it. Now that only sums join, this is the case `box`
            // is there to resolve: box each arm, and the arms join as sums.
            if let Some(domains) = distinct_data_domains(&lows) {
                return Err(ConstrainError::DomainJoinConflict {
                    domains: vec![domains.0, domains.1],
                });
            }
            // A var-var edge carries the watch downward (see `link_watches`); the
            // closure below only re-offers `lv`'s lowers to `rhs` when the levels let
            // this arm run, which is precisely what a `let` RHS breaks.
            if let Type::Infer(rv) = rhs {
                link_watches(lv, rv, cache)?;
            }
            for low in lows.iter() {
                let (tau_l, tau_u) = bridge_holder_gap(&low.self_subst, sl);
                constrain_go(
                    &low.ty,
                    rhs,
                    &Subst::then(&low.ty_subst, &tau_l),
                    &Subst::then(sr, &tau_u),
                    cache,
                )?;
            }
            Ok(())
        }

        // Variable on rhs, lhs has compatible level: record the lower edge in
        // native form (`lhs‹sl› <: V‹sr›`), then close the new lower against
        // each existing upper (`V‹up.self_subst› <: up.ty‹up.ty_subst›`) the
        // same way — forward composition only. This closure step is where the
        // inverted-storage convention lost dependent discharges: the upper
        // edge's forward morphism was reconstructed by inverting its stored
        // inverse, and a non-invertible discharge degraded to `id` twice over.
        // Here the forward morphism is read directly off the edge.
        (_, Type::Infer(rv)) if type_level(lhs) <= rv.level => {
            let ups = {
                let bound = Bound::edge(sr.clone(), lhs.clone(), sl.clone());
                crate::ccl::infer_var::observe_bound_scope(rv, "lower", &bound, cache.derivation);
                let mut s = rv.bounds.borrow_mut();
                s.lower_mut().push(bound);
                let ups = Rc::clone(s.upper());
                drop(s);
                if let Some(k) = lhs.fun_kind_of() {
                    // Both ends, as above.
                    if let FunKind::Var(other) = &k {
                        other.record(FunKind::Var(Rc::clone(&rv.fun_kind)), false);
                    }
                    rv.fun_kind.record(k, true);
                }
                ups
            };
            // The arriving type may be the answer to a kinding edge this variable holds.
            answer_type_kinds(rv)?;
            // No join here, and none is needed: a candidate arriving at a variable that
            // already holds others reaches the joining arm above when *its* own outgoing
            // edge is drawn, and a variable's denotation is read from its lower bounds
            // whenever that happens. Joining here as well would mean re-deriving a join
            // per arriving candidate, and the pointwise closure this arm performs is
            // exactly right for the edge it draws.
            //
            // Deliver the contribution to any trait obligation this variable is an
            // operand of. This arm is the *only* hook site needed: an operand type
            // reaches an obligation as a lower bound, and the closure below plus its
            // dual in the upper arm mean a bound reaching a variable that flows into
            // a watched one is re-constrained *directly against* the watched
            // variable — so both arrival orders (edge-then-bound, bound-then-edge)
            // land the concrete type here. The one path that bypasses the closure is
            // `extrude`, which seeds a proxy's bounds by direct writes; it copies the
            // watch list instead.
            notify_lower(rv, lhs, cache)?;
            if let Type::Infer(lv) = lhs {
                link_watches(lv, rv, cache)?;
            }
            for up in ups.iter() {
                let (tau_l, tau_u) = bridge_holder_gap(sr, &up.self_subst);
                constrain_go(
                    lhs,
                    &up.ty,
                    &Subst::then(sl, &tau_l),
                    &Subst::then(&up.ty_subst, &tau_u),
                    cache,
                )?;
            }
            Ok(())
        }

        // Level mismatch: variable's level is below the other side's.
        // Lift the other side down via extrude and retry.
        (Type::Infer(lv), _) => {
            let new_rhs = extrude(rhs, false, lv.level, &mut ExtrudeCache::new());
            constrain_go(lhs, &new_rhs, sl, sr, cache)
        }
        (_, Type::Infer(rv)) => {
            let new_lhs = extrude(lhs, true, rv.level, &mut ExtrudeCache::new());
            constrain_go(&new_lhs, rhs, sl, sr, cache)
        }

        // Feed handles are invariant in the payload: feeding writes into
        // the channel (contravariant capability) while reading consumes it
        // (covariant), so a feed handle meeting a feed handle equates the
        // payloads. The bidirectional edge is what carries a feed
        // contribution made through a function parameter back to the
        // caller's channel — with a one-way edge the callee's contribution
        // would land on the parameter variable and never reach the
        // argument's payload.
        // The payload edges run under *identity* morphisms: a feed handle's
        // payload is the channel's plain value type, not content living
        // inside a Pi binder's scope, so apply-site discharges accumulated
        // on the way to the handle do not transport into it. (They also
        // must not: the invariant two-way edge would make two distinct
        // discharges meet at one payload variable — the non-invertible
        // bridge corner — for ordinary chained defer functions. The cost is
        // that a binder-dependent refinement *inside* a fed value's type is
        // not discharged across the handle — out of scope alongside the
        // filter-feed-through-UDF gaps (see design/mutability.md §4 and the
        // `ccl/channelize.rs` module docs).)
        // Transparent read: a non-mutable consumer of a feed channel consumes its
        // whole stream `domain ⇒ value` (`sum(d)`, `d + 1`, a `x <<= y` chain
        // feeding one defer from another). Unlike a mutable variable (dereffed to its scalar
        // `value` above), a feed reads as the reconstructed channel function.
        (
            Type::History {
                value,
                domain,
                history_kind: HistoryKind::Append,
            },
            _,
        ) => {
            let chan = Type::Fun {
                name: None,
                // A feed's read view is a collection stream: a data function.
                fun_kind: FunKind::Data(None),
                domain: domain.clone(),
                codomain: value.clone(),
            };
            constrain_go(&chan, rhs, sl, sr, cache)
        }
        // A *channel-shaped* lhs meeting a feed requirement is the read view of
        // that handle: a use position that both held the handle and was read
        // coalesces to the bare channel, and monomorphization's two-way pin then
        // meets that view against the definition's feed channel. Align it with
        // the reconstructed channel function. Structural validation of *genuine*
        // misuse (feeding a plain collection) still lands in channelize's checks.
        (
            Type::Fun { .. },
            Type::History {
                value,
                domain,
                history_kind: HistoryKind::Append,
            },
        ) => {
            let chan = Type::Fun {
                name: None,
                // A feed's read view is a collection stream: a data function.
                fun_kind: FunKind::Data(None),
                domain: domain.clone(),
                codomain: value.clone(),
            };
            constrain_go(lhs, &chan, sl, sr, cache)
        }
        // Any other plain value can never satisfy a feed requirement: reading is
        // transparent, but the write capability cannot be conjured (`g(5)` where
        // `g` feeds its parameter). A `<<` targeting a `:=` mutable variable lands here
        // too, as the handle it is — the left side matches `_`, so the cross-kind pair
        // the invariance arm above declined needs no rule of its own.
        (
            _,
            Type::History {
                history_kind: HistoryKind::Append,
                ..
            },
        ) => Err(ConstrainError::NotAFeed {
            found: lhs.clone(),
            required: rhs.clone(),
        }),

        // A nominal channel domain is *deferred-compatible* with any
        // domain-shaped type it meets — the assembly (channelize) is what
        // determines the concrete domain, and the strict post-channelize
        // `typecheck` wall re-checks the substituted result, so the solver
        // records nothing here. Legitimate edges this absorbs:
        //   - `x <<= [v, …]` (define): `ChanDom(x)` vs `UIntRange(n)` — the
        //     defined collection's domain IS the channel's eventual domain;
        //   - `x <<= y` (forwarding): `ChanDom(x)` vs `ChanDom(y)` (distinct
        //     names — the reflexive same-name arm short-circuits above);
        //   - a refined-source contribution: `ChanDom(d)` vs `{D | p}`;
        //   - a source-domained contribution: `ChanDom(d)` vs a
        //     `DataSource`/`Variant` (union-of-sources) domain.
        // A structurally non-domain meet — a channel domain against a scalar,
        // function, product, or history — is a genuine type error and falls
        // through to the mismatch arm, so an ill-domained feed program gets
        // an inference diagnostic rather than a post-channelize wall panic.
        (
            Type::ChanDom(..),
            Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Variant(..)
            | Type::Refinement(..)
            | Type::ChanDom(..)
            | Type::Hole,
        )
        | (
            Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Variant(..)
            | Type::Refinement(..)
            | Type::Hole,
            Type::ChanDom(..),
        ) => Ok(()),

        // Refinement subtyping:
        //   {b₁ | S₁} <: {b₂ | S₂}  iff  b₁ <: b₂  and  σ(S₂) ⊆ σ(S₁) ∪ refinements(b₁)
        // (more refinements ⇒ subtype). Refinements match by [`Refinement`]'s
        // `PartialEq` — structural predicate equality — so a refinement join planning
        // rebuilt as a fresh term still matches; never by predicate
        // implication. The two sides live in different binder contexts, so an
        // lhs refinement is transported through the correspondence (`σ(S₁)`, via
        // [`Subst::force_refinement`]) before comparing: a predicate mentioning
        // a Pi binder matches its renamed — or, when a discharge edge composed
        // into σ on the way through a variable, *discharged* — copy on the
        // rhs. Under the identity this is plain structural equality. The lhs
        // carries every
        // refinement rhs requires when its explicit layers `S₁` plus whatever
        // its *base* `b₁` carries cover `S₂`.
        //
        // `peel_refinements` strips the explicit layers down to the bases, so a
        // top-level refinement whose base is a variable reaches here rather than
        // the var arms above. That base variable can still acquire the deficit
        // `S₂ \ S₁`, so we flow it onto the variable (`b₁ <: {b₂ | deficit}`)
        // rather than rejecting — the refinement analog of how the
        // record/function arms thread structure through variables. The
        // requirement then fails later iff the variable resolves to a concrete
        // base lacking those refinements. Without this, a value that is *already*
        // refined could never be cast to add a further refinement (nested
        // list-comprehension filters: `{D|p} ⇒ V <: {?a|q} ⇒ V`), even though
        // the assignment `?a := {D|p}` exists.
        //
        // When `b₁` is *concrete* and the deficit is non-empty it is a genuine
        // mismatch: an unrefined value cannot stand in where a refined one is
        // demanded (`T ⊀ {T|p}`), and a value refined by S₁ cannot carry a
        // *different* refinement it lacks (`{T|q} ⊀ {T|p}`). Acquiring a
        // refinement on a concrete value is an explicit `Restrict`, not
        // subsumption.
        (Type::Refinement(..), _) | (_, Type::Refinement(..)) => {
            let (lbase, lrefs) = (lhs.peel_refinements(), lhs.refinements());
            let (rbase, rrefs) = (rhs.peel_refinements(), rhs.refinements());
            // The refinements rhs requires that no transported lhs layer
            // matches (by `Refinement`'s structural `PartialEq`). Each side's
            // refinements are forced through its own morphism into the ambient frame
            // before comparing (`sl(S₁)` vs `sr(S₂)`); the deficit keeps the
            // *untransported* rhs refinements, since the recursive constraint below
            // carries `sr` for them.
            let lrefs_in_ambient: Vec<Refinement> =
                lrefs.iter().map(|l| sl.force_refinement(l)).collect();
            let deficit: RefinementSet = rrefs
                .iter()
                .filter(|r| !lrefs_in_ambient.contains(&sr.force_refinement(r)))
                .cloned()
                .collect();
            if deficit.is_empty() {
                // lhs's explicit layers already supply every refinement rhs requires.
                constrain_go(lbase, rbase, sl, sr, cache)
            } else if matches!(lbase, Type::Infer(_)) {
                // Variable base: flow the deficit onto it (`b₁ <: {b₂ | deficit}`)
                // rather than rejecting; it fails later iff the variable
                // resolves to a concrete base lacking those refinements.
                let demanded = Type::refined(rbase.clone(), deficit);
                constrain_go(lbase, &demanded, sl, sr, cache)
            } else {
                Err(ConstrainError::Mismatch {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })
            }
        }

        _ => Err(ConstrainError::Mismatch {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }),
    }
}

/// Give an extrusion proxy the same trait obligations as the variable it
/// approximates.
///
/// Extrusion seeds a proxy's bounds by **direct writes** rather than through
/// `constrain_go`, so it is the one path where a concrete type can reach a watched
/// variable's stand-in without passing the narrowing hook. A bound recorded on the
/// proxy afterwards would otherwise never reach the obligation, and the operand's
/// type would silently fail to narrow it.
///
/// Copied unconditionally, at both polarities. The proxy and the original stay
/// linked, so a fact can legitimately arrive at both — but narrowing is an
/// idempotent set intersection, which makes the duplicate delivery a no-op rather
/// than something to reason about per polarity.
fn copy_watches(from: &Rc<InferVar>, to: &Rc<InferVar>) {
    let watches = from.watches.borrow().clone();
    if !watches.is_empty() {
        to.watches.borrow_mut().extend(watches);
    }
}

/// Lift `ty` so that all its variables live at level ≤ `target_level`.
///
/// When a constraint crosses level boundaries (e.g. an outer-scope variable
/// gets constrained against an inner-scope type), variables at higher
/// levels must be approximated by fresh variables at the target level so
/// the constraint can be recorded locally. `pol` selects which bound to
/// preserve: positive (`true`) keeps the lower bound, negative (`false`)
/// keeps the upper bound.
///
/// Outside generalized `let`s every variable shares level 0, so extrude is a
/// no-op there; it fires for real once let-generalization (`scoped_let`) mints
/// RHS variables at a deeper level and a cross-level constraint arises (the
/// constrain_subtype solver's level-mismatch branches).
pub fn extrude(ty: &Type, pol: bool, target_level: Level, cache: &mut ExtrudeCache) -> Type {
    if type_level(ty) <= target_level {
        return ty.clone();
    }
    match ty {
        // Not a type — an annotation-position obligation, erased by
        // `normalize_annotation` before any constraint is emitted (see `Type::BoundedHole`).
        Type::BoundedHole(_) => {
            unreachable!(
                "Type::BoundedHole reached the solver; `normalize_annotation` must erase it"
            )
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_) => ty.clone(),
        Type::Fun {
            name,
            fun_kind,
            domain: d,
            codomain: c,
        } => Type::Fun {
            name: name.clone(),
            // A sum's **candidates** are an invariant position, so they cross a level
            // boundary through two-way proxies rather than the polar one-way
            // approximation — the same reason a `History` payload does. The kind premise matches
            // candidates *by value*, so neither direction of a candidate's bounds is the
            // "unused" one: a one-way proxy inherits whichever side the polarity picked
            // and silently drops the other, which for a candidate is usually fatal.
            fun_kind: match fun_kind {
                FunKind::Data(Some(ws)) => FunKind::Data(Some(Rc::new(
                    ws.iter()
                        .map(|w| w.map_types(|t| extrude_invariant(t, target_level, cache)))
                        .collect(),
                ))),
                other => other.clone(),
            },
            domain: Box::new(extrude(d, !pol, target_level, cache)),
            codomain: Box::new(extrude(c, pol, target_level, cache)),
        },
        Type::Tuple(ts) => Type::Tuple(
            ts.iter()
                .map(|t| extrude(t, pol, target_level, cache))
                .collect(),
        ),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), extrude(t, pol, target_level, cache)))
                .collect(),
        ),
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                // Variant payloads are covariant — same polarity, no flip.
                .map(|(k, t)| (k.clone(), extrude(t, pol, target_level, cache)))
                .collect(),
            *openness,
        ),
        Type::Refinement(inner, r) => {
            Type::refined(extrude(inner, pol, target_level, cache), r.clone())
        }
        Type::WitnessRef(_) => ty.clone(),
        // Invariant payload: polarity is meaningless under invariance, so
        // both children are extruded with two-way proxies (a history is read
        // *and* written) instead of the polar one-way approximation below.
        Type::History {
            value,
            domain,
            history_kind,
        } => Type::History {
            value: Box::new(extrude_invariant(value, target_level, cache)),
            domain: Box::new(extrude_invariant(domain, target_level, cache)),
            history_kind: *history_kind,
        },
        Type::Infer(tv) => {
            if let Some(existing) = cache.get(&(tv.uid, pol)) {
                return Type::Infer(Rc::clone(existing));
            }
            // Conservative approximation: a fresh variable at the target
            // level, linked to the original by the appropriate bound. It
            // proxies the original, so it inherits the original's telescope —
            // the bounds copied below close against the same scope.
            let nvs = InferVar::fresh_in(target_level, &tv.telescope);
            cache.insert((tv.uid, pol), Rc::clone(&nvs));
            copy_watches(tv, &nvs);
            // Kinding constraints ride along at **both** polarities, unlike the bounds
            // below. The proxy stands in for the original wherever the outer scope reads
            // it, and "must inhabit 𝐾" is a property of what that resolves to, not of a
            // direction of flow — a one-sided copy would let a scope boundary launder
            // the constraint away. The kind's own type children extrude with it: a
            // parameterized kind carries types like any other position.
            {
                let carried: Vec<_> = tv
                    .bounds
                    .borrow()
                    .type_kinds
                    .iter()
                    .map(|k| k.map_children(|t| extrude(t, pol, target_level, cache)))
                    .collect();
                nvs.bounds.borrow_mut().type_kinds = carried;
            }

            // Each branch snapshots only the list it does *not* push to — the
            // positive one seeds from `lower` and writes `upper`, the negative
            // mirrors it — so a branch never holds the list it is about to write
            // and its own push never forks the shared list. (The snapshot is
            // needed regardless: the bounds are read across a `borrow_mut` and
            // across the recursion below.)
            if pol {
                // Positive: original flows into new var. Original gains
                // `nvs` as an upper bound; new var inherits original's
                // lower bounds (extruded at the same polarity).
                let lows = Rc::clone(tv.bounds.borrow().lower());
                tv.bounds
                    .borrow_mut()
                    .upper_mut()
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, pol, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().set_lower(new_lows);
            } else {
                // Negative: new var flows into original. Original gains
                // `nvs` as a lower bound; new var inherits original's
                // upper bounds.
                let ups = Rc::clone(tv.bounds.borrow().upper());
                tv.bounds
                    .borrow_mut()
                    .lower_mut()
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, pol, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().set_upper(new_ups);
            }
            Type::Infer(nvs)
        }
    }
}

/// Extrusion for an *invariant* position — a [`Type::History`] payload.
///
/// The polar extrusion above approximates a variable one-directionally
/// (positive keeps lower bounds, negative keeps upper). Under invariance the
/// proxy must track the original in **both** directions, so every variable
/// gets a single fresh proxy at the target level linked to the original by
/// both a lower and an upper bound. The standard lower×upper closure in
/// `constrain_go` then keeps the pair equated: every future bound recorded
/// on the original closes against the proxy edge and lands on the proxy
/// (and vice versa for reads through the original), so neither side's
/// constraints are lost. Structural recursion does not flip polarity —
/// equality is symmetric in every position.
fn extrude_invariant(ty: &Type, target_level: Level, cache: &mut ExtrudeCache) -> Type {
    if type_level(ty) <= target_level {
        return ty.clone();
    }
    match ty {
        Type::Infer(tv) => {
            // The proxy is polarity-agnostic and must be linked to the original
            // in BOTH directions. Two cache states can precede us:
            //
            //  * A prior *invariant* extrusion of this variable registered one
            //    two-way proxy under both keys — reuse it wholesale.
            //  * A prior *polar* extrusion (`extrude` above) minted a proxy
            //    under a single key with only *one* bound link. Reusing that
            //    proxy naively would hand the invariant position a one-way
            //    proxy, silently dropping the other bound direction across the
            //    level boundary. Instead,
            //    reuse the proxy (it is the same original variable) but add the
            //    link the polar extrusion omitted, upgrading it to two-way.
            let cached_pos = cache.get(&(tv.uid, true)).cloned();
            let cached_neg = cache.get(&(tv.uid, false)).cloned();
            if let (Some(p), Some(n)) = (&cached_pos, &cached_neg)
                && Rc::ptr_eq(p, n)
            {
                // Already two-way (a prior invariant extrusion).
                return Type::Infer(Rc::clone(p));
            }

            // Reuse a one-way polar proxy if present (prefer the positive-key
            // one; either is the same original variable), else mint fresh.
            let nvs = cached_pos
                .clone()
                .or_else(|| cached_neg.clone())
                .unwrap_or_else(|| InferVar::fresh_in(target_level, &tv.telescope));
            // Which bound links does the reused proxy already carry? A polar
            // proxy under the `true` key has the positive link (`tv <: proxy`);
            // under the `false` key, the negative link (`proxy <: tv`). A fresh
            // proxy has neither.
            let has_pos_link = cached_pos.as_ref().is_some_and(|p| Rc::ptr_eq(p, &nvs));
            let has_neg_link = cached_neg.as_ref().is_some_and(|n| Rc::ptr_eq(n, &nvs));
            cache.insert((tv.uid, true), Rc::clone(&nvs));
            cache.insert((tv.uid, false), Rc::clone(&nvs));
            copy_watches(tv, &nvs);

            // Snapshot the original's bounds, excluding any edge that already
            // points at this proxy (a polar extrusion pushed one such link into
            // `tv`); re-seeding from it would create a spurious `proxy <: proxy`
            // self-edge.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                let not_proxy = |b: &Bound| !matches!(&b.ty, Type::Infer(v) if v.uid == nvs.uid);
                (
                    s.lower()
                        .iter()
                        .filter(|b| not_proxy(b))
                        .cloned()
                        .collect::<Vec<_>>(),
                    s.upper()
                        .iter()
                        .filter(|b| not_proxy(b))
                        .cloned()
                        .collect::<Vec<_>>(),
                )
            };
            // Positive link: `tv <: proxy`; proxy inherits `tv`'s lower bounds.
            if !has_pos_link {
                tv.bounds
                    .borrow_mut()
                    .upper_mut()
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, true, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().lower_mut().extend(new_lows);
            }
            // Negative link: `proxy <: tv`; proxy inherits `tv`'s upper bounds.
            if !has_neg_link {
                tv.bounds
                    .borrow_mut()
                    .lower_mut()
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, false, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().upper_mut().extend(new_ups);
            }
            Type::Infer(nvs)
        }
        // Every structural position under an invariant constructor is
        // itself invariant; refinement predicates are not walked (same as
        // the polar extrusion).
        _ => {
            let mut out = ty.clone();
            out.walk_children_mut(|t| *t = extrude_invariant(t, target_level, cache));
            out
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ccl::ty::FunKindVar;
    use std::rc::Rc;

    use smol_str::SmolStr;

    use super::*;
    use crate::ccl::infer::solver::test_helpers::{record, refined, variant};
    use crate::ccl::infer::solver::{coalesce_compact, compact_type, fresh_var, fun, prim};
    use crate::ccl::subst::Subst;
    use crate::ccl::{
        BaseType, BinOpKind, CompareKind, Lit, Name, Refinement, Type, TypedExpr, TypedExprNode,
    };

    /// `{Int | escaped}` — a refinement naming a uniquified binder that nothing in
    /// scope binds, the shape the closure invariant rejects.
    #[cfg(debug_assertions)]
    fn escaped_refinement() -> Type {
        crate::ccl::ccl_utils::refine_with_bare(
            Type::Base(BaseType::Int),
            &TypedExpr::var(Name::fresh("escaped")),
        )
    }

    /// The `Fun`/`Fun` opening does not fire between two concrete sides, so a free
    /// reference sharing a binder's display spelling cannot capture the reopened
    /// index.
    ///
    /// `(x: Int) ⇒ {Int | __elem == #0}` and `Int ⇒ {Int | __elem == x}` state
    /// different refinements: one is about the function's own argument, the other about
    /// whatever binds `x` outside the type. Opening the closed side at its
    /// display name spells both `__elem == x` and reads them as one. Uniquified
    /// binders make the collision need the same uid, which is the same binder,
    /// and the concrete relation must not depend on that convention.
    #[test]
    fn a_concrete_pair_does_not_open_at_a_shared_spelling() {
        let x = Name::raw("x");
        let refinement = |referenced: &Name| {
            Type::Refinement(
                Box::new(Type::Base(BaseType::Int)),
                Refinement::born(Rc::new(TypedExpr::binop(
                    TypedExpr::var(Name::elem()),
                    BinOpKind::Compare(CompareKind::Equals),
                    TypedExpr::var(referenced.clone()),
                )))
                .into(),
            )
        };
        // Construction closes the reference into `#0`.
        let closed = Type::pi(x.clone(), Type::Base(BaseType::Int), refinement(&x));
        // The same spelling, free: no function in this type binds it.
        let free = Type::fun(Type::Base(BaseType::Int), refinement(&x));
        assert!(
            crate::ccl::subst::type_free_vars(&free).contains(&x),
            "the right side's reference must be free for this to be the capture case"
        );
        assert!(
            constrain_subtype(&closed, &free, &mut ConstrainCache::new()).is_err(),
            "a closed refinement about the function's own binder does not satisfy one \
             about a free name that shares its spelling"
        );
    }

    /// A whole-tree re-derivation enforces the closure invariant, exactly as the
    /// live solve does: the tree it walks holds every binder its refinements name, so
    /// a reference to one it does not is the escape the invariant catches.
    ///
    /// This is what a `Derivation::SubTree` cache is excused from. The two
    /// tests together are why that excuse is narrow: a probe over a sub-tree
    /// has no context to hold the binder, and a walk over the whole tree does.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "open bound recorded")]
    fn a_whole_tree_re_derivation_enforces_the_closure_invariant() {
        let escaped = escaped_refinement();
        let mut cache = ConstrainCache::for_derivation(Derivation::PostPass);
        let v = fresh_var(0);
        let _ = constrain_subtype(&escaped, &v, &mut cache);
    }

    /// Two references to one index, spelled under different binders, at a cut where Γ
    /// classifies only one of them.
    ///
    /// The shape is a comprehension over a conditional collection: the collection is
    /// `Σ (σ_coll : 𝐾). (σ_coll ⤇ Int)` and the index reaching it is the enclosing
    /// Σ-typed lambda's parameter, a bare reference the *lambda's* type binds. A cut inside
    /// the body classifies the collection's binder and not the parameter's, so a probe that
    /// read the pair as free rejected every such program — 80 tests, all of them
    /// well-typed at every whole-tree wall.
    #[test]
    fn a_sub_tree_probe_abstains_where_only_one_reference_is_classified() {
        use crate::ccl::infer_var::fresh_witness_binder_id;
        use crate::ccl::ty::{TypeKind, Witness, WitnessContext};

        let kind = TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let collection = Witness::bound_to(fresh_witness_binder_id(), kind.clone());
        let parameter = Witness::bound_to(fresh_witness_binder_id(), kind);
        let (classified, unclassified) = (
            Type::WitnessRef(*collection.id()),
            Type::WitnessRef(*parameter.id()),
        );
        // Γ holds the collection's binder, the one the cut kept.
        let gamma = WitnessContext::default().extended(std::slice::from_ref(&collection));

        let mut probe = ConstrainCache::for_derivation(Derivation::SubTree);
        probe.seed_context(&gamma);
        constrain_subtype(&unclassified, &classified, &mut probe)
            .expect("a sub-tree probe gives no verdict on a reference its context binds");

        let mut whole = ConstrainCache::for_derivation(Derivation::PostPass);
        whole.seed_context(&gamma);
        constrain_subtype(&unclassified, &classified, &mut whole)
            .expect_err("over a whole tree an unclassified reference is free");
    }

    /// A sub-tree probe records the same bound without complaint: its refinements
    /// reference binders the context it was cut from holds, and no walk of the
    /// sub-tree can enter them.
    #[test]
    #[cfg(debug_assertions)]
    fn a_sub_tree_probe_admits_a_reference_its_context_binds() {
        let escaped = escaped_refinement();
        let mut cache = ConstrainCache::for_derivation(Derivation::SubTree);
        let v = fresh_var(0);
        constrain_subtype(&escaped, &v, &mut cache)
            .expect("a sub-tree's free reference is admitted");
    }

    /// The tripwire is armed for the one place the record/variant arms and the
    /// trivial-equality short-circuit can disagree.
    ///
    /// On a duplicate-keyed record the short-circuit accepts `t <: t`, while the
    /// arm it shadows — find-first field lookup — answers the *first* `a` for both
    /// of the rhs's `a` fields and demands `Int <: Bool`. The disagreement is not a
    /// bug in either one; it is a type outside the uniquely-keyed invariant both
    /// rest on. Pinning that the assert *fires* is what keeps the guard from
    /// rotting into a no-op.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "duplicate record key")]
    fn dup_key_record_trips_the_uniquely_keyed_invariant() {
        let dup = Type::Record(vec![
            ("a".to_string(), Type::Base(BaseType::Int)),
            ("a".to_string(), Type::Base(BaseType::Bool)),
        ]);
        let mut cache = ConstrainCache::new();
        let _ = constrain_subtype(&dup, &dup.clone(), &mut cache);
    }

    /// A kinding constraint must cross a scope boundary with its variable. `extrude`
    /// mints a proxy at the target level and copies the variable's constraint state
    /// onto it; a kinding constraint is part of that state, and unlike a bound it is
    /// not polar, so both polarities carry it.
    ///
    /// Losing it here is a silent *acceptance* — the constraint would survive only on a
    /// variable the outer scope no longer reads — which is the same failure mode
    /// `test_kinding_constraint_survives_instantiation` pins for the freshening
    /// boundary.
    #[test]
    fn extrusion_carries_a_kinding_constraint_at_both_polarities() {
        for pol in [true, false] {
            let inner = InferVar::fresh(2);
            inner
                .bounds
                .borrow_mut()
                .type_kinds
                .push(TypeKind::UIntRanges);
            let mut cache = ExtrudeCache::new();
            let out = extrude(&Type::Infer(Rc::clone(&inner)), pol, 0, &mut cache);
            let Type::Infer(proxy) = out else {
                panic!("extruding a variable yields a variable, got {out:?}");
            };
            assert_eq!(proxy.level, 0, "proxy sits at the target level");
            assert_eq!(
                proxy.bounds.borrow().type_kinds,
                vec![TypeKind::UIntRanges],
                "pol={pol}: the proxy must inhabit the same kind"
            );
        }
    }

    /// A factored pairing is a data-function edge, so it inherits domain invariance
    /// (`src/ccl/design/type-inference.md`, "The Σ rule"): a refined range and the
    /// bare range pair in neither direction — the plain data functions do not relate
    /// either (`a_data_domain_relates_only_to_itself`).
    #[test]
    fn sigma_width_pairs_factored_domains_invariantly() {
        let sum = |kind| Type::sum_over(kind, None, prim(BaseType::Int));
        let refined_range = refined(Type::UIntRange(3), 7);

        let bare = sum(TypeKind::Enumerated(vec![Type::UIntRange(3)]));
        let filtered = sum(TypeKind::Enumerated(vec![refined_range.clone()]));
        let wider = sum(TypeKind::Enumerated(vec![
            Type::UIntRange(3),
            refined_range.clone(),
        ]));

        assert!(
            constrain_subtype(&bare, &wider, &mut ConstrainCache::new()).is_ok(),
            "a candidate subset widens"
        );
        assert!(
            constrain_subtype(&wider, &bare, &mut ConstrainCache::new()).is_err(),
            "and not conversely"
        );
        assert!(
            constrain_subtype(&bare, &filtered, &mut ConstrainCache::new()).is_err(),
            "a refined candidate is a different candidate"
        );
        assert!(
            constrain_subtype(&filtered, &bare, &mut ConstrainCache::new()).is_err(),
            "in either direction"
        );
    }

    #[test]
    fn refined_superset_is_subtype() {
        // {Int | p, q} <: {Int | p}  — more refinements ⇒ subtype.
        let (p, q) = (1, 2);
        let lhs = refined(refined(prim(BaseType::Int), p), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn refined_missing_refinement_is_not_subtype() {
        // {Int | q} </: {Int | p}  — a q-refined value cannot stand in for a
        // p-refined one. `refined` gives p and q structurally-distinct
        // predicates, so the refinements don't match.
        let (p, q) = (1, 2);
        let lhs = refined(prim(BaseType::Int), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn structurally_equal_predicate_matches_across_distinct_terms() {
        // {Int | p} <: {Int | q} when p and q carry *structurally identical*
        // predicates in distinct `Rc`s — exactly what join planning produces
        // by re-minting a refinement at each marker. Equality of the
        // predicate `Expr`, not `Rc` identity, decides the match
        // (`Refinement: PartialEq`).
        use crate::ccl::{Lit, TypedExpr};
        let mk = || {
            Type::refined_one(
                prim(BaseType::Int),
                Refinement::born(Rc::new(TypedExpr::lit(Lit::Bool(true)))),
            )
        };
        let lhs = mk();
        let rhs = mk();
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn a_data_domain_relates_only_to_itself() {
        // A data domain is invariant (`design/type-inference.md`, "Data domains are
        // invariant"), so a data function relates to another only when the domains
        // are the same domain — pinned in all four directions, base and refinement.
        // Two collections that differ are not ordered either way; their join is a Σ,
        // not one of them.
        use crate::ccl::{Lit, TypedExpr};
        let refined_dom = || {
            Type::refined_one(
                Type::UIntRange(3),
                Refinement {
                    predicate: Rc::new(TypedExpr::lit(Lit::Bool(true))),
                },
            )
        };
        let refined = Type::data_fun(refined_dom(), prim(BaseType::Int));
        let bare = Type::data_fun(Type::UIntRange(3), prim(BaseType::Int));
        let wider = Type::data_fun(Type::UIntRange(9), prim(BaseType::Int));

        // Bare domain position: the plain lattice, drop-only.
        assert!(
            constrain_subtype(
                &refined_dom(),
                &Type::UIntRange(3),
                &mut ConstrainCache::new()
            )
            .is_ok()
        );
        assert!(
            constrain_subtype(
                &Type::UIntRange(3),
                &refined_dom(),
                &mut ConstrainCache::new()
            )
            .is_err()
        );

        // Behind a data function, neither refinement direction relates.
        assert!(
            matches!(
                constrain_subtype(&bare, &refined, &mut ConstrainCache::new()),
                Err(ConstrainError::DataDomainMismatch { .. })
            ),
            "a collection may not acquire a domain filter by subsumption"
        );
        assert!(
            constrain_subtype(&refined, &bare, &mut ConstrainCache::new()).is_err(),
            "nor drop one"
        );

        // A *compute* function over the same domains keeps the contravariant lattice:
        // invariance is about collections, not about refinements behind any function.
        assert!(
            constrain_subtype(
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &fun(refined_dom(), prim(BaseType::Int)),
                &mut ConstrainCache::new()
            )
            .is_ok(),
            "a capability's domain is not data — acquiring a refinement is sound"
        );

        // Nor either base direction.
        assert!(
            constrain_subtype(&bare, &wider, &mut ConstrainCache::new()).is_err(),
            "a narrower range domain does not stand in for a wider one"
        );
        assert!(
            constrain_subtype(&wider, &bare, &mut ConstrainCache::new()).is_err(),
            "nor a wider one for a narrower — no contravariant widening of a data domain"
        );

        // The same domain does relate: invariance is equality, not a blanket
        // rejection of `Data`/`Data` edges.
        assert!(
            constrain_subtype(&bare, &bare, &mut ConstrainCache::new()).is_ok(),
            "a data function relates to itself"
        );
        assert!(
            constrain_subtype(&refined, &refined, &mut ConstrainCache::new()).is_ok(),
            "including through a domain refinement"
        );
    }

    #[test]
    fn structurally_equal_refinements_hash_equal() {
        // The `Hash`/`Eq` contract: structurally-equal refinements in
        // distinct `Rc`s are `==`, so they must also hash equal — otherwise the
        // `ConstrainCache` (`HashSet<(Type, Type)>`) cycle-break could miss a
        // match. Pins consistency between `Refinement`'s `PartialEq` and `Hash`.
        use crate::ccl::{Lit, TypedExpr};
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mk = || {
            Type::refined_one(
                prim(BaseType::Int),
                Refinement::born(Rc::new(TypedExpr::lit(Lit::Bool(true)))),
            )
        };
        let a = mk();
        let b = mk();
        let hash = |t: &Type| {
            let mut h = DefaultHasher::new();
            t.hash(&mut h);
            h.finish()
        };
        assert_eq!(a, b, "structurally-equal refinements must be ==");
        assert_eq!(hash(&a), hash(&b), "== refinements must hash equal");

        // The cache scenario: a structurally-equal pair finds the same entry
        // (same key), so a revisit under the same side-morphisms is recognised.
        let mut cache = ConstrainCache::new();
        let sid = (Subst::id(), Subst::id());
        cache
            .edge_bridges(a.clone(), prim(BaseType::Int))
            .push(sid.clone());
        assert!(
            cache.edge_bridges(b, prim(BaseType::Int)).contains(&sid),
            "structurally-equal refined key must hit the same cache entry"
        );

        // A structurally *different* predicate must not collapse into it.
        let c = Type::refined_one(
            prim(BaseType::Int),
            Refinement::born(Rc::new(TypedExpr::lit(Lit::Bool(false)))),
        );
        assert_ne!(a, c, "distinct predicates must stay distinct");
    }

    #[test]
    fn refined_drops_to_base() {
        // {Int | p} <: Int  — dropping a refinement is widening.
        let p = 1;
        let lhs = refined(prim(BaseType::Int), p);
        let rhs = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn refined_var_base_absorbs_deficit() {
        // {?a | q} <: {Int | p}: the explicit layer only supplies q, but the
        // base variable ?a can acquire the deficit {p}, so the constraint
        // succeeds by flowing `?a <: {Int | p}`. This is what lets a value
        // that is *already* refined be cast to add a further refinement (nested
        // list-comprehension filters: `{D|p} ⇒ V <: {?a|q} ⇒ V`); a concrete
        // `{p} ⊆ {q}` check would reject it.
        let (p, q) = (1, 2);
        let a = fresh_var(0);
        let lhs = refined(a.clone(), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
        // The deficit must have been recorded on ?a as the upper bound
        // `{Int | p}`, so coalescing ?a yields a base carrying p.
        let Type::Infer(v) = &a else { unreachable!() };
        let expected = refined(prim(BaseType::Int), p);
        assert!(
            v.bounds.borrow().upper().iter().any(|u| u.ty == expected),
            "?a should carry {{Int | p}} as an upper bound, got {:?}",
            v.bounds.borrow().upper()
        );
    }

    #[test]
    fn refined_concrete_base_still_rejects_deficit() {
        // {Int | q} </: {Int | p}: with a *concrete* base there is nothing to
        // absorb the deficit, so the strict rejection (`{T|q} ⊀ {T|p}`) is
        // preserved — only a variable base can acquire missing refinements.
        let (p, q) = (1, 2);
        let lhs = refined(prim(BaseType::Int), q);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn unrefined_does_not_flow_into_refined() {
        // Int </: {Int | p}  — a refinement is *required*, not one the
        // consumer silently applies. An unrefined value cannot stand in
        // where a refined one is demanded; acquiring the refinement is an
        // explicit `Restrict`, not subsumption.
        let p = 1;
        let lhs = prim(BaseType::Int);
        let rhs = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn constrain_identical_primitives_succeeds() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&a, &b, &mut cache).is_ok());
    }

    #[test]
    fn constrain_distinct_primitives_fails() {
        let a = prim(BaseType::Int);
        let b = prim(BaseType::String);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&a, &b, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn constrain_function_propagates_contravariance() {
        // (Int -> Int) <: (Int -> Int) — succeeds.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_ok());
    }

    #[test]
    fn constrain_function_mismatch_on_codomain_fails() {
        // (Int -> Int) <: (Int -> String) — fails on codomain.
        let f1 = fun(prim(BaseType::Int), prim(BaseType::Int));
        let f2 = fun(prim(BaseType::Int), prim(BaseType::String));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&f1, &f2, &mut cache).is_err());
    }

    #[test]
    fn constrain_record_width_subtyping_succeeds() {
        // {a: Int, b: Bool} <: {a: Int} — drop field b, OK.
        let lhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let rhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&lhs, &rhs, &mut cache).is_ok());
    }

    #[test]
    fn constrain_record_missing_field_fails() {
        // {a: Int} <: {a: Int, b: Bool} — lhs lacks field b.
        let lhs = record(&[(FieldKey::Name("a".into()), prim(BaseType::Int))]);
        let rhs = record(&[
            (FieldKey::Name("a".into()), prim(BaseType::Int)),
            (FieldKey::Name("b".into()), prim(BaseType::Bool)),
        ]);
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&lhs, &rhs, &mut cache),
            Err(ConstrainError::MissingField { .. })
        ));
    }

    #[test]
    fn constrain_var_against_prim_records_upper_bound() {
        // α <: Int → α gains Int as an upper bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &p, &mut cache).unwrap();
        if let Type::Infer(state) = &v {
            let s = state.bounds.borrow();
            assert_eq!(s.upper().len(), 1);
            assert!(s.lower().is_empty());
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_prim_against_var_records_lower_bound() {
        // Int <: α → α gains Int as a lower bound.
        let v = fresh_var(0);
        let p = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&p, &v, &mut cache).unwrap();
        if let Type::Infer(state) = &v {
            let s = state.bounds.borrow();
            assert!(s.upper().is_empty());
            assert_eq!(s.lower().len(), 1);
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_var_to_var_records_bound_without_immediate_propagation() {
        // Setup: α has upper Int. Then β <: α.
        //
        // Note: the solver's constrain_subtype rule, when both sides are
        // variables, fires the Var-on-lhs branch first and registers
        // rhs (α) directly in lhs (β)'s upper bounds. α's existing
        // uppers are NOT eagerly transferred to β — that transitive
        // chain (β <: Int) is recovered at simplification time by
        // walking the bounds graph.
        let alpha = fresh_var(0);
        let beta = fresh_var(0);
        let int_ty = prim(BaseType::Int);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&alpha, &int_ty, &mut cache).unwrap();
        constrain_subtype(&beta, &alpha, &mut cache).unwrap();

        if let Type::Infer(state) = &beta {
            let s = state.bounds.borrow();
            assert_eq!(s.upper().len(), 1);
            // The recorded upper bound is α itself, not Int.
            assert!(matches!(&s.upper()[0].ty, Type::Infer(_)));
        } else {
            unreachable!()
        }
    }

    #[test]
    fn constrain_propagates_when_var_already_has_lower_bound() {
        // β has Int as a lower bound (e.g. Int has flowed in). Now
        // constrain_subtype β <: String. The propagation rule pushes the new
        // upper through β's existing lowers, raising Int <: String —
        // which fails as expected.
        let beta = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &beta, &mut cache).unwrap();
        let result = constrain_subtype(&beta, &prim(BaseType::String), &mut cache);
        assert!(matches!(result, Err(ConstrainError::Mismatch { .. })));
    }

    #[test]
    fn constrain_function_via_var_succeeds() {
        // λx. x typed as α -> α; constrain_subtype α -> α <: Int -> Int succeeds.
        let v = fresh_var(0);
        let identity = fun(v.clone(), v.clone());
        let int_to_int = fun(prim(BaseType::Int), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&identity, &int_to_int, &mut cache).is_ok());
    }

    /// `[A] <: [A, B]` — subtype's tag set is a subset of supertype's. Accept.
    #[test]
    fn variant_width_sub_accept() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs, &mut cache).expect("[A] <: [A, B] should hold");
    }

    /// `[A, B] <: [A]` — supertype is missing a tag that lhs has. Reject.
    #[test]
    fn variant_width_sub_reject_missing_tag() {
        let lhs = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        let rhs = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        let err = constrain_subtype(&lhs, &rhs, &mut cache)
            .expect_err("[A, B] <: [A] should be rejected: B not in rhs");
        match err {
            ConstrainError::ExtraTag { tag, .. } => {
                assert_eq!(tag, FieldKey::Name(SmolStr::from("B")))
            }
            other => panic!("expected ExtraTag, got {other:?}"),
        }
    }

    /// Payload depth is covariant: `[A(Int)] <: [A(Int)]` passes,
    /// `[A(Int)] <: [A(Str)]` fails on payload mismatch.
    #[test]
    fn variant_payload_covariance() {
        let lhs = variant([("A", prim(BaseType::Int))]);
        let rhs_ok = variant([("A", prim(BaseType::Int))]);
        let rhs_bad = variant([("A", prim(BaseType::String))]);

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_ok, &mut c).expect("equal payloads accept");

        let mut c = ConstrainCache::new();
        constrain_subtype(&lhs, &rhs_bad, &mut c)
            .expect_err("Int payload should not flow into String payload");
    }

    /// Variable on lhs flowed against a variant: rhs becomes upper bound;
    /// subsequent lower-bound additions on lhs propagate against rhs.
    #[test]
    fn variant_var_lhs_propagation() {
        let v = fresh_var(0);
        let upper = variant([("A", prim(BaseType::Int))]);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &upper, &mut cache).unwrap();
        // The propagation rule recorded `upper` on v's upper bounds. A
        // subsequent `concrete <: v` adds concrete to lower and propagates
        // it against upper — concrete must satisfy `concrete <: upper`.
        let concrete_ok = variant([("A", prim(BaseType::Int))]);
        constrain_subtype(&concrete_ok, &v, &mut cache).expect("[A(Int)] <: v <: [A(Int)] ok");

        let v2 = fresh_var(0);
        let upper2 = variant([("A", prim(BaseType::Int))]);
        let mut cache2 = ConstrainCache::new();
        constrain_subtype(&v2, &upper2, &mut cache2).unwrap();
        let concrete_bad = variant([("A", prim(BaseType::Int)), ("B", prim(BaseType::String))]);
        constrain_subtype(&concrete_bad, &v2, &mut cache2)
            .expect_err("[A, B] must not flow into v whose upper is [A]");
    }

    // --- Feed handles (`Type::History { kind: Feed }`) ---

    /// A feed history over `domain ⇒ value`. Its read view is the whole
    /// stream `Fun { domain, value }` (unlike an `Overwrite`, which derefs to the
    /// scalar `value`); the invariant `constrain` arms treat it as that `Fun`.
    fn feed_ty(domain: Type, value: Type) -> Type {
        Type::History {
            value: Box::new(value),
            domain: Box::new(domain),
            history_kind: HistoryKind::Append,
        }
    }

    #[test]
    fn feed_meets_feed_invariantly() {
        // feed(D, a) <: feed(D, b) equates value and domain: a contribution
        // that later lands on b (the function-parameter side) must reach a (the
        // caller's argument) — and an incompatible read off a must then fail.
        let a = fresh_var(0);
        let b = fresh_var(0);
        let d = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &feed_ty(d.clone(), a.clone()),
            &feed_ty(d.clone(), b.clone()),
            &mut cache,
        )
        .unwrap();
        // The callee feeds an Int into its parameter's value.
        constrain_subtype(&prim(BaseType::Int), &b, &mut cache).unwrap();
        // Reading the caller's value as a String must now fail: the Int
        // contribution flowed backwards through the invariant edge.
        assert!(matches!(
            constrain_subtype(&a, &prim(BaseType::String), &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn feed_reads_transparently_as_stream() {
        // feed(D, Int) <: (D ⤇ Int) — a non-feed consumer reads the whole
        // stream, which is the accumulated *collection*…
        let d = Type::UIntRange(3);
        let mut cache = ConstrainCache::new();
        assert!(
            constrain_subtype(
                &feed_ty(d.clone(), prim(BaseType::Int)),
                &data_fun(d.clone(), prim(BaseType::Int)),
                &mut cache
            )
            .is_ok()
        );
        // …but the stream's value still has to match the consumer.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &feed_ty(d.clone(), prim(BaseType::Int)),
                &data_fun(d, prim(BaseType::String)),
                &mut cache
            ),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn plain_value_is_not_a_feed() {
        // Int </: feed(D, Int) — reading a feed handle is transparent, but the
        // write capability cannot be conjured from a plain (non-stream) value.
        // A `Fun` LHS aligns into the feed (that is how `x << stream` works);
        // only a scalar hits the `NotAFeed` arm.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &prim(BaseType::Int),
                &feed_ty(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache
            ),
            Err(ConstrainError::NotAFeed { .. })
        ));
    }

    #[test]
    fn feed_in_var_bounds_discharges_through_read() {
        // `x << y` chains feed(D, ρ_y) as a lower bound of ρ_x; a later read
        // `ρ_x <: (D ⤇ Int)` must discharge through the feed handle
        // transparently.
        let d = Type::UIntRange(3);
        let x = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&feed_ty(d.clone(), prim(BaseType::Int)), &x, &mut cache).unwrap();
        assert!(constrain_subtype(&x, &data_fun(d, prim(BaseType::Int)), &mut cache).is_ok());
    }

    #[test]
    fn feed_var_coalesces_to_feed() {
        // A var bounded by feed(D, Int) coalesces carrying the Feed
        // constructor (the `history_slot` survives compact → simplify →
        // coalesce). An `Overwrite` handle reaching a variable survives the same
        // way — the relation holds no rule that would collapse it to its value,
        // because a read derefs at the rule that emits it instead.
        use crate::ccl::infer::solver::simplify_type;
        let v = fresh_var(0);
        let h = feed_ty(Type::UIntRange(3), prim(BaseType::Int));
        let mut cache = ConstrainCache::new();
        constrain_subtype(&h, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(out, h);
    }

    #[test]
    fn feed_payload_level_and_freshen() {
        // `type_level` sees through the value; freshening a quantified value
        // var mints a fresh one (freshening is polarity-free).
        use crate::ccl::infer::solver::{FreshenCache, FreshenLevel, freshen_above};
        let v1 = fresh_var(1);
        let h = feed_ty(Type::UIntRange(3), v1.clone());
        assert_eq!(type_level(&h), 1);
        let inst = freshen_above(0, &h, FreshenLevel::At(0), &mut FreshenCache::new());
        assert_eq!(type_level(&inst), 0);
        let Type::History { value, .. } = &inst else {
            panic!("freshen changed the constructor: {inst}");
        };
        let (Type::Infer(orig), Type::Infer(minted)) = (&v1, value.as_ref()) else {
            unreachable!("fresh_var yields Type::Infer");
        };
        assert_ne!(
            orig.uid, minted.uid,
            "quantified value var must be freshened"
        );
    }

    #[test]
    fn feed_extrudes_with_two_way_proxy() {
        // Extruding feed(D, ?v@1) to level 0 must produce feed(D, ?proxy@0)
        // with the original linked to the proxy in BOTH directions — the
        // invariant value may neither lose writes (lower) nor reads (upper)
        // across the level boundary.
        let v1 = fresh_var(1);
        let h = feed_ty(Type::UIntRange(3), v1.clone());
        let out = extrude(&h, true, 0, &mut ExtrudeCache::new());
        let Type::History { value, .. } = &out else {
            panic!("extrude changed the constructor: {out}");
        };
        let Type::Infer(proxy) = value.as_ref() else {
            panic!("extruded value should be the proxy var, got {value}");
        };
        assert_eq!(proxy.level, 0);
        let Type::Infer(orig) = &v1 else {
            unreachable!("fresh_var yields Type::Infer");
        };
        let bounds = orig.bounds.borrow();
        let proxy_ty = Type::Infer(Rc::clone(proxy));
        assert!(
            bounds.upper().iter().any(|b| b.ty == proxy_ty),
            "original value var is missing the upper link to its proxy"
        );
        assert!(
            bounds.lower().iter().any(|b| b.ty == proxy_ty),
            "original value var is missing the lower link to its proxy"
        );
    }

    #[test]
    fn invariant_extrude_upgrades_a_one_way_polar_cache_hit() {
        // The same variable appears in BOTH a polar position and an invariant
        // (`Feed` value) payload within one type. The structural walk extrudes
        // the polar occurrence first — minting a *one-way* proxy cached under
        // that polarity — then reaches the `Feed` value, whose
        // `extrude_invariant` hits the cache. The cached proxy must be upgraded
        // to link the original in BOTH directions; otherwise the invariant
        // payload silently loses one bound direction across the level boundary.
        let v1 = fresh_var(1);
        let Type::Infer(orig) = &v1 else {
            unreachable!("fresh_var yields Type::Infer");
        };
        // Tuple element 0 (covariant, polar) extrudes before element 1's `Feed`
        // value (invariant), so the one-way polar proxy lands in the cache
        // first and the `Feed` extrusion is the cache hit under test.
        let ty = Type::Tuple(vec![v1.clone(), feed_ty(Type::UIntRange(3), v1.clone())]);
        let out = extrude(&ty, true, 0, &mut ExtrudeCache::new());
        let Type::Tuple(elems) = &out else {
            panic!("extrude changed the constructor: {out}");
        };
        let Type::Infer(polar_proxy) = &elems[0] else {
            panic!(
                "polar element should extrude to a proxy var, got {}",
                elems[0]
            );
        };
        let Type::History { value, .. } = &elems[1] else {
            panic!("second element should stay a Feed, got {}", elems[1]);
        };
        let Type::Infer(feed_proxy) = value.as_ref() else {
            panic!("feed value should extrude to a proxy var, got {value}");
        };
        // The invariant position must reuse the polar proxy — same original
        // variable — not mint a disconnected second one.
        assert!(
            Rc::ptr_eq(polar_proxy, feed_proxy),
            "invariant position minted a second proxy instead of reusing the polar one"
        );
        // Both bound directions must survive the cache hit.
        let proxy_ty = Type::Infer(Rc::clone(feed_proxy));
        let bounds = orig.bounds.borrow();
        assert!(
            bounds.upper().iter().any(|b| b.ty == proxy_ty),
            "original is missing the upper (positive) link to its proxy"
        );
        assert!(
            bounds.lower().iter().any(|b| b.ty == proxy_ty),
            "original is missing the lower (negative) link after the cache hit"
        );
    }

    // --- Mutable handles (`Type::History { kind: Overwrite }`) ---

    fn mut_ty(value: Type, domain: Type) -> Type {
        Type::History {
            value: Box::new(value),
            domain: Box::new(domain),
            history_kind: HistoryKind::Overwrite,
        }
    }

    // There is no deref arm to test: a mutable variable mention that denotes its value is
    // dereffed by the rule that emits it (`emit::emit_value_read`), so `Mut(V) <: V` is not
    // a subtyping fact. That `cnt + 1` yields `Int` rather than leaving a `Mut` on an
    // inference variable is pinned where it is decided,
    // `a_mut_var_read_yields_its_value_in_a_value_position` in `tests/type_check.rs`.

    #[test]
    fn mut_meets_mut_invariantly() {
        // Mut(?v0,?d0) <: Mut(?v1,?d1) equates values AND domains (pass-by-ref):
        // the callee's per-call domain resolves to the argument mutable variable's domain,
        // and the value is invariant (read + write). A value flowing into v1
        // reaches v0 through the two-way edge, so a conflicting read of v0 fails.
        let (v0, d0, v1, d1) = (fresh_var(0), fresh_var(0), fresh_var(0), fresh_var(0));
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &mut_ty(v0.clone(), d0.clone()),
            &mut_ty(v1.clone(), d1.clone()),
            &mut cache,
        )
        .unwrap();
        constrain_subtype(&prim(BaseType::Int), &v1, &mut cache).unwrap();
        assert!(matches!(
            constrain_subtype(&v0, &prim(BaseType::String), &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
        // The domains equated too: a value pinned on d1 conflicts on d0.
        constrain_subtype(&prim(BaseType::UInt), &d1, &mut cache).unwrap();
        assert!(matches!(
            constrain_subtype(&d0, &prim(BaseType::String), &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn a_value_does_not_satisfy_a_mut_demand() {
        // `Int <: Mut(Int, D)` is **not** a subtyping fact, the mirror of
        // `Mut(V) <: V` not being one: a mutable variable is neither above nor below its
        // value, and a relation that coerces either way cannot tell a read from a
        // handle. A position that means the value says so itself — `emit_apply`
        // reads through the parameter's handle for a pass-by-reference argument,
        // and every other operand derefs at `emit::emit_value_read`.
        let m = mut_ty(prim(BaseType::Int), prim(BaseType::UInt));
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&prim(BaseType::Int), &m, &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    /// Build a refinement whose predicate is the **bare** `__elem > <rhs>` —
    /// the element is the implicit `REFINEMENT_BINDER`, free in the predicate,
    /// exactly as real refinements are shaped (no element-binding lambda).
    fn gt_refinement(rhs: TypedExpr) -> Refinement {
        let pred = TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Greater),
            rhs,
        );
        Refinement::born(Rc::new(pred))
    }

    fn coalesce(ty: &Type) -> Type {
        coalesce_compact(&compact_type(ty)).expect("coalesce")
    }

    /// The refinement predicate of a `Fun(Refinement(_, r), _)`, rendered.
    fn domain_predicate(ty: &Type) -> String {
        let Type::Fun { domain, .. } = ty else {
            panic!("expected fun, got {ty}");
        };
        let [r] = domain.refinements() else {
            panic!("expected a singly-refined domain, got {domain}");
        };
        crate::ccl::symbolic::symbolic(&r.predicate)
    }

    // renaming the codomain refinement's reference to the bound key.
    #[test]
    fn pi_correspondence_renames_codomain_refinement() {
        let arena = crate::ccl::infer::InferArena::new();
        let result = fresh_var(0);
        let Type::Infer(result_var) = &result else {
            unreachable!()
        };

        // g : (k: Int) ⇒ ({i | i > k} ⇒ Int)
        let g_ty = Type::pi(
            "k",
            prim(BaseType::Int),
            Type::fun(
                Type::refined_one(prim(BaseType::Int), gt_refinement(TypedExpr::var("k"))),
                prim(BaseType::Int),
            ),
        );
        // expected : (x: Int) ⇒ result
        let expected = Type::pi("x", prim(BaseType::Int), result.clone());

        let mut cache = ConstrainCache::new();
        constrain_subtype(&g_ty, &expected, &mut cache).expect("constrain");

        // result coalesces to `{i | i > x} ⇒ Int` — k renamed to the expected
        // binder x by the derived correspondence.
        let res = coalesce(&Type::Infer(Rc::clone(result_var)));
        assert_eq!(domain_predicate(&res), "__elem > x");
        drop(arena);
    }

    // at coalesce, yielding the fully-substituted predicate `i > 0`: the
    // dependent application `g(0)`.
    #[test]
    fn dependent_application_discharges_through_coalesce() {
        let arena = crate::ccl::infer::InferArena::new();
        let result = fresh_var(0);
        let Type::Infer(result_var) = &result else {
            unreachable!()
        };

        let g_ty = Type::pi(
            "k",
            prim(BaseType::Int),
            Type::fun(
                Type::refined_one(prim(BaseType::Int), gt_refinement(TypedExpr::var("k"))),
                prim(BaseType::Int),
            ),
        );
        let expected = Type::pi("x", prim(BaseType::Int), result.clone());
        let mut cache = ConstrainCache::new();
        constrain_subtype(&g_ty, &expected, &mut cache).expect("constrain");

        // The application term γ: its type is `result` under the discharge
        // [x ↦ 0] (what emit_apply mints).
        let gamma = fresh_var(0);
        let Type::Infer(gamma_var) = &gamma else {
            unreachable!()
        };
        gamma_var
            .bounds
            .borrow_mut()
            .lower_mut()
            .push(Bound::with_subst(
                Type::Infer(Rc::clone(result_var)),
                Subst::discharge("x", TypedExpr::lit(Lit::Int(0))),
            ));

        let app_ty = coalesce(&Type::Infer(Rc::clone(gamma_var)));
        // g(0) : {i | i > 0} ⇒ Int — both the correspondence rename and the
        // discharge fired, composed along the coalesce walk.
        assert_eq!(domain_predicate(&app_ty), "__elem > 0");
        drop(arena);
    }

    /// `g : (k: Int) ⇒ ({i | i > k} ⇒ Int)`, shared by the dependent-edge
    /// order tests below.
    fn dependent_g_ty() -> Type {
        Type::pi(
            "k",
            prim(BaseType::Int),
            Type::fun(
                Type::refined_one(prim(BaseType::Int), gt_refinement(TypedExpr::var("k"))),
                prim(BaseType::Int),
            ),
        )
    }

    // application result flows into a consumer (a contravariant argument
    // slot) BEFORE the function's concrete codomain arrives (the function
    // was a parameter; its value reaches the apply site last). The consumer
    // edge is recorded across `result` while the discharge `[x ↦ 0]` is the
    // only morphism in hand; when `Cod` arrives later it must cross that
    // edge still wearing the discharge. The regression this guards:
    // holder-context-normalized storage (invert at record, re-invert at
    // closure) destroys the non-invertible discharge in the round trip,
    // leaving the consumer's copy with a free binder — `i > x` instead of
    // `i > 0`.
    #[test]
    fn dependent_discharge_survives_opaque_constraint_order() {
        let arena = crate::ccl::infer::InferArena::new();
        let result = fresh_var(0);
        let Type::Infer(result_var) = &result else {
            unreachable!()
        };
        let expected = Type::pi("x", prim(BaseType::Int), result.clone());
        let mut cache = ConstrainCache::new();

        // g(0): the application's type is `result` under [x ↦ 0].
        let gamma = fresh_var(0);
        let Type::Infer(gamma_var) = &gamma else {
            unreachable!()
        };
        gamma_var
            .bounds
            .borrow_mut()
            .lower_mut()
            .push(Bound::with_subst(
                Type::Infer(Rc::clone(result_var)),
                Subst::discharge("x", TypedExpr::lit(Lit::Int(0))),
            ));

        // The consumer edge first: g(0) flows into an argument slot.
        let consumer = fresh_var(0);
        let Type::Infer(consumer_var) = &consumer else {
            unreachable!()
        };
        constrain_subtype(&gamma, &consumer, &mut cache).expect("g(0) <: consumer");

        // The function's concrete type arrives last (opaque order).
        constrain_subtype(&dependent_g_ty(), &expected, &mut cache).expect("g <: expected");

        // Both materializations must show the discharged predicate.
        let app_ty = coalesce(&Type::Infer(Rc::clone(gamma_var)));
        assert_eq!(domain_predicate(&app_ty), "__elem > 0", "result node");
        let consumer_ty = coalesce(&Type::Infer(Rc::clone(consumer_var)));
        assert_eq!(
            domain_predicate(&consumer_ty),
            "__elem > 0",
            "consumer copy (crossed the upper edge)"
        );
        drop(arena);
    }

    // both flowing into one position: the constraint `Cod <: V` arrives
    // twice with *different* morphisms (`[k ↦ 0]`, `[k ↦ 1]`). A cache
    // keyed on the `(lhs, rhs)` pair alone conflates them and silently
    // swallows the second edge; V must receive both discharged copies.
    #[test]
    fn distinct_discharges_of_one_codomain_both_recorded() {
        let arena = crate::ccl::infer::InferArena::new();
        let g_ty = dependent_g_ty();
        let mut cache = ConstrainCache::new();
        let v = fresh_var(0);
        let Type::Infer(vv) = &v else { unreachable!() };

        for lit in [0i64, 1] {
            let r = fresh_var(0);
            let expected = Type::pi("k", prim(BaseType::Int), r.clone());
            constrain_subtype(&g_ty, &expected, &mut cache).expect("g <: expected");
            let app = fresh_var(0);
            let Type::Infer(av) = &app else {
                unreachable!()
            };
            av.bounds.borrow_mut().lower_mut().push(Bound::with_subst(
                r.clone(),
                Subst::discharge("k", TypedExpr::lit(Lit::Int(lit))),
            ));
            constrain_subtype(&app, &v, &mut cache).expect("app <: V");
        }

        let lows = Rc::clone(vv.bounds.borrow().lower());
        let rendered: Vec<String> = lows
            .iter()
            .map(|b| format!("{}", b.materialize()))
            .collect();
        assert_eq!(
            lows.len(),
            2,
            "V must receive BOTH discharged copies, got: {rendered:?}"
        );
        drop(arena);
    }

    // their emit-time inference-var type slots, must bridge as one fiber
    // rather than hitting the distinct-discharge tripwire. A discharge
    // captures its argument expression at emit time; two syntactic
    // occurrences of the same argument (or one type reaching a variable
    // along two propagation paths) mint distinct `Infer` slots, so strict
    // structural `Subst` equality misses and only `eq_modulo_ty_slots`
    // recognizes the captures as the same written term.
    #[test]
    fn bridge_unifies_same_fiber_captures_with_distinct_ty_slots() {
        let arena = crate::ccl::infer::InferArena::new();
        // Non-var capture (`y + 1`) so neither side is rename-shaped; fresh
        // slot per capture, as emission would mint.
        let capture = || {
            let mut y = TypedExpr::var("y");
            y.ty = fresh_var(0);
            TypedExpr::binop(
                y,
                BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
                TypedExpr::lit(Lit::Int(1)),
            )
        };
        let lo = Subst::discharge("k", capture());
        let hi = Subst::discharge("k", capture());
        assert_ne!(lo, hi, "premise: strict equality misses (distinct slots)");

        let (tau_l, tau_u) = bridge_holder_gap(&lo, &hi);
        assert!(
            tau_l.is_id() && tau_u.is_id(),
            "same-written captures must bridge as the same fiber"
        );
        drop(arena);
    }

    // `Subst::eq_modulo_ty_slots` (backed by the codebase's type-blind
    // `eq_refinement_predicate`) — the comparison the bridge relies on:
    // insensitive to inferred slots (positive), but a genuine structural or
    // name difference must still distinguish (negatives — what keeps the
    // bridge from conflating genuinely different fibers).
    #[test]
    fn eq_modulo_ty_slots_ignores_slots_but_not_structure() {
        let arena = crate::ccl::infer::InferArena::new();
        let capture = |name: &str, lit: i64| {
            let mut v = TypedExpr::var(name);
            v.ty = fresh_var(0);
            Subst::discharge(
                "k",
                TypedExpr::binop(
                    v,
                    BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
                    TypedExpr::lit(Lit::Int(lit)),
                ),
            )
        };
        // Same written term, distinct slots: equal.
        assert!(capture("y", 1).eq_modulo_ty_slots(&capture("y", 1)));
        // Different literal: unequal.
        assert!(!capture("y", 1).eq_modulo_ty_slots(&capture("y", 2)));
        // Different variable name: unequal.
        assert!(!capture("y", 1).eq_modulo_ty_slots(&capture("z", 1)));
        // Binder slots are blind too: identical lambda captures whose param
        // slots differ compare equal.
        let lam = || {
            let mut l = TypedExpr::lambda("w", Type::Hole, TypedExpr::var("w"));
            if let TypedExprNode::Lambda { param, .. } = &mut l.node {
                param.ty = fresh_var(0);
            }
            Subst::discharge("k", l)
        };
        assert!(lam().eq_modulo_ty_slots(&lam()));
        drop(arena);
    }

    // ----- FunKind edge (`Data` and `Compute` are incomparable) -----------

    // --- Conditional-collection Sigma rules (subtyping: the Σ rule; consumption:
    //     consume) — see `design/type-inference.md`, "4.6 Data vs compute functions" ---

    /// The sum over `domains` — `Σ (𝐷 : [domains]). 𝐷 ⤇ Int`, what materializing a merged
    /// domain's type kind produces.
    fn conditional(domains: Vec<Type>) -> Type {
        Type::sum_over(TypeKind::Enumerated(domains), None, prim(BaseType::Int))
    }

    /// **A map's key bounds its domains, so the type kinds order by the bound.**
    /// `SubtypesOf` is the first type kind with a parameter, and this is what the parameter buys: a demand
    /// for a map keyed by `Int` is satisfied by one keyed by a *refined* `Int`, because
    /// every domain below the refinement is below `Int`. The converse is not a subtype —
    /// a domain below `Int` need not satisfy the refinement.
    ///
    /// Contrast [`conditional_is_subtype_by_candidate_subset`], where the kinds *list* their
    /// domains and
    /// containment is a pairing: here nothing is enumerated and the containment is one
    /// covariant edge on the bounds.
    #[test]
    fn a_map_orders_by_its_key_bound() {
        let string = || prim(BaseType::String);
        let narrow = Type::map_of(refined(prim(BaseType::Int), 7), string());
        let wide = Type::map_of(prim(BaseType::Int), string());
        assert!(
            constrain_subtype(&narrow, &wide, &mut ConstrainCache::new()).is_ok(),
            "a map keyed by a refined Int satisfies a demand for one keyed by Int"
        );
        assert!(
            constrain_subtype(&wide, &narrow, &mut ConstrainCache::new()).is_err(),
            "and not conversely"
        );
    }

    /// **A map's key type is inferred from the domains that reach it.** Two boxed
    /// collections joined by a conditional are a sum over named candidates; passing that
    /// where a `Map(?k, V)` is demanded relates those candidates to `SubtypesOf(?k)`, and the
    /// containment is one edge per candidate — so both domains land below `?k` and the key
    /// is determined by what was joined rather than annotated.
    ///
    /// The candidate-pairing rule cannot do this: it pairs each candidate *invariantly*
    /// against one of the other kind's, so an unannotated key would have to equal both
    /// domains at once and nothing would flow into it.
    #[test]
    fn a_map_key_is_inferred_from_the_domains_that_reach_it() {
        let arena = crate::ccl::infer::InferArena::new();
        let key = fresh_var(0);
        let Type::Infer(kv) = key.clone() else {
            unreachable!("fresh_var is an inference variable")
        };
        let joined = conditional(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let demand = Type::map_of(key, prim(BaseType::Int));
        constrain_subtype(&joined, &demand, &mut ConstrainCache::new())
            .expect("named domains lie below a bound nothing has fixed");
        let lows = Rc::clone(kv.bounds.borrow().lower());
        let rendered: Vec<String> = lows
            .iter()
            .map(|b| format!("{}", b.materialize()))
            .collect();
        assert_eq!(
            rendered,
            vec!["[0, 1]".to_string(), "[0, 2]".to_string()],
            "both joined domains lie below the key"
        );
        drop(arena);
    }

    /// **A key bound names no domains to pair.** So no set of candidates contains it however
    /// wide the bound is — the direction that would let a map be read as a conditional
    /// collection over an enumerable set of keys.
    #[test]
    fn a_map_kind_is_contained_in_no_candidate_set() {
        let map = Type::map_of(prim(BaseType::Int), prim(BaseType::Int));
        let named = conditional(vec![Type::UIntRange(2)]);
        assert!(constrain_subtype(&map, &named, &mut ConstrainCache::new()).is_err());
    }

    /// **Candidates lie below a kind that admits every one of them.** The premise is set
    /// containment, so it is asked once per candidate and `Type` — which admits all of them
    /// — is above every kind and below nothing narrower.
    #[test]
    fn candidates_lie_below_a_kind_that_admits_them() {
        let sum = |kind| Type::sum_over(kind, None, prim(BaseType::Int));
        let ranges = sum(TypeKind::UIntRanges);
        let named = sum(TypeKind::Enumerated(vec![
            Type::UIntRange(2),
            Type::UIntRange(3),
        ]));
        let filtered = sum(TypeKind::Enumerated(vec![refined(Type::UIntRange(3), 7)]));
        let universe = sum(TypeKind::Type);

        assert!(
            constrain_subtype(&named, &ranges, &mut ConstrainCache::new()).is_ok(),
            "every candidate is a range"
        );
        assert!(
            constrain_subtype(&filtered, &ranges, &mut ConstrainCache::new()).is_err(),
            "a refined range is not a range, so a filtered collection is not a `List`"
        );
        for k in [&named, &ranges, &universe] {
            assert!(
                constrain_subtype(k, &universe, &mut ConstrainCache::new()).is_ok(),
                "{k} <: ⊤"
            );
        }
        assert!(
            constrain_subtype(&universe, &ranges, &mut ConstrainCache::new()).is_err(),
            "⊤ is below nothing narrower"
        );
    }

    /// **An unresolved candidate is not a rejection.** It has no shape to read a property
    /// off, so it takes the kinding edge and is answered wherever a type reaches it — which
    /// is what lets a generalized definition carry a `List` annotation whose source only its
    /// uses can supply (`test_kinding_constraint_survives_instantiation`).
    #[test]
    fn an_unresolved_candidate_takes_the_kinding_edge() {
        let arena = crate::ccl::infer::InferArena::new();
        let sum = |kind| Type::sum_over(kind, None, prim(BaseType::Int));
        let d = fresh_var(0);
        let Type::Infer(v) = d.clone() else {
            unreachable!("fresh_var is an inference variable")
        };
        constrain_subtype(
            &sum(TypeKind::Enumerated(vec![d])),
            &sum(TypeKind::UIntRanges),
            &mut ConstrainCache::new(),
        )
        .expect("an unresolved candidate defers rather than rejecting");
        assert_eq!(
            v.bounds.borrow().type_kinds,
            vec![TypeKind::UIntRanges],
            "the demand rides the candidate until it resolves"
        );
        drop(arena);
    }

    #[test]
    fn conditional_is_subtype_by_candidate_subset() {
        // A conditional collection is a Sigma over candidate domains;
        // the kind premise is by-value subset — every lhs candidate domain
        // appears among the rhs candidates. The reverse (rhs has an extra
        // domain the lhs lacks) is not a subtype.
        let sub = conditional(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let sup = conditional(vec![
            Type::UIntRange(2),
            Type::UIntRange(3),
            Type::UIntRange(4),
        ]);
        assert!(constrain_subtype(&sub, &sup, &mut ConstrainCache::new()).is_ok());
        assert!(constrain_subtype(&sup, &sub, &mut ConstrainCache::new()).is_err());
    }

    #[test]
    fn conditional_consumed_as_fun() {
        // A conditional collection reaching a consumer pins the consumer's kind
        // variable; a *fresh* domain var accumulates the witness (the `sum` /
        // comprehension case).
        let cond = conditional(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let consumer = Type::consumer_fun(fresh_var(0), prim(BaseType::Int));
        assert!(constrain_subtype(&cond, &consumer, &mut ConstrainCache::new()).is_ok());
        // A consumer demanding a *concrete narrower* domain fails: the concrete type
        // meets the witness at every candidate, and `[0, 3)` is not `[0, 2)` — the
        // conditional collection never silently narrows to a single domain.
        let narrow = Type::consumer_fun(Type::UIntRange(2), prim(BaseType::Int));
        assert!(constrain_subtype(&cond, &narrow, &mut ConstrainCache::new()).is_err());
    }

    // --- `UIntRanges`-kind Sigma rules (List): consumption, subtyping ---

    /// **A kind naming no candidates is consumed by the same rule candidates are.** Naming
    /// the witness needs no candidates — that is what naming buys over presenting — so
    /// `List`'s `UIntRanges` and `Collection`'s `Type` reach a consumer through the factored
    /// arm with nothing to enumerate.
    ///
    /// Worth its own test because the failure is silent in the other direction: a rule
    /// written to read candidates first answers `None` for `UIntRanges` and falls through to
    /// a flat mismatch, so a `List(𝑇)` annotation stops being consumable and nothing else in
    /// the suite says why.
    #[test]
    fn a_kind_naming_no_candidates_pins_a_consumer() {
        let int = prim(BaseType::Int);
        for kind in [TypeKind::UIntRanges, TypeKind::Type] {
            let collection = Type::sum_over(kind.clone(), None, int.clone());
            // A consumer with a fresh domain variable: the common case (`sum`, a
            // comprehension). Its domain accumulates the witness.
            let consumer = Type::consumer_fun(fresh_var(0), int.clone());
            assert!(
                constrain_subtype(&collection, &consumer, &mut ConstrainCache::new()).is_ok(),
                "a {kind} collection must be consumable: {collection}"
            );
        }
    }

    /// The **cross-form** Σ edge: the unfactored sum `box` builds, below the
    /// factored sum a `List(𝑉)` annotation is. Both spellings of one type, so this is
    /// the ordinary Σ rule read on instantiated bodies — and it is the edge every
    /// `List`-annotated parameter depends on.
    #[test]
    fn a_boxed_collection_is_below_a_list_annotation() {
        let int = prim(BaseType::Int);
        let boxed = Type::sum_over(
            TypeKind::Enumerated(vec![Type::UIntRange(2)]),
            None,
            int.clone(),
        );
        let list = Type::list_of(int);
        assert!(
            constrain_subtype(&boxed, &list, &mut ConstrainCache::new()).is_ok(),
            "box(xs) must reach List(V) by the Σ rule"
        );
    }

    // ----- FunKind edge (the `Compute <: Data` rejection) -----------

    fn data_fun(d: Type, c: Type) -> Type {
        Type::data_fun(d, c)
    }

    #[test]
    fn kind_data_where_compute_is_rejected() {
        // `Data ⋠ Compute`: there is no upcast from a collection to a
        // capability. A collection's domain is invariant — it *is* the data — so
        // re-viewing it as a capability, whose domain is contravariant, is not a
        // weakening of the same claim but a different one.
        // `[0, 2] ⤇ Int ⊀ [0, 2] ⇒ Int`.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache,
            ),
            Err(ConstrainError::KindMismatch { .. })
        ));
    }

    #[test]
    fn kind_compute_where_data_is_rejected() {
        // `Compute ⋠ Data`: a capability supplied where a collection is demanded is
        // the rejection (the silent-row-loss guard). `[0, 2] ⇒ Int ⊀ [0, 2] ⤇ Int`.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache,
            ),
            Err(ConstrainError::KindMismatch { .. })
        ));
    }

    /// **One rule, every derivation.** A check asks what the solve asks, so a rejection is a
    /// rejection wherever the edge is drawn — the previous version of this test named every
    /// cache and used one.
    #[test]
    fn a_rejection_holds_at_every_derivation() {
        for derivation in [
            Derivation::LiveSolve,
            Derivation::PostPass,
            Derivation::SubTree,
        ] {
            // A capability where a collection is demanded: the fun-kind rejection.
            assert!(
                matches!(
                    constrain_subtype(
                        &fun(Type::UIntRange(3), prim(BaseType::Int)),
                        &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                        &mut ConstrainCache::for_derivation(derivation),
                    ),
                    Err(ConstrainError::KindMismatch { .. })
                ),
                "a capability reaching a collection position is caught at {derivation:?}"
            );
            // **The Σ kind premise, at every derivation.** The universe is not contained in
            // a key bound, so a collection where a keyed collection is demanded is a
            // rejection — and it is the only premise that looks at the kinds, the domain edge
            // being discharged by the binder correspondence.
            assert!(
                constrain_subtype(
                    &Type::collection_of(prim(BaseType::Int)),
                    &Type::map_of(prim(BaseType::Int), prim(BaseType::Int)),
                    &mut ConstrainCache::for_derivation(derivation),
                )
                .is_err(),
                "Collection is not below Map at {derivation:?}"
            );
            // A candidate dropped is a narrower kind, and narrower is not above.
            assert!(
                constrain_subtype(
                    &conditional(vec![Type::UIntRange(2), Type::UIntRange(3)]),
                    &conditional(vec![Type::UIntRange(2)]),
                    &mut ConstrainCache::for_derivation(derivation),
                )
                .is_err(),
                "a sum with an extra candidate is not below one without it at {derivation:?}"
            );
            // What must still be accepted: a keyed collection *is* a collection.
            assert!(
                constrain_subtype(
                    &Type::map_of(prim(BaseType::Int), prim(BaseType::Int)),
                    &Type::collection_of(prim(BaseType::Int)),
                    &mut ConstrainCache::for_derivation(derivation),
                )
                .is_ok(),
                "Map is below Collection at {derivation:?}"
            );
        }
    }

    /// A function over a fixed domain and codomain, so a test varies only the
    /// kind — which is the only thing `constrain_fun_kind` reads.
    fn fun_at(fun_kind: FunKind) -> Type {
        Type::Fun {
            name: None,
            fun_kind,
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(prim(BaseType::Int)),
        }
    }

    #[test]
    fn a_var_var_kind_edge_makes_each_side_read_the_other_s_pin() {
        // The edge relates the two kinds, so a pin either side carries is a pin
        // both read — whichever side it was recorded on.
        let (a, b) = (FunKindVar::fresh(), FunKindVar::fresh());
        let mut cache = ConstrainCache::new();
        // Pin `a` to compute, leaving `b` unpinned.
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Compute),
            &mut cache,
        )
        .expect("a var meeting Compute records the pin");
        assert_eq!(a.resolved(), KindPin::Compute);
        assert_eq!(b.resolved(), KindPin::Unpinned);

        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&b))),
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &mut cache,
        )
        .expect("a var-var kind edge is never a rejection");
        assert_eq!(
            b.resolved(),
            KindPin::Compute,
            "the unpinned side reads the other's pin"
        );
        assert_eq!(
            a.resolved(),
            KindPin::Compute,
            "and the pinned side is unchanged"
        );
    }

    /// A pin arriving **after** the edge crosses it, which is what makes the arm
    /// order-independent: the join is folded at the read, so it sees every pin the
    /// component ever acquired rather than the ones present when the edge landed.
    #[test]
    fn a_pin_arriving_after_a_var_var_kind_edge_still_crosses_it() {
        let (a, b) = (FunKindVar::fresh(), FunKindVar::fresh());
        // The edge first, both sides unpinned — nothing to carry.
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Var(Rc::clone(&b))),
            &mut ConstrainCache::new(),
        )
        .expect("a var-var kind edge is never a rejection");
        assert_eq!(a.resolved(), KindPin::Unpinned);
        assert_eq!(b.resolved(), KindPin::Unpinned);

        // Then a concrete kind reaches `a` only.
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Data(None)),
            &mut ConstrainCache::new(),
        )
        .expect("a var meeting Data records the pin");
        // `Data(None)` is a *plain* collection, one of the three concrete kinds — the pin
        // records which, not merely that it is not a capability.
        assert_eq!(a.resolved(), KindPin::Plain);
        assert_eq!(
            b.resolved(),
            KindPin::Plain,
            "the far side of the edge reads a pin that arrived after it"
        );
    }

    /// The relation is transitive at the read, because the join folds the whole
    /// component and not just one edge's far end.
    #[test]
    fn a_pin_crosses_a_chain_of_var_var_kind_edges() {
        let (a, b, c) = (
            FunKindVar::fresh(),
            FunKindVar::fresh(),
            FunKindVar::fresh(),
        );
        for (x, y) in [(&a, &b), (&b, &c)] {
            constrain_subtype(
                &fun_at(FunKind::Var(Rc::clone(x))),
                &fun_at(FunKind::Var(Rc::clone(y))),
                &mut ConstrainCache::new(),
            )
            .expect("a var-var kind edge is never a rejection");
        }
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Data(None)),
            &mut ConstrainCache::new(),
        )
        .unwrap();
        assert_eq!(
            c.resolved(),
            KindPin::Plain,
            "two edges away, and still one answer"
        );
        assert_eq!(b.resolved(), KindPin::Plain);
        assert_eq!(a.resolved(), KindPin::Plain);
    }

    /// **A plain collection and a sum do not merge.** Neither is below the other, so one
    /// function required to be both holds two fun kinds at once — the same contradiction a
    /// capability meeting a collection is, and read at the same place.
    #[test]
    fn a_plain_collection_and_a_sum_do_not_merge() {
        let v = FunKindVar::fresh();
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &fun_at(FunKind::Data(None)),
            &fun_at(FunKind::Var(Rc::clone(&v))),
            &mut cache,
        )
        .expect("a plain collection pins the var plain");
        assert_eq!(v.resolved(), KindPin::Plain);

        let sum = Type::sum_over(
            TypeKind::Enumerated(vec![Type::UIntRange(3)]),
            None,
            prim(BaseType::Int),
        );
        let _ = constrain_subtype(&sum, &fun_at(FunKind::Var(Rc::clone(&v))), &mut cache);
        assert_eq!(
            v.resolved(),
            KindPin::Conflict,
            "a sum reaching a variable already pinned to a plain collection is the conflict"
        );
    }

    /// Pinning either end of a related pair to a different point is the conflict,
    /// read from every member — the pins are joined, never arbitrated.
    #[test]
    fn a_var_var_kind_edge_between_disagreeing_pins_conflicts_from_either_end() {
        // The pin crosses the edge, so the *second* concrete kind meets a component that
        // already holds the first — and a concrete kind settles the variable it meets, so
        // the contradiction is reported at that edge rather than carried to coalesce.
        let (a, b) = (FunKindVar::fresh(), FunKindVar::fresh());
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Var(Rc::clone(&b))),
            &mut ConstrainCache::new(),
        )
        .expect("a var-var kind edge is never a rejection");
        constrain_subtype(
            &fun_at(FunKind::Var(Rc::clone(&a))),
            &fun_at(FunKind::Compute),
            &mut ConstrainCache::new(),
        )
        .expect("nothing else has reached the component yet");
        assert!(
            matches!(
                constrain_subtype(
                    &fun_at(FunKind::Var(Rc::clone(&b))),
                    &fun_at(FunKind::Data(None)),
                    &mut ConstrainCache::new(),
                ),
                Err(ConstrainError::KindMismatch { .. })
            ),
            "a collection demanded of a component pinned compute, read from the far end"
        );
        assert_eq!(a.resolved(), KindPin::Conflict);
        assert_eq!(b.resolved(), KindPin::Conflict);
    }

    #[test]
    fn a_var_var_kind_edge_between_disagreeing_pins_is_a_conflict() {
        // Absorption, not arbitration: holding both points is `Conflict`, exactly as on a
        // concrete edge — and it is the edge that *completes* the conflict that reports it,
        // whichever kind of edge that is. A variable between the two ends hides nothing:
        // `resolved` folds the whole component.
        let fun_over = fun_at;
        let (a, b) = (FunKindVar::fresh(), FunKindVar::fresh());
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &fun_over(FunKind::Var(Rc::clone(&a))),
            &fun_over(FunKind::Compute),
            &mut cache,
        )
        .unwrap();
        constrain_subtype(
            &fun_over(FunKind::Var(Rc::clone(&b))),
            &fun_over(FunKind::Data(None)),
            &mut cache,
        )
        .unwrap();
        assert!(
            matches!(
                constrain_subtype(
                    &fun_over(FunKind::Var(Rc::clone(&a))),
                    &fun_over(FunKind::Var(Rc::clone(&b))),
                    &mut cache,
                ),
                Err(ConstrainError::KindMismatch { .. })
            ),
            "relating a compute-pinned kind to a data-pinned one is the same rejection a \
             concrete pair is"
        );
        assert_eq!(a.resolved(), KindPin::Conflict);
        assert_eq!(b.resolved(), KindPin::Conflict);
    }

    #[test]
    fn kind_var_demanded_as_data_is_pinned_data() {
        // A kind var meeting `Data` is *pinned* to it, never an eager rejection,
        // and resolves at coalesce. A compute function meeting the same var would
        // pin it the other way, and holding both points is `KindPin::Conflict`.
        let v = FunKindVar::fresh();
        let var_fun = Type::Fun {
            name: None,
            fun_kind: FunKind::Var(Rc::clone(&v)),
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(prim(BaseType::Int)),
        };
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &var_fun,
            &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
            &mut cache,
        )
        .expect("a var meeting Data records the pin, never an eager rejection");
        assert_eq!(
            v.resolved(),
            KindPin::Plain,
            "pinned to a plain collection, and no compute function met this var"
        );
    }
}

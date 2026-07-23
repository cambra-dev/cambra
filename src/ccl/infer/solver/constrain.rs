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
use crate::ccl::ty::{FunKind, FunKindVar, SigmaType, TypeKind};
use crate::ccl::{Bound, HistoryKind, InferVar, InferVarId, Level, Refinement, Type};

use super::type_level;
use crate::ccl::FieldKey;
use crate::ccl::ccl_utils::strip_refinements;

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
    /// A compute function (a capability, `⇒`) was supplied where a data
    /// collection (`⤇`) is demanded. `Data <: Compute` is the safe
    /// upcast — a collection is callable at any index in its domain — but the
    /// reverse would iterate a *declared* domain the value does not actually
    /// cover, silently dropping rows. Raised only when the cache is
    /// kind-aware (constraint emission); the post-inference check is kind-blind
    /// (see [`ConstrainCache`]), since lambda elimination preserves denotation
    /// but not kind representation.
    ComputeWhereDataRequired {
        /// The supplied compute function.
        lhs: Type,
        /// The demanded data collection.
        rhs: Type,
    },
    /// Two collections over domains that are not the same domain met at one
    /// position. A data domain is invariant (see
    /// `src/ccl/design/type-inference.md`, "Data domains are invariant"), so
    /// neither collection stands in for the other; their join is a Σ over the two
    /// candidate domains, which is not yet representable. The coalesce-time face
    /// of the same fact — reached when no edge forces the question earlier — is
    /// [`super::coalesce::CoalesceError::DomainJoinConflict`]. Like
    /// [`Self::ComputeWhereDataRequired`], raised only when the cache is
    /// kind-aware.
    DataDomainMismatch {
        /// The supplied collection's domain.
        lhs: Type,
        /// The domain demanded at the position.
        rhs: Type,
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
///
/// Carries the `kind_aware` mode flag alongside the edge map. The
/// `Compute <: Data` kind rejection (a capability supplied where a collection is
/// demanded — see [`ConstrainError::ComputeWhereDataRequired`]) fires only
/// during constraint **emission** (inference), where kinds are being inferred
/// and a mismatch is a real domain-loss bug. The post-inference structural
/// check is **kind-blind**: lambda elimination is denotation-preserving but not
/// kind-preserving (`Type::without_pi_names` canonicalizes every reconstructed
/// arrow to `Compute`), so a point-free map flowing into a `Data` argument is
/// well-denoted and must not be re-rejected on kind. FunKind is an inference-time
/// property, so the flag rides the cache that is already threaded through the
/// whole recursion.
pub struct ConstrainCache {
    edges: HashMap<(Type, Type), Vec<(Subst, Subst)>>,
    kind_aware: bool,
}

impl ConstrainCache {
    /// A kind-aware cache (constraint emission / inference): the
    /// `Compute <: Data` rejection is live.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
            kind_aware: true,
        }
    }

    /// A kind-blind cache (the post-inference structural check): kind
    /// mismatches are ignored (see the type doc).
    pub fn new_kind_blind() -> Self {
        Self {
            edges: HashMap::new(),
            kind_aware: false,
        }
    }

    /// The composite-substitution bridges recorded for a subtyping edge,
    /// inserting an empty list on first visit. This is the cycle breaker: a
    /// re-entry on the same `(lhs, rhs)` pair finds its in-progress entry rather
    /// than recursing forever.
    fn edge_bridges(&mut self, lhs: Type, rhs: Type) -> &mut Vec<(Subst, Subst)> {
        self.edges.entry((lhs, rhs)).or_default()
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

/// Constrain the kind edge `k0 <: k1` over the two-point lattice
/// `Data ⊑ Compute` (`Data` bottom / most specific, `Compute` top).
///
/// Concrete edges: `Data <: κ` and `κ <: Compute` always hold; `Compute <: Data`
/// is the sole failure — returned as `true` (the caller raises
/// [`ConstrainError::ComputeWhereDataRequired`], having the full function types
/// for the diagnostic) **iff** `kind_aware` (emission mode).
///
/// Variable edges set `forced_*` flags, resolved at coalesce
/// ([`super::compact::KindMerge`]): a compute value flowing *into* a var forces
/// it `Compute`; a var *demanded* as data forces it `Data`; a var-to-var edge
/// records a `<:` link ([`FunKindVar::link`]). Forces propagate transitively along
/// links as they arrive, so ordering does not matter (a force after its link
/// still reaches the far end). A var that ends up with both flags is the
/// conflict — surfaced loudly at coalesce, never here.
fn constrain_kind(k0: &FunKind, k1: &FunKind, kind_aware: bool) -> bool {
    use FunKind::*;
    match (k0, k1) {
        // `Data` is bottom, `Compute` is top: these edges always hold.
        (Data, _) | (_, Compute) => false,
        // The one rejection — a capability supplied where a collection is demanded.
        (Compute, Data) => kind_aware,
        // A compute value flows into this var: it cannot be `Data`. The force
        // propagates up any `<:` links already drawn to this var.
        (Compute, Var(v1)) => {
            v1.force_compute();
            false
        }
        // This var is demanded as data: it cannot be `Compute`. Propagates down.
        (Var(v0), Data) => {
            v0.force_data();
            false
        }
        // A var-to-var edge `v0 <: v1`: record the link so a force arriving on
        // either end *after* this edge still reaches the other. See [`FunKindVar`].
        (Var(v0), Var(v1)) => {
            FunKindVar::link(v0, v1);
            false
        }
    }
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
            kind: FunKind::Data,
            domain,
            ..
        } = &low.ty
        else {
            continue;
        };
        let d = low.ty_subst.apply_type(domain);
        if let Some(prev) = seen.iter().find(|p| **p != d) {
            return Some((prev.clone(), d));
        }
        if !seen.contains(&d) {
            seen.push(d);
        }
    }
    None
}

/// A data function over a **free witness**, read as the sum it is: `𝑤 ⤇ 𝑉` with `𝑤 :: 𝐾`
/// becomes `Σ 𝑤 ∈ 𝐾. 𝑤 ⤇ 𝑉`.
///
/// **Binding the witness, at constraint time.** Consuming a sum names its witness and
/// leaves the consumer's result over that name; the carrier binds it at materialization
/// (`free_witness_kind`, in `src/ccl/infer/solver/compact.rs`), but a comparison that
/// runs *during* solving — an annotation check, most visibly — sees the type before then
/// and would read a collection position as a bare witness. So the same fact is read here.
///
/// The range comes from the index, which is the only place it can come from: a reference
/// is a name, and what it ranges over belongs to the binder rather than to the name —
/// which is also why the witness stays a plain identity in
/// [`AtomKey`](super::compact::AtomKey), whose `Ord` a range could not satisfy.
fn closed_sum(ty: &Type) -> Option<Type> {
    let Type::Fun {
        name,
        domain,
        codomain,
        ..
    } = ty
    else {
        return None;
    };
    // **Bound by the witness it binds.** The sum this forms is the one the consuming rule
    // named — `SigmaType::over` would mint a binder of its own and leave the consumer's
    // other occurrences (its index term, its domain slot) naming the witness instead,
    // which is a disagreement no single type is ill-formed enough to show.
    let binder = free_witness_of(domain)?;
    // An occurrence names a binder, and the binder is what has a range
    // (`crate::ccl::ty::witness_ctx`). Total for the same reason [`determined_domain`] is:
    // this domain *is* a witness, so a consuming rule named it, and naming records the
    // range.
    let kind = crate::ccl::ty::witness_ctx::range(binder)
        .unwrap_or_else(|| unreachable!("a witness domain has no recorded range: {binder:?}"));
    let w = Type::WitnessRef(binder);
    Some(Type::Sigma(Box::new(SigmaType::bound(
        crate::ccl::ty::Witness::bound_to(binder, kind),
        Type::Fun {
            name: name.clone(),
            kind: FunKind::Data,
            domain: Box::new(w),
            codomain: codomain.clone(),
        },
    ))))
}

/// The range of the free witness a domain position **is** — written there, or demanded of
/// a variable standing there.
///
/// Elimination names the consumed sum's witness against whatever domain the consumer
/// declared, and a consumer mints a fresh one, so the position usually reads `?d` with the
/// witness on its upper bounds. Following the bound is the move [`candidate_shape`] makes,
/// in the direction this fact travels: a candidate is determined by what flows *into* it,
/// a consumed domain by what is demanded *of* it.
///
/// The depth bound is a cycle guard, not a search budget — `?a <: ?b`, `?b <: ?a` is a
/// recursive type the solver rejects later, and this must not hang first. Any real chain
/// is one hop.
/// The one domain `binder` can be, when its range leaves it no choice.
///
/// A range naming exactly one domain *determines* the witness, so it **is** that domain and
/// an edge against it is the ordinary one between two domains. A range naming several does
/// not: accepting a concrete demand would pin the witness to one of them, which is the
/// silent narrowing a lossless data join exists to rule out.
fn determined_domain(binder: crate::ccl::infer_var::WitnessBinderId) -> Option<Type> {
    // A miss is a bug, not the ordinary `None` below: a witness reaching an edge was named
    // when a sum was consumed, and naming it is what records the range.
    let range = crate::ccl::ty::witness_ctx::range(binder).unwrap_or_else(|| {
        unreachable!("a witness reached a subtyping edge with no recorded range: {binder:?}")
    });
    match range.listed() {
        Some([sole]) => Some(sole.clone()),
        _ => None,
    }
}

/// Bring every sum among a variable's lower bounds under **one binder**, and answer the
/// rewritten bounds.
///
/// A variable whose lower bounds are dependent sums holds one sum-typed value: however
/// many arms describe it, the conditional that built it made one choice. Each arm arrives
/// carrying whatever binder its own introduction minted, so those binders are competing
/// names for one witness — and the rename settles it before anything consumes them. That is
/// what lets each arm reach a consumer **on its own**: two arms of one conditional now
/// emit the same domain edge instead of two, so no join has to be assembled first.
///
/// A binder is bound, so the rename is α-conversion and changes no type. The rewrite is
/// written back to the variable, so the graph carries one binder from here on and
/// compaction reads the same identity off these bounds that constraining used.
fn unify_sum_witnesses(lv: &Rc<InferVar>, lows: Vec<Bound>) -> Vec<Bound> {
    let sums: Vec<_> = lows
        .iter()
        .filter_map(|b| match &b.ty {
            Type::Sigma(s) => Some(s.binder()),
            _ => None,
        })
        .collect();
    if sums.is_empty() {
        return lows;
    }
    let w = lv.witness_binder(&sums);
    if sums.iter().all(|b| *b == w) {
        return lows;
    }
    let renamed: Vec<Bound> = lows
        .into_iter()
        .map(|b| match &b.ty {
            Type::Sigma(s) => Bound {
                ty: Type::Sigma(Box::new(s.rename_binder(w))),
                ..b
            },
            _ => b,
        })
        .collect();
    lv.bounds.borrow_mut().lower = renamed.clone();
    renamed
}

/// The **domain** half of consuming a sum: name the witness, and publish what it ranges
/// over.
///
/// The consumer's domain is told *which* witness it ranges over — a reference to the
/// sum's binder. A reference is a leaf and not a [`Type::Infer`], so nothing can unify it
/// away, which is what stops a conditional collection being narrowed to one arm by a
/// demand. Every sum
/// describing one value has already been brought under one binder
/// ([`crate::ccl::infer_var::InferVar::witness_binder`]), so the arms of a conditional
/// reaching this consumer separately emit the *same* edge, and the ordinary pointwise
/// closure needs no join assembled ahead of it.
///
/// The witness is **not bound here**: the consumer's result is an unresolved variable at
/// this point, so the reference stays free in the graph until materialization binds it
/// (in `src/ccl/infer/solver/compact.rs`). None may survive coalesce still free — that is
/// the escape check.
fn demand_domain_range(
    domain: &Type,
    binder: crate::ccl::infer_var::WitnessBinderId,
    range: &TypeKind,
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
) -> Result<(), ConstrainError> {
    // The range lives in the sum's context; the index is read from everywhere, so it is
    // rendered into the common one first.
    let range = range.map_children(|d| sl.apply_type(d));
    // **The context may already have named this witness**, and then it names it. A
    // consumer whose domain *is* a witness reference was written against a consumption
    // that already happened — the post-λ-elimination wall re-deriving a recorded tree is
    // the case that matters — and the sum's own binder is bound, so bringing it under the
    // name the context supplies is α-conversion and changes nothing. Minting here instead
    // would demand that two independent derivations agree on an id, which only a name
    // carried by the *term* could deliver; taking the name the context offers is the same
    // move the `Fun` rule makes for a Pi binder, which is derived from the correspondence
    // rather than reproduced.
    if let Type::WitnessRef(named) = domain {
        crate::ccl::ty::witness_ctx::note_range(*named, &range);
        return Ok(());
    }
    // Publish before handing out a reference: a `Type::WitnessRef` names a binder and
    // nothing else, so the range has to be findable from the binder alone.
    crate::ccl::ty::witness_ctx::note_range(binder, &range);
    constrain_go(domain, &Type::WitnessRef(binder), sr, sl, cache)
}

fn free_witness_of(domain: &Type) -> Option<crate::ccl::infer_var::WitnessBinderId> {
    fn go(ty: &Type, depth: usize) -> Option<crate::ccl::infer_var::WitnessBinderId> {
        match ty {
            Type::WitnessRef(w) => Some(*w),
            Type::Infer(v) if depth > 0 => {
                let uppers: Vec<Type> = v
                    .bounds
                    .borrow()
                    .upper
                    .iter()
                    .map(|u| u.ty.clone())
                    .collect();
                uppers.iter().find_map(|u| go(u, depth - 1))
            }
            _ => None,
        }
    }
    go(domain, 8)
}

/// The candidate **domains** a collection-shaped type contributes.
///
/// A plain data function has the one domain it was written with. A *factored* sum
/// `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉` contributes its candidates whole — they already *are* domains, and
/// taking them whole is what makes the join **associative**: a nested conditional
/// deposits an already-joined sum as one lower bound, and unioning its candidates into
/// the outer join flattens `Σ 𝐷 ∈ {𝐷₀, Σ 𝐸 ∈ {𝐷₁, 𝐷₂}. 𝐸}. 𝐷` to `Σ 𝐷 ∈ {𝐷₀, 𝐷₁, 𝐷₂}. 𝐷`
/// rather than nesting a sum inside a candidate list.
///
/// An *unfactored* sum `Σ σ ∈ {𝑇ᵢ}. σ` — what `box`ing each arm of a conditional builds —
/// contributes the **domains of** its candidates, and only when every one of them is a
/// data function. Its candidates are whole types, so reading them as domains directly
/// would build `Σ 𝐷 ∈ {𝐷₀ ⤇ 𝑉₀, …}. 𝐷 ⤇ 𝑉`: a collection indexed by collections. The
/// re-read is sound because `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ <: Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ ⨆𝑉ᵢ` is plain
/// Σ-width — pair `𝑖` with `𝑖`, and the bodies relate by the ordinary `Fun` rule, since
/// the domains are equal (data domains being invariant) and the codomains join. Not an
/// equality: the reverse holds only when the candidates already share an element type.
///
/// `None` for anything else, including a described kind (which lists no candidates) and a
/// bare variable (which has no domain to read yet).
fn collection_candidates(ty: &Type) -> Option<Vec<Type>> {
    match ty {
        Type::Fun {
            kind: FunKind::Data,
            domain,
            ..
        } => Some(vec![domain.as_ref().clone()]),
        Type::Sigma(s) => {
            let listed = s.kind().listed()?;
            match s.body_residue() {
                Some(_) => Some(listed.to_vec()),
                None => data_candidate_domains(listed),
            }
        }
        _ => None,
    }
}

/// The element types a collection-shaped type carries — every one that has to flow into
/// the join's shared element position.
///
/// One for a data function or a factored sum (the shared codomain). An unfactored sum
/// carries one **per candidate**, and they need not agree: `⨆𝑉ᵢ` is the element type of
/// the factored sum it lies below, so each candidate's contributes.
fn collection_codomains(ty: &Type) -> Vec<Type> {
    match ty {
        Type::Fun { codomain, .. } => vec![codomain.as_ref().clone()],
        Type::Sigma(s) => match s.body_residue() {
            Some((_, cod)) => vec![cod.clone()],
            // Read through the same [`candidate_shape`] the domains are read through, so
            // the two halves of one candidate cannot disagree about whether it resolved.
            None => s
                .kind()
                .listed()
                .into_iter()
                .flatten()
                .filter_map(|c| match candidate_shape(c)? {
                    Type::Fun { codomain, .. } => Some(*codomain),
                    _ => None,
                })
                .collect(),
        },
        _ => unreachable!("collection_codomains follows collection_candidates"),
    }
}

/// The **shape** a Σ candidate has: itself, or — when it is still a variable — the
/// structural type its bounds have already determined for it.
///
/// A candidate is the one position in a sum that is not reached by the ordinary polar
/// bound walk. Every other position is a place the solver is *solving for*, and asking
/// what it is before coalesce would be guessing. A candidate is not: it is the type of
/// the term that was `box`ed, fixed by the argument edge of the introduction that built
/// the sum, and that edge is emitted when the sum is *created* — necessarily before any
/// edge that consumes it. So this reads a determined fact, and reads it exactly as
/// compaction would, only earlier.
///
/// Variable-to-variable bounds are followed, since a chain of them still determines one
/// shape; `depth` stops a cycle (`?a <: ?b`, `?b <: ?a`), which the solver rejects later
/// as a recursive type and which must not hang here.
fn candidate_shape(ty: &Type) -> Option<Type> {
    fn go(ty: &Type, depth: usize) -> Option<Type> {
        let Type::Infer(v) = ty else {
            return Some(ty.clone());
        };
        if depth == 0 {
            return None;
        }
        // A candidate is determined by what *flows into* it — the argument of the
        // introduction — so it is the lower bounds that carry the shape.
        let lower = v.bounds.borrow().lower.clone();
        lower.iter().find_map(|b| go(&b.ty, depth - 1))
    }
    // Deep enough for any chain a real program builds, short enough that a cycle costs
    // nothing; the shape is found at depth 1 whenever the sum was built by `box`.
    go(ty, 8)
}

/// The candidates' domains, when **every** candidate is a data function — the test for
/// "this unfactored sum is a conditional collection".
///
/// All-or-nothing: a sum mixing a collection with a scalar has no collection reading at
/// all, and half of one would silently drop the scalar candidate. A candidate whose shape
/// is not yet determined answers `None` the same way a scalar does — the sum is then
/// related candidate-by-candidate, which is the rule, just without the refactoring.
fn data_candidate_domains(candidates: &[Type]) -> Option<Vec<Type>> {
    Some(
        data_candidate_fibers(candidates)?
            .into_iter()
            .map(|(d, _)| d)
            .collect(),
    )
}

/// Each candidate's `(domain, element)` — the **fibered view** of an unfactored sum whose
/// candidates are all collections.
///
/// This is what makes `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ` comparable to a factored sum: read that way,
/// both sides are a sum over *domains* carrying an element type, and Σ-width's
/// `𝐵₀[𝑑] <: 𝐵₁[𝑒]` decomposes into a domain pairing plus element edges — the same two
/// halves the factored/factored case already splits into. Comparing raw *candidates*
/// instead asks `𝐷₀ ⤇ 𝑉 <: 𝐷₀`, an arrow below a range, which is why the relation between
/// the two forms looked absent rather than derivable.
///
/// Each candidate is seen through [`candidate_shape`], so one still standing as an
/// inference variable arrives resolved. All-or-nothing: a sum mixing a collection with a
/// scalar has no collection reading at all, and half of one would silently drop the
/// scalar candidate.
fn data_candidate_fibers(candidates: &[Type]) -> Option<Vec<(Type, Type)>> {
    candidates
        .iter()
        .map(|c| match candidate_shape(c)? {
            Type::Fun {
                kind: FunKind::Data,
                domain,
                codomain,
                ..
            } => Some((*domain, *codomain)),
            _ => None,
        })
        .collect()
}

/// Σ-width: witness-range containment plus body subtyping. The **only** way a sum is
/// related to another sum, and the only way one is entered — no arm puts a non-sum below a
/// sum, because only a term builds one (`src/ccl/design/type-inference.md`, "Only a term
/// builds a sum"). `lhs`/`rhs` are the original types, carried only for the mismatch
/// diagnostic.
#[allow(clippy::too_many_arguments)]
fn constrain_sigma_width(
    a: &SigmaType,
    b: &SigmaType,
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
    lhs: &Type,
    rhs: &Type,
) -> Result<(), ConstrainError> {
    // **Different forms.** An unfactored sum of collections below a factored one is
    // ordinary Σ-width, but only when the rule is read as it is stated — on *instantiated
    // bodies*. Pairing raw candidates instead asks `𝐷₀ ⤇ 𝑉 <: 𝐷₀`, an arrow below a range,
    // which is why the two forms looked unrelated.
    //
    // Read through the fibered view both sides are a sum over domains carrying an element
    // type, and `𝐵₀[𝑑] <: 𝐵₁[𝑒]` decomposes exactly as it does when both sides are
    // factored: the domains pair, the element types flow. The difference is only that an
    // unfactored sum has one element type *per candidate* rather than one shared, so the
    // element edges are emitted per candidate instead of once.
    if a.body_residue().is_none()
        && let Some((_, cod_b)) = b.body_residue()
        && let Some(candidates) = a.kind().listed()
        && let Some(fibers) = data_candidate_fibers(candidates)
    {
        let domains = TypeKind::Enumerated(fibers.iter().map(|(d, _)| d.clone()).collect());
        let Some(obligations) = domains.contains(b.kind()) else {
            return Err(ConstrainError::Mismatch {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            });
        };
        discharge_obligations(obligations, sl, sr, cache, lhs, rhs)?;
        for (_, elem) in fibers {
            constrain_go(&elem, cod_b, sl, sr, cache)?;
        }
        return Ok(());
    }
    // Every witness is a type classified by a kind, so this is the whole rule: kind
    // containment, then the body edge.
    let Some(obligations) = a.kind().contains(b.kind()) else {
        return Err(ConstrainError::Mismatch {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        });
    };
    discharge_obligations(obligations, sl, sr, cache, lhs, rhs)?;
    // The body of every sum is `𝑤 ⤇ 𝑉` ([`SigmaType::over`]), so instantiating a pairing
    // `(𝑑, 𝑒)` gives `𝑑 ⤇ 𝑉₀ <: 𝑒 ⤇ 𝑉₁`, and the `Fun`/`Fun` decomposition of *that* is
    // exactly the two halves below. They are emitted separately rather than by handing
    // instantiated bodies to `constrain_go`, because their dependencies differ: one is
    // per-pairing and one is not, and re-deriving the codomain edge inside a search
    // would emit it once per attempt — including failed attempts.
    // The codomain edge, **once**: `𝑉` does not mention the witness (one codomain is
    // shared across a sum's candidates), so it is the same edge for every pairing. It
    // also *has* to be emitted here rather than deferred — post-coalesce records no
    // bounds, so anything needed to resolve a variable must go in while the graph is
    // still being built. Deferral is available only for what is purely a check.
    let (Some((bind_a, cod_a)), Some((bind_b, cod_b))) = (a.body_residue(), b.body_residue())
    else {
        // No residue on one side: a body that *is* the witness varies entirely with it,
        // so the pairing search above already compared the whole body and there is
        // nothing left to emit. Two sums whose bodies differ in *shape* are related by
        // that search too — an arrow candidate either does or does not lie below the
        // other side's instantiated body — so a mixed pair needs no rule of its own.
        return Ok(());
    };
    let cod_sl = match (bind_a, bind_b) {
        (Some(k), Some(x)) => sl.extended_rename(k, x),
        _ => sl.clone(),
    };
    constrain_go(cod_a, cod_b, &cod_sl, sr, cache)
}

/// Discharge everything a [`KindObligations`] carries.
///
/// **One reader.** Both Σ-width paths go through here — the same-form one, and the
/// cross-form one that reads an unfactored sum through its fibers — because an
/// obligation is a *set* of things containment could not answer, and a path that
/// discharges some of them silently accepts the rest. Two copies drift by omission: the
/// field a later kind adds gets wired into whichever copy the author was looking at, and
/// the other one keeps accepting.
fn discharge_obligations(
    obligations: crate::ccl::ty::KindObligations,
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
    lhs: &Type,
    rhs: &Type,
) -> Result<(), ConstrainError> {
    // A candidate with no shape yet gets a **kinding constraint** on its variable rather
    // than an optimistic acceptance: recorded during emission without knowing what the
    // variable will become, read when it resolves, which is what the solver already does
    // for every other constraint on a variable.
    for (v, k) in obligations.kinds {
        v.bounds.borrow_mut().kinds.push(k);
    }
    // Kind **parameters** are invariant, so each pair goes through `constrain_go` in both
    // directions — the sub side under `sl` and the sup side under `sr`, swapped for the
    // reverse edge. Emitted alongside a pending kinding constraint, not instead of it: the
    // relation requires the pair either way, and withholding it would drop the only edge
    // that pins an open parameter.
    for (sub, sup) in &obligations.params {
        constrain_go(sub, sup, sl, sr, cache)?;
        constrain_go(sup, sub, sr, sl, cache)?;
    }
    if let Some((subs, sups)) = &obligations.pairing {
        discharge_pairing(subs, sups, sl, sr, cache, lhs, rhs)?;
    }
    Ok(())
}

/// Discharge a [`KindObligations::pairing`] — the `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁` of Σ-width — by
/// searching for a sup candidate each sub candidate's **domain** edge relates to.
///
/// The search is safe here for one reason: candidates are **ground**. A search inside a
/// bounds-recording solver is otherwise hazardous, since different pairings record
/// different constraints and a wrong commitment cannot be undone — but a comparison
/// between two ground types records nothing on any variable, so an attempt that fails
/// leaves no trace and the choice is confluent. A non-ground candidate therefore gets
/// only the `𝑒 = 𝑑` instance (syntactic equality), which needs no search at all.
///
/// The per-pairing edge is the *domain* half of `𝑑 ⤇ 𝑉₀ <: 𝑒 ⤇ 𝑉₁`, so it runs in the
/// same direction the `Fun`/`Fun` arm uses — contravariant, with the two sides'
/// morphisms swapped rather than inverted.
fn discharge_pairing(
    subs: &[Type],
    sups: &[Type],
    sl: &Subst,
    sr: &Subst,
    cache: &mut ConstrainCache,
    lhs: &Type,
    rhs: &Type,
) -> Result<(), ConstrainError> {
    for d in subs {
        if !sups.iter().any(|e| probe_edge(e, d, sr, sl, cache)) {
            return Err(ConstrainError::Mismatch {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            });
        }
    }
    Ok(())
}

/// Whether `sub <: sup` holds **without recording anything** — the adjacency test a Σ
/// pairing search runs before committing to a correspondence.
///
/// Two disciplines, both load-bearing, which is why both searches over Σ candidates go
/// through here rather than each rolling its own probe.
///
/// A scratch cache keeps a failed attempt from leaving an entry in the real one's
/// cycle-breaker memo. That is *not* what makes the attempt harmless, though: bounds live
/// on the inference variables, not the cache, so a probe against a variable-bearing pair
/// would record a constraint for a correspondence that may then be rejected — and no
/// cache can undo that. Groundness is therefore the actual precondition, and a non-ground
/// pair gets only the `𝑒 = 𝑑` instance, which needs no search at all.
///
/// Kind-awareness is mirrored from the live cache so a probe never applies a stricter
/// rule than the pass it is running inside.
fn probe_edge(sub: &Type, sup: &Type, ssub: &Subst, ssup: &Subst, cache: &ConstrainCache) -> bool {
    if sub == sup {
        return true;
    }
    if crate::ccl::subst::type_contains_infer(sub) || crate::ccl::subst::type_contains_infer(sup) {
        return false;
    }
    let mut scratch = if cache.kind_aware {
        ConstrainCache::new()
    } else {
        ConstrainCache::new_kind_blind()
    };
    constrain_go(sub, sup, ssub, ssup, &mut scratch).is_ok()
}

/// Whether `union_dom` is a gated **partition** of the single domain `target`:
/// a `Variant` with contiguous `Index(0..n)` tags (n ≥ 1) whose every payload,
/// with its gate refinement stripped, is structurally `target` (also stripped).
/// This is the shape lambda_elim's value-`Case` fan-out gives *same-domain* arms
/// — the signature the same-domain collapse in the `Fun`/`Fun` arm realizes as
/// the plain data function `target ⤇ W`. Requiring the stripped payloads to equal `target` keeps a
/// genuine heterogeneous `++` flowing into a fresh-var domain out of this rule
/// (its legs differ, or the target is an unresolved var, so the ordinary
/// contravariant arm applies).
fn is_index_partition_of(union_dom: &Type, target: &Type) -> bool {
    let Type::Variant(tags) = union_dom else {
        return false;
    };
    if tags.is_empty() {
        return false;
    }
    let base = strip_refinements(target);
    tags.iter()
        .enumerate()
        .all(|(i, (k, payload))| *k == FieldKey::Index(i) && strip_refinements(payload) == base)
}

/// Constrain `lhs‹sl› <: rhs‹sr›` — each side under its own context morphism,
/// both mapping into the constraint's shared ambient frame.
///
/// Both are `Subst::id()` for ordinary monomorphic constraints — in which
/// case every arm below reduces exactly to the substitution-free solver.
/// Non-identity morphisms are *derived* when constraining two function types
/// whose codomains mention their binders (the Pi-vs-Pi arm mints the binder
/// correspondence, recorded on the lhs side) or introduced by a dependent
/// application's discharge riding a closure step.
///
/// Edge-storage convention: bounds are recorded in their **native two-sided
/// form** (see [`Bound`]) — an upper entry on `V` is `V‹self_subst› <:
/// ty‹ty_subst›`, a lower entry `ty‹ty_subst› <: V‹self_subst›` — with *no
/// inversion at record time*. The transitive closure recovers a previously
/// recorded edge's forward morphism by reading it directly, reconciling the
/// two entries' holder views via `bridge_holder_gap` and composing forward;
/// the only inversions anywhere are of renames (lossless).
/// This is what lets a non-invertible discharge survive crossing a consumer
/// edge that was recorded before the producer's content arrived.
fn constrain_go(
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

        // Bridge rule 2 (gated-partition `⧺` <: plain data function): the
        // `Variant`-domain union `⧺ᵢ ({D | π̂ᵢ} ⤇ W)` that lambda_elim's
        // value-`Case` fan-out produces for **same-domain** arms *is* the plain
        // data function `D ⤇ W` — an exhaustive + disjoint partition of `D`
        // (exhaustiveness guaranteed by the stamping phase, not proven here; see
        // lambda_elim's `build_value_case_fanout` and `design/type-inference.md`,
        // "4.6 Data vs compute functions and conditional-collection domain
        // joins"). Each leg `{D | π̂ᵢ} <: D` by refinement width (covariant, not the
        // function-domain contravariance below), codomain covariant. Fires only
        // when every leg refines the *same concrete* target domain `D`, so a
        // genuine heterogeneous `++` flowing into a fresh-var domain still takes
        // the ordinary contravariant arm below (its domain var resolves to the
        // `Variant`, iterating every leg).
        (
            Type::Fun {
                kind: FunKind::Data,
                domain: union_dom,
                codomain: c0,
                ..
            },
            Type::Fun {
                domain: d1,
                codomain: c1,
                ..
            },
        ) if is_index_partition_of(union_dom, d1) => {
            if let Type::Variant(tags) = union_dom.as_ref() {
                for (_, payload) in tags {
                    constrain_go(payload, d1, sl, sr, cache)?;
                }
            }
            constrain_go(c0, c1, sl, sr, cache)
        }

        // **Binding the witness, at constraint time.** A data function over a free
        // witness — the shape consuming a sum leaves behind — *is* the sum
        // `Σ 𝑤 ∈ 𝐾. 𝑤 ⤇ 𝑉` ([`closed_sum`]),
        // so the edge is decided by the Σ rules rather than by the function rules. It has
        // to run before the `Fun`/`Fun` arm below: data domains are invariant, so that arm
        // would relate `𝑤` to the other side's domain in both directions, and a witness
        // ranging over several candidates relates to no concrete domain at all. Two
        // consumed `box`ed arms meet exactly that way, and would be reported as a domain
        // conflict between the collections the author had just boxed.
        //
        // Only the **left** is closed. On the right the same shape is a consumer whose
        // domain the consuming rule just named, and binding it would demand a sum of whatever
        // flows in, which has no rule. Left-only is enough because the two
        // spellings meet as soon as either side is a sum: `Σ <: Σ` is width.
        (Type::Fun { .. }, _) if closed_sum(lhs).is_some() => {
            let repaired = closed_sum(lhs).expect("guarded by the arm");
            constrain_go(&repaired, rhs, sl, sr, cache)
        }

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
                kind: k0,
                domain: d0,
                codomain: c0,
            },
            Type::Fun {
                name: n1,
                kind: k1,
                domain: d1,
                codomain: c1,
            },
        ) => {
            // The kind edge over the lattice `Data ⊑ Compute` (see
            // `constrain_kind`): `Data <: κ` and `κ <: Compute` always hold; a
            // concrete `Compute <: Data` is the rejection (a capability where an
            // domain is demanded → silent row loss), live only when the cache is
            // kind-aware (emission, not the kind-blind post-inference check).
            // FunKind vars accumulate `forced_*` flags here and resolve at coalesce.
            let kind_aware = cache.kind_aware;
            if constrain_kind(k0, k1, kind_aware) {
                return Err(ConstrainError::ComputeWhereDataRequired {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                });
            }
            let cod_sl = match (n0, n1) {
                (Some(k), Some(x)) => sl.extended_rename(k, x),
                _ => sl.clone(),
            };
            // The domain edge. A *compute* domain is contravariant: it is a
            // parameter, nothing can enumerate it, and accepting more inputs than
            // demanded only under-promises. A **data** domain is *invariant* — it is
            // the loop bound op-conversion emits and it reappears in every
            // consumer's result, so narrowing or widening it changes which rows the
            // consumer reads (`src/ccl/design/type-inference.md`, "Data domains are
            // invariant"). Invariance is spelled the only order-independent way it
            // can be, as both edges; anything conditional on *when* the edge fires
            // would make typing depend on constraint order.
            //
            // Emitting both directions does not preempt a domain join. Two domains
            // meeting at one variable is a join like any other, and the join of two
            // data functions is a Σ over the candidate domains — at a domain position
            // exactly as at a `Case` result. Until Σ is representable that join has
            // no answer, which is the error below; the same fact reaches coalesce as
            // `CoalesceError::DomainJoinConflict` when no edge forces it earlier.
            if kind_aware && matches!(k0, FunKind::Data) && matches!(k1, FunKind::Data) {
                if constrain_go(d1, d0, sr, sl, cache).is_err()
                    || constrain_go(d0, d1, sl, sr, cache).is_err()
                {
                    return Err(ConstrainError::DataDomainMismatch {
                        lhs: (**d0).clone(),
                        rhs: (**d1).clone(),
                    });
                }
            } else {
                constrain_go(d1, d0, sr, sl, cache)?;
            }
            constrain_go(c0, c1, &cod_sl, sr, cache)
        }

        // (Dependent-sum (Σ) rules live just below, after the `Record` arm. They are
        // rules on the sum itself: the solver knows dependent sums, not any surface
        // concept — `List`, `Map`, `Collection` and a conditional collection are the
        // same rules at different witness kinds, not four sets of arms. One is genuine
        // subtyping: the width `Σ <: Σ` (a smaller sum is-a bigger sum). The other,
        // `Σ <: Fun`, is **not** subsumption but a sum *consumed*, discharged through this
        // solver: a Σ value is one branch, not a function total on the union, so it
        // cannot be subsumed to one — consuming it distributes the consumer over the
        // witness. There is deliberately no third, entering arm: a sum is introduced by
        // `box`, a term, and never by subsumption from a bare collection.
        //
        // No arm dispatches on the kind, which is why a new kind needs no new arm here.
        // Only **two** questions below are kind-dependent at all: containment
        // ([`TypeKind::contains`], the width premise) and whether the kind names a finite
        // set of candidates ([`TypeKind::listed`]). What a consumer is presented with is
        // *not* a third — a sum names its witness the same way for every kind — so a kind
        // has to supply containment and a listed/described answer, and nothing else. See
        // `src/ccl/design/type-inference.md`, "4.6 Data vs compute functions and
        // conditional-collection domain joins".)

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

        // **No subtyping edge builds a sum.** A data function is never below one, whatever
        // its domain: entering a sum is a *term* (`box`), not a subtyping edge
        // (`src/ccl/design/type-inference.md`, "Only a term builds a sum"). Without this,
        // `[1] if c else [2, 3]` acquires a sum type nobody wrote, which is exactly the
        // implicitness `box` exists to remove — and the join of two collections over
        // distinct domains silently becomes a sum instead of the error it is.
        //
        // A `Fun(Data)` against a `Sigma` therefore falls through to the structural
        // mismatch below.

        // **`Σ <: Fun`**: a sum *consumed* as a plain collection.
        //
        // One rule, for both spellings of a conditional collection. What consuming a sum
        // needs from the sum is its candidate **domains** and the element types carried
        // at them, and [`collection_candidates`] / [`collection_codomains`] answer that
        // for the factored `Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ 𝑉` and the unfactored `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ`
        // alike. Nothing downstream of that point can tell which arrived, which is why
        // there is no longer a split here.
        //
        // The domains do not become an edge. They become a **range demand** on the
        // consumer's domain — see [`demand_domain_range`] — and the element types flow
        // covariantly into its codomain, one edge each.
        (
            Type::Sigma(s),
            Type::Fun {
                name: n1,
                domain: d1,
                codomain: c1,
                ..
            },
        ) => {
            match s.body_residue() {
                // A **factored** sum, `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉`. Naming the witness needs no
                // candidates at all — that is exactly what naming buys over presenting —
                // so a *described* kind (`List`'s `UIntRanges`, `Collection`'s `Any`)
                // goes through here on the same rule as a listing one, with nothing to
                // enumerate and nothing special to say.
                //
                // The body may be dependent, so the Pi binder correspondence the
                // `Fun`/`Fun` arm would derive has to be derived here too — the body is
                // destructured rather than recursed into.
                Some((binder, cod)) => {
                    demand_domain_range(d1, s.binder(), s.kind(), sl, sr, cache)?;
                    let cod_sl = match (binder.as_ref(), n1) {
                        (Some(k), Some(x)) => sl.extended_rename(k, x),
                        _ => sl.clone(),
                    };
                    constrain_go(cod, c1, &cod_sl, sr, cache)
                }
                // An **unfactored** sum, `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ`: the body *is* the witness,
                // so the candidates are whole types and the domains have to be read out
                // of them ([`collection_candidates`]) before there is a range to name.
                // Each candidate carries its own element type, and they need not agree —
                // a join of element types is lossless, so the consumer's codomain joins
                // them by being their common upper bound, with no variable to join
                // through.
                None => match collection_candidates(lhs) {
                    Some(domains) => {
                        let range = TypeKind::Enumerated(domains);
                        demand_domain_range(d1, s.binder(), &range, sl, sr, cache)?;
                        for cod in collection_codomains(lhs) {
                            constrain_go(&cod, c1, sl, sr, cache)?;
                        }
                        Ok(())
                    }
                    // **Witness-forgetting consumption**, the rule for a sum this
                    // consumer cannot read as a collection: `Σ σ ∈ {𝑇ᵢ}. σ <: 𝑈` exactly
                    // when every `𝑇ᵢ <: 𝑈`. A Σ value is a pair, so a consumer valid at
                    // *every* candidate is valid on it. A described kind lists nothing to
                    // distribute over and stays a mismatch.
                    None => {
                        let Some(candidates) = s.kind().listed() else {
                            return Err(ConstrainError::Mismatch {
                                lhs: lhs.clone(),
                                rhs: rhs.clone(),
                            });
                        };
                        for c in candidates {
                            constrain_go(c, rhs, sl, sr, cache)?;
                        }
                        Ok(())
                    }
                },
            }
        }

        // **Σ-width** `Σ <: Σ` — the general rule, and the only Σ *subtyping* rule:
        //
        //     K₀ <: K₁      w: K₀ ⊢ B₀[w] <: B₁[w]
        //     ─────────────────────────────────────
        //       Σ (w: K₀). B₀  <:  Σ (w: K₁). B₁
        //
        // witness-kind containment ([`TypeKind::contains`]) plus **body** subtyping. The
        // body is an arbitrary type — the witness may appear anywhere in it, not
        // only in a domain position — so the bodies are compared by recursing
        // through the ordinary arms rather than by destructuring a data function
        // out of them. That is also what relates the two bodies' Pi binders: the
        // Fun/Fun arm derives the correspondence itself.
        (Type::Sigma(a), Type::Sigma(b)) => constrain_sigma_width(a, b, sl, sr, cache, lhs, rhs),

        // **One witness, named twice.** A tree records its bound occurrences as
        // [`Type::WitnessRef`], and Check re-runs the consuming rule on that tree — so the
        // same witness meets itself here, once free and once bound. Reflexivity, and the only
        // reason it needs a rule at all is that the two forms are separate leaves.
        //
        // Not the `𝑒 = 𝑑` reading the catch-all below rejects: that is about relating two
        // *different* witnesses, where the left's choice is arbitrary-but-concrete and the
        // right may answer it differently. Identity is what tells the two situations apart,
        // and without it this case could not be stated.
        (Type::WitnessRef(a), Type::WitnessRef(b)) if a == b => Ok(()),

        // Only a **determined** witness relates. A kind naming exactly one domain leaves
        // the witness no choice, so it *is* that domain and the edge is the ordinary one
        // between two domains. A kind naming several does not: the witness could be any of
        // them, and accepting a concrete demand would pin it to one — the silent narrowing
        // a lossless data join exists to rule out, and the property
        // `conditional_consumed_as_fun` pins. "Transparent through its kind" means
        // transparent when the kind *determines* it, not whenever the kind admits it.
        (_, Type::WitnessRef(w)) if !matches!(lhs, Type::Infer(_)) => match determined_domain(*w) {
            Some(sole) => constrain_go(lhs, &sole, sl, sr, cache),
            None => Err(ConstrainError::Mismatch {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            }),
        },
        (Type::WitnessRef(w), _) if !matches!(rhs, Type::Infer(_)) => match determined_domain(*w) {
            Some(sole) => constrain_go(&sole, rhs, sl, sr, cache),
            None => Err(ConstrainError::Mismatch {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            }),
        },

        // A bare witness reference never reaches an edge. Σ-width pairs *candidates*
        // and emits the codomain edge directly ([`constrain_sigma_width`]), and every
        // other Σ arm destructures the body through [`SigmaType::body_fun`] — so no
        // uninstantiated body is ever compared. A `Type::WitnessRef` arriving here means one
        // was, which is a bug and not a case to relate.
        //
        // Relating two witnesses to each other could only mean "treat the left and right
        // witnesses as the same thing", which is the `𝑒 = 𝑑` reading of the rule rather
        // than the rule: the left's choice of witness is arbitrary-but-concrete, and the
        // right may answer it differently for each left choice.
        // A witness meeting a **variable** is an ordinary edge and belongs to the variable
        // arms below: a free witness flows into the consumer's domain slot, which is a
        // variable, and that is how it reaches the graph at all. Only the non-variable
        // cases are handled above — determined witnesses relate, undetermined ones are a
        // mismatch — so nothing is left here to relate.
        //
        // The check this once made ("a *bound* witness reached an edge, so an
        // uninstantiated body was compared") cannot be made at this site any more. Bound
        // and free are one leaf now, and telling them apart needs the witness scope, which
        // subtyping does not thread — compaction does, and asks there.
        (Type::WitnessRef(_), _) | (_, Type::WitnessRef(_))
            if !matches!(lhs, Type::Infer(_)) && !matches!(rhs, Type::Infer(_)) =>
        {
            unreachable!("a witness reached a subtyping edge unrelated: {lhs} <: {rhs}")
        }

        // Variant: width-subtyping is the dual. lhs's tags must all appear
        // in rhs (with a payload subtype check). Payload depth is covariant.
        (Type::Variant(a), Type::Variant(b)) => {
            for (k, t0) in a {
                match b.iter().find(|(bk, _)| bk == k) {
                    Some((_, t1)) => constrain_go(t0, t1, sl, sr, cache)?,
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
        // versa) is *not* matched here: it falls through to the deref arms below,
        // where a mutable variable demanded as a feed lands in `NotAFeed` — the type-level
        // guardrail that `<<` targets a `defer` channel, not a `:=` mutable variable.
        (
            Type::History {
                value: v0,
                domain: d0,
                kind: k0,
            },
            Type::History {
                value: v1,
                domain: d1,
                kind: k1,
            },
        ) if k0 == k1 => {
            constrain_go(v0, v1, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(v1, v0, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(d0, d1, &Subst::id(), &Subst::id(), cache)?;
            constrain_go(d1, d0, &Subst::id(), &Subst::id(), cache)
        }
        // Implicit deref (read): a `Mut` handle meeting any non-`Mut` demand —
        // concrete OR an inference variable — reads its value. This MUST precede
        // the `Infer` arms below: `+`/`<` etc. are polymorphic (`∀α. α → α → α`),
        // so `cnt + 1` emits `Mut(Int, D) <: ?α`; dereffing here flows `Int` onto
        // `?α`, whereas the `(_, Infer)` arm would record the handle itself as a
        // lower bound and coalesce `?α` to a `Mut`.
        (
            Type::History {
                value,
                kind: HistoryKind::Overwrite,
                ..
            },
            _,
        ) => constrain_go(value, rhs, sl, sr, cache),

        // Variable on lhs, rhs has compatible level: record the upper edge in
        // native form (`V‹sl› <: rhs‹sr›`, no inversion), then close each
        // existing lower (`low.ty‹low.ty_subst› <: V‹low.self_subst›`) against
        // the new upper by bridging the holder gap and composing **forward**
        // onto the two content sides.
        (Type::Infer(lv), _) if type_level(rhs) <= lv.level => {
            let lows = {
                let mut s = lv.bounds.borrow_mut();
                s.upper
                    .push(Bound::edge(sl.clone(), rhs.clone(), sr.clone()));
                s.lower.clone()
            };
            let lows = unify_sum_witnesses(lv, lows);
            // **No join here.** A variable's lower bounds are joined where every other
            // join is: at compaction, off these same bounds. Assembling one here as well
            // would compute it twice, by two rules, and — because this arm runs again on
            // every arriving upper edge — recompute it, which is what made the joined
            // sum's binder need an identity stable under recomputation.
            //
            // Each Σ lower bound instead reaches the consumer on its own, below. That is
            // sound because consuming a sum records its domain half as a *range* demand,
            // whose conjunction is a union ([`demand_domain_range`]): the arms of one
            // conditional arriving separately, in any order, converge on the same witness
            // over the same candidates. Emitting a contravariant edge per candidate is
            // what would break — the consumer's domain would have to lie below every
            // arm's domain, their meet, which is the silent narrowing a lossless data
            // join exists to rule out.
            // A declined join over **collection** lower bounds is a type error, not a
            // reason to fall back. Relating two collections over distinct domains to one
            // consumer pointwise is exactly what the join exists to prevent — the
            // consumer's domain would have to lie below both — and the transitive closure
            // does not terminate on it. Now that only sums join, this is the case `box`
            // is there to resolve: box each arm, and the arms join as sums.
            if let Some(domains) = distinct_data_domains(&lows) {
                return Err(ConstrainError::DataDomainMismatch {
                    lhs: domains.0,
                    rhs: domains.1,
                });
            }
            for low in lows {
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
                let mut s = rv.bounds.borrow_mut();
                s.lower
                    .push(Bound::edge(sr.clone(), lhs.clone(), sl.clone()));
                s.upper.clone()
            };
            // No join here, and none is needed: a candidate arriving at a variable that
            // already holds others reaches the joining arm above when *its* own outgoing
            // edge is drawn, and a variable's denotation is read from its lower bounds
            // whenever that happens. Joining here as well would mean re-deriving a join
            // per arriving candidate, and the pointwise closure this arm performs is
            // exactly right for the edge it draws.
            for up in ups {
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
                kind: HistoryKind::Append,
            },
            _,
        ) => {
            let chan = Type::Fun {
                name: None,
                // A feed's read view is a collection stream: a data function.
                kind: FunKind::Data,
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
        // misuse (feeding a plain collection) still lands in desugar's checks.
        (
            Type::Fun { .. },
            Type::History {
                value,
                domain,
                kind: HistoryKind::Append,
            },
        ) => {
            let chan = Type::Fun {
                name: None,
                // A feed's read view is a collection stream: a data function.
                kind: FunKind::Data,
                domain: domain.clone(),
                codomain: value.clone(),
            };
            constrain_go(lhs, &chan, sl, sr, cache)
        }
        // Any other plain value can never satisfy a feed requirement: reading is
        // transparent, but the write capability cannot be conjured (`g(5)` where
        // `g` feeds its parameter, or a `<<` targeting a `:=` mutable variable — which the
        // mutable deref above reduced to `(value, feed)` landing here).
        (
            _,
            Type::History {
                kind: HistoryKind::Append,
                ..
            },
        ) => Err(ConstrainError::NotAFeed {
            found: lhs.clone(),
            required: rhs.clone(),
        }),

        // A non-`Mut` value meeting a `Mut` demand: deref the demand to its
        // value. `x: Int = cnt` copies the current value; `MutWrite`
        // reconciliation flows a written value into the mutable variable's value. Unlike a
        // feed (where the write capability can't be conjured), a `Mut` demand is
        // satisfied structurally by its value here, and the *second-class
        // discipline check* — not the solver — is what rejects passing a
        // non-variable (`bump(5)`, `bump(a + b)`) to a `Mut` parameter. (A
        // `Mut`-lhs was already dereffed above; an `Infer`-lhs recorded the `Mut`
        // as an upper bound — the `Mut`-param-via-variable case.)
        (
            _,
            Type::History {
                value,
                kind: HistoryKind::Overwrite,
                ..
            },
        ) => constrain_go(lhs, value, sl, sr, cache),

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
            | Type::Variant(_)
            | Type::Refinement(..)
            | Type::ChanDom(..)
            | Type::Hole,
        )
        | (
            Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Variant(_)
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
            let (lbase, lrefs) = peel_refinements(lhs);
            let (rbase, rrefs) = peel_refinements(rhs);
            // The refinements rhs requires that no transported lhs layer
            // matches (by `Refinement`'s structural `PartialEq`). Each side's
            // refinements are forced through its own morphism into the ambient frame
            // before comparing (`sl(S₁)` vs `sr(S₂)`); the deficit keeps the
            // *untransported* rhs refinements, since the recursive constraint below
            // carries `sr` for them.
            let lrefs_in_ambient: Vec<Refinement> =
                lrefs.iter().map(|l| sl.force_refinement(l)).collect();
            let deficit: Vec<&Refinement> = rrefs
                .iter()
                .copied()
                .filter(|r| !lrefs_in_ambient.contains(&sr.force_refinement(r)))
                .collect();
            if deficit.is_empty() {
                // lhs's explicit layers already supply every refinement rhs requires.
                constrain_go(lbase, rbase, sl, sr, cache)
            } else if matches!(lbase, Type::Infer(_)) {
                // Variable base: flow the deficit onto it (`b₁ <: {b₂ | deficit}`)
                // rather than rejecting; it fails later iff the variable
                // resolves to a concrete base lacking those refinements.
                let demanded = wrap_refinements(rbase, &deficit);
                constrain_go(lbase, &demanded, sl, sr, cache)
            } else {
                Err(ConstrainError::Mismatch {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })
            }
        }

        // **Elimination against a non-function**, and deliberately *last*: `Σ 𝐷 ∈ 𝐾. 𝐵[𝐷]
        // <: 𝑈` for any `𝑈` the arms above did not already claim. A Σ value is a pair, so
        // a `𝑈` valid at *every* candidate is valid on it. The two arms above are this
        // same rule at the shapes that carry their own extra structure — a function
        // consumer, whose domain and codomain edges run in opposite directions, and a sum
        // consumer, which is width.
        //
        // Position matters: reaching this rule earlier would swallow a variable on the
        // right, which must record the sum as a *bound* rather than distribute over it.
        // Sitting immediately above the fallthrough, it claims only what would otherwise
        // be a flat mismatch.
        //
        // The shape that reaches it is a sum standing in a **domain** position:
        // `Σ 𝐷 ∈ 𝐾. 𝐷` is what a consumer is handed for "whichever domain the witness
        // picked", and it meets a concrete domain
        // whenever that demand resolved to one. With the consuming rule restricted to function
        // consumers this edge had no rule at all, so an `Array(2, 𝑉)` demanded of a
        // `List(𝑉)` that had already narrowed to exactly `{[0, 2)}` was rejected against
        // its own sole candidate.
        //
        // A described kind lists nothing to distribute over and stays a mismatch: the
        // consumer would have to be valid at domains not yet named.
        (Type::Sigma(s), _) if s.kind().listed().is_some() => {
            for c in s.kind().listed().expect("guarded above") {
                constrain_go(&s.instantiate_body(c), rhs, sl, sr, cache)?;
            }
            Ok(())
        }

        _ => Err(ConstrainError::Mismatch {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }),
    }
}

/// Peel all outer [`Type::Refinement`] layers, returning the bare base type
/// and the refinements carried by the peeled layers (outermost first).
fn peel_refinements(ty: &Type) -> (&Type, Vec<&Refinement>) {
    let mut refs = Vec::new();
    let mut cur = ty;
    while let Type::Refinement(inner, r) = cur {
        refs.push(r);
        cur = inner;
    }
    (cur, refs)
}

/// Re-wrap `base` in the given [`Type::Refinement`] layers (passed
/// outermost-first), preserving their order.
///
/// Used by [`constrain_subtype`]'s refinement arm to rebuild the deficit
/// refinement `{rbase | S₂ \ S₁}` from the rhs's own layers, so the kept refinements
/// retain their real [`crate::ccl::Refinement`] payloads (predicate `Rc`s).
fn wrap_refinements(base: &Type, refs: &[&Refinement]) -> Type {
    refs.iter().rev().fold(base.clone(), |acc, r| {
        Type::Refinement(Box::new(acc), (*r).clone())
    })
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
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn
        | Type::Hole => ty.clone(),
        Type::Fun {
            name,
            kind,
            domain: d,
            codomain: c,
        } => Type::Fun {
            name: name.clone(),
            kind: kind.clone(),
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
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                // Variant payloads are covariant — same polarity, no flip.
                .map(|(k, t)| (k.clone(), extrude(t, pol, target_level, cache)))
                .collect(),
        ),
        Type::Refinement(inner, r) => Type::Refinement(
            Box::new(extrude(inner, pol, target_level, cache)),
            r.clone(),
        ),
        // The witness's type children are the real (contravariant) domain, so
        // they extrude at `!pol` — matching the single-`Fun` domain above; the
        // body (a data function over the witness) extrudes covariantly. The
        // witness reference is a leaf at level 0, so it short-circuits.
        // A sum's **candidates** are an invariant position, so they cross a level
        // boundary through two-way proxies rather than the polar one-way approximation
        // below — the same reason a `History` payload does. Σ-width matches candidates
        // *by value*, so neither direction of a candidate's bounds is the "unused" one:
        // a one-way proxy inherits whichever side the polarity picked and silently drops
        // the other, which for a candidate is usually fatal. A candidate is a *domain*,
        // and a domain's content arrives as an **upper** bound (a comprehension's key
        // must lie in its source's domain), so a positive one-way proxy — what `!pol`
        // yields for a sum in a negative position — inherits only lower bounds and
        // carries nothing at all.
        Type::Sigma(s) => Type::Sigma(Box::new(SigmaType::bound(
            s.witness
                .map_types(|t| extrude_invariant(t, target_level, cache)),
            extrude(&s.body, pol, target_level, cache),
        ))),
        Type::WitnessRef(_) => ty.clone(),
        // Invariant payload: polarity is meaningless under invariance, so
        // both children are extruded with two-way proxies (a history is read
        // *and* written) instead of the polar one-way approximation below.
        Type::History {
            value,
            domain,
            kind,
        } => Type::History {
            value: Box::new(extrude_invariant(value, target_level, cache)),
            domain: Box::new(extrude_invariant(domain, target_level, cache)),
            kind: *kind,
        },
        Type::Infer(tv) => {
            if let Some(existing) = cache.get(&(tv.uid, pol)) {
                return Type::Infer(Rc::clone(existing));
            }
            // Conservative approximation: a fresh variable at the target
            // level, linked to the original by the appropriate bound.
            let nvs = InferVar::fresh(target_level);
            cache.insert((tv.uid, pol), Rc::clone(&nvs));
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
                    .kinds
                    .iter()
                    .map(|k| k.map_children(|t| extrude(t, pol, target_level, cache)))
                    .collect();
                nvs.bounds.borrow_mut().kinds = carried;
            }

            // Snapshot the bounds we'll need to extrude before we mutate
            // the original; otherwise we'd race the borrow checker.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                (s.lower.clone(), s.upper.clone())
            };

            if pol {
                // Positive: original flows into new var. Original gains
                // `nvs` as an upper bound; new var inherits original's
                // lower bounds (extruded at the same polarity).
                tv.bounds
                    .borrow_mut()
                    .upper
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, pol, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().lower = new_lows;
            } else {
                // Negative: new var flows into original. Original gains
                // `nvs` as a lower bound; new var inherits original's
                // upper bounds.
                tv.bounds
                    .borrow_mut()
                    .lower
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, pol, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().upper = new_ups;
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
            //    proxy naively — as this branch used to — would hand the
            //    invariant position a one-way proxy, silently dropping the
            //    other bound direction across the level boundary. Instead,
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
                .unwrap_or_else(|| InferVar::fresh(target_level));
            // Which bound links does the reused proxy already carry? A polar
            // proxy under the `true` key has the positive link (`tv <: proxy`);
            // under the `false` key, the negative link (`proxy <: tv`). A fresh
            // proxy has neither.
            let has_pos_link = cached_pos.as_ref().is_some_and(|p| Rc::ptr_eq(p, &nvs));
            let has_neg_link = cached_neg.as_ref().is_some_and(|n| Rc::ptr_eq(n, &nvs));
            cache.insert((tv.uid, true), Rc::clone(&nvs));
            cache.insert((tv.uid, false), Rc::clone(&nvs));

            // Snapshot the original's bounds, excluding any edge that already
            // points at this proxy (a polar extrusion pushed one such link into
            // `tv`); re-seeding from it would create a spurious `proxy <: proxy`
            // self-edge.
            let (lows, ups) = {
                let s = tv.bounds.borrow();
                let not_proxy = |b: &Bound| !matches!(&b.ty, Type::Infer(v) if v.uid == nvs.uid);
                (
                    s.lower
                        .iter()
                        .filter(|b| not_proxy(b))
                        .cloned()
                        .collect::<Vec<_>>(),
                    s.upper
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
                    .upper
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_lows: Vec<_> = lows
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, true, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().lower.extend(new_lows);
            }
            // Negative link: `proxy <: tv`; proxy inherits `tv`'s upper bounds.
            if !has_neg_link {
                tv.bounds
                    .borrow_mut()
                    .lower
                    .push(Bound::conc(Type::Infer(Rc::clone(&nvs))));
                let new_ups: Vec<_> = ups
                    .iter()
                    .map(|b| Bound {
                        self_subst: b.self_subst.clone(),
                        ty: extrude(&b.ty, false, target_level, cache),
                        ty_subst: b.ty_subst.clone(),
                    })
                    .collect();
                nvs.bounds.borrow_mut().upper.extend(new_ups);
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
    use std::rc::Rc;

    use smol_str::SmolStr;

    use super::*;
    use crate::ccl::infer::solver::test_helpers::{record, refined, variant};
    use crate::ccl::infer::solver::{coalesce_compact, compact_type, fresh_var, fun, prim};
    use crate::ccl::subst::Subst;
    use crate::ccl::{
        BaseType, BinOpKind, CompareKind, Lit, Name, Refinement, Type, TypedExpr, TypedExprNode,
    };

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
            inner.bounds.borrow_mut().kinds.push(TypeKind::UIntRanges);
            let mut cache = ExtrudeCache::new();
            let out = extrude(&Type::Infer(Rc::clone(&inner)), pol, 0, &mut cache);
            let Type::Infer(proxy) = out else {
                panic!("extruding a variable yields a variable, got {out:?}");
            };
            assert_eq!(proxy.level, 0, "proxy sits at the target level");
            assert_eq!(
                proxy.bounds.borrow().kinds,
                vec![TypeKind::UIntRanges],
                "pol={pol}: the proxy must inhabit the same kind"
            );
        }
    }

    /// The Σ-width `∃` is a **search**, not set membership. A candidate with no verbatim
    /// counterpart on the right can still be paired with one its body edge relates to —
    /// here a bare range against a *refined* range, which the body edge admits as row
    /// addition behind the arrow (`domain_refinement_edges_today` pins that edge).
    ///
    /// Under the identity pairing alone this is a mismatch, which is what made a
    /// candidate-specific correspondence look like it needed a rule of its own.
    #[test]
    fn sigma_width_pairs_candidates_by_their_body_edge_not_by_equality() {
        let sum = |kind| Type::Sigma(Box::new(SigmaType::over(kind, None, prim(BaseType::Int))));
        let refined_range = refined(Type::UIntRange(3), 7);

        let bare = sum(TypeKind::Enumerated(vec![Type::UIntRange(3)]));
        let filtered = sum(TypeKind::Enumerated(vec![refined_range.clone()]));

        // No candidate is shared, so set membership rejects; the pairing is found by
        // running the body edge.
        assert!(
            constrain_subtype(&bare, &filtered, &mut ConstrainCache::new()).is_ok(),
            "a bare candidate pairs with the refined one it widens into"
        );

        // Not symmetric, and for a reason outside this rule: the reverse pairing would
        // need the *opposite* data-domain edge — dropping a domain refinement — which a
        // data domain's invariance rejects outright, not pending a decision
        // (`src/ccl/design/type-inference.md`, "Data domains are invariant"). The search
        // finds a pairing when one exists; it does not invent the edge.
        assert!(
            constrain_subtype(&filtered, &bare, &mut ConstrainCache::new()).is_err(),
            "and does not pair in the direction the body edge rejects"
        );

        // A candidate with *no* counterpart still fails, so the search has not become a
        // blanket accept.
        let unrelated = sum(TypeKind::Enumerated(vec![prim(BaseType::String)]));
        assert!(
            constrain_subtype(&bare, &unrelated, &mut ConstrainCache::new()).is_err(),
            "no pairing exists, so the edge is a mismatch"
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
            Type::Refinement(
                Box::new(prim(BaseType::Int)),
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
            Type::Refinement(
                Box::new(Type::UIntRange(3)),
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

        // Behind a data arrow, neither refinement direction relates.
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

        // A *compute* arrow over the same domains keeps the contravariant lattice:
        // invariance is about collections, not about refinements behind any arrow.
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
            Type::Refinement(
                Box::new(prim(BaseType::Int)),
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
        let c = Type::Refinement(
            Box::new(prim(BaseType::Int)),
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
        // list-comprehension filters: `{D|p} ⇒ V <: {?a|q} ⇒ V`); a ground
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
            v.bounds.borrow().upper.iter().any(|u| u.ty == expected),
            "?a should carry {{Int | p}} as an upper bound, got {:?}",
            v.bounds.borrow().upper
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
            assert_eq!(s.upper.len(), 1);
            assert!(s.lower.is_empty());
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
            assert!(s.upper.is_empty());
            assert_eq!(s.lower.len(), 1);
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
            assert_eq!(s.upper.len(), 1);
            // The recorded upper bound is α itself, not Int.
            assert!(matches!(&s.upper[0].ty, Type::Infer(_)));
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
            kind: HistoryKind::Append,
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
        // feed(D, Int) <: (D ⇒ Int) — a non-feed consumer reads the whole
        // stream…
        let d = Type::UIntRange(3);
        let mut cache = ConstrainCache::new();
        assert!(
            constrain_subtype(
                &feed_ty(d.clone(), prim(BaseType::Int)),
                &fun(d.clone(), prim(BaseType::Int)),
                &mut cache
            )
            .is_ok()
        );
        // …but the stream's value still has to match the consumer.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &feed_ty(d.clone(), prim(BaseType::Int)),
                &fun(d, prim(BaseType::String)),
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
        // `ρ_x <: (D ⇒ Int)` must discharge through the feed handle
        // transparently.
        let d = Type::UIntRange(3);
        let x = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&feed_ty(d.clone(), prim(BaseType::Int)), &x, &mut cache).unwrap();
        assert!(constrain_subtype(&x, &fun(d, prim(BaseType::Int)), &mut cache).is_ok());
    }

    #[test]
    fn feed_var_coalesces_to_feed() {
        // A var bounded by feed(D, Int) coalesces carrying the Feed
        // constructor (the `history_slot` survives compact → simplify →
        // coalesce). Contrast `mut_derefs_at_a_variable_not_the_handle`, where
        // the deref arm collapses an `Overwrite` var to its bare value.
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
            bounds.upper.iter().any(|b| b.ty == proxy_ty),
            "original value var is missing the upper link to its proxy"
        );
        assert!(
            bounds.lower.iter().any(|b| b.ty == proxy_ty),
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
            bounds.upper.iter().any(|b| b.ty == proxy_ty),
            "original is missing the upper (positive) link to its proxy"
        );
        assert!(
            bounds.lower.iter().any(|b| b.ty == proxy_ty),
            "original is missing the lower (negative) link after the cache hit"
        );
    }

    // --- Mutable handles (`Type::History { kind: Overwrite }`) ---

    fn mut_ty(value: Type, domain: Type) -> Type {
        Type::History {
            value: Box::new(value),
            domain: Box::new(domain),
            kind: HistoryKind::Overwrite,
        }
    }

    #[test]
    fn mut_reads_transparently_as_value() {
        // Mut(Int, D) <: Int — a read derefs to the value…
        let m = mut_ty(prim(BaseType::Int), prim(BaseType::UInt));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&m, &prim(BaseType::Int), &mut cache).is_ok());
        // …but the value still has to match the consumer.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&m, &prim(BaseType::String), &mut cache),
            Err(ConstrainError::Mismatch { .. })
        ));
    }

    #[test]
    fn mut_derefs_at_a_variable_not_the_handle() {
        // THE crux (plan decision #1): `cnt + 1` emits `Mut(Int, D) <: ?α`. The
        // deref arm fires *before* the `Infer` arm, so `?α` coalesces to `Int`,
        // NOT to a `Mut` handle — the deliberate contrast with
        // `feed_var_coalesces_to_feed`. If the deref arm were placed after the
        // `Infer` arms, `?α` would carry the `Mut` constructor and reads would
        // break.
        use crate::ccl::infer::solver::simplify_type;
        let v = fresh_var(0);
        let m = mut_ty(prim(BaseType::Int), prim(BaseType::UInt));
        let mut cache = ConstrainCache::new();
        constrain_subtype(&m, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(out, prim(BaseType::Int));
    }

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
    fn value_meets_mut_demand_derefs() {
        // Int <: Mut(Int, D) — a plain value meeting a `Mut` demand derefs to the
        // value (the discipline check, not the solver, rejects passing a
        // non-variable to a `Mut` parameter). A conflicting value still fails.
        let m = mut_ty(prim(BaseType::Int), prim(BaseType::UInt));
        let mut cache = ConstrainCache::new();
        assert!(constrain_subtype(&prim(BaseType::Int), &m, &mut cache).is_ok());
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(&prim(BaseType::String), &m, &mut cache),
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
        let Type::Refinement(_, r) = domain.as_ref() else {
            panic!("expected refined domain, got {domain}");
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
                Type::Refinement(
                    Box::new(prim(BaseType::Int)),
                    gt_refinement(TypedExpr::var("k")),
                ),
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
                Type::Refinement(
                    Box::new(prim(BaseType::Int)),
                    gt_refinement(TypedExpr::var("k")),
                ),
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
        gamma_var.bounds.borrow_mut().lower.push(Bound::with_subst(
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
                Type::Refinement(
                    Box::new(prim(BaseType::Int)),
                    gt_refinement(TypedExpr::var("k")),
                ),
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
        gamma_var.bounds.borrow_mut().lower.push(Bound::with_subst(
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
            av.bounds.borrow_mut().lower.push(Bound::with_subst(
                r.clone(),
                Subst::discharge("k", TypedExpr::lit(Lit::Int(lit))),
            ));
            constrain_subtype(&app, &v, &mut cache).expect("app <: V");
        }

        let lows = vv.bounds.borrow().lower.clone();
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

    // --- Conditional-collection Sigma rules (subtyping: width; consumption:
    //     consume) — see `design/type-inference.md`, "4.6 Data vs compute functions
    //     and conditional-collection domain joins" ---

    /// The **factored** sum over `domains` — `Σ 𝐷 ∈ {domains}. 𝐷 ⤇ Int`, what
    /// materializing a merged domain kind produces. The unfactored sibling `box`
    /// builds is `SigmaType::of`.
    fn conditional(domains: Vec<Type>) -> Type {
        TypeKind::Enumerated(domains).into_data_fun(None, prim(BaseType::Int))
    }

    #[test]
    fn conditional_width_is_subtype() {
        // A conditional collection is a Sigma over candidate domains;
        // width-subtyping is by-value subset — every lhs candidate domain
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
        // Elimination: a conditional collection used as a plain function. A
        // *fresh* domain var absorbs the discriminated union of the candidate
        // domains (the `sum` / comprehension case).
        let cond = conditional(vec![Type::UIntRange(2), Type::UIntRange(3)]);
        let consumer = fun(fresh_var(0), prim(BaseType::Int));
        assert!(constrain_subtype(&cond, &consumer, &mut ConstrainCache::new()).is_ok());
        // A consumer demanding a *concrete narrower* domain fails: the
        // conditional collection never silently narrows to a single domain.
        let narrow = fun(Type::UIntRange(2), prim(BaseType::Int));
        assert!(constrain_subtype(&cond, &narrow, &mut ConstrainCache::new()).is_err());
    }

    // --- `UIntRanges`-kind Sigma rules (List): consumption, width ---

    /// **A described range is consumed by the same rule a listing one is.** Naming the
    /// witness needs no candidates — that is what naming buys over presenting — so
    /// `List`'s `UIntRanges` and `Collection`'s `Any` reach a consumer through the
    /// factored arm with nothing to enumerate.
    ///
    /// Worth its own test because the failure is silent in the other direction: a rule
    /// written to read candidates first answers `None` for a described kind and falls
    /// through to a flat mismatch, so a `List(𝑇)` annotation stops being consumable and
    /// nothing else in the suite says why.
    #[test]
    fn a_described_range_is_consumed_by_naming_its_witness() {
        let int = prim(BaseType::Int);
        for kind in [TypeKind::UIntRanges, TypeKind::Any] {
            let collection = kind.clone().into_data_fun(None, int.clone());
            // A consumer with a fresh domain variable: the common case (`sum`, a
            // comprehension). Its domain resolves to the witness.
            let consumer = fun(fresh_var(0), int.clone());
            assert!(
                constrain_subtype(&collection, &consumer, &mut ConstrainCache::new()).is_ok(),
                "a {kind} collection must be consumable: {collection}"
            );
        }
    }

    /// **Every kind goes through the same rules.** A witness kind decides only
    /// containment ([`TypeKind::contains`]); consumption and width are written once, so
    /// a kind that names no domains at all is still consumed and still widens with no
    /// rule of its own. `Any` is the case that proves it: nothing constructs it from source yet,
    /// and it needs no solver code.
    ///
    /// It also pins where ⊤ *stops*. A sum widens to it, because that is Σ-width with
    /// `𝐾 ⊆ Any`. A bare `𝐷 ⤇ 𝑉` does **not**: that edge would build a sum by
    /// subsumption, and a structural top is an upper bound of every pair of data
    /// functions — precisely the implicit join `box` exists to surface.
    #[test]
    fn every_witness_kind_uses_the_same_sigma_rules() {
        let int = prim(BaseType::Int);
        let collection = TypeKind::Any.into_data_fun(None, int.clone());
        let list = Type::list_of(int.clone());
        let concrete = Type::data_fun(Type::UIntRange(3), int.clone());

        // Width to ⊤: a *sum* reaches it, a bare data function does not.
        assert!(constrain_subtype(&list, &collection, &mut ConstrainCache::new()).is_ok());
        assert!(
            constrain_subtype(&concrete, &collection, &mut ConstrainCache::new()).is_err(),
            "a bare data function must not enter the top sum by subsumption"
        );
        // Width, and the codomain still flows.
        assert!(constrain_subtype(&collection, &collection, &mut ConstrainCache::new()).is_ok());
        let collection_bool = TypeKind::Any.into_data_fun(None, prim(BaseType::Bool));
        assert!(
            constrain_subtype(&collection, &collection_bool, &mut ConstrainCache::new()).is_err()
        );
        // The universe is not a *sub*-kind of a narrower description.
        assert!(constrain_subtype(&collection, &list, &mut ConstrainCache::new()).is_err());
        // Consumed: a consumer's fresh domain variable absorbs the named witness.
        let consumer = fun(fresh_var(0), int);
        assert!(constrain_subtype(&collection, &consumer, &mut ConstrainCache::new()).is_ok());
    }

    /// `into_data_fun` is the single materialization, so what it builds is decided by
    /// one test: a **merged domain kind** listing exactly one domain determines that
    /// domain and needs no witness; every other kind carries one. Says nothing about a
    /// `box`ed value — `Σ σ ∈ {𝐷 ⤇ 𝑉}. σ` is a sum over one candidate and stays one.
    #[test]
    fn a_determined_domain_kind_materializes_without_a_witness() {
        let int = prim(BaseType::Int);
        let sole = TypeKind::Enumerated(vec![Type::UIntRange(3)]);
        assert!(!sole.needs_witness());
        assert_eq!(
            sole.into_data_fun(None, int.clone()),
            Type::data_fun(Type::UIntRange(3), int.clone())
        );
        for kind in [
            TypeKind::Enumerated(vec![Type::UIntRange(2), Type::UIntRange(3)]),
            TypeKind::UIntRanges,
            TypeKind::Any,
        ] {
            assert!(kind.needs_witness(), "{kind} must materialize as a sum");
            assert!(matches!(
                kind.into_data_fun(None, int.clone()),
                Type::Sigma(_)
            ));
        }
    }

    /// The **cross-form** width edge: the unfactored sum `box` builds, below the
    /// factored sum a `List(𝑉)` annotation is. Both spellings of one type, so this is
    /// ordinary Σ-width read on instantiated bodies — and it is the edge every
    /// `List`-annotated parameter depends on.
    #[test]
    fn a_boxed_collection_is_below_a_list_annotation() {
        let int = prim(BaseType::Int);
        let boxed = Type::Sigma(Box::new(SigmaType::of(TypeKind::Enumerated(vec![
            Type::data_fun(Type::UIntRange(2), int.clone()),
        ]))));
        let list = Type::list_of(int);
        assert!(
            constrain_subtype(&boxed, &list, &mut ConstrainCache::new()).is_ok(),
            "box(xs) must reach List(V) by width"
        );
    }

    /// A keyed kind's key type is a **parameter**, not a candidate: comparing two
    /// keyed kinds *relates* the two key types invariantly rather than testing them
    /// for equality. So a wrong key type is rejected in both directions, and an
    /// **open** one is pinned by the kind it is compared against — the thing a
    /// predicate-only containment cannot do.
    #[test]
    fn keyed_kind_relates_its_key_type_invariantly() {
        let str_ = prim(BaseType::String);
        let int_map = Type::map_of(prim(BaseType::Int), str_.clone());
        let string_map = Type::map_of(prim(BaseType::String), str_.clone());

        for (sub, sup) in [(&int_map, &string_map), (&string_map, &int_map)] {
            assert!(
                constrain_subtype(sub, sup, &mut ConstrainCache::new()).is_err(),
                "Map(Int, _) and Map(String, _) must not relate in either direction"
            );
        }

        // An open key type is *pinned*, not merely matched: the edge succeeds and
        // leaves the variable bounded by the demanded key type.
        let open = Type::infer();
        let mut cache = ConstrainCache::new();
        constrain_subtype(&Type::map_of(open.clone(), str_), &int_map, &mut cache)
            .expect("an open key type is pinned by the kind it is compared against");
        let Type::Infer(v) = &open else {
            unreachable!("Type::infer() is a variable")
        };
        let bounds = v.bounds.borrow();
        let is_int = |b: &Bound| b.ty == prim(BaseType::Int);
        assert!(
            bounds.upper.iter().any(is_int) && bounds.lower.iter().any(is_int),
            "invariance should bound the key variable above *and* below by Int, got \
             lower={:?} upper={:?}",
            bounds.lower,
            bounds.upper
        );
    }

    // ----- FunKind edge (the `Compute <: Data` rejection) -----------

    fn data_fun(d: Type, c: Type) -> Type {
        Type::data_fun(d, c)
    }

    #[test]
    fn kind_data_upcasts_to_compute() {
        // `Data <: Compute` is the safe upcast — a collection is callable at any
        // index in its domain. `[0, 2] ⤇ Int <: [0, 2] ⇒ Int`.
        let mut cache = ConstrainCache::new();
        assert!(
            constrain_subtype(
                &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache,
            )
            .is_ok()
        );
    }

    #[test]
    fn kind_compute_where_data_is_rejected() {
        // `Compute ⋢ Data`: a capability supplied where a collection is demanded is
        // the rejection (the silent-row-loss guard). `[0, 2] ⇒ Int ⊀ [0, 2] ⤇ Int`.
        let mut cache = ConstrainCache::new();
        assert!(matches!(
            constrain_subtype(
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache,
            ),
            Err(ConstrainError::ComputeWhereDataRequired { .. })
        ));
    }

    #[test]
    fn kind_rejection_is_off_in_the_kind_blind_check() {
        // The post-inference check is kind-blind: the very `Compute <: Data`
        // edge the emission cache rejects is accepted here (lambda elimination
        // preserves denotation, not kind representation).
        let mut cache = ConstrainCache::new_kind_blind();
        assert!(
            constrain_subtype(
                &fun(Type::UIntRange(3), prim(BaseType::Int)),
                &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
                &mut cache,
            )
            .is_ok()
        );
    }

    #[test]
    fn kind_var_demanded_as_data_is_forced_data() {
        // A kind var *demanded* as `Data` acquires `forced_data` (no eager
        // rejection — the var may still legitimately resolve `Data`); it
        // resolves at coalesce. A compute value flowing into it would set
        // `forced_compute`, and both flags together is the conflict.
        let v = FunKindVar::fresh();
        let var_fun = Type::Fun {
            name: None,
            kind: FunKind::Var(Rc::clone(&v)),
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(prim(BaseType::Int)),
        };
        let mut cache = ConstrainCache::new();
        constrain_subtype(
            &var_fun,
            &data_fun(Type::UIntRange(3), prim(BaseType::Int)),
            &mut cache,
        )
        .expect("var <: Data records forced_data, never an eager rejection");
        assert!(v.bounds.borrow().forced_data, "demanded as data");
        assert!(
            !v.bounds.borrow().forced_compute,
            "no compute value flowed in"
        );
    }

    #[test]
    fn kind_var_link_then_late_force_propagates() {
        // Regression: a force that arrives *after* a var-var link must still
        // reach the far end. Draw `v0 <: v1` first, then force `v0` compute via
        // a later edge (`Compute <: v0`). Transitive propagation must carry
        // `forced_compute` up to `v1`; the old one-shot copy dropped it, letting
        // `v1` fall to its (possibly `Data`) domain default — a silent miskind.
        let v0 = FunKindVar::fresh();
        let v1 = FunKindVar::fresh();
        let fun_of = |v: &Rc<FunKindVar>| Type::Fun {
            name: None,
            kind: FunKind::Var(Rc::clone(v)),
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(prim(BaseType::Int)),
        };
        let mut cache = ConstrainCache::new();
        // Link first: `v0 <: v1`.
        constrain_subtype(&fun_of(&v0), &fun_of(&v1), &mut cache).expect("var-var link");
        assert!(!v1.bounds.borrow().forced_compute, "not forced yet");
        // Force later: a compute function flows into `v0` (`Compute <: v0`).
        constrain_subtype(
            &fun(Type::UIntRange(3), prim(BaseType::Int)),
            &fun_of(&v0),
            &mut cache,
        )
        .expect("compute <: var records forced_compute");
        assert!(v0.bounds.borrow().forced_compute, "v0 forced compute");
        assert!(
            v1.bounds.borrow().forced_compute,
            "compute force propagates up the link to v1 after the fact"
        );
    }
}

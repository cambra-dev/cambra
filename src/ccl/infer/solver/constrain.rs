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
use crate::ccl::ty::{FunKind, FunKindVar};
use crate::ccl::{
    BaseType, Bound, HistoryKind, InferVar, InferVarId, Level, Refinement, RefinementSet, Type,
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
    /// A compute function (a capability, `⇒`) was supplied where a data
    /// collection (`⤇`) is demanded. `Data <: Compute` is the safe
    /// upcast — a collection is callable at any index in its domain — but the
    /// reverse would iterate a *declared* domain the value does not actually
    /// cover, silently dropping rows. Raised only when the cache is
    /// kind-aware (constraint emission); the post-inference check is kind-blind
    /// (see [`ConstrainCache`]), since elimination preserves denotation but not
    /// kind representation.
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
    /// An operand's type ruled out the last implementation of a trait an operator
    /// requires — `1 > "a"`, or `\x -> x + 1` applied to a string.
    ///
    /// Raised from the bound-recording arm that delivered the offending type, so it
    /// fires the moment the program states the conflict rather than at a later phase
    /// that goes looking for it.
    NoTraitImpl {
        /// The trait with no implementation left.
        trait_: Trait,
        /// The operand position whose type ruled the last one out.
        position: u8,
        /// The type that arrived there — a base no implementation accepts, or a
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

/// The domain a gated **partition** normalizes to: a `Variant` with
/// contiguous `Index(0..n)` tags (n ≥ 1) whose every payload is exactly one
/// gate refinement over one shared domain — the shape lambda_elim's
/// value-`Case` fan-out mints (`build_value_case_fanout`: each arm gated by
/// its first-match predicate over the arms' common domain). Returns that
/// common domain; `None` for anything shaped differently (heterogeneous
/// `++`, ungated legs, gate stacks), which then takes the ordinary arms.
///
/// Detection is **target-independent** (unlike the retired
/// `is_index_partition_of`, which compared stripped legs against the
/// demand's domain): the partition *is* its plain form regardless of what it
/// meets, and normalizing before comparing is what makes the collapse
/// compose — the target-relative arm only connected a partition to
/// literally-same-domain demands, so subsumption failed to be transitive
/// (see `differential.rs :: bridge_normalization_composes`).
///
/// A leg's claims are its **gate** plus whatever the shared domain already
/// claimed, and the two are told apart by *agreement*: the gates are per-leg by
/// construction (first-match predicates, mutually exclusive), so a claim every
/// leg carries belongs to the domain and a claim only some carry is a gate.
/// Hence the common claims are the **intersection** across legs, which must
/// survive into the normal form — dropping them would normalize
/// `⧺ᵢ{{𝐸 | 𝑝} | π̂ᵢ}` to `𝐸`, claiming the gates cover all of `𝐸` when they
/// cover only its `𝑝`-satisfying part, and would let the collapse accept a
/// demand for the whole of `𝐸`.
///
/// When the legs **all claim the same thing** nothing distinguishes gate from
/// domain — the intersection is every leg's whole set — and the claims are
/// taken as gate and peeled. That covers the lone leg (an unconditional arm,
/// the fan-out's `else`) and its degenerate multi-leg twin under one rule. A
/// leg may also be bare: post-elimination rebuilds carry the gate in the
/// *term* (a `filter_values` restrict) with the leg type equal to the domain
/// outright.
fn partition_domain(union_dom: &Type) -> Option<Type> {
    let Type::Variant(tags) = union_dom else {
        return None;
    };
    let (first, rest) = tags.split_first()?;
    let mut common: Option<&Type> = None;
    for (i, (k, payload)) in tags.iter().enumerate() {
        if *k != FieldKey::Index(i) {
            return None;
        }
        let under = payload.peel_refinements();
        match common {
            None => common = Some(under),
            Some(c) if *c == *under => {}
            Some(_) => return None,
        }
    }
    let base = common?.clone();
    if rest.iter().all(|(_, p)| p.claims() == first.1.claims()) {
        return Some(base);
    }
    let shared: RefinementSet = first
        .1
        .claims()
        .iter()
        .filter(|r| rest.iter().all(|(_, p)| p.claims().contains(r)))
        .cloned()
        .collect();
    Some(Type::refined(base, shared))
}

/// The plain form of a partition-domained function
/// (`⧺ᵢ({𝐷 | π̂ᵢ}) ⤇ W  ↦  𝐷 ⤇ W`, and likewise for `⇒`), or `None` when
/// `f` is not one. The collapse is a fact about the *domain* — the gates
/// cover `𝐷` as a set — so it applies at any kind: the fan-out type shows
/// up on compute-kinded views of the same selection too, and normalizing
/// only one kind would desynchronize two sides carrying the same partition.
/// Kind, binder, and codomain ride along untouched, so the general `Fun`
/// arm's machinery (kind edge, domain variance, Pi correspondence) applies
/// to them on the re-entry.
fn normalized_partition_fun(f: &Type) -> Option<Type> {
    let Type::Fun {
        name,
        kind,
        domain,
        codomain,
    } = f
    else {
        return None;
    };
    let dnorm = partition_domain(domain)?;
    Some(Type::Fun {
        name: name.clone(),
        kind: kind.clone(),
        domain: Box::new(dnorm),
        codomain: codomain.clone(),
    })
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

        // Partition normalization (the retired "bridge rule 2", re-homed):
        // the `Variant`-domain union `⧺ᵢ ({D | π̂ᵢ} ⤇ W)` that lambda_elim's
        // value-`Case` fan-out produces for **same-domain** arms *is* the
        // plain data function `D ⤇ W` — an exhaustive + disjoint partition
        // of `D` (exhaustiveness guaranteed by the stamping phase, not
        // proven here; see lambda_elim's `build_value_case_fanout` and
        // `design/type-inference.md` §4.6). That identity is an *equation*,
        // so it is realized as a rewrite: normalize the partitioned side(s)
        // to the plain form and re-enter the ordinary arms — which then
        // supply everything the former bespoke edge set skipped: the kind
        // edge, domain variance (invariant data-data, contravariant against
        // a compute demand — the latter is what makes the collapse
        // *compose*; the old target-relative arm broke transitivity of
        // subsumption), and the Pi correspondence on the codomain edge.
        //
        // Variable domains are excluded: a partition meeting a fresh-var
        // domain records its actual (partition) type on the variable
        // exactly as before — normalization is a comparison-time view, not
        // a rewrite of what inference learns.
        (Type::Fun { domain: ld, .. }, Type::Fun { domain: rd, .. })
            if !matches!(**ld, Type::Infer(_))
                && !matches!(**rd, Type::Infer(_))
                && (normalized_partition_fun(lhs).is_some()
                    || normalized_partition_fun(rhs).is_some()) =>
        {
            let l2 = normalized_partition_fun(lhs).unwrap_or_else(|| lhs.clone());
            let r2 = normalized_partition_fun(rhs).unwrap_or_else(|| rhs.clone());
            constrain_go(&l2, &r2, sl, sr, cache)
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
            // eliminator's result, so narrowing or widening it changes which rows the
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
        // versa) is *not* matched here: it falls through to the `(_, Append)` arm below,
        // which accepts any left-hand shape, so a mutable variable demanded as a feed
        // lands in `NotAFeed` — the type-level guardrail that `<<` targets a `defer`
        // channel, not a `:=` mutable variable.
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
        // There is deliberately **no deref arm here.** A register mention that denotes
        // its value is dereffed by the rule that emits it (`emit::read_operand`), so a
        // handle reaching this relation is a handle: the only edges that carry one are
        // a pass-by-reference argument against its parameter, which the invariance arm
        // above relates, and a write's target.
        //
        // As a subtyping rule the deref was a coercion in disguise — it made `Mut(V)`
        // sit *below* `V` while `Mut` is invariant in `V`, and it fired against a fresh
        // inference variable, so nothing downstream could tell a read from a handle
        // being passed along. That is precisely why passing a register to a `Mut(V)`
        // parameter needed a separate compensating contribution: the handle was gone
        // before the invariance rule could see it.

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
            // A var-var edge carries the watch downward (see `link_watches`); the
            // closure below only re-offers `lv`'s lowers to `rhs` when the levels let
            // this arm run, which is precisely what a `let` RHS breaks.
            if let Type::Infer(rv) = rhs {
                link_watches(lv, rv, cache)?;
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
        // `g` feeds its parameter). A `<<` targeting a `:=` mutable variable lands here
        // too, as the handle it is — the left side matches `_`, so the cross-kind pair
        // the invariance arm above declined needs no rule of its own.
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
            let (lbase, lrefs) = (lhs.peel_refinements(), lhs.claims());
            let (rbase, rrefs) = (rhs.peel_refinements(), rhs.claims());
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
        // `normalize_annotation` before any constraint is emitted (see `Type::Below`).
        Type::Below(_) => {
            unreachable!("Type::Below reached the solver; `normalize_annotation` must erase it")
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
        Type::Refinement(inner, r) => {
            Type::refined(extrude(inner, pol, target_level, cache), r.clone())
        }
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
            copy_watches(tv, &nvs);

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
            copy_watches(tv, &nvs);

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

    // The deref arm these two tests covered is gone: a register mention that denotes
    // its value is dereffed by the rule that emits it (`emit::read_operand`), so
    // `Mut(V) <: τ` is no longer a subtyping fact and there is nothing to assert here.
    // The property they protected — `cnt + 1` yields `Int` rather than leaving a `Mut`
    // on an inference variable — is now pinned where it is decided:
    // `a_register_read_yields_its_value_in_an_operand_position` in `tests/type_check.rs`,
    // and the `mutability` integration suite end to end.

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
        let [r] = domain.claims() else {
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
        // edge the emission cache rejects is accepted here (elimination
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

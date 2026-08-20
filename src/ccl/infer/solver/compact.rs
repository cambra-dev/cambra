//! Bound-graph flattening: `compact_type` walks a [`Type`] and produces a
//! [`CompactGraph`] — a per-position bag of contributions (variables, atoms,
//! a record/variant shape, a function shape, and a refinement set)
//! ready for simplification and coalescing.
//!
//! [`CompactType`] / [`CompactGraph`] are the shared currency consumed by the
//! sibling [`mod@super::simplify_type`] and [`super::coalesce`] modules.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::subst::{RefinementScope, Subst};
use crate::ccl::{
    BaseType, HistoryKind, InferVarId, Name, Openness, RefinementSet, Type, fresh_infer_var_id,
};

use crate::ccl::FieldKey;

// ---------------------------------------------------------------------------
// CompactType + compact_type: bound-graph flattening
// ---------------------------------------------------------------------------
//
// `compact_type` walks a `Type` and produces a `CompactType` per
// position, transitively expanding variable bounds at the appropriate
// polarity and merging structurally (records by union/intersection of
// fields, functions by polar recursion).
//
// `simplify_type` — the polar co-occurrence analyzer that merges
// redundant variables — is implemented and wired between `compact_type`
// and `coalesce_compact`. The one stubbed path is recursive-variable
// merging (guarded by `rec_vars.contains_key`), which only fires when
// recursive types are present; it is deferred until those are supported.

/// "Atomic" leaf-shaped types other than functions and records.
///
/// CompactType bundles all of these into a single set per position;
/// merging two CompactTypes unions their atom sets, which is the
/// correct behavior at both polarities (atomic types are nominal —
/// `Int` and `String` either match or don't, no field-level subtyping).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomKey {
    /// Primitive (Int, UInt, String, Bool, Unit).
    Prim(BaseType),
    /// Finite index range `[0, n)`.
    UIntRange(usize),
    /// Externally-registered data source.
    Source(SmolStr),
    /// The transaction-commit domain (nullary, like a base type).
    Txn,
    /// a nominal feed-channel domain (rigid until
    /// channelize substitutes it).
    ChanDom(Name, crate::ccl::ChanLevel),
}

impl AtomKey {
    /// The atom `ty` contributes, or `None` for a non-atomic type. Shared with
    /// the sibling specialization-key walk, which classifies leaves the same way
    /// (see `src/ccl/infer/solver/spec_key.rs`).
    pub(super) fn from_type(ty: &Type) -> Option<AtomKey> {
        match ty {
            Type::Base(b) => Some(AtomKey::Prim(b.clone())),
            Type::UIntRange(n) => Some(AtomKey::UIntRange(*n)),
            Type::DataSource(n) => Some(AtomKey::Source(SmolStr::from(n.as_str()))),
            Type::Txn => Some(AtomKey::Txn),
            Type::ChanDom(n, l) => Some(AtomKey::ChanDom(n.clone(), *l)),
            _ => None,
        }
    }

    pub(super) fn to_type(&self) -> Type {
        match self {
            AtomKey::Prim(b) => Type::Base(b.clone()),
            AtomKey::UIntRange(n) => Type::UIntRange(*n),
            AtomKey::Source(n) => Type::DataSource(n.to_string()),
            AtomKey::Txn => Type::Txn,
            AtomKey::ChanDom(n, l) => Type::ChanDom(n.clone(), *l),
        }
    }
}

/// Flat per-position representation of a type.
///
/// At positive position, this conceptually represents a *union* of the
/// listed components (`vars ⊔ atoms ⊔ rec ⊔ fun`). At negative
/// position, an *intersection*. Cambra's output type system supports
/// neither directly, so [`coalesce_compact`](super::coalesce::coalesce_compact)
/// picks a single concrete type from these bag-of-types contributions and
/// errors on conflict.
/// The kind of a merged function slot. Three-state so [`CompactType::merge`]
/// stays infallible: a `Data ⊔ Compute` collision that would collapse a
/// data function's domain alternatives becomes `Conflict` and is reported loudly at coalesce
/// ([`super::coalesce::CoalesceError::DomainJoinConflict`]), never a mid-merge
/// panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum KindMerge {
    /// domain — the ordinary contravariant meet.
    Compute,
    /// domain — joins are lossless (`union_domains`).
    Data,
    /// A data/compute or multi-domain collision; deferred to coalesce.
    Conflict,
    /// A kind variable nothing pinned. **Not** the same as `Compute`: nothing
    /// *required* a capability here, so meeting or joining this with a resolved
    /// kind yields that kind rather than a collision. It becomes `Compute` only
    /// at coalesce, where the capability default applies because nothing else
    /// determined it.
    Unknown,
}

impl KindMerge {
    /// Resolve a function's kind. FunKind is a **provenance** property, not a
    /// function of the domain: a concrete [`FunKind`](crate::ccl::ty::FunKind)
    /// passes through unchanged. Data collections — list literals, comprehensions,
    /// `groupby` — are concrete-stamped `Data` at construction; a bare lambda is
    /// concrete `Compute` (a capability, `emit_lambda`). Only an *inferred* kind
    /// ([`FunKind::Var`](crate::ccl::ty::FunKind::Var) — a function parameter or a
    /// freshened scheme kind) reaches the flags, and the two points are
    /// incomparable, so those record *pins* rather than bounds: pinned to
    /// `Compute` → `Compute`, to `Data` → `Data`, to both → the conflict, to
    /// neither → [`KindMerge::Unknown`], which coalesce resolves to the `Compute`
    /// capability default. No domain inspection is
    /// involved: a capability supplied where a collection is demanded (e.g.
    /// `sum(λ x → x + 1)`) is a concrete `Compute` value against a concrete `Data`
    /// demand, rejected up front in [`constrain_kind`](super::constrain) — it
    /// never reaches a var here.
    pub(super) fn of(kind: &crate::ccl::ty::FunKind) -> Self {
        use crate::ccl::ty::{FunKind, KindPin};
        match kind {
            FunKind::Compute => KindMerge::Compute,
            FunKind::Data => KindMerge::Data,
            FunKind::Var(v) => match v.pin() {
                KindPin::Conflict => KindMerge::Conflict,
                // A var pinned only as data is `Data` (e.g. a parameter used only
                // as a collection). A capability flowing in would carry a concrete
                // `Compute`, reaching `KindPin::Conflict` or failing at
                // `constrain_kind` first.
                KindPin::Data => KindMerge::Data,
                KindPin::Compute => KindMerge::Compute,
                // Unpinned: not yet an answer — see `KindMerge::Unknown`.
                KindPin::Unpinned => KindMerge::Unknown,
            },
        }
    }
}

/// A merged function shape. `domains` holds one entry for an ordinary function
/// (the meet of the merged domains); a positive `Data ⊔ Data` join accumulates
/// ≥ 2 deduplicated alternatives, which coalesce reconciles (see `union_domains`).
/// `Compute` slots always carry exactly one.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactFun {
    /// The Pi (element) binder, `na.or(nb)` on merge.
    pub name: Option<Name>,
    /// The merged kind.
    pub kind: KindMerge,
    /// Domain alternatives — `len == 1` unless a `Data ⊔ Data` join accumulated more.
    pub domains: Vec<CompactType>,
    /// The codomain (covariant).
    pub codomain: Box<CompactType>,
}

/// The join of two data-function domain-alternative lists: the union of the
/// alternatives, deduplicated by structural [`CompactType`] equality. Never a
/// meet — a `Data` domain *is* the data, so narrowing it drops rows.
///
/// Both alternatives are kept because whether they are really two domains cannot
/// be decided here: at compact time a domain still carries unresolved variable
/// identity, so two structurally identical domains can compare unequal. Coalesce
/// re-runs the comparison on the materialized [`Type`]s and decides there — one
/// surviving domain is a plain data function, and more than one is a join with no
/// lossless single-domain answer.
fn union_domains(mut a: Vec<CompactType>, b: Vec<CompactType>) -> Vec<CompactType> {
    for d in b {
        if !a.contains(&d) {
            a.push(d);
        }
    }
    a
}

impl CompactFun {
    /// Merge two function slots. `pol` is the *outer* polarity; domains merge
    /// contravariantly (at `!pol`), the codomain covariantly (at `pol`).
    fn merge(pol: bool, a: CompactFun, b: CompactFun) -> CompactFun {
        use KindMerge::*;
        let name = a.name.clone().or_else(|| b.name.clone());
        let codomain = Box::new(CompactType::merge(pol, *a.codomain, *b.codomain));
        // The contravariant domain meet, defined only when both sides carry a
        // single domain (a multi-domain collection has no single domain to meet).
        let meet = |x: Vec<CompactType>, y: Vec<CompactType>| -> Vec<CompactType> {
            debug_assert!(x.len() == 1 && y.len() == 1, "meet of a multi-domain");
            vec![CompactType::merge(
                !pol,
                x.into_iter().next().unwrap(),
                y.into_iter().next().unwrap(),
            )]
        };
        // On any prior conflict, stay conflicted (keep the wider domain list
        // so coalesce can render diagnostics).
        let widest = |x: Vec<CompactType>, y: Vec<CompactType>| {
            if x.len() >= y.len() { x } else { y }
        };
        let (kind, domains) = if a.kind == Conflict || b.kind == Conflict {
            (Conflict, widest(a.domains, b.domains))
        } else if a.kind == Unknown || b.kind == Unknown {
            // Nothing required a kind on one side, so the other side's answer
            // stands — at either polarity, and with the domains combined the way
            // that answer calls for.
            let kind = if a.kind == Unknown { b.kind } else { a.kind };
            let domains = if pol && kind == Data {
                union_domains(a.domains, b.domains)
            } else if a.domains.len() == 1 && b.domains.len() == 1 {
                meet(a.domains, b.domains)
            } else {
                widest(a.domains, b.domains)
            };
            (kind, domains)
        } else if pol {
            // Positive (join).
            match (a.kind, b.kind) {
                (Data, Data) => (Data, union_domains(a.domains, b.domains)),
                (Compute, Compute) => (Compute, meet(a.domains, b.domains)),
                // `Data ⊔ Compute` has no answer. The kinds are incomparable, so
                // neither arm stands in for the other, and the contravariant meet
                // the compute reading would take is row loss on the data one.
                _ => (Conflict, widest(a.domains, b.domains)),
            }
        } else if a.kind != b.kind {
            // Negative (meet): `Data ⊓ Compute` has no answer either — one
            // position cannot require both readings of a function.
            (Conflict, widest(a.domains, b.domains))
        } else {
            let k = a.kind;
            if a.domains.len() == 1 && b.domains.len() == 1 {
                (k, meet(a.domains, b.domains))
            } else {
                // Two multi-domain requirements meeting at a negative position — no current
                // program produces this; flag it loudly at coalesce.
                (Conflict, widest(a.domains, b.domains))
            }
        };
        CompactFun {
            name,
            kind,
            domains,
            codomain,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct CompactType {
    /// Variable contributions from this position. Multiple variables
    /// can co-occur (e.g. when two projection morphisms both flow into
    /// the same parameter, both record-vars accumulate here).
    pub vars: BTreeSet<InferVarId>,
    /// Atomic-type contributions.
    pub atoms: BTreeSet<AtomKey>,
    /// Record fields, if any. At positive polarity these are
    /// intersected (kept only when both sides have the field); at
    /// negative, unioned (kept when either side has the field).
    ///
    /// `None` and `Some(empty)` are **distinct** and both load-bearing in
    /// [`merge`](Self::merge): `None` means "no record component here" and
    /// acts as the merge *identity* (the other side passes through
    /// untouched — it imposes nothing, i.e. ⊤). `Some(map)` means a record
    /// shape is present; `Some(empty)` specifically arises from
    /// *intersecting* two disjoint field sets at positive polarity and is
    /// the *absorbing* element, not the identity. Collapsing to a bare
    /// `BTreeMap` would conflate the two, and the intersect identity (⊤)
    /// has no finite-map representation anyway.
    pub rec: Option<BTreeMap<FieldKey, CompactType>>,
    /// Variant tags, if any. The polarities are the **dual** of `rec`:
    /// at positive polarity tags are *unioned* (a producer of `[A]` or
    /// `[B]` could emit `[A, B]`); at negative polarity tags are
    /// *intersected* (a consumer accepting `[A, B]` AND `[B, C]` only
    /// reliably handles `[B]`). Payload merge for matching tags uses
    /// the same polarity as the outer merge (covariant depth).
    ///
    /// `None` vs `Some(empty)` carry the same distinct meanings as for
    /// [`rec`](Self::rec) — `None` is the merge identity, `Some(empty)`
    /// the absorbing element (here from intersecting disjoint tag sets at
    /// negative polarity).
    pub var: Option<CompactVariant>,
    /// Function shape, if any: see [`CompactFun`]. Carries the Pi binder, the
    /// merged [`KindMerge`], the domain alternatives (one, unless a positive
    /// `Data ⊔ Data` join accumulated alternatives via [`union_domains`]), and the
    /// codomain. Recursively merged with polarity flip on the domain.
    pub fun: Option<CompactFun>,
    /// Refinement contributions at this position — the same
    /// [`RefinementSet`](crate::ccl::RefinementSet) the materialized `Type`
    /// carries, so flattening and coalescing agree on what a refinement set *is*
    /// rather than each keeping its own bag. A refinement set is width-subtyped
    /// exactly like `rec`: more refinements ⇒ subtype (`{T | p, q} <: {T | p}`), so
    /// at positive polarity the sets are *intersected* and at negative
    /// *unioned* (see [`CompactType::merge`]).
    ///
    /// `None` and `Some(empty)` are **distinct**, the same distinction
    /// [`rec`](Self::rec) draws and for the same reason. `None` is "no refinement
    /// contribution here" and is the merge identity: a hole imposes nothing, and
    /// a bare variable's content is its identity alone
    /// ([`CompactType::from_var`]). `Some(empty)` is a *value* that guarantees
    /// nothing, which is absorbing under the positive intersect — `Int` joined
    /// with `{Int | p}` really is `Int`. Collapsing the two makes a bare
    /// variable erase the refinements a sibling bound established, so every
    /// value-shaped contribution is built from [`CompactType::value`] and only
    /// the two non-values keep the `None`.
    pub refinements: Option<RefinementSet>,
    /// History-handle `(value, domain, kind)`, if a [`Type::History`]
    /// contributed here — a mutable variable (`kind: Overwrite`) or a feed channel
    /// (`kind: Feed`).
    ///
    /// Both children recurse at the **same polarity** as the handle itself: a
    /// history is invariant in both at the constraint level (`constrain_go`
    /// checks both directions when two same-kind handles meet), so by the time
    /// compaction runs both directions' information has already been propagated
    /// onto each child's variables, and compaction only needs a deterministic
    /// materialization, not a second polarity analysis.
    pub history_slot: Option<(Box<CompactType>, Box<CompactType>, HistoryKind)>,
}

/// A variant contribution: the tag map, and whether the arm set is the whole one.
///
/// The two travel together because they are one fact — "which tags, and is that
/// all of them" — and every operation that reshapes the map has to say what
/// becomes of the [`Openness`]. Compaction is the only place an `Open` demand can
/// be dropped silently (a lost marker turns a `case _:`'s scrutinee demand back
/// into an exact sum), so the coupling is structural rather than by convention.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CompactVariant {
    pub tags: BTreeMap<FieldKey, CompactType>,
    pub openness: Openness,
}

impl CompactVariant {
    /// A **closed** arm set — every producer of a sum, and every variant
    /// contribution that did not come from an open demand.
    pub fn closed(tags: BTreeMap<FieldKey, CompactType>) -> Self {
        Self {
            tags,
            openness: Openness::Closed,
        }
    }

    /// The openness of two arm sets meeting at one position.
    ///
    /// `Open` survives only when *both* sides are open: an open arm set imposes
    /// no requirement on the tag set, so a closed side meeting it contributes the
    /// requirement and the result is closed. Nothing else could be right at either
    /// polarity — a *producer* is always closed, so a positive merge is closed by
    /// construction.
    ///
    /// The tag *map* still merges by the ordinary rule below. That is an
    /// approximation when exactly one side is open: an exact meet would keep the
    /// closed side's tag set whole rather than intersecting the two. No program
    /// reaches it — a scrutinee takes one `Case` demand per `match`, and two open
    /// demands on one variable meet as `Open`/`Open` — so the exact rule is left
    /// unstated rather than written and untested.
    fn meet_openness(a: Openness, b: Openness) -> Openness {
        match (a, b) {
            (Openness::Open, Openness::Open) => Openness::Open,
            _ => Openness::Closed,
        }
    }
}

impl CompactType {
    /// No contribution at all — ⊤. Every slot is the merge identity, including
    /// the refinement slot, so merging this into a position leaves it unchanged. The
    /// two callers are a `Hole` and a dropped spurious-cycle bound; a value with
    /// no refinements is [`Self::value`], not this.
    fn empty() -> Self {
        Self::default()
    }

    /// A contribution that **is** a value, as opposed to the two that are not: a
    /// hole (⊤, no information) and a bare variable ([`Self::from_var`], whose
    /// content is its identity alone). Both of those keep
    /// [`refinements`](Self::refinements) at `None`, the merge identity, which is
    /// what [`Self::default`] gives; a value carries a refinement set even when it is
    /// empty, because "guarantees nothing" is itself information and is absorbing
    /// under the positive intersect.
    ///
    /// Every value-shaped arm of [`compact_go`] builds from this, so the reading
    /// a contribution gets is decided where the contribution is made rather than
    /// re-derived by inspecting it later.
    pub(super) fn value() -> Self {
        Self {
            refinements: Some(RefinementSet::default()),
            ..Self::default()
        }
    }

    /// Merge two CompactTypes at the given polarity.
    ///
    /// - `vars`, `atoms`: union (always).
    /// - `rec`: at positive polarity, *intersect* keys (a value of both
    ///   `{a, b}` and `{a, c}` is reliably only `{a}`); at negative,
    ///   *union* keys.
    /// - `fun`: recursively merge each side, flipping polarity on the
    ///   domain.
    ///
    /// - `refinements`: `None` is the identity; two present sets intersect at
    ///   positive polarity and union at negative
    ///   ([`merge_refinements`](Self::merge_refinements)).
    pub(super) fn merge(pol: bool, lhs: CompactType, rhs: CompactType) -> CompactType {
        let mut vars = lhs.vars;
        vars.extend(rhs.vars);
        let mut atoms = lhs.atoms;
        atoms.extend(rhs.atoms);
        let rec = match (lhs.rec, rhs.rec) {
            // `None` is the identity: a position with no record component
            // imposes nothing, so the other side passes through. A present
            // `Some(empty)` is *not* identity — see the `rec` field docs.
            (None, r) | (r, None) => r,
            (Some(a), Some(b)) => Some(Self::merge_records(pol, a, b)),
        };
        let var = match (lhs.var, rhs.var) {
            (None, v) | (v, None) => v,
            (Some(a), Some(b)) => Some(Self::merge_variants(pol, a, b)),
        };
        let fun = match (lhs.fun, rhs.fun) {
            (None, f) | (f, None) => f,
            (Some(a), Some(b)) => Some(CompactFun::merge(pol, a, b)),
        };
        let refinements = match (lhs.refinements, rhs.refinements) {
            // `None` is the identity, exactly as for the shape slots above.
            (None, r) | (r, None) => r,
            (Some(a), Some(b)) => Some(Self::merge_refinements(pol, a, b)),
        };
        // History children merge componentwise at the outer polarity
        // (invariance was already enforced when the constraint edges were
        // recorded). Two histories at one position share a kind — a mutable variable and a
        // feed never meet here (the constraint solver's kind-guarded
        // history/history rule rejects that), so keep either side's kind.
        let history_slot = match (lhs.history_slot, rhs.history_slot) {
            (None, m) | (m, None) => m,
            (Some((va, da, ka)), Some((vb, db, kb))) => {
                debug_assert_eq!(ka, kb, "compaction merged histories of different kinds");
                Some((
                    Box::new(Self::merge(pol, *va, *vb)),
                    Box::new(Self::merge(pol, *da, *db)),
                    ka,
                ))
            }
        };
        CompactType {
            vars,
            atoms,
            rec,
            var,
            fun,
            refinements,
            history_slot,
        }
    }

    /// Merge two refinement sets. The set-op tracks
    /// polarity the same way `rec` does — positive ⇒ *intersect*,
    /// negative ⇒ *union* — because refinement-sets width-subtype like
    /// record fields (more refinements ⇒ subtype). At a positive
    /// position the value reliably carries only the refinements *both*
    /// sides guarantee; at a negative position a consumer that may
    /// impose either set imposes their union.
    fn merge_refinements(pol: bool, lhs: RefinementSet, rhs: RefinementSet) -> RefinementSet {
        if pol {
            // The types are being unioned, so the refinements should be intersected.
            lhs.intersect(&rhs)
        } else {
            // The types are being intersected, so the refinements should be unioned.
            lhs.union(&rhs)
        }
    }

    /// Merge two variant-tag maps. Variant width-sub is the **dual** of
    /// records: at positive polarity tags are *unioned* (a producer of
    /// `[A]` OR `[B]` could emit either), at negative polarity they are
    /// *intersected* (a consumer accepting `[A,B]` AND `[B,C]` only
    /// reliably handles `[B]`). Payload depth at matching tags is
    /// covariant — payloads recurse at the outer polarity `pol`, not
    /// flipped.
    fn merge_variants(pol: bool, lhs: CompactVariant, rhs: CompactVariant) -> CompactVariant {
        // Variants invert the set-op vs records (so `!pol` selects
        // intersect-vs-union) but keep payload polarity at the outer
        // `pol` (covariant depth, same as records).
        CompactVariant {
            openness: CompactVariant::meet_openness(lhs.openness, rhs.openness),
            tags: Self::merge_keyed(!pol, pol, lhs.tags, rhs.tags),
        }
    }

    /// Merge two record-field maps. At positive polarity fields are
    /// *intersected* (the union of two record values has at least the
    /// fields common to both), at negative polarity they are *unioned*
    /// (a function accepting both `{a,b}` and `{a,c}` accepts `{a,b,c}`).
    /// Payload depth at matching fields is covariant — payloads recurse
    /// at the outer polarity `pol`.
    fn merge_records(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // For records the set-op aligns with polarity (pos = intersect)
        // and payload polarity also tracks `pol` (covariant depth).
        Self::merge_keyed(pol, pol, lhs, rhs)
    }

    /// Shared keyed-merge skeleton used by both records and variants.
    ///
    /// The two flags are independent because the relationship between
    /// the outer polarity and the *set operation on keys* differs
    /// between records (pos = intersect) and variants (pos = union),
    /// while the relationship between the outer polarity and *payload
    /// recursion* is the same in both (covariant depth, recurse at
    /// outer polarity).
    ///
    /// - `intersect_keys = true`: keep only keys present on both sides.
    /// - `intersect_keys = false`: keep keys present on either side.
    /// - `payload_pol`: polarity passed to the recursive
    ///   [`CompactType::merge`] for matching payloads.
    ///
    /// See [`Self::merge_records`] and [`Self::merge_variants`] for how
    /// outer polarity maps onto these two flags at each call site.
    fn merge_keyed<K: Ord + Clone>(
        intersect_keys: bool,
        payload_pol: bool,
        lhs: BTreeMap<K, CompactType>,
        rhs: BTreeMap<K, CompactType>,
    ) -> BTreeMap<K, CompactType> {
        let mut out = BTreeMap::new();
        if intersect_keys {
            for (k, v_lhs) in &lhs {
                if let Some(v_rhs) = rhs.get(k) {
                    out.insert(
                        k.clone(),
                        Self::merge(payload_pol, v_lhs.clone(), v_rhs.clone()),
                    );
                }
            }
        } else {
            for (k, v_lhs) in lhs {
                let merged = match rhs.get(&k) {
                    Some(v_rhs) => Self::merge(payload_pol, v_lhs, v_rhs.clone()),
                    None => v_lhs,
                };
                out.insert(k, merged);
            }
            for (k, v_rhs) in rhs {
                out.entry(k).or_insert(v_rhs);
            }
        }
        out
    }

    pub(super) fn from_atom(a: AtomKey) -> Self {
        let mut atoms = BTreeSet::new();
        atoms.insert(a);
        Self {
            atoms,
            ..Self::value()
        }
    }

    fn from_var(uid: InferVarId) -> Self {
        let mut vars = BTreeSet::new();
        vars.insert(uid);
        Self {
            vars,
            ..Self::default()
        }
    }
}

/// Compact type with side-table of recursive variable definitions.
///
/// `rec_vars[uid]` holds the bound for a recursive variable; its
/// occurrences in `term` and elsewhere are represented by
/// `CompactType { vars: {uid}, .. }`. The solver rejects residual
/// recursive types at coalesce time (per plan R2), so non-empty
/// `rec_vars` is itself an error condition unless we're handling a
/// user-annotated recursive type — which we don't yet.
#[derive(Debug, Clone)]
pub struct CompactGraph {
    pub term: CompactType,
    pub rec_vars: BTreeMap<InferVarId, CompactType>,
}

/// Walk a `Type`, transitively expanding variable bounds at the
/// appropriate polarity, and produce a CompactType.
///
/// The `parents` set tracks variables whose bounds we are currently
/// walking, so that spurious cycles (`?a <: ?b` and `?b <: ?a`) — which
/// don't represent real recursive types — get pruned.
pub fn compact_type(ty: &Type) -> CompactGraph {
    compact_type_with(ty, true)
}

/// [`compact_type`] with the opposite-polarity collapse suppressed **entirely**,
/// including at the position the walk enters — the polarity-correct walk alone.
///
/// The collapse answers "what type must this position have"; without it the walk
/// answers the strictly narrower "what reached this position *from the side it is
/// read from*". Those differ exactly where the collapse is doing its job, and a
/// caller that must not mistake a demand for a value needs the second question:
/// an upper bound deposited on an otherwise value-free position makes
/// [`compact_type`] report a type while nothing has actually flowed there.
///
/// Suppressing it walk-wide rather than at the entry is the same thing:
/// [`fallback_allowed`] already confines the collapse to the entered position, so
/// disabling it there disables it everywhere.
pub fn compact_type_polarity_only(ty: &Type) -> CompactGraph {
    compact_type_with(ty, false)
}

fn compact_type_with(ty: &Type, collapse: bool) -> CompactGraph {
    let mut st = CompactState {
        in_process: HashSet::new(),
        recursive: HashMap::new(),
        rec_vars: BTreeMap::new(),
        collapse,
        scope: RefinementScope::default(),
    };
    let term = compact_go(ty, true, &Subst::id(), None, &mut st);
    CompactGraph {
        term,
        rec_vars: st.rec_vars,
    }
}

/// The variables whose bounds the current path is walking, as a chain of stack
/// frames rather than a set on the heap.
///
/// It is a **path**, not a set: one entry per variable on the current bound chain,
/// reset at every structural boundary, and only ever asked whether a uid is on it.
/// A `BTreeSet` answers the same question and allocates a copy of itself at every
/// variable visit to do so — which on a bound-graph walk is millions of copies, for
/// a path that is a handful of entries deep. Borrowing the caller's frame costs
/// nothing and says what the thing is.
struct ParentPath<'a> {
    uid: InferVarId,
    prev: Option<&'a ParentPath<'a>>,
}

impl ParentPath<'_> {
    /// Whether `uid` is on the path. Linear in the path's depth, which is the
    /// length of one variable's bound chain.
    fn contains(&self, uid: InferVarId) -> bool {
        let mut frame = Some(self);
        while let Some(f) = frame {
            if f.uid == uid {
                return true;
            }
            frame = f.prev;
        }
        false
    }
}

/// Whether the opposite-polarity fallback may fire at the variable currently
/// being walked, given the chain that reached it.
///
/// **Only at a position** — the variable the walk entered structurally, never one
/// reached by following another variable's bounds.
///
/// Walking `𝑎 <: 𝑏 <: 𝑐` computes `𝑎`'s transitive upper bound, and finding none
/// is a *correct* conclusion: `𝑎`'s upper bound is ⊤. What the fallback does next
/// — take the lower bound instead — is not a subtyping inference but a **choice**,
/// the collapse of the `∀α ⊒ 𝐿` this system cannot represent (see the rationale in
/// [`compact_go`]). Choices do not propagate along subtyping edges: `𝐿 <: 𝑐` and
/// `𝑎 <: 𝑐` together say nothing whatever about `𝐿` versus `𝑎`. So the collapse is
/// only ever applied to the variable whose quantifier is being eliminated.
///
/// Letting it fire further along makes a function's domain the join of everything
/// the program does with any use's result: an arm binder's upper-bound chain runs
/// out through the `match` result and the codomain into the call site's operands,
/// and the join sitting there comes back as the domain's demand. See
/// `design/type-inference.md`, "The collapse happens at the position".
///
/// A structural boundary starts a new position, which is why [`compact_go`] resets
/// `parents` to `None` at every structural child.
fn fallback_allowed(parents: Option<&ParentPath<'_>>, st: &CompactState) -> bool {
    st.collapse && parents.is_none()
}

/// Walk-wide state threaded through [`compact_go`]: the cycle-tracking tables.
/// (`parents` stays a per-path argument — it is scoped to one variable's bound
/// chain and reset across structural boundaries — and the substitution
/// accumulator composes per edge.)
struct CompactState {
    /// Variables whose bounds are currently being walked, per polarity.
    in_process: HashSet<(InferVarId, bool)>,
    /// Placeholder ids minted for genuinely recursive revisits.
    recursive: HashMap<(InferVarId, bool), InferVarId>,
    /// Bounds of recursive variables (surfaced as `RecursiveType` errors by
    /// `coalesce_compact`).
    rec_vars: BTreeMap<InferVarId, CompactType>,
    /// Whether the opposite-polarity collapse may fire at all on this walk.
    /// False for [`compact_type_polarity_only`]; see [`fallback_allowed`].
    collapse: bool,
    /// The functions the walk is inside of, and the closing memo over them
    /// (`src/ccl/design/type-inference.md`, "Where the conversions run"): a
    /// refinement's references to enclosing binders become indices before
    /// `merge_refinements` compares refinements, so a closed cast and a live emitted
    /// function meeting at one variable spell one refinement one way. `key_go` threads
    /// the same type, so a key and a compacted type agree.
    scope: RefinementScope,
}

/// Compact `ty` at polarity `pol`, composing `subst_acc` — the substitution
/// accumulated from the edges walked so far — into every refinement predicate
/// materialized along the way. `subst_acc` is `Subst::id()` for ordinary
/// (non-dependent) types, in which case it is a perfect no-op and this behaves
/// exactly as the substitution-free solver. A non-identity accumulator arises
/// from Pi-binder correspondences and dependent-application discharges: each
/// bound edge composes its own `subst` in (`then(edge_subst, subst_acc)`), and
/// the composite is applied where a refinement predicate is reached — the
/// coalesce-time forcing of suspended substitutions (design §3.6).
///
/// **Sibling walk — change the two together.** `key_go`
/// (`src/ccl/infer/solver/spec_key.rs`) traverses `Type` in lockstep with this
/// function: the same polarity flip on a `Fun` domain, the same no-flip on
/// `History` children, the same `then(edge_subst, subst_acc)` composition at a
/// bound edge, the same binder shadowing for a Pi codomain, the same
/// `(uid, pol)` cycle guard. That agreement *is* the soundness argument for a
/// specialization key: a bound the key cannot see is one the clone's own
/// resolution cannot see either, because the clone resolves through this walk
/// over the same edges from the same side. Nothing enforces it, so a new `Type`
/// variant — or a change to how an edge substitution composes, or to where
/// polarity flips — has to be mirrored there in the same change. A divergence is
/// silent, and what it produces is a shared clone whose interior was resolved
/// against a different use's argument.
fn compact_go(
    ty: &Type,
    pol: bool,
    subst_acc: &Subst,
    parents: Option<&ParentPath<'_>>,
    st: &mut CompactState,
) -> CompactType {
    match ty {
        // Not a type — an annotation-position obligation, erased by
        // `normalize_annotation` before any constraint is emitted (see `Type::BoundedHole`).
        Type::BoundedHole(_) => {
            unreachable!(
                "Type::BoundedHole reached the solver; `normalize_annotation` must erase it"
            )
        }
        // Atomic types contribute a single atom. A term substitution never
        // touches an atom, so `subst_acc` is irrelevant here.
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn => CompactType::from_atom(AtomKey::from_type(ty).unwrap()),
        // Refinements ride the lattice as a refinement set: compact the underlying
        // type, then attach this layer's refinement. Walking a variable's bound
        // that is `Refinement(D, r)` therefore unions `r` into that variable's
        // compacted position — the propagation path. The accumulated
        // substitution is *forced* on the refinement: it rebuilds the predicate
        // with its free binders rewritten (e.g. discharging a dependent
        // application's argument) before the refinement lands in the position.
        // The predicate is an immutable term, so a non-vacuous force builds a
        // fresh predicate from the (freshened) bound's content directly.
        Type::Refinement(inner, refinements) => {
            let mut ct = compact_go(inner, pol, subst_acc, parents, st);
            for r in refinements {
                let r = subst_acc.force_refinement(r);
                // References to the walk's enclosing binders become indices
                // before the refinement is compared or stored.
                let r = st.scope.close(&r);
                ct.refinements
                    .get_or_insert_with(RefinementSet::default)
                    .insert(r);
            }
            ct
        }
        // A bare `Hole` shouldn't reach the solver (emission turns it into a
        // fresh var), but treat it as no contribution for exhaustiveness.
        Type::Hole | Type::SharedHole(_) => CompactType::empty(),
        Type::Fun {
            name,
            kind,
            domain: d,
            codomain: c,
        } => {
            // Function: domain is contravariant. A fresh `parents` set
            // per child mirrors Scala's `Set.empty` argument — cycles
            // span only one variable's bound chain, not across
            // function boundaries.
            let dom = compact_go(d, !pol, subst_acc, None, st);
            // A Pi binder shadows the accumulated substitution inside the
            // codomain (it binds the name locally), so restrict it there.
            let cod_acc = match name {
                Some(b) => subst_acc.shadow(b),
                None => subst_acc.clone(),
            };
            // Entering the codomain crosses this function — named or not, it
            // deepens what a refinement landing below closes against.
            st.scope.enter(name.clone());
            let cod = compact_go(c, pol, &cod_acc, None, st);
            st.scope.exit();
            CompactType {
                fun: Some(CompactFun {
                    name: name.clone(),
                    kind: KindMerge::of(kind),
                    domains: vec![dom],
                    codomain: Box::new(cod),
                }),
                ..CompactType::value()
            }
        }
        // Tuples and records share the structural `rec` representation,
        // keyed by `Index` and `Name` respectively.
        Type::Tuple(ts) => {
            let mut compacted = BTreeMap::new();
            for (i, v) in ts.iter().enumerate() {
                compacted.insert(FieldKey::Index(i), compact_go(v, pol, subst_acc, None, st));
            }
            CompactType {
                rec: Some(compacted),
                ..CompactType::value()
            }
        }
        Type::Record(fs) => {
            let mut compacted = BTreeMap::new();
            for (n, v) in fs {
                compacted.insert(
                    FieldKey::Name(SmolStr::from(n.as_str())),
                    compact_go(v, pol, subst_acc, None, st),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..CompactType::value()
            }
        }
        Type::Variant(tags, openness) => {
            // Variant payloads are covariant — recurse at the same
            // polarity (no flip, unlike Fun's domain). The merge rule
            // for variants flips records' polarity behaviour, but
            // payload depth is unaffected.
            let mut compacted = BTreeMap::new();
            for (k, v) in tags {
                compacted.insert(k.clone(), compact_go(v, pol, subst_acc, None, st));
            }
            CompactType {
                var: Some(CompactVariant {
                    tags: compacted,
                    openness: *openness,
                }),
                ..CompactType::value()
            }
        }
        // A history's children compact at the same polarity as the reference —
        // invariant in both (enforced at constraint time, so this is
        // materialization only; see the `CompactType::history_slot` docs).
        // Fresh `parents` per child. The `kind` (overwrite vs
        // feed) rides along so coalesce rebuilds the same flavour.
        Type::History {
            value,
            domain,
            kind,
        } => {
            let value = compact_go(value, pol, subst_acc, None, st);
            let domain = compact_go(domain, pol, subst_acc, None, st);
            CompactType {
                history_slot: Some((Box::new(value), Box::new(domain), *kind)),
                ..CompactType::value()
            }
        }
        Type::Infer(state) => {
            let uid = state.uid;
            let key = (uid, pol);
            if st.in_process.contains(&key) {
                if parents.is_some_and(|p| p.contains(uid)) {
                    // Spurious cycle (a <: b and b <: a with no
                    // structural intermediary). Drop the bound.
                    return CompactType::empty();
                }
                // Real recursive cycle: mint a fresh UID to mark this slot.
                // We need only the identifier here — the cycle is surfaced
                // by `coalesce_compact` as a `RecursiveType` error before
                // any level-sensitive code observes it — so we don't
                // allocate a full `InferVar` (no bounds, no level value
                // to defend).
                let placeholder = *st.recursive.entry(key).or_insert_with(fresh_infer_var_id);
                return CompactType::from_var(placeholder);
            }
            st.in_process.insert(key);
            // The opposite-polarity fallback below is monomorphization's
            // coalesce-time *read* for a contravariant position. A function
            // domain is negative, so an argument flowing in (`arg <: domain`) is
            // recorded as a *lower* bound of the domain var — but negative
            // coalesce reads *upper* bounds. The fallback recovers the concrete
            // type from the lower side. Choosing a concrete type for a
            // negative-position var that only ever receives `arg` *is*
            // monomorphizing it; the answer is the concrete `arg`.
            //
            // Algebraic subtyping's "principal" answer for such a var is
            // `∀α ⊇ arg. …`, which would need a `Type::ForAll`. Cambra uses
            // implicit, level-based polymorphism and lowers it to concrete code,
            // so the desired output here is the concrete `arg`, not a quantifier
            // — this is a pragmatic fit, not a ban on ever representing `∀`.
            //
            // The read is sound because every variable reaching coalesce is
            // *monomorphically determined* — pinned to one type by its uses, or
            // its bounds collide into `IncompatibleBounds` (never a silent
            // mis-type). This invariant is the structural-collision check; it
            // predates let-polymorphism. A generalized binding's definition is
            // never coalesced in place (the inference engine keeps it aside and
            // coalesces per-use *clones* pinned to one resolved use type);
            // only those clones and the per-use instantiations reach here,
            // each fixed by a single use site.
            let s = state.bounds.borrow();
            // `Rc::clone`, not a copy: taking the list out of the `RefCell` is a
            // refcount bump, and this is the walk's hot read.
            let primary_bounds = Rc::clone(if pol { s.lower() } else { s.upper() });
            // When the polarity-correct list is empty we fall back to the
            // opposite-polarity bounds (see the rationale above). Track which
            // polarity the bounds came from so we walk + merge them at THAT
            // polarity — record merge is asymmetric (union at negative,
            // intersection at positive), and using the wrong polarity collapses
            // disjoint-field records to the empty record at coalesce time. Fix
            // for the multi-gen iter-record case: lambda param `__iter_record`
            // accumulates upper bounds (open records `{.0}` and `{.1}`) from
            // projections; we want their negative-polarity union (both fields)
            // when the Var is coalesced at positive polarity, not the
            // positive-polarity intersection (empty).
            //
            // This fallback handles a *bare* under-determined domain var: it
            // materializes the type locally at coalesce from the lower-bound
            // side. The other half of the contravariant-domain story — a
            // *structured* domain (a tuple/record with `Infer`s inside, which
            // this per-var read cannot reassemble) — is recovered separately
            // by `coalesce_node`'s `specialize_projection_domain` /
            // `specialize_lambda_domain`. Both Apply edges are one-way (no
            // emit-time reverse whose eager cross-component propagation would
            // cover these halves); see `design/type-inference.md` ("Apply is
            // one-way" and "Closing the single-sided blind spots (no separate
            // pass)").
            let opposite_bounds = Rc::clone(if pol { s.upper() } else { s.lower() });
            drop(s);
            // Walk bounds, transitively expanding, seeded from the variable's own
            // identity: `from_var` is not a value, so it imposes nothing at any
            // slot and the fold's first step is the identity but for carrying the
            // uid ([`CompactType::refinements`] for why the refinement slot needs the
            // same `None` the shape slots have).
            //
            // Whether this variable is the *position* being materialized, which is
            // the only place the opposite-polarity collapse below may happen
            // ([`fallback_allowed`]).
            let allow_fallback = fallback_allowed(parents, st);
            let new_parents = ParentPath { uid, prev: parents };
            let mut bound = CompactType::from_var(uid);
            for b in primary_bounds.iter() {
                // Compose this edge's morphisms onto the accumulator before
                // descending: a bound reached transitively through `v → w → …`
                // arrives with every edge's morphism composed (design §3.6).
                // Identity edges leave `subst_acc` unchanged (the common case).
                let inner_acc = Subst::then(&b.render_subst(), subst_acc);
                let bc = compact_go(&b.ty, pol, &inner_acc, Some(&new_parents), st);
                bound = CompactType::merge(pol, bound, bc);
            }
            // Opposite-polarity fallback: walk the other side too if the
            // primary walk did not produce any concrete (atom / shape)
            // contribution. Without this, a variable whose only concrete
            // information lives on the opposite polarity coalesces to
            // `Type::Infer(?N)` instead of its real type — most commonly
            // a fresh lambda param whose Apply-site bound flows in at the
            // opposite polarity from where the lambda is coalesced. This is the
            // coalesce-time read of monomorphization; it is sound because every
            // var reaching coalesce is monomorphically determined (one type or
            // an `IncompatibleBounds` error). See the rationale above, and
            // [`fallback_allowed`] for why it happens only at a position.
            let no_concrete = {
                let CompactType {
                    atoms,
                    rec,
                    fun,
                    history_slot,
                    var,
                    // Not shape. Both are carried across the fallback explicitly
                    // below, rather than deciding whether it fires.
                    vars: _,
                    refinements: _,
                } = &bound;
                // A variant shape counts as concrete only at a **positive**
                // position, where it is the value's own tags — read off the lower
                // bounds, it is what the thing *is*, and the fallback firing past
                // it would overwrite the value with its own upper bound (a bounded
                // annotation reading back as the binder's type).
                //
                // At a negative position it is not a determination at all: an arm
                // binder's upper bounds are the arms the body can *handle*, so
                // stopping here would make a domain the sum of everything the
                // `match` accepts rather than the argument it was given. That
                // direction still needs the argument the fallback finds.
                let var_is_shape = pol && var.is_some();
                atoms.is_empty()
                    && rec.is_none()
                    && fun.is_none()
                    && history_slot.is_none()
                    && !var_is_shape
            };
            if no_concrete && allow_fallback {
                let mut recovered: Option<CompactType> = None;
                for b in opposite_bounds.iter() {
                    let inner_acc = Subst::then(&b.render_subst(), subst_acc);
                    let bc = compact_go(&b.ty, !pol, &inner_acc, Some(&new_parents), st);
                    recovered = Some(match recovered {
                        None => bc,
                        Some(acc) => CompactType::merge(!pol, acc, bc),
                    });
                }
                if let Some(mut recovered) = recovered {
                    // Carry what the polarity-correct walk *did* find — variable
                    // identities and refinement demands — across without letting
                    // it into the structural fold.
                    //
                    // Replacing rather than merging is what the *negative* case
                    // needs: there the primary result may hold a variant shape,
                    // and it is the arms the body can handle rather than anything
                    // that flowed in, so merging would union those tags into the
                    // domain. (At a positive position `no_concrete` now implies
                    // there is no shape at all to lose.)
                    //
                    // Refinements union instead of intersecting: a demanded
                    // predicate is checked against the value the fallback found,
                    // so both hold of it.
                    recovered.vars.extend(std::mem::take(&mut bound.vars));
                    if let Some(demanded) = bound.refinements.take() {
                        recovered
                            .refinements
                            .get_or_insert_with(RefinementSet::default)
                            .extend(demanded);
                    }
                    bound = recovered;
                }
            }
            st.in_process.remove(&key);
            // Recursive types: store the bound under the placeholder
            // variable and emit a reference.
            if let Some(rec_uid) = st.recursive.get(&key) {
                let rec_uid = *rec_uid;
                st.rec_vars.insert(rec_uid, bound);
                return CompactType::from_var(rec_uid);
            }
            bound
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Compact merge at positive polarity unions tags.
    #[test]
    fn compact_merge_variants_positive_unions() {
        let int_a = CompactType {
            var: Some(CompactVariant::closed(
                [(FieldKey::Name(SmolStr::from("A")), CompactType::default())]
                    .into_iter()
                    .collect(),
            )),
            ..Default::default()
        };
        let int_b = CompactType {
            var: Some(CompactVariant::closed(
                [(FieldKey::Name(SmolStr::from("B")), CompactType::default())]
                    .into_iter()
                    .collect(),
            )),
            ..Default::default()
        };
        let merged = CompactType::merge(true, int_a, int_b);
        let var = merged.var.expect("variant present");
        assert!(var.tags.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.tags.contains_key(&FieldKey::Name(SmolStr::from("B"))));
    }

    /// Compact merge at negative polarity intersects tags.
    #[test]
    fn compact_merge_variants_negative_intersects() {
        let int_ab = CompactType {
            var: Some(CompactVariant::closed(
                [
                    (FieldKey::Name(SmolStr::from("A")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            )),
            ..Default::default()
        };
        let int_bc = CompactType {
            var: Some(CompactVariant::closed(
                [
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("C")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            )),
            ..Default::default()
        };
        let merged = CompactType::merge(false, int_ab, int_bc);
        let var = merged.var.expect("variant present");
        assert!(!var.tags.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.tags.contains_key(&FieldKey::Name(SmolStr::from("B"))));
        assert!(!var.tags.contains_key(&FieldKey::Name(SmolStr::from("C"))));
    }

    /// Openness meets: `Open` survives only when both sides are open.
    ///
    /// An open arm set imposes no requirement on the tag set, so a closed side
    /// meeting it contributes the requirement and the result is closed. A
    /// *producer* is always closed, which is why a positive merge cannot come out
    /// open however the tags combine.
    #[test]
    fn compact_merge_variants_meets_openness() {
        let arms = |openness| CompactType {
            var: Some(CompactVariant {
                tags: [(FieldKey::Name(SmolStr::from("A")), CompactType::default())]
                    .into_iter()
                    .collect(),
                openness,
            }),
            ..Default::default()
        };
        let openness_of = |ct: CompactType| ct.var.expect("variant present").openness;
        for pol in [true, false] {
            assert_eq!(
                openness_of(CompactType::merge(
                    pol,
                    arms(Openness::Open),
                    arms(Openness::Open)
                )),
                Openness::Open
            );
            assert_eq!(
                openness_of(CompactType::merge(
                    pol,
                    arms(Openness::Open),
                    arms(Openness::Closed)
                )),
                Openness::Closed
            );
            assert_eq!(
                openness_of(CompactType::merge(
                    pol,
                    arms(Openness::Closed),
                    arms(Openness::Open)
                )),
                Openness::Closed
            );
        }
        // `None` is the merge identity for the whole variant component, openness
        // included: an absent arm set has no openness to contribute, so the
        // present side passes through rather than being closed by a default.
        assert_eq!(
            openness_of(CompactType::merge(
                true,
                CompactType::default(),
                arms(Openness::Open)
            )),
            Openness::Open
        );
    }

    /// Payload-depth polarity for variant merge: payloads at matching
    /// tags must recurse at the *outer* variant polarity (covariant
    /// depth), NOT the flipped polarity used to pick "union vs
    /// intersect tags". The two are independent and the helper has to
    /// thread them separately.
    ///
    /// To make the difference visible we use records as payloads —
    /// record-field merging is itself polarity-sensitive (pos =
    /// intersect, neg = union). At positive variant polarity the
    /// payload should merge at pos → record fields intersect.
    #[test]
    fn compact_merge_variants_propagates_outer_polarity_to_payloads() {
        // Both sides have tag "A". Payload on lhs: CompactType { rec:
        // {a: ?} }, payload on rhs: CompactType { rec: {b: ?} }.
        let payload_a = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("a")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let payload_b = CompactType {
            rec: Some(
                [(FieldKey::Name(SmolStr::from("b")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let lhs = CompactType {
            var: Some(CompactVariant::closed(
                [(FieldKey::Name(SmolStr::from("A")), payload_a)]
                    .into_iter()
                    .collect(),
            )),
            ..Default::default()
        };
        let rhs = CompactType {
            var: Some(CompactVariant::closed(
                [(FieldKey::Name(SmolStr::from("A")), payload_b)]
                    .into_iter()
                    .collect(),
            )),
            ..Default::default()
        };
        // Outer positive variant merge: tags union (one tag A here).
        // Payload depth covariant → payload merges at pos → record
        // fields intersect → empty rec map (no field in both).
        let merged = CompactType::merge(true, lhs, rhs);
        let var = merged.var.expect("variant present");
        let payload = var
            .tags
            .get(&FieldKey::Name(SmolStr::from("A")))
            .expect("tag A");
        let rec = payload.rec.as_ref().expect("payload rec present");
        assert!(
            rec.is_empty(),
            "positive payload merge intersects fields; got {rec:?}"
        );
    }

    /// `None` and `Some(empty)` in the refinement slot are different merges, which is
    /// what [`CompactType::value`] exists to keep apart. A bare variable knows
    /// nothing about refinements, so a sibling bound's refinement passes through; a value
    /// that carries no refinement guarantees nothing, and an empty set is absorbing
    /// under the positive intersect, so the same refinement is erased.
    #[test]
    fn a_bare_variable_is_refinement_neutral_and_an_unrefined_value_is_not() {
        use crate::ccl::Refinement;
        use crate::ccl::infer::solver::test_helpers::dep_pred;

        let refinement = Refinement::born(dep_pred("x"));
        let refined = CompactType {
            refinements: Some(RefinementSet::one(refinement.clone())),
            ..CompactType::value()
        };
        assert_eq!(
            CompactType::merge(
                true,
                CompactType::from_var(fresh_infer_var_id()),
                refined.clone()
            )
            .refinements,
            Some(RefinementSet::one(refinement)),
            "a bare variable must not erase a sibling bound's refinement"
        );
        assert_eq!(
            CompactType::merge(true, CompactType::value(), refined).refinements,
            Some(RefinementSet::new()),
            "a value carrying no refinement erases it: an empty set is absorbing under intersect"
        );
    }
}

#[cfg(test)]
mod refinement_closing_tests {
    use super::*;
    use crate::ccl::infer::solver::test_helpers::dep_pred;
    use crate::ccl::ty::FunKind;
    use crate::ccl::{Refinement, TypedExprNode};

    fn dep_fun(binder: &str) -> Type {
        Type::Fun {
            name: Some(Name::raw(binder)),
            kind: FunKind::Data,
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(Type::refined_one(
                Type::Base(BaseType::Int),
                Refinement::born(dep_pred(binder)),
            )),
        }
    }

    /// **Acceptance: merging α-variant dependent bounds is canonical.**
    /// Without closing against the walk's enclosing binders, the merged fun
    /// shape kept the *first arrival's* binder while the refinement sets unioned
    /// both α-copies of one constraint, coalescing to the order-dependent — and
    /// dangling — `(𝑥: 𝐷) ⤇ {{Int | __elem == 𝑥} | __elem == 𝑦}`. With each
    /// refinement closed against them as it lands (`CompactState::scope`),
    /// α-variants compact identically: the copies dedup and nothing dangles. The
    /// binder *slot* is display metadata and still follows arrival
    /// (`na.or(nb)`), so the equality is modulo `without_pi_names`.
    #[test]
    fn alpha_variant_bound_merge_is_canonical() {
        use crate::ccl::infer::solver::{
            ConstrainCache, coalesce_compact, constrain_subtype, fresh_var, simplify_type,
        };
        let coalesce_with_order = |first: &Type, second: &Type| {
            let v = fresh_var(0);
            constrain_subtype(&v, first, &mut ConstrainCache::new()).unwrap();
            constrain_subtype(&v, second, &mut ConstrainCache::new()).unwrap();
            coalesce_compact(&simplify_type(compact_type(&v))).unwrap()
        };
        let (fx, fy) = (dep_fun("x"), dep_fun("y"));
        let a = coalesce_with_order(&fx, &fy);
        let b = coalesce_with_order(&fy, &fx);
        assert_eq!(
            a.without_pi_names(),
            b.without_pi_names(),
            "α-variant bound merge must be arrival-order-independent"
        );
        // The α-copies collapsed: one refinement, spelled as the index, nothing
        // dangling.
        let Type::Fun { codomain, .. } = &a else {
            panic!("expected a function, got {a}");
        };
        let Type::Refinement(base, refinements) = &**codomain else {
            panic!("expected a refined codomain, got {codomain}");
        };
        assert!(
            !matches!(&**base, Type::Refinement(..)),
            "a refinement's base is never itself refined under `RefinementSet`, got {codomain}"
        );
        let Some(r) = refinements.sole() else {
            panic!(
                "the two α-copies of one constraint must dedup to one refinement, got {codomain}"
            );
        };
        assert!(
            crate::ccl::subst::type_free_vars(&a).is_empty(),
            "no refinement may dangle on a free binder name: {a}"
        );
        let TypedExprNode::BinOp { right, .. } = &r.predicate.node else {
            panic!(
                "expected the dependent refinement, got {}",
                crate::ccl::symbolic::symbolic(&r.predicate)
            );
        };
        assert!(
            matches!(&right.node, TypedExprNode::Var(n) if n.pi_bound_index() == Some(0)),
            "the refinement's binder reference lands as the index #0"
        );
    }

    /// **Acceptance: closing against the walk's enclosing binders keeps distinct
    /// binders distinct.** A predicate referencing the *inner* binder denotes a
    /// different type from one referencing the *outer*, and the two must not
    /// compact alike. Conflating them shares a specialization silently: two
    /// uses reach one clone whose interior was resolved against the other's
    /// argument.
    #[test]
    fn closing_keeps_distinct_binders_distinct() {
        let nested = |referenced: &str| Type::Fun {
            name: Some(Name::raw("x")),
            kind: FunKind::Data,
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(Type::Fun {
                name: Some(Name::raw("y")),
                kind: FunKind::Data,
                domain: Box::new(Type::UIntRange(4)),
                codomain: Box::new(Type::refined_one(
                    Type::Base(BaseType::Int),
                    Refinement::born(dep_pred(referenced)),
                )),
            }),
        };
        assert_ne!(
            compact_type(&nested("y")).term,
            compact_type(&nested("x")).term,
            "closing against the walk's enclosing binders must not conflate the inner and \
             outer Pi binders"
        );
    }
}

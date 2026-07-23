//! Bound-graph flattening: `compact_type` walks a [`Type`] and produces a
//! [`CompactGraph`] — a per-position bag of contributions (variables, atoms,
//! a record/variant shape, a function shape, and a refinement set)
//! ready for simplification and coalescing.
//!
//! [`CompactType`] / [`CompactGraph`] are the shared currency consumed by the
//! sibling [`mod@super::simplify_type`] and [`super::coalesce`] modules.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use smol_str::SmolStr;

use crate::ccl::subst::Subst;
use crate::ccl::{BaseType, HistoryKind, InferVarId, Name, Refinement, Type, fresh_infer_var_id};

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
    /// A reference to the nearest enclosing sum's witness — [`Type::WitnessRef`],
    /// which is nullary and anonymous exactly as [`Txn`](Self::Txn) is.
    ///
    /// It is an atom because it is a *bound* nullary type: it stands for one candidate
    /// without saying which, so it matches only itself, and the union-merge atoms get is
    /// the right law (a witness meeting a concrete type is two atoms at one position —
    /// the same collision `Int` meeting `String` is). Putting it in the body rather than
    /// factoring it out is what makes a sum's body an ordinary [`CompactType`], and
    /// hence what makes `𝐵 ⊓ 𝑇` an ordinary merge.
    Witness(crate::ccl::infer_var::WitnessBinderId),
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
            Type::WitnessRef(b) => Some(AtomKey::Witness(*b)),
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
            AtomKey::Witness(b) => Type::WitnessRef(*b),
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
/// stays infallible: a merge with no representable answer — a `Data ⊔ Compute`
/// collision that would collapse a sum's domain, or a domain join/meet the kind
/// lattice cannot form — becomes `Conflict` and is reported loudly at coalesce
/// ([`super::coalesce::CoalesceError::DomainJoinConflict`]), never a mid-merge
/// panic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum KindMerge {
    /// domain — the ordinary contravariant meet ([`meet_witness_kinds`]).
    Compute,
    /// domain — joins are lossless ([`join_witness_kinds`]).
    Data,
    /// A **kind** collision: a slot demanded as a data domain while being — or being fed
    /// as — a compute capability, the coalesce-time face of `Compute <: Data`.
    Conflict,
    /// The two **domains** have no common answer. Distinct data domains are the ordinary
    /// case, since a domain is the data and there is no sum above two of them without a
    /// term to build one.
    ///
    /// Separate from [`Conflict`](Self::Conflict) because they are different facts and
    /// want different diagnostics — one says "box these arms", the other "this is a
    /// function, not a collection". Coalesce used to tell them apart by asking whether the
    /// merged kind named more than one domain, which reads the *shape* of the answer
    /// rather than the reason for it, and mis-reported the moment a second producer
    /// existed whose candidates could deduplicate to one.
    DomainConflict,
}

impl KindMerge {
    /// Resolve a function's kind. FunKind is a **provenance** property, not a
    /// function of the domain: a concrete [`FunKind`](crate::ccl::ty::FunKind)
    /// passes through unchanged. Data collections — list literals, comprehensions,
    /// `groupby` — are concrete-stamped `Data` at construction; a bare lambda is
    /// concrete `Compute` (a capability, `emit_lambda`). Only an *inferred* kind
    /// ([`FunKind::Var`](crate::ccl::ty::FunKind::Var) — a function parameter or a
    /// freshened scheme kind) resolves from its bounds over the two-point lattice
    /// `Data ⊑ Compute`: a `Compute` lower bound → `Compute`, a `Data` upper bound
    /// (demand) → `Data`, both → the `Compute <: Data` conflict, neither → the
    /// `Compute` capability default. No domain inspection is involved: a capability
    /// supplied where a collection is demanded (e.g. `sum(λ x → x + 1)`) is a concrete
    /// `Compute` value against a `Data` demand, rejected up front in
    /// [`constrain_kind`](super::constrain) — it never reaches a var here.
    pub(super) fn of(kind: &crate::ccl::ty::FunKind) -> Self {
        use crate::ccl::ty::FunKind;
        match kind {
            FunKind::Compute => KindMerge::Compute,
            FunKind::Data => KindMerge::Data,
            FunKind::Var(v) => {
                let b = v.bounds.borrow();
                match (b.forced_compute, b.forced_data) {
                    (true, true) => KindMerge::Conflict,
                    // A var demanded as data with no compute lower bound is `Data`
                    // (e.g. a parameter used only as a collection). A capability
                    // flowing in would carry a concrete `Compute`, forcing the
                    // `(true, _)` arms or failing at `constrain_kind` first.
                    (false, true) => KindMerge::Data,
                    (true, false) => KindMerge::Compute,
                    // Unconstrained → `Compute` (a capability is the default).
                    (false, false) => KindMerge::Compute,
                }
            }
        }
    }
}

/// A merged function shape — the **single** carrier for every arrow-shaped type,
/// plain function and dependent sum alike. What distinguishes them is the
/// [`CompactWitnessKind`], so both reach one position through one slot and
/// [`CompactFun::merge`] reconciles them; there is no second route for a sum.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactFun {
    /// The Pi (element) binder, `na.or(nb)` on merge.
    pub name: Option<Name>,
    /// The merged kind.
    pub kind: KindMerge,
    /// The domain — **one** domain, compacted like any other position.
    ///
    /// Exactly one, and coalesce asserts it. Nothing puts a candidate *set* here:
    /// entering a sum is a term, so a join never forms a conditional collection out of
    /// two ordinary collections, and a consumed sum *names* its witness rather than
    /// putting a sum where a domain belongs. A candidate set lives one level up, on the witness a Σ
    /// binds ([`CompactSigma::kind`]).
    pub domain: Box<CompactType>,
    /// The codomain (covariant).
    pub codomain: Box<CompactType>,
}

/// What a Σ's **witness** ranges over — the compacted form of its witness slot, whose two
/// shapes are the two ways that slot can be filled.
///
/// A witness kind and nothing else: [`CompactSigma::kind`] is the only field of this type
/// and [`CompactSigma::merge`] the only caller of the lattice below. A *function* slot's
/// domain is one ordinary [`CompactType`] ([`CompactFun::domain`]).
///
/// Not an identity between domains and kinds: a domain is a *type*, and a
/// [`TypeKind`](crate::ccl::ty::TypeKind) *classifies* types. What this carries is
/// either the compacted candidate types themselves (`Enumerated`) or the classifier
/// with nothing compacted under it (`Described`) — and that split is the one
/// distinction the lattice cares about, since only listed candidates can be joined and
/// met as a set.
#[derive(Debug, Clone, PartialEq)]
pub enum CompactWitnessKind {
    /// [`TypeKind::Enumerated`](crate::ccl::ty::TypeKind::Enumerated), its
    /// candidates compacted and deduplicated by structural [`CompactType`]
    /// equality. One candidate is an ordinary function; two or more is a
    /// conditional collection.
    Enumerated(Vec<CompactType>),
    /// A kind that *describes* its domains rather than listing them
    /// ([`UIntRanges`](crate::ccl::ty::TypeKind::UIntRanges) — a `List`;
    /// [`Any`](crate::ccl::ty::TypeKind::Any) — a `Collection`). Such a kind
    /// carries no candidate types, so there is nothing to compact and nothing for
    /// the lattice to join or meet: it rides through verbatim, and only the
    /// codomain (the element type, the sole var-bearing part) is compacted.
    Described(crate::ccl::ty::TypeKind),
}

impl CompactWitnessKind {
    /// The described-kind constructor. A kind that lists its candidates belongs in
    /// [`Enumerated`](Self::Enumerated), where they participate in the lattice.
    fn described(kind: crate::ccl::ty::TypeKind) -> Self {
        debug_assert!(
            kind.listed().is_none(),
            "a kind that lists its domains belongs in CompactWitnessKind::Enumerated, \
             where they participate in the lattice"
        );
        CompactWitnessKind::Described(kind)
    }

    /// The listing constructor, and the mirror of [`described`](Self::described)'s
    /// guard: a listing with **no** candidates denotes no domain at all, and
    /// [`needs_witness`](crate::ccl::ty::TypeKind::needs_witness) reads it as needing one
    /// (`len != 1`), so it would materialize
    /// as the uninhabited `Σ 𝐷 ∈ {}. 𝐷 ⤇ 𝑉` rather than fail. The same invariant
    /// [`SigmaType::over`](crate::ccl::ty::SigmaType::over) asserts, checked on this side
    /// of the compact boundary too so a caller computing candidates cannot cross it with
    /// an empty result.
    fn enumerated(candidates: Vec<CompactType>) -> Self {
        debug_assert!(
            !candidates.is_empty(),
            "a compacted domain listing must hold at least one candidate"
        );
        CompactWitnessKind::Enumerated(candidates)
    }
}

/// A domain join or meet: the merged domain, or both operands handed back when the
/// kind lattice has no representable answer — which the caller reports as
/// [`KindMerge::Conflict`], with both domains still in hand for the diagnostic.
type WitnessKindMerge = Result<CompactWitnessKind, (CompactWitnessKind, CompactWitnessKind)>;

/// The **join** of two domains: what a value drawn from either ranges over.
///
/// Within one *listed* set a data join is lossless, so it is a union — the candidate
/// domains coalesce materializes as a conditional collection. Across kinds it is the
/// wider of the two ([`order_by_kind`]).
///
/// In practice this is **only** the union: every join measured across the suite is
/// `Enumerated`/`Enumerated`. A described kind
/// reaches a *meet* — a `List(𝑇)` parameter annotation and a consumer's `𝐷 ⤇ 𝑉` demand arrive as
/// two upper bounds on one variable, which the constraint solver never relates to each other —
/// but by the time a value carrying an annotation reaches a **join**, its domain has been
/// narrowed to a concrete one, so there is nothing cross-kind left to order.
///
/// The cross-kind arm below is therefore kept as lattice completion rather than as a path any
/// program is known to take. It is not turned into a conflict, because widening to the wider
/// kind is the right answer if a program ever does reach it; the note is here so the next reader
/// knows it is unexercised rather than assuming it is load-bearing.
fn join_witness_kinds(a: CompactWitnessKind, b: CompactWitnessKind) -> WitnessKindMerge {
    use CompactWitnessKind::*;
    if let Some(d) = resolve_named(&a, &b) {
        return Ok(d);
    }
    match (a, b) {
        (Enumerated(mut xs), Enumerated(ys)) => {
            for d in ys {
                if !xs.contains(&d) {
                    xs.push(d);
                }
            }
            Ok(Enumerated(xs))
        }
        // Every other pairing is ordered by the kind lattice, and a join keeps the
        // **wider** side — `UIntRanges ⊔ Any` is `Any`, because ⊤ absorbs. Unordered is a
        // genuine conflict: there is no third domain to widen to that would keep both
        // sides' compacted contents.
        (a, b) => match order_witness_kinds(a, b) {
            KindOrder::Ordered { wider, .. } => Ok(wider),
            KindOrder::Resolves(d) => Ok(d),
            KindOrder::Unrelated(a, b) => Err((a, b)),
        },
    }
}

/// A **dependent sum** in a compact position: a witness kind and a body.
///
/// The kind is a [`CompactWitnessKind`] — listed candidates, themselves compacted so an
/// unresolved one can still resolve, or a description that lists none.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactSigma {
    pub kind: CompactWitnessKind,
    /// The binder this sum introduces, carried through compaction so a round trip keeps
    /// it — a type that merely passed through the carrier comes back equal to itself
    /// rather than an α-variant. Dropping it is the same class of loss as dropping the
    /// kind.
    ///
    /// Private for the reason [`crate::ccl::ty::SigmaType`]'s is: the binder and the body
    /// naming it must be chosen together, and [`CompactSigma::fresh`] /
    /// [`CompactSigma::rebuild`] are the only pairings that cannot get it wrong.
    binder: crate::ccl::infer_var::WitnessBinderId,
    /// The body, compacted whole — with the witness present in it as
    /// [`AtomKey::Witness`] wherever [`Type::WitnessRef`] stood.
    ///
    /// Storing the *whole* body rather than its witness-independent residue is what
    /// makes the cross-slot laws ordinary merges. `Σ ⊓ 𝑇` strengthens the body by `𝑇`
    /// ([`CompactType::distribute_sigma`]), and a residue has nowhere to put a demand
    /// that lands on the witness position — a consumer's `?d ⤇ 𝑉` meeting a
    /// collection's `σ ⤇ 𝑉` is exactly that, and it is the merge that resolves `?d` *to*
    /// the witness.
    pub body: Box<CompactType>,
}

impl CompactSigma {
    /// No `fresh` counterpart, deliberately: **no sum is born at the compact level.**
    /// Every one either enters the carrier from a [`crate::ccl::Type`] (this constructor),
    /// or is derived from one already here — [`rebuild`](Self::rebuild),
    /// [`alpha_convert`](Self::alpha_convert). Origination is a `Type`-level act
    /// ([`crate::ccl::ty::SigmaType::fresh`]), and a `fresh` here would only be a way to
    /// mint one over a body that names something else.
    ///
    /// The sum that **closes** `binder` — the compact counterpart of
    /// [`crate::ccl::ty::SigmaType::closing`]: re-pairing a consumer whose domain resolved
    /// to a free witness re-forms that sum, and the binder it binds is the one the
    /// consuming rule named, not this sum's to choose.
    pub(super) fn closing(
        binder: crate::ccl::infer_var::WitnessBinderId,
        kind: CompactWitnessKind,
        body: CompactType,
    ) -> CompactSigma {
        CompactSigma {
            kind,
            binder,
            body: Box::new(body),
        }
    }

    /// **The same sum** with rebuilt parts — merged, distributed, simplified — so it keeps
    /// its binder. Minting here strands the body's occurrences.
    pub(super) fn rebuild(&self, kind: CompactWitnessKind, body: CompactType) -> CompactSigma {
        CompactSigma {
            kind,
            binder: self.binder,
            body: Box::new(body),
        }
    }

    /// **The same sum under another binder** — α-conversion, occurrences renamed with it.
    ///
    /// The only way to put a sum on a binder it did not have, and it renames rather than
    /// letting a caller assign one: a binder set without renaming strands the body's
    /// occurrences, which is the whole failure this type's constructors exist to prevent.
    pub(super) fn alpha_convert(&self, to: crate::ccl::infer_var::WitnessBinderId) -> CompactSigma {
        if self.binder == to {
            return self.clone();
        }
        CompactSigma {
            kind: rename_witness_kind(&self.kind, self.binder, to),
            binder: to,
            body: Box::new(rename_witness(&self.body, self.binder, to)),
        }
    }

    /// This sum's binder — what its body's [`AtomKey::Witness`] atoms name.
    pub(super) fn binder(&self) -> crate::ccl::infer_var::WitnessBinderId {
        self.binder
    }

    /// The body at a candidate — `𝐵[𝑑]` at the compact level, the operation every Σ
    /// rule is written in terms of, and the compact mirror of
    /// [`SigmaType::instantiate_body`](crate::ccl::ty::SigmaType::instantiate_body).
    fn instantiate(&self, candidate: &CompactType) -> CompactType {
        subst_witness(&self.body, self.binder, candidate)
    }

    /// The **factored view** of a witness-bodied sum whose candidates are all data
    /// functions: `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ` seen as `Σ 𝐷 ∈ {𝐷ᵢ}. 𝐷 ⤇ ⨆𝑉ᵢ`.
    ///
    /// Both directions of this are Σ-width, so with a shared element type the two forms
    /// are *equivalent* and this loses nothing; with differing element types the
    /// unfactored form is strictly below and this is a widening to their join.
    ///
    /// The element types join **whatever the ambient polarity** — they are the element
    /// types of a sum's *alternatives*, and the shared element type of a set of
    /// alternatives is their least upper bound by definition, which the position the sum
    /// sits at says nothing about. So this takes no polarity: merging them negatively
    /// instead *unions* their refinements, and two literal singleton arms (`[2]` and
    /// `[3, 3]`) would factor to the contradictory `{2 | __elem == 3}` rather than `Int`.
    ///
    /// `None` when the sum is not a collection sum — a described kind (nothing to view;
    /// it is already factored) or a candidate that is not a data function, which is a
    /// genuine mismatch rather than a form difference.
    fn factored_view(&self) -> Option<CompactSigma> {
        let CompactWitnessKind::Enumerated(candidates) = &self.kind else {
            return None;
        };
        let mut domains = Vec::with_capacity(candidates.len());
        let mut elem: Option<CompactType> = None;
        let mut binder: Option<Name> = None;
        for c in candidates {
            let f = c.fun.as_ref()?;
            if f.kind != KindMerge::Data {
                return None;
            }
            binder = binder.or_else(|| f.name.clone());
            domains.push((*f.domain).clone());
            elem = Some(match elem {
                None => (*f.codomain).clone(),
                Some(acc) => CompactType::merge(true, acc, (*f.codomain).clone()),
            });
        }
        Some(self.rebuild(
            CompactWitnessKind::enumerated(domains),
            CompactType {
                fun: Some(CompactFun {
                    name: binder,
                    kind: KindMerge::Data,
                    domain: Box::new(CompactType::from_atom(AtomKey::Witness(self.binder))),
                    codomain: Box::new(elem?),
                }),
                ..CompactType::default()
            },
        ))
    }

    /// Whether the body *is* the witness — `Σ 𝑤 ∈ 𝐾. 𝑤`, what
    /// [`Builtin::Box`](crate::ccl::Builtin) introduces.
    ///
    /// The distinction is load-bearing for the cross-slot laws: a demand merged into
    /// such a body lands entirely on the binder, so it is the **candidates** it narrows,
    /// not the body.
    fn body_is_witness(&self) -> bool {
        let o = self.body.occupied();
        self.body.atoms.len() == 1
            && self.body.atoms.contains(&AtomKey::Witness(self.binder))
            && o.fun.is_none()
            && !o.others
    }
}

/// `ct` with every witness atom replaced by `candidate`.
///
/// `ct` with every occurrence of binder `from` renamed to `to` — α-conversion at the
/// compact level.
///
/// What makes two sums **mergeable**. A merged sum is one sum, so its body's occurrences
/// have to name one binder; two sums built by different derivations name theirs
/// differently, and merging their bodies without renaming leaves two witness atoms at one
/// position, read downstream as two alternatives and reported as a collection conflicting
/// with itself.
///
/// Stops at a sum that **rebinds** `from`: inside it the name belongs to that binder, so
/// renaming would capture. This is the one place the scoping really is positional, because
/// shadowing is a fact about nesting rather than about identity.
fn rename_witness(
    ct: &CompactType,
    from: crate::ccl::infer_var::WitnessBinderId,
    to: crate::ccl::infer_var::WitnessBinderId,
) -> CompactType {
    let rename_map = |m: &BTreeMap<FieldKey, CompactType>| {
        m.iter()
            .map(|(k, v)| (k.clone(), rename_witness(v, from, to)))
            .collect()
    };
    CompactType {
        atoms: ct
            .atoms
            .iter()
            .map(|a| match a {
                AtomKey::Witness(b) if *b == from => AtomKey::Witness(to),
                other => other.clone(),
            })
            .collect(),
        rec: ct.rec.as_ref().map(rename_map),
        var: ct.var.as_ref().map(rename_map),
        fun: ct.fun.as_ref().map(|f| CompactFun {
            name: f.name.clone(),
            kind: f.kind,
            domain: Box::new(rename_witness(&f.domain, from, to)),
            codomain: Box::new(rename_witness(&f.codomain, from, to)),
        }),
        sigma: ct.sigma.as_ref().map(|sg| {
            let body = if sg.binder() == from {
                (*sg.body).clone()
            } else {
                rename_witness(&sg.body, from, to)
            };
            sg.rebuild(rename_witness_kind(&sg.kind, from, to), body)
        }),
        history_slot: ct.history_slot.as_ref().map(|(v, d, k)| {
            (
                Box::new(rename_witness(v, from, to)),
                Box::new(rename_witness(d, from, to)),
                *k,
            )
        }),
        witness: ct.witness.clone(),
        vars: ct.vars.clone(),
        kinds: ct.kinds.clone(),
        refinements: ct.refinements.clone(),
    }
}

fn rename_witness_kind(
    d: &CompactWitnessKind,
    from: crate::ccl::infer_var::WitnessBinderId,
    to: crate::ccl::infer_var::WitnessBinderId,
) -> CompactWitnessKind {
    match d {
        CompactWitnessKind::Enumerated(xs) => {
            CompactWitnessKind::Enumerated(xs.iter().map(|x| rename_witness(x, from, to)).collect())
        }
        CompactWitnessKind::Described(_) => d.clone(),
    }
}

/// Matches by **binder identity**, as its `Type`-level twin does, so it descends
/// everywhere: an occurrence under a nested sum carries that sum's binder and does not
/// match this one. The scoping asymmetry a positional rule must hand-maintain — stop at a
/// nested body, but descend into its kind, which is written in the outer scope — falls out
/// of the identity instead of being encoded in the walk.
fn subst_witness(
    ct: &CompactType,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &CompactType,
) -> CompactType {
    let mut out = CompactType {
        // A **free** witness rides through untouched: it belongs to whichever consumed sum
        // named it, so this binder's substitution is none of its business.
        witness: ct.witness.clone(),
        atoms: ct
            .atoms
            .iter()
            .filter(|a| **a != AtomKey::Witness(binder))
            .cloned()
            .collect(),
        vars: ct.vars.clone(),
        kinds: ct.kinds.clone(),
        refinements: ct.refinements.clone(),
        rec: ct
            .rec
            .as_ref()
            .map(|m| subst_witness_keyed(m, binder, candidate))
            .clone(),
        var: ct
            .var
            .as_ref()
            .map(|m| subst_witness_keyed(m, binder, candidate)),
        fun: ct.fun.as_ref().map(|f| CompactFun {
            name: f.name.clone(),
            kind: f.kind,
            domain: Box::new(subst_witness(&f.domain, binder, candidate)),
            codomain: Box::new(subst_witness(&f.codomain, binder, candidate)),
        }),
        sigma: ct.sigma.as_ref().map(|s| {
            // Descends into a nested sum's body too: capture-avoidance is by binder
            // identity, not by position, so an occurrence belonging to the inner binder
            // carries it and simply does not match.
            s.rebuild(
                subst_witness_kind(&s.kind, binder, candidate),
                subst_witness(&s.body, binder, candidate),
            )
        }),
        history_slot: ct.history_slot.as_ref().map(|(v, d, k)| {
            (
                Box::new(subst_witness(v, binder, candidate)),
                Box::new(subst_witness(d, binder, candidate)),
                *k,
            )
        }),
    };
    if ct.atoms.contains(&AtomKey::Witness(binder)) {
        // Merge polarity is irrelevant: the position held nothing but the witness in the
        // slots the candidate can occupy, so this is a graft, not a reconciliation.
        out = CompactType::merge(true, out, candidate.clone());
    }
    out
}

fn subst_witness_keyed<K: Ord + Clone>(
    m: &BTreeMap<K, CompactType>,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &CompactType,
) -> BTreeMap<K, CompactType> {
    m.iter()
        .map(|(k, v)| (k.clone(), subst_witness(v, binder, candidate)))
        .collect()
}

/// The domains `ct` names as a **data collection**, when a witness of `kind` may be
/// each of them — the test for "`𝑇` picks out a candidate of `𝐾`".
///
/// It runs the same [`TypeKind::contains_ground`](crate::ccl::ty::TypeKind::contains_ground)
/// as the Σ-width premise, so a pairing the lattice admits here is one the subtyping
/// rules admit too. `None` when `ct` is not a data collection, or only **names** its domain
/// position rather than saying what it is ([`names_position`]) — a consumer's fresh domain
/// variable and a bare witness reference both name no domain, so neither can pick a
/// candidate; they are what consuming a sum resolves, and must reach the body instead.
fn admitted_domain(ct: &CompactType, kind: &CompactWitnessKind) -> Option<Vec<CompactType>> {
    let f = ct.fun.as_ref()?;
    if f.kind != KindMerge::Data {
        return None;
    }
    let named = denoted_domains(&f.domain)?;
    let theirs = crate::ccl::ty::TypeKind::Enumerated(named);
    let ours = witness_type_kind(kind)?;
    theirs
        .contains_ground(&ours)
        .then(|| vec![(*f.domain).clone()])
}

/// Whether a position's concrete content is **only** a witness — bound (`σ`) or free
/// (`σ#𝑛`) — and nothing else. Variables and kinding constraints do not disqualify it, for
/// the same reason they never count as content: they name or constrain the position rather
/// than filling it.
///
/// Both forms name rather than fill, so both answer here. A *bound* one is the sum's own
/// domain read inside its body; a *free* one is a consumer's domain after a consumed sum
/// named it. Neither is a type with content to distribute, and treating either as one is
/// what puts a witness where a domain belongs.
fn is_bare_witness(ct: &CompactType) -> bool {
    let o = ct.occupied();
    let bound_only = o.atoms == 1
        && ct.atoms.iter().any(|a| matches!(a, AtomKey::Witness(_)))
        && ct.witness.is_none();
    let free_only = o.atoms == 0 && ct.witness.is_some();
    (bound_only || free_only) && o.fun.is_none() && !o.others
}

/// Split a position into the **content** that a cross-slot Σ law pushes into a sum's
/// body and the **names** that stay where they were written.
///
/// This is the [Naming a position is not filling
/// it](`src/ccl/design/type-inference.md`) split, applied: variables and kinding
/// constraints name a position rather than contributing to one. By the time this runs,
/// compaction has folded a variable's bounds into the concrete slots, so moving the name
/// inward would relocate it without moving any information, and simplification reads
/// co-occurrence off where names sit.
fn split_content(ct: &CompactType) -> (CompactType, CompactType) {
    let content = CompactType {
        vars: BTreeSet::new(),
        kinds: Vec::new(),
        ..ct.clone()
    };
    let names = CompactType {
        vars: ct.vars.clone(),
        kinds: ct.kinds.clone(),
        ..CompactType::default()
    };
    (content, names)
}

fn subst_witness_kind(
    d: &CompactWitnessKind,
    binder: crate::ccl::infer_var::WitnessBinderId,
    candidate: &CompactType,
) -> CompactWitnessKind {
    match d {
        CompactWitnessKind::Enumerated(xs) => CompactWitnessKind::Enumerated(
            xs.iter()
                .map(|x| subst_witness(x, binder, candidate))
                .collect(),
        ),
        CompactWitnessKind::Described(_) => d.clone(),
    }
}

impl CompactSigma {
    /// Merge two sums at one position. Both laws are *derived* from the subtyping
    /// rules rather than chosen (`src/ccl/design/type-inference.md`, "How a sum flows
    /// through the solver"):
    ///
    /// - **positive** — width relates a sum to another when its candidates pair into
    ///   the other's kind, so the least upper bound is the sum over *both*: union the
    ///   kinds. This is what keeps both alternatives in `box(xs) if c else box(ys)`.
    /// - **negative** — a value satisfying two sum demands is one whose candidates pair
    ///   into each, so the demands *meet*.
    ///
    /// Bodies merge at the outer polarity, covariantly: the body varies with the
    /// witness, and the witness is what the kinds just combined.
    ///
    /// A kind conflict cannot be reported from here — the signature returns a merged
    /// value, as every slot merge does — so an unrelated pairing keeps the left side and
    /// the disagreement surfaces where kinds are compared with a graph to fail into.
    fn merge(pol: bool, a: CompactSigma, b: CompactSigma) -> CompactSigma {
        let a_binder = a.binder;
        // **One form before merging.** Kinds and bodies merge slot against slot, which is
        // only meaningful when the bodies have the same shape — a witness body and an
        // arrow body have no merge, and left alone they coalesce to the collision
        // `σ | (σ ⤇ 𝑉)`. The two forms are interconvertible (both directions are Σ-width),
        // so the mismatch is one of spelling, not of type: put the witness-bodied side
        // into the other's form and merge normally.
        //
        // Factored is the target rather than unfactored because it is the only form a
        // *described* kind has — and the case that most needs this is exactly a described
        // one, a `List(𝑉)` annotation meeting a `box`ed conditional collection.
        let (a, b) = match (a.body_is_witness(), b.body_is_witness()) {
            (true, false) => (a.factored_view().unwrap_or(a), b),
            (false, true) => (a, b.factored_view().unwrap_or(b)),
            _ => (a, b),
        };
        // **α-convert before merging.** The two sums name their binders independently, so
        // `b`'s occurrences are renamed to `a`'s — otherwise the merged body carries two
        // witness atoms for one witness.
        let b = b.alpha_convert(a_binder);
        let kind = if pol {
            join_witness_kinds(a.kind.clone(), b.kind)
        } else {
            meet_witness_kinds(pol, a.kind.clone(), b.kind)
        }
        .unwrap_or(a.kind);
        // `a`'s binder, and `b` was α-converted onto it above: the merged sum is one sum,
        // so its body's occurrences have to name one binder.
        CompactSigma::closing(a_binder, kind, CompactType::merge(pol, *a.body, *b.body))
    }
}

/// Which of a position's **concrete** slots are occupied.
///
/// `vars` is deliberately not among them. By the time the domain lattice reads a
/// position, compaction has folded every variable's bounds into these slots, and
/// coalesce likewise materializes a position from them alone — so a leftover variable
/// alongside resolved content says nothing about what the position denotes.
///
/// Built by destructuring, so a new [`CompactType`] slot is a compile error here
/// rather than a silently-ignored contribution.
struct Occupied<'a> {
    /// Whether a free witness names this position. Separate from `atoms` because it
    /// answers a different question: not "what type is here" but "whose domain is this".
    witness: bool,
    atoms: usize,
    fun: Option<&'a CompactFun>,
    others: bool,
}

impl CompactType {
    fn occupied(&self) -> Occupied<'_> {
        let CompactType {
            vars: _,
            // A kinding constraint says what a position must *be*, never that it is
            // occupied — it is a condition on the answer, like `vars`, not a
            // contribution to it.
            kinds: _,
            // A free witness *names* the position rather than filling it, exactly as a
            // bound one does — but it is real content for the purpose of "is anything
            // here", since a position holding one is the witness and nothing else may
            // claim it. Reported separately so callers can tell the two apart.
            witness,
            atoms,
            rec,
            var,
            fun,
            sigma,
            refinements,
            history_slot,
        } = self;
        Occupied {
            witness: witness.is_some(),
            atoms: atoms.len(),
            fun: fun.as_ref(),
            others: rec.is_some()
                || var.is_some()
                || sigma.is_some()
                || !refinements.is_empty()
                || history_slot.is_some(),
        }
    }
}

/// The domains a compacted **data**-function domain position denotes, as types.
///
/// [`CompactType::merge`] unions atom sets. At a scalar position that is the only
/// sound reading — `Int` and `String` cannot both hold, so two atoms are a collision
/// — but a data function's domain *is* the data, and the join law for data is
/// lossless, so atoms meeting there are *alternatives*: one domain each. Both facts
/// live in the same atom set, so which reading applies is decided by the enclosing
/// arrow's kind, which only the caller knows.
///
/// `None` when the position denotes no domain set at all: its concrete content must
/// be nothing but atoms, since anything alongside them (a record, a nested arrow, a
/// refinement) means this is an ordinary domain that merely accumulated bounds — and
/// then the atoms really are a collision. Variables do not disqualify it; compaction
/// has already folded their bounds in.
///
/// This is the single reading of a domain position. Both consumers need it: coalesce
/// materializes the alternatives as a sum's candidates, and
/// [`meet_witness_kinds`] tests them for membership in a witness kind. When the two
/// disagreed — one accepting several atoms, the other only one — a conditional
/// collection reaching a `List`-annotated parameter was rejected.
pub(super) fn denoted_domains(ct: &CompactType) -> Option<Vec<Type>> {
    let o = ct.occupied();
    // A position a free witness names denotes no domain *set*: it is one domain, the
    // one the witness picked, and which one is not settled here. Same reading as a bare
    // variable — naming a position is not filling it.
    let bare_atoms = o.atoms >= 1 && o.fun.is_none() && !o.others && !o.witness;
    bare_atoms.then(|| ct.atoms.iter().map(|a| a.to_type()).collect())
}

/// How the kind lattice orders two domains — the whole of the cross-kind lattice, and
/// the one place a meet and a join differ only in which side they keep.
enum KindOrder {
    /// Ordered by containment: a meet keeps `narrower`, a join keeps `wider`.
    Ordered {
        narrower: CompactWitnessKind,
        wider: CompactWitnessKind,
    },
    /// One side has not resolved to a shape and carries nothing concrete — a
    /// consumer's fresh domain *variable*. Consuming a sum is what would have resolved
    /// it *to* the other side, so both meet and join are that other side.
    Resolves(CompactWitnessKind),
    /// Neither contains the other.
    Unrelated(CompactWitnessKind, CompactWitnessKind),
}

/// The kind to order a compacted domain **by**, so the lattice can compare it against
/// another.
///
/// This is *not* "the kind of these domains" — a type inhabits an up-set of kinds, so
/// there is nothing to recover. It is the **minimal** kind containing them: the listing
/// of what the candidates resolved to. A described slot already *is* a kind and is
/// returned as itself; `None` means the candidates have no shapes yet, so no minimal
/// kind is determined and the caller must fall back to
/// [`KindOrder::Resolves`] rather than to a guess.
fn witness_type_kind(d: &CompactWitnessKind) -> Option<crate::ccl::ty::TypeKind> {
    match d {
        CompactWitnessKind::Described(k) => Some(k.clone()),
        // Every candidate must yield domains for a minimal kind to exist here; a candidate
        // yielding *several* — the arms of a conditional collection arriving as atoms on
        // one position — contributes each of them (see [`denoted_domains`]).
        CompactWitnessKind::Enumerated(xs) => xs
            .iter()
            .map(denoted_domains)
            .collect::<Option<Vec<_>>>()
            .map(|per_candidate| {
                crate::ccl::ty::TypeKind::Enumerated(per_candidate.into_iter().flatten().collect())
            }),
    }
}

/// Order two domains by witness-kind containment.
///
/// This runs the **same** [`TypeKind::contains`](crate::ccl::ty::TypeKind::contains) as
/// the Σ-width subtyping rule, so the compact lattice and the subtyping rules cannot
/// drift: `Array <: List` and `List <: Collection` order the same way here as there.
/// Deriving the order from containment rather than computing a fresh kind is also what
/// keeps a domain's *compacted contents*: the answer is one of the two inputs, not a
/// rebuilt kind that would drop them.
///
/// It is also where a `List(𝑇)` parameter annotation and a consumer's `𝐷 ⤇ 𝑉` demand
/// are reconciled. They are two *upper* bounds on one variable, which the constraint
/// solver never relates to each other, so the meet is the only place a sum can be consumed
/// between them — and, measured across the suite, the only caller that reaches
/// this at all. A join is always a union of listings ([`join_witness_kinds`]), so the order it
/// reads is a meet's order.
///
/// A merge has no constraint graph to emit obligations into, so it orders by
/// [`TypeKind::contains_ground`](crate::ccl::ty::TypeKind::contains_ground) — the same
/// containment under the only discharge available here, where a parameter pair must
/// already hold as written and a pending kinding constraint cannot hold at all. Anything
/// else is `Unrelated` rather than accepted on a relation nothing here can discharge.
fn order_witness_kinds(a: CompactWitnessKind, b: CompactWitnessKind) -> KindOrder {
    let holds = crate::ccl::ty::TypeKind::contains_ground;
    match (witness_type_kind(&a), witness_type_kind(&b)) {
        (Some(ka), Some(kb)) => {
            if holds(&ka, &kb) {
                KindOrder::Ordered {
                    narrower: a,
                    wider: b,
                }
            } else if holds(&kb, &ka) {
                KindOrder::Ordered {
                    narrower: b,
                    wider: a,
                }
            } else {
                KindOrder::Unrelated(a, b)
            }
        }
        // A side with no shape yet resolves to the other, but only when it carries
        // nothing concrete — otherwise picking the other side would silently drop it.
        (None, Some(_)) if names_position(&a) => KindOrder::Resolves(b),
        (Some(_), None) if names_position(&b) => KindOrder::Resolves(a),
        _ => KindOrder::Unrelated(a, b),
    }
}

/// Whether this domain only **names** the position rather than saying what it is —
/// nothing concrete to lose by taking the other side.
///
/// Two things name a position without filling it. A bare **variable** is the familiar
/// one: a consumer's fresh domain, which consuming a sum is what resolves. A bare
/// **witness reference** is the other: inside a sum's body, `σ` *is* the position, so a
/// concrete domain arriving there says which domain the witness took rather than
/// standing beside it as a second alternative. Keeping them apart is what produced
/// `{Σ σ ∈ {[0, 1]}. σ, σ}` — a collection reported as conflicting with its own witness.
///
/// A described kind never names: it is itself the shape.
fn names_position(d: &CompactWitnessKind) -> bool {
    match d {
        CompactWitnessKind::Described(_) => false,
        CompactWitnessKind::Enumerated(xs) => xs.iter().all(|x| {
            let o = x.occupied();
            (o.atoms == 0 || is_bare_witness(x)) && o.fun.is_none() && !o.others
        }),
    }
}

/// The side that carries content, when exactly one of them does — the lattice answer for
/// both a join and a meet, since a name for a position constrains nothing.
fn resolve_named(a: &CompactWitnessKind, b: &CompactWitnessKind) -> Option<CompactWitnessKind> {
    match (names_position(a), names_position(b)) {
        (true, false) => Some(b.clone()),
        (false, true) => Some(a.clone()),
        _ => None,
    }
}

/// The contravariant **meet** of two witness kinds — the strongest contract that satisfies
/// both. `dpol` is the *domain's* own polarity (the flip of the enclosing function's),
/// under which two single candidates' contents merge.
///
/// Within one *listed* set the meet operates on the candidates; across kinds it is the
/// narrower of the two ([`order_witness_kinds`]).
fn meet_witness_kinds(
    dpol: bool,
    a: CompactWitnessKind,
    b: CompactWitnessKind,
) -> WitnessKindMerge {
    use CompactWitnessKind::*;
    if let Some(d) = resolve_named(&a, &b) {
        return Ok(d);
    }
    match (a, b) {
        // Two ordinary domains meet by merging their content, so each side's
        // information reaches the other — an ordering would keep one and drop the
        // other's bounds.
        (Enumerated(xs), Enumerated(ys)) if xs.len() == 1 && ys.len() == 1 => {
            let x = xs.into_iter().next().expect("len == 1");
            let y = ys.into_iter().next().expect("len == 1");
            Ok(Enumerated(vec![CompactType::merge(dpol, x, y)]))
        }
        // Every other pairing is ordered by the same kind lattice the join uses, and a
        // meet keeps the **narrower** side: an `Array(2, 𝑉)` demanded of a `List(𝑉)`
        // parameter meets at the `Array`. `Resolves` is a sum being consumed, at the
        // lattice level — a consumer's fresh domain variable carrying nothing concrete is
        // exactly what a consumed sum would have resolved *to* the other side, so keeping
        // that side is that resolution.
        (a, b) => match order_witness_kinds(a, b) {
            KindOrder::Ordered { narrower, .. } => Ok(narrower),
            KindOrder::Resolves(d) => Ok(d),
            KindOrder::Unrelated(a, b) => Err((a, b)),
        },
    }
}

/// The merged [`KindMerge`] of two function slots, independent of polarity: `Data` is the
/// stronger contract and wins wherever either side has it; `Data ⊔ Compute` is an honest
/// upcast to a callable and lands on `Compute`.
fn kind_of(a: &KindMerge, b: &KindMerge) -> KindMerge {
    match (a, b) {
        (KindMerge::Data, KindMerge::Data) => KindMerge::Data,
        _ => KindMerge::Compute,
    }
}

/// Whether these **types** denote more than one domain — the [`denotes_several_domains`]
/// reading, applied after a merge has put both sides in one position.
fn denotes_several_domains_ty(ds: &[Type]) -> bool {
    let mut seen: Vec<&Type> = Vec::new();
    for d in ds {
        if !seen.contains(&d) {
            seen.push(d);
        }
    }
    seen.len() > 1
}

impl CompactFun {
    /// Merge two function slots. `pol` is the *outer* polarity; the domain merges
    /// contravariantly (at `!pol`), the codomain covariantly (at `pol`).
    fn merge(pol: bool, a: CompactFun, b: CompactFun) -> CompactFun {
        use KindMerge::*;
        let name = a.name.clone().or_else(|| b.name.clone());
        let codomain = Box::new(CompactType::merge(pol, *a.codomain, *b.codomain));
        // A failed join/meet is not a panic: it becomes a **domain** conflict, keeping
        // the wider of the two domains so coalesce's diagnostic names the richer shape.
        let conflicted = |k: &KindMerge| matches!(k, Conflict | DomainConflict);
        // The domain merges **contravariantly** and as one ordinary position — there is no
        // domain lattice left to consult, because a `fun` slot holds one domain. What was a
        // join or meet of candidate *sets* is now the same `CompactType::merge` every other
        // position gets.
        let domain = Box::new(CompactType::merge(
            !pol,
            (*a.domain).clone(),
            (*b.domain).clone(),
        ));
        // **Distinct domains have no common data-function type.** A domain is the data, so
        // two collections over different domains share no type at all, and there is no sum
        // above them either — entering one is a term. The merge above has put both domains
        // in one position; several *denoted* domains there is exactly that conflict, and it
        // is what `[1] if c else [2, 3]` must report instead of quietly acquiring a sum.
        let several = matches!(kind_of(&a.kind, &b.kind), Data)
            && denoted_domains(&domain).is_some_and(|ds| denotes_several_domains_ty(&ds));
        let kind = if conflicted(&a.kind) || conflicted(&b.kind) {
            // A conflict already recorded keeps its *reason* — the two are different facts
            // and want different diagnostics.
            if a.kind == Conflict || b.kind == Conflict {
                Conflict
            } else {
                DomainConflict
            }
        } else if several {
            DomainConflict
        } else {
            kind_of(&a.kind, &b.kind)
        };
        CompactFun {
            name,
            kind,
            domain,
            codomain,
        }
    }
}

/// The range to **bind** a domain position over, when that position is nothing but a free
/// witness — together with any restriction alongside.
///
/// This is the other half of the round trip. Consuming a sum named its witness — a
/// [`Type::WitnessRef`] to the sum's own binder, with the range left on the binder
/// ([`crate::ccl::ty::witness_ctx`]) — and a data function built over that name is not a
/// function on some domain, it *is* the sum, so binding it here re-forms it. `𝑤` never
/// escapes: it is free between those two points and nowhere else.
///
/// Two shapes are read, because the two consuming arms still write the fact down
/// differently — the arrow-bodied arm names the witness, the witness-bodied arm still
/// hands over a sum standing where a domain belongs. Both say "this domain is the
/// witness's".
///
/// `vars` is deliberately not part of the test: the position carries the consumer's own
/// domain variable, which is what the naming resolved. What matters is that nothing
/// *concrete* joined it — a resolved shape there means an ordinary domain, and re-pairing
/// would discard it.
fn free_witness_kind(
    dom: &CompactType,
    pol: bool,
    subst_acc: &Subst,
    st: &mut CompactState,
) -> Option<(
    crate::ccl::infer_var::WitnessBinderId,
    CompactWitnessKind,
    Vec<Refinement>,
)> {
    let bare =
        dom.fun.is_none() && dom.rec.is_none() && dom.var.is_none() && dom.history_slot.is_none();
    if !bare {
        return None;
    }
    match (
        dom.witness.as_ref(),
        dom.atoms.len(),
        dom.kinds.as_slice(),
        dom.sigma.as_ref(),
    ) {
        // The witness names the position and carries the kind it ranges over — one fact,
        // read straight off the slot.
        (Some((binder, kind)), 0, _, None) => Some((
            *binder,
            compact_kind(kind, !pol, subst_acc, st),
            dom.refinements.clone(),
        )),
        _ => None,
    }
}

/// `domain` with `restriction` pushed onto every candidate.
///
/// A restriction belongs on the candidates, not at the position: left where it was
/// written it would read as a refined *sum type* standing as a domain, and a sum is not
/// a domain (`src/ccl/design/type-inference.md`, "A variable's lower bounds are one
/// value").
fn restrict_candidates(
    domain: &CompactWitnessKind,
    restriction: &[Refinement],
) -> CompactWitnessKind {
    if restriction.is_empty() {
        return domain.clone();
    }
    match domain {
        CompactWitnessKind::Enumerated(candidates) => CompactWitnessKind::enumerated(
            candidates
                .iter()
                .map(|c| {
                    let mut c = c.clone();
                    for r in restriction {
                        if !c.refinements.contains(r) {
                            c.refinements.push(r.clone());
                        }
                    }
                    c
                })
                .collect(),
        ),
        // A described kind lists no candidates to restrict. Its domains are characterized
        // rather than enumerated, so there is nothing here to attach the restriction to
        // and it stays at the position.
        CompactWitnessKind::Described(_) => domain.clone(),
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
    pub var: Option<BTreeMap<FieldKey, CompactType>>,
    /// Arrow shape, if any: see [`CompactFun`]. Carries the Pi binder, the merged
    /// [`KindMerge`], the [`CompactWitnessKind`], and the codomain. Recursively merged
    /// with polarity flip on the domain. Plain functions *and* dependent sums both
    /// live here — one slot, so the two ways a sum reaches a position (directly, and
    /// as the domain a consumed sum named) merge instead of colliding.
    pub fun: Option<CompactFun>,
    /// A **dependent sum** at this position, when its body is not an arrow.
    ///
    /// A Σ is a type constructor, so it gets a slot of its own with its own
    /// polarity-dual merge law, exactly as `rec`, `var` and `fun` do
    /// (`src/ccl/design/type-inference.md`, "How a sum flows through the solver").
    /// Arrow-bodied sums still ride the [`fun`](Self::fun) slot; this holds the ones
    /// that slot cannot express — a body that *is* the witness, which is what
    /// [`Builtin::Box`](crate::ccl::Builtin) introduces.
    pub sigma: Option<CompactSigma>,
    /// The **free witness** this position is, if it is one: the name a consumed sum gave
    /// the domain its witness picked, with the range it varies over.
    ///
    /// A slot rather than an [`AtomKey`], and not for convenience. The atom set is a
    /// `BTreeSet` — set membership, `Ord`, "either match or don't, no field-level
    /// subtyping" — and a witness carrying a kind has exactly the field-level structure
    /// that excludes. It also has to be *read* at materialization, where a lone witness
    /// position binds to `Σ 𝑤 ∈ 𝐾. 𝑤`; an atom could carry the identity but never the
    /// kind, so binding it would have nothing to work from.
    pub witness: Option<(
        crate::ccl::infer_var::WitnessBinderId,
        crate::ccl::ty::TypeKind,
    )>,
    /// Refinement contributions at this position. A set with `==`
    /// membership (deduplicated by [`Refinement`]'s structural `PartialEq`),
    /// stored as a `Vec` in first-insertion order. A refinement-set is
    /// width-subtyped exactly like `rec`: more refinements ⇒ subtype
    /// (`{T | p, q} <: {T | p}`), so at positive polarity the sets are
    /// *intersected* and at negative *unioned* (see
    /// [`CompactType::merge`]). The stored [`Refinement`] is the payload
    /// carried to coalesce.
    pub refinements: Vec<Refinement>,
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
    /// **Kinding** constraints gathered from the variables contributing here —
    /// `α :: 𝐾` for each, conjunctively. Folded in by the variable walk exactly as
    /// its bounds are, and discharged by
    /// [`coalesce_compact`](super::coalesce::coalesce_compact) against the type this
    /// position materializes to. Not polar: a kinding constraint is an assertion about
    /// a resolution, so both merge directions union.
    ///
    /// This slot is why the check needs no side channel. A variable's kinding
    /// constraint reaches the position it determines by the same route its bounds do,
    /// so "check it where the variable resolves" is a local question at coalesce
    /// rather than a list to be drained afterwards.
    pub kinds: Vec<crate::ccl::ty::TypeKind>,
}

impl CompactType {
    fn empty() -> Self {
        Self::default()
    }

    /// Merge two CompactTypes at the given polarity.
    ///
    /// - `vars`, `atoms`: union (always).
    /// - `rec`: at positive polarity, *intersect* keys (a value of both
    ///   `{a, b}` and `{a, c}` is reliably only `{a}`); at negative,
    ///   *union* keys.
    /// - `fun`: recursively merge each side, flipping polarity on the
    ///   domain.
    pub(super) fn merge(pol: bool, lhs: CompactType, rhs: CompactType) -> CompactType {
        // **The cross-slot Σ laws.** A sum meeting a *non*-sum cannot be handled
        // slot-against-slot the way `Σ ⊔ Σ` and `Σ ⊓ Σ` are, because the two live in
        // different slots — so it is decided here, before the per-slot merges
        // (`src/ccl/design/type-inference.md`, "How a sum flows through the solver").
        //
        // Both directions reduce to **distributing over the candidates**, and both are
        // derived rather than chosen:
        //
        // - **positive (`Σ ⊔ 𝑇`)** — no subtyping edge builds a sum, so none lies above a bare
        //   `𝑇`, so every upper bound of both is a non-sum; consuming the sum then requires
        //   it above every candidate. The sum *dissolves* into the join. This is what makes
        //   `box(xs) if c else xs` collapse to `xs`'s type.
        // - **negative (`Σ ⊓ 𝑇`)** — only a sum satisfies a sum demand, and a sum
        //   satisfies a plain demand by being consumed, so `𝑇` strengthens the body. For a
        //   witness-bodied sum the body *is* the witness, so that is again each
        //   candidate.
        //
        // Restricted to a witness-bodied sum, which is the only shape this slot holds:
        // an arrow-bodied one needs `𝐵[𝑑]` at the compact level, which arrives with the
        // migration off the `fun` slot.
        if let Some(out) = Self::distribute_sigma(pol, &lhs, &rhs) {
            return out;
        }
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
        let sigma = match (lhs.sigma, rhs.sigma) {
            (None, s) | (s, None) => s,
            (Some(a), Some(b)) => Some(CompactSigma::merge(pol, a, b)),
        };
        let refinements = Self::merge_refinements(pol, lhs.refinements, rhs.refinements);
        // Conjunction at both polarities: the position must satisfy every kinding
        // constraint of every variable that determines it. Deduplicated so a variable
        // reached twice through the bound graph does not grow the list.
        let mut kinds = lhs.kinds;
        for k in rhs.kinds {
            if !kinds.contains(&k) {
                kinds.push(k);
            }
        }
        // **A free witness absorbs a domain its range admits.** A witness meeting a
        // concrete type is normally a collision, exactly as `Int` meeting `String` is —
        // two things claiming one position. A *free* one is different: the position
        // **is** the witness, so a concrete domain arriving says which candidate the
        // witness took, not that something else lives there. When the kind admits it the
        // witness absorbs it; when it does not, the atoms stay and the collision stands,
        // which is a consumer demanding a domain the witness cannot be.
        //
        // Absorbing rather than resolving is what keeps the sum abstract: the close reads
        // the witness's kind, so a consumer of a `List(𝑉)` gives back a collection over the
        // witness, not over whichever domain happened to reach it.
        let witness = match (lhs.witness, rhs.witness) {
            (None, w) | (w, None) => w,
            // Two free witnesses at one position are **usually the same one**: a consumed
            // sum's witness is its own binder, so every route to that sum names it
            // identically and this arm is reflexive. Two *different* binders here is two
            // consumptions claiming one domain, which is the conflation identity
            // exists to catch — but this is not where it can be caught, since the
            // signature returns a merged value with no graph to fail into. Keeping the
            // left is the same convention the sigma slot uses; a real disagreement
            // surfaces where kinds are compared.
            (Some(a), Some(_)) => Some(a),
        };
        if let Some((_, kind)) = &witness
            && !atoms.is_empty()
        {
            let others: Vec<Type> = atoms.iter().map(AtomKey::to_type).collect();
            if crate::ccl::ty::TypeKind::Enumerated(others).contains_ground(kind) {
                atoms = BTreeSet::new();
            }
        }
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
            witness,
            atoms,
            kinds,
            rec,
            var,
            fun,
            sigma,
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
    /// Apply the cross-slot Σ law when exactly one side carries a sum and the other
    /// carries concrete non-sum content. `None` when the law does not apply — no sum, two
    /// sums (handled slot-against-slot), or a sum meeting a position that contributes
    /// nothing concrete, where the sum simply passes through.
    fn distribute_sigma(pol: bool, lhs: &CompactType, rhs: &CompactType) -> Option<CompactType> {
        let (sig_side, other) = match (&lhs.sigma, &rhs.sigma) {
            (Some(_), None) => (lhs, rhs),
            (None, Some(_)) => (rhs, lhs),
            _ => return None,
        };
        let o = other.occupied();
        if o.atoms == 0 && o.fun.is_none() && !o.others {
            return None;
        }
        // **A bare witness reference is not content.** `σ` *names* the position it stands
        // in — the sum's own domain, read inside the body that binds it — rather than
        // contributing a type to it. So `Σ ⋈ σ` is the sum, at either polarity: there is
        // nothing to distribute over.
        //
        // Every arm below reads `other` as a type `𝑇` with upper bounds of its own, which
        // a binder reference does not have. The dissolve arm in particular folds each
        // `𝐵[𝑑]` into the very position `σ` occupies, so the candidate and the reference
        // to it end up as two atoms in one bag — read later as two alternatives, and
        // reported as a domain conflict between a collection and its own witness. This is
        // the same reading [`KindOrder::Resolves`] already takes of a bare variable: a
        // name for a position is not a contribution to it.
        if is_bare_witness(other) {
            let (_, names) = split_content(other);
            return Some(Self::merge(pol, sig_side.clone(), names));
        }
        let sigma = sig_side.sigma.as_ref().expect("matched Some above");
        // Everything on the sum's side *except* its sum, so a position carrying both a
        // sum and other content keeps the other content.
        let rest = CompactType {
            sigma: None,
            ..sig_side.clone()
        };
        // Every arm below is the same rule read at a different shape — `𝐵[𝑑]` against
        // `𝑇`, for whichever `𝑑` the pairing determines. What differs is only *where*
        // the answer can be written down.

        // **`Σ ⊔ 𝑇` at a listing kind** — the one pairing that leaves the Σ world. With
        // no subtyping edge building a sum, nothing above `𝑇` is a sum, so every upper
        // bound of both is a non-sum, and consuming the sum puts it above every `𝐵[𝑑]`: the join is
        // `𝑇 ⊔ ⨆_𝑑 𝐵[𝑑]`. This is what collapses `box(xs) if c else xs` to `xs`'s type.
        if pol && let CompactWitnessKind::Enumerated(candidates) = &sigma.kind {
            let mut acc = Self::merge(pol, rest, other.clone());
            for c in candidates {
                acc = Self::merge(pol, acc, sigma.instantiate(c));
            }
            return Some(acc);
        }
        let (content, names) = split_content(other);
        // **`𝑇` names a domain the kind admits.** Then `𝑇` picks out the candidate, and
        // the pairing is the single instance `𝐵[𝑑_𝑇] ⋈ 𝑇` — no sum survives, because `𝑇`
        // *is* one of the candidates and the sum over a single candidate is that
        // candidate. This is the arm that monomorphizes a `List(𝑉)` parameter to the
        // concrete collection passed to it. Note it is a statement about the *kind*
        // admitting `𝑇`, not about `𝑇` being below the sum: no subtyping edge builds a
        // sum, which is what makes entering an abstract collection type require `box`.
        if let Some(named) = admitted_domain(&content, &sigma.kind) {
            let mut acc = Self::merge(pol, rest, Self::merge(pol, content, names));
            for d in named {
                acc = Self::merge(pol, acc, sigma.instantiate(&d));
            }
            return Some(acc);
        }
        // **The body *is* the witness.** `𝐵[𝑑] ⋈ 𝑇` is then `𝑑 ⋈ 𝑇`, so the whole
        // pairing lands on the binder and it is the **candidates** that move:
        // `Σ (w ∈ {𝑑ᵢ}). w ⋈ 𝑇 = Σ (w ∈ {𝑑ᵢ ⋈ 𝑇}). w`. Not a special case but the
        // general rule computed exactly — a one-body carrier can express a per-candidate
        // body only when the body either is the witness (here) or does not meet `𝑇` at
        // the witness's position (below).
        if sigma.body_is_witness()
            && let CompactWitnessKind::Enumerated(candidates) = &sigma.kind
        {
            return Some(Self::merge(
                pol,
                rest,
                CompactType {
                    // The **same sum**, with the pairing pushed onto its candidates.
                    sigma: Some(
                        sigma.rebuild(
                            CompactWitnessKind::enumerated(
                                candidates
                                    .iter()
                                    .map(|d| Self::merge(pol, d.clone(), content.clone()))
                                    .collect(),
                            ),
                            (*sigma.body).clone(),
                        ),
                    ),
                    ..names
                },
            ));
        }
        // **Otherwise the sum survives and `𝑇` strengthens its body.**
        //
        // - `Σ ⊓ 𝑇` — only a sum satisfies a sum demand, and a sum is below `𝑇` when it is
        //   consumed (`∀ 𝑑 ∈ 𝐾. 𝐵[𝑑] <: 𝑇`), so the greatest such sum keeps `𝐾` and
        //   strengthens the body. Nothing is enumerated, which is why a described kind
        //   needs no discharge of its own: a consumer's `?d ⤇ 𝑉` meeting a collection's
        //   `σ ⤇ 𝑉` is this merge, and it is what resolves `?d` *to* the witness.
        // - `Σ ⊔ 𝑇` at a described kind — the dissolved form needs candidates the kind
        //   does not name; the sum with `𝑇` joined into its body is what *is*
        //   expressible, and it is the least upper bound among sums.
        //
        // `other`'s variables stay at the outer position — they name where they were
        // written, and compaction has already folded their bounds into the content that
        // moves inward.
        Some(Self::merge(
            pol,
            rest,
            CompactType {
                // The same sum with a strengthened body.
                sigma: Some(sigma.rebuild(
                    sigma.kind.clone(),
                    Self::merge(pol, (*sigma.body).clone(), content),
                )),
                ..names
            },
        ))
    }

    fn merge_refinements(pol: bool, lhs: Vec<Refinement>, rhs: Vec<Refinement>) -> Vec<Refinement> {
        if pol {
            // The types are being unioned, so the refinements should be intersected.
            lhs.into_iter().filter(|r| rhs.contains(r)).collect()
        } else {
            // The types are being intersected, so the refinements should be unioned.
            let mut out = lhs;
            for r in rhs {
                if !out.contains(&r) {
                    out.push(r);
                }
            }
            out
        }
    }

    /// Merge two variant-tag maps. Variant width-sub is the **dual** of
    /// records: at positive polarity tags are *unioned* (a producer of
    /// `[A]` OR `[B]` could emit either), at negative polarity they are
    /// *intersected* (a consumer accepting `[A,B]` AND `[B,C]` only
    /// reliably handles `[B]`). Payload depth at matching tags is
    /// covariant — payloads recurse at the outer polarity `pol`, not
    /// flipped.
    fn merge_variants(
        pol: bool,
        lhs: BTreeMap<FieldKey, CompactType>,
        rhs: BTreeMap<FieldKey, CompactType>,
    ) -> BTreeMap<FieldKey, CompactType> {
        // Variants invert the set-op vs records (so `!pol` selects
        // intersect-vs-union) but keep payload polarity at the outer
        // `pol` (covariant depth, same as records).
        Self::merge_keyed(!pol, pol, lhs, rhs)
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
            ..Self::default()
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
    let mut st = CompactState {
        witness_scope: BTreeSet::new(),
        in_process: HashSet::new(),
        recursive: HashMap::new(),
        rec_vars: BTreeMap::new(),
    };
    let term = compact_go(ty, true, &Subst::id(), &BTreeSet::new(), &mut st);
    CompactGraph {
        term,
        rec_vars: st.rec_vars,
    }
}

/// Walk-wide state threaded through [`compact_go`]: the cycle-tracking tables.
/// (`parents` stays a per-path argument — it is scoped to one variable's bound
/// chain and reset across structural boundaries — and the substitution
/// accumulator composes per edge.)
struct CompactState {
    /// Witness binders bound by sums this compaction has descended through — what tells a
    /// bound [`Type::WitnessRef`] from a free one, since they are the same leaf.
    witness_scope: BTreeSet<crate::ccl::infer_var::WitnessBinderId>,
    /// Variables whose bounds are currently being walked, per polarity.
    in_process: HashSet<(InferVarId, bool)>,
    /// Placeholder ids minted for genuinely recursive revisits.
    recursive: HashMap<(InferVarId, bool), InferVarId>,
    /// Bounds of recursive variables (surfaced as `RecursiveType` errors by
    /// `coalesce_compact`).
    rec_vars: BTreeMap<InferVarId, CompactType>,
}

/// A witness [`TypeKind`] as a [`CompactWitnessKind`]: listed candidates decomposed into the
/// lattice, a description carried whole. The one conversion, so a kind reaching the
/// carrier as a Σ's witness and one reaching it as a *kinding constraint* on a free
/// witness become the same thing — which is what lets binding read either.
fn compact_kind(
    kind: &crate::ccl::ty::TypeKind,
    pol: bool,
    subst_acc: &Subst,
    st: &mut CompactState,
) -> CompactWitnessKind {
    match kind.listed() {
        Some(domains) => CompactWitnessKind::enumerated(
            domains
                .iter()
                .map(|d| compact_go(d, pol, subst_acc, &BTreeSet::new(), st))
                .collect(),
        ),
        // A described kind names no candidates to decompose into the lattice.
        None => CompactWitnessKind::described(kind.clone()),
    }
}

/// What a **free** witness ranges over, read from the range index.
///
/// Total, and deliberately loud when it is not: a witness exists because a consumed sum
/// named it, and naming it is what records the range. Defaulting to an empty listing would
/// be the worst available answer: `Σ 𝐷 ∈ {}. 𝐷` inhabits nothing, yet passes
/// [`TypeKind::needs_witness`] and is vacuously contained in every kind, so it propagates as
/// a plausible ⊥ instead of failing (see [`crate::ccl::ty::SigmaType::over`]).
fn witness_range(w: crate::ccl::infer_var::WitnessBinderId) -> crate::ccl::ty::TypeKind {
    crate::ccl::ty::witness_ctx::range(w).unwrap_or_else(|| {
        unreachable!("a free witness reached compaction with no recorded range: {w:?}")
    })
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
    parents: &BTreeSet<InferVarId>,
    st: &mut CompactState,
) -> CompactType {
    match ty {
        // Atomic types contribute a single atom. A term substitution never
        // touches an atom, so `subst_acc` is irrelevant here.
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn => CompactType::from_atom(AtomKey::from_type(ty).unwrap()),
        // **A witness reference lands in one of two places, and scope decides which.**
        //
        // Bound by a sum this compaction has descended through, it is an ordinary atom:
        // nullary, standing for one candidate without saying which, matching only itself
        // (see [`AtomKey::Witness`]). *Free* — named by a consumed sum and not yet bound —
        // it fills the witness slot instead, because materialization has to
        // read back what it ranges over in order to rebuild the sum.
        //
        // Asking scope is what lets both be one leaf. The range comes from the index
        // rather than from the occurrence, since an occurrence names a binder and the
        // binder is what has a range (`crate::ccl::ty::witness_ctx`).
        Type::WitnessRef(w) if st.witness_scope.contains(w) => {
            CompactType::from_atom(AtomKey::Witness(*w))
        }
        Type::WitnessRef(w) => CompactType {
            witness: Some((*w, witness_range(*w))),
            ..CompactType::default()
        },
        // Refinements ride the lattice as a refinement set: compact the underlying
        // type, then attach this layer's refinement. Walking a variable's bound
        // that is `Refinement(D, r)` therefore unions `r` into that variable's
        // compacted position — the propagation path. The accumulated
        // substitution is *forced* on the refinement: it rebuilds the predicate
        // with its free binders rewritten (e.g. discharging a dependent
        // application's argument) before the refinement lands in the position.
        // The predicate is an immutable term, so a non-vacuous force builds a
        // fresh predicate from the (freshened) bound's content directly.
        Type::Refinement(inner, r) => {
            let mut ct = compact_go(inner, pol, subst_acc, parents, st);
            let r = subst_acc.force_refinement(r);
            if !ct.refinements.contains(&r) {
                ct.refinements.push(r);
            }
            ct
        }
        // A bare `Hole` shouldn't reach the solver (emission turns it into a
        // fresh var), but treat it as no contribution for exhaustiveness.
        Type::Hole => CompactType::empty(),
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
            let dom = compact_go(d, !pol, subst_acc, &BTreeSet::new(), st);
            // A Pi binder shadows the accumulated substitution inside the
            // codomain (it binds the name locally), so restrict it there.
            let cod_acc = match name {
                Some(b) => subst_acc.shadow(b),
                None => subst_acc.clone(),
            };
            let cod = compact_go(c, pol, &cod_acc, &BTreeSet::new(), st);
            // **Binding the witness.** A *data* function whose domain is nothing but a
            // sum *is* that sum, carrying this function's codomain: the domain position is
            // where consuming a sum left the witness it named, and binding it here is what
            // that rule deferred.
            //
            // The `Data` guard is the whole justification. A **compute** function's
            // domain is an ordinary parameter type, and a collection parameter
            // (`λ (xs: List(𝑇)) → …`) is exactly a sum there — re-pairing it would
            // turn the function into its own argument. A **data** function's domain is
            // a *domain*: a range, a source, a candidate union. It is never a bare
            // sum, because a sum is a collection type and not a domain — so when one
            // appears there, a consumed sum put it there.
            //
            // Doing it *here* rather than at materialization is what makes the two
            // routes to one sum meet. A position can hold the sum directly (a
            // `List(𝑇)` annotation) *and* a consumer that named its witness (`sum(a)`
            // demanding `?d ⤇ Int`, with `?d`'s bound that sum) — the same type
            // reached two ways. Re-pairing during compaction puts both in the `fun`
            // slot, where [`CompactFun::merge`] reconciles them.
            if let Some((binder, kind, restriction)) = free_witness_kind(&dom, pol, subst_acc, st) {
                // The consumed sum carried the *producer's* element type; this function's
                // codomain is what the consumer produced from it, so the fiber is rebuilt
                // around the new codomain — in the same two shapes
                // [`TypeKind::into_data_fun`](crate::ccl::ty::TypeKind::into_data_fun)
                // builds, so a re-paired sum and a materialized one are one spelling.
                return CompactType {
                    // **Bound by the witness it binds.** The sum re-pairing forms is the
                    // one the consuming rule named.
                    sigma: Some(CompactSigma::closing(
                        binder,
                        restrict_candidates(&kind, &restriction),
                        CompactType {
                            fun: Some(CompactFun {
                                name: name.clone(),
                                kind: KindMerge::Data,
                                domain: Box::new(CompactType::from_atom(AtomKey::Witness(binder))),
                                codomain: Box::new(cod),
                            }),
                            ..CompactType::default()
                        },
                    )),
                    ..Default::default()
                };
            }
            CompactType {
                fun: Some(CompactFun {
                    name: name.clone(),
                    kind: KindMerge::of(kind),
                    domain: Box::new(dom),
                    codomain: Box::new(cod),
                }),
                ..Default::default()
            }
        }
        // Tuples and records share the structural `rec` representation,
        // keyed by `Index` and `Name` respectively.
        Type::Tuple(ts) => {
            let mut compacted = BTreeMap::new();
            for (i, v) in ts.iter().enumerate() {
                compacted.insert(
                    FieldKey::Index(i),
                    compact_go(v, pol, subst_acc, &BTreeSet::new(), st),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..Default::default()
            }
        }
        Type::Record(fs) => {
            let mut compacted = BTreeMap::new();
            for (n, v) in fs {
                compacted.insert(
                    FieldKey::Name(SmolStr::from(n.as_str())),
                    compact_go(v, pol, subst_acc, &BTreeSet::new(), st),
                );
            }
            CompactType {
                rec: Some(compacted),
                ..Default::default()
            }
        }
        Type::Variant(tags) => {
            // Variant payloads are covariant — recurse at the same
            // polarity (no flip, unlike Fun's domain). The merge rule
            // for variants flips records' polarity behaviour, but
            // payload depth is unaffected.
            let mut compacted = BTreeMap::new();
            for (k, v) in tags {
                compacted.insert(
                    k.clone(),
                    compact_go(v, pol, subst_acc, &BTreeSet::new(), st),
                );
            }
            CompactType {
                var: Some(compacted),
                ..Default::default()
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
            let value = compact_go(value, pol, subst_acc, &BTreeSet::new(), st);
            let domain = compact_go(domain, pol, subst_acc, &BTreeSet::new(), st);
            CompactType {
                history_slot: Some((Box::new(value), Box::new(domain), *kind)),
                ..Default::default()
            }
        }
        // A Σ is a type constructor, so it takes a slot of its own with its own
        // polarity-dual merge law, exactly as `rec`, `var` and `fun` do
        // (`src/ccl/design/type-inference.md`, "How a sum flows through the solver").
        // Both shapes of body go there: the witness kind and the body are independent
        // positions, and the body is compacted whole — its [`Type::WitnessRef`]
        // occurrences becoming witness atoms — so nothing about it needs to be an arrow.
        Type::Sigma(s) => {
            // The kind is **covariant**: Σ-width asks `∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁`, so a bigger
            // kind is a supertype and the candidates sit at the enclosing polarity.
            // Coalesce re-forms the identical Σ, so a sum re-entering compaction — a
            // generalized binding's scheme freshened at a use site — round-trips.
            let kind = compact_kind(s.kind(), pol, subst_acc, st);
            CompactType {
                // The sum entering the carrier keeps its binder, so materializing it
                // again yields the same type rather than an α-variant of it.
                sigma: Some(CompactSigma::closing(s.binder(), kind, {
                    // The body is under this sum's binder: an occurrence of it there is
                    // bound, and only occurrences of *other* binders are still free.
                    let fresh = st.witness_scope.insert(s.binder());
                    let body = compact_go(&s.body, pol, subst_acc, &BTreeSet::new(), st);
                    if fresh {
                        st.witness_scope.remove(&s.binder());
                    }
                    body
                })),
                ..CompactType::default()
            }
        }
        Type::Infer(state) => {
            let uid = state.uid;
            let key = (uid, pol);
            if st.in_process.contains(&key) {
                if parents.contains(&uid) {
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
            let primary = if pol { &s.lower } else { &s.upper };
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
            let primary_bounds = primary.clone();
            let opposite_bounds = if pol {
                s.upper.clone()
            } else {
                s.lower.clone()
            };
            let kinds = s.kinds.clone();
            drop(s);
            // Walk bounds, transitively expanding. We fold the bounds'
            // contributions *without* seeding from the variable's own identity
            // (`CompactType::from_var(uid)`) and inject the var id only at the
            // end. Seeding with `from_var` would mix the variable's *empty*
            // refinement set into the merge, and at positive polarity `merge`
            // *intersects* refinement sets (`merge_refinements`) — so the empty
            // seed would intersect away every bound's refinements (∅ is absorbing under
            // intersection). The variable identity must be refinement-*neutral*;
            // `rec`/`var`/`fun` get this for free from their `None` merge
            // identity, but refinement sets have no such sentinel, so we keep
            // the var out of the structural fold.
            let mut new_parents = parents.clone();
            new_parents.insert(uid);
            let mut bound: Option<CompactType> = None;
            for b in &primary_bounds {
                // Compose this edge's morphisms onto the accumulator before
                // descending: a bound reached transitively through `v → w → …`
                // arrives with every edge's morphism composed (design §3.6).
                // Identity edges leave `subst_acc` unchanged (the common case).
                let inner_acc = Subst::then(&b.render_subst(), subst_acc);
                let bc = compact_go(&b.ty, pol, &inner_acc, &new_parents, st);
                bound = Some(match bound {
                    None => bc,
                    Some(acc) => CompactType::merge(pol, acc, bc),
                });
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
            // an `IncompatibleBounds` error). See the rationale above.
            let no_concrete = bound.as_ref().is_none_or(|b| {
                b.atoms.is_empty() && b.rec.is_none() && b.fun.is_none() && b.history_slot.is_none()
            });
            if no_concrete {
                for b in &opposite_bounds {
                    let inner_acc = Subst::then(&b.render_subst(), subst_acc);
                    let bc = compact_go(&b.ty, !pol, &inner_acc, &new_parents, st);
                    bound = Some(match bound {
                        None => bc,
                        Some(acc) => CompactType::merge(!pol, acc, bc),
                    });
                }
            }
            // Inject the variable's own identity (refinement-neutral) so it
            // shows up in the CompactType — equivalent to the old `from_var`
            // seed for `vars`, but without polluting the refinement merge.
            let mut bound = bound.unwrap_or_else(CompactType::empty);
            bound.vars.insert(uid);
            // The variable's kinding constraints join its identity: they are facts
            // about what this position resolves to, and coalesce reads them there.
            for k in kinds {
                if !bound.kinds.contains(&k) {
                    bound.kinds.push(k);
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
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let int_b = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("B")), CompactType::default())]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(true, int_a, int_b);
        let var = merged.var.expect("variant present");
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
    }

    /// Compact merge at negative polarity intersects tags.
    #[test]
    fn compact_merge_variants_negative_intersects() {
        let int_ab = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("A")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let int_bc = CompactType {
            var: Some(
                [
                    (FieldKey::Name(SmolStr::from("B")), CompactType::default()),
                    (FieldKey::Name(SmolStr::from("C")), CompactType::default()),
                ]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        };
        let merged = CompactType::merge(false, int_ab, int_bc);
        let var = merged.var.expect("variant present");
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("A"))));
        assert!(var.contains_key(&FieldKey::Name(SmolStr::from("B"))));
        assert!(!var.contains_key(&FieldKey::Name(SmolStr::from("C"))));
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
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_a)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        let rhs = CompactType {
            var: Some(
                [(FieldKey::Name(SmolStr::from("A")), payload_b)]
                    .into_iter()
                    .collect(),
            ),
            ..Default::default()
        };
        // Outer positive variant merge: tags union (one tag A here).
        // Payload depth covariant → payload merges at pos → record
        // fields intersect → empty rec map (no field in both).
        let merged = CompactType::merge(true, lhs, rhs);
        let var = merged.var.expect("variant present");
        let payload = var.get(&FieldKey::Name(SmolStr::from("A"))).expect("tag A");
        let rec = payload.rec.as_ref().expect("payload rec present");
        assert!(
            rec.is_empty(),
            "positive payload merge intersects fields; got {rec:?}"
        );
    }
}

/// The compact witness substitution `𝐵[𝑑]` and the α-rename beside it — both matching by
/// binder identity, so the scoping is a consequence rather than a rule the walk encodes.
#[cfg(test)]
mod compact_witness_subst_tests {
    use super::*;

    fn witness(b: crate::ccl::infer_var::WitnessBinderId) -> CompactType {
        CompactType::from_atom(AtomKey::Witness(b))
    }

    fn binder() -> crate::ccl::infer_var::WitnessBinderId {
        crate::ccl::infer_var::fresh_witness_binder_id()
    }

    fn int() -> CompactType {
        CompactType::from_atom(AtomKey::Prim(BaseType::Int))
    }

    /// A bare witness body instantiates to the candidate itself — the `box` shape.
    #[test]
    fn a_bare_witness_body_instantiates_to_the_candidate() {
        let b = binder();
        let sigma = CompactSigma {
            binder: b,
            kind: CompactWitnessKind::Enumerated(vec![int()]),
            body: Box::new(witness(b)),
        };
        assert!(sigma.body_is_witness());
        assert_eq!(sigma.instantiate(&int()), int());
    }

    /// A collection body `σ ⤇ 𝑉` instantiates to `𝑑 ⤇ 𝑉`: the witness sits in the body's
    /// domain, so substitution reaches it without the slot destructuring the arrow.
    #[test]
    fn a_collection_body_instantiates_its_domain() {
        let b = binder();
        let sigma = CompactSigma {
            binder: b,
            kind: CompactWitnessKind::described(crate::ccl::ty::TypeKind::UIntRanges),
            body: Box::new(CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domain: Box::new(witness(b)),
                    codomain: Box::new(int()),
                }),
                ..CompactType::default()
            }),
        };
        assert!(!sigma.body_is_witness());
        let range = CompactType::from_atom(AtomKey::UIntRange(3));
        assert_eq!(*sigma.instantiate(&range).fun.unwrap().domain, range);
    }

    /// An occurrence belonging to an **inner** binder is left alone when the outer one is
    /// substituted — by naming a different binder, not by the walk declining to look.
    #[test]
    fn substitution_leaves_an_inner_binders_occurrence_alone() {
        let (outer, inner_b) = (binder(), binder());
        let inner = CompactType {
            sigma: Some(CompactSigma {
                binder: inner_b,
                kind: CompactWitnessKind::Enumerated(vec![int()]),
                body: Box::new(witness(inner_b)),
            }),
            ..CompactType::default()
        };
        assert_eq!(subst_witness(&inner, outer, &int()), inner);
    }

    /// Two sums built independently name their binders differently; the α-rename is what
    /// lets their bodies merge as one sum rather than collide as two witnesses.
    #[test]
    fn the_rename_carries_a_body_onto_another_sums_binder() {
        let (from, to) = (binder(), binder());
        let body = CompactType {
            fun: Some(CompactFun {
                name: None,
                kind: KindMerge::Data,
                domain: Box::new(witness(from)),
                codomain: Box::new(int()),
            }),
            ..CompactType::default()
        };
        let renamed = rename_witness(&body, from, to);
        assert_eq!(*renamed.fun.unwrap().domain, witness(to));
    }

    /// A sum that **rebinds** the name shadows it, so the rename stops at its body — the
    /// one place scoping is positional, because shadowing is about nesting.
    #[test]
    fn the_rename_stops_at_a_shadowing_binder() {
        let (from, to) = (binder(), binder());
        let shadowed = CompactType {
            sigma: Some(CompactSigma {
                binder: from,
                kind: CompactWitnessKind::Enumerated(vec![int()]),
                body: Box::new(witness(from)),
            }),
            ..CompactType::default()
        };
        assert_eq!(rename_witness(&shadowed, from, to), shadowed);
    }

    /// A nested sum's **kind** is written in the outer scope, so an outer occurrence among
    /// its candidates is reached — the half a positional rule is likeliest to lose.
    #[test]
    fn substitution_reaches_an_outer_occurrence_in_a_nested_sums_kind() {
        let outer = binder();
        let nested = CompactType {
            sigma: Some(CompactSigma {
                binder: binder(),
                kind: CompactWitnessKind::Enumerated(vec![witness(outer)]),
                body: Box::new(int()),
            }),
            ..CompactType::default()
        };
        let CompactWitnessKind::Enumerated(kind) =
            subst_witness(&nested, outer, &int()).sigma.unwrap().kind
        else {
            panic!("expected a listed kind");
        };
        assert_eq!(kind, vec![int()]);
    }
}

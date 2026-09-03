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
pub use crate::ccl::ty::KindPin;

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
    ///
    /// Carries the **binder**, whose kind can reach a `RefCell` — an undecided candidate is
    /// an ordinary inference variable, whose bounds are a cell — hence
    /// the `mutable_key_type` allows on the sets these atoms key. Ordering and equality
    /// read the binder id alone (`impl Ord for Witness`), which no write touches, so a
    /// key's position in a set is fixed at insertion.
    Witness(crate::ccl::ty::WitnessId),
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

/// [`TypeKind`](crate::ccl::ty::TypeKind) with its types compacted — the same classifier,
/// carried through the lattice.
///
/// Variant for variant with `TypeKind`, `CompactType` standing where `Type` does. The one
/// thing that differs is what the types inside are: a kind's parameters and candidates are
/// positions like any other, so they compact and merge like any other, rather than riding
/// through as written.
///
/// Not an identity between domains and kinds: a domain is a *type*, and a kind *classifies*
/// types.
#[derive(Debug, Clone, PartialEq)]
pub enum CompactTypeKind {
    /// A finite listing of candidate domains, compacted and deduplicated by structural
    /// [`CompactType`] equality. One candidate is an ordinary collection; two or more is a
    /// conditional collection.
    Enumerated(Vec<CompactType>),
    /// Every domain below a type — a `Map`'s key bound. The parameter compacts, which is
    /// what lets an unannotated key be determined by the domains that reach it.
    SubtypesOf(Box<CompactType>),
    /// Every `UIntRange` — a `List`'s domain kind. Lists no candidates and takes no
    /// parameter, so there is nothing under it to compact.
    UIntRanges,
    /// Every domain — the top of the kind order, what a `Collection` is summed over.
    Type,
}

impl CompactTypeKind {
    /// The kind a position ranges over when two contributions meet there.
    ///
    /// **A listing answers a description.** A description states a property every candidate
    /// has (`UIntRanges`, `Type`, a bound); a listing names the candidates themselves, so
    /// where both reach a position the listing is what it ranges over and the description is
    /// already discharged by it. Two listings *union*: a conditional's arms are alternatives,
    /// and the position is over whichever the program picked.
    fn merge(pol: bool, a: CompactTypeKind, b: CompactTypeKind) -> CompactTypeKind {
        use CompactTypeKind::{Enumerated, SubtypesOf, Type as AnyType, UIntRanges};
        match (a, b) {
            (Enumerated(mut xs), Enumerated(ys)) => {
                for y in ys {
                    if !xs.contains(&y) {
                        xs.push(y);
                    }
                }
                Enumerated(xs)
            }
            (Enumerated(xs), _) | (_, Enumerated(xs)) => Enumerated(xs),
            (SubtypesOf(x), SubtypesOf(y)) => SubtypesOf(Box::new(CompactType::merge(pol, *x, *y))),
            // `Type` is the top of the kind order, so it imposes nothing on the other side.
            (AnyType, other) | (other, AnyType) => other,
            (SubtypesOf(x), UIntRanges) | (UIntRanges, SubtypesOf(x)) => SubtypesOf(x),
            (UIntRanges, UIntRanges) => UIntRanges,
        }
    }
}

/// A binder as compaction carries it: **which** binder, and what it ranges over with the
/// kind's children in the lattice.
///
/// The children are the reason this is not a [`Witness`](crate::ccl::ty::Witness). A
/// listing's candidates and a bound's parameter are ordinary types the solver resolves, so
/// they compact at the position that reached them and materialize with everything else; a
/// `Witness` would carry them as raw `Type`s straight through to the output.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactWitness {
    /// Which binder this is — the whole of its identity.
    pub id: crate::ccl::ty::WitnessId,
    /// What it ranges over.
    pub type_kind: CompactTypeKind,
}

/// A merged function shape — the **single** carrier for every function-shaped type,
/// plain function and dependent sum alike. What distinguishes them is the
/// [`CompactTypeKind`], so both reach one position through one slot and
/// [`CompactFun::merge`] reconciles them; there is no second route for a sum.
#[derive(Debug, Clone, PartialEq)]
pub struct CompactFun {
    /// The Pi (element) binder, `na.or(nb)` on merge.
    pub name: Option<Name>,
    /// The merged kind — **compute or data, and nothing else**. What a data function is
    /// indexed by lives in [`binders`](Self::binders), where it is merged rather than
    /// snapshotted.
    pub kind: KindPin,
    /// The binders this function is over, outermost first — what its kind states, carried so
    /// materialization can close the sum without asking the kind graph again.
    ///
    /// The *identity* at a position is settled before a merge sees it — the kind edge that
    /// related two sides put their binders in correspondence — so a merge reconciles only
    /// what each side says the position ranges over.
    pub binders: Vec<CompactWitness>,
    /// The two **domains** had no common answer.
    ///
    /// Not a kind, which is why it is not in the kind: a domain disagreement says the arms
    /// are over different data and wants "box these arms", where a kind collision says
    /// "this is a function, not a collection". Carried beside the kind so neither
    /// diagnostic has to be recovered from the shape of the other.
    pub domains_disagree: bool,
    /// The domain — **one** domain, compacted like any other position.
    ///
    /// Exactly one, and coalesce asserts it. Nothing puts a candidate *set* here:
    /// entering a sum is a term, so a join never forms a conditional collection out of
    /// two ordinary collections, and a consumed sum *names* its witness rather than
    /// putting a sum where a domain belongs. A candidate set lives one level up, on the
    /// witness a Σ binds ([`CompactWitness::type_kind`]).
    pub domain: Box<CompactType>,
    /// The two domains a merge had to **combine** into this one, where it had to.
    ///
    /// The single domain position cannot say afterwards that it was assembled from two:
    /// the contravariant meet unions a record's fields and a position's refinements, so
    /// `{a}` and `{b}` leave as `{a, b}` and look exactly like one domain reached twice.
    /// Whether that combination is legal depends on the slot's kind, which a merge may not
    /// know yet — an unpinned kind can still become either — so the pair is recorded here
    /// and the rule applied once, where the kind is resolved
    /// (`design/type-inference.md`, "Data domains are invariant").
    ///
    /// The operands rather than a flag, because the diagnostic names them: the merged
    /// position is neither of the domains the program wrote, so reporting it says a
    /// collection conflicts over a domain that appears nowhere in the source. Boxed —
    /// every function slot carries this and almost none of them fill it.
    pub combined: Option<CombinedDomains>,
    /// The codomain (covariant).
    pub codomain: Box<CompactType>,
}

/// The two domains a merge had to combine — an **unordered** pair.
///
/// Unordered because `CompactFun` derives `PartialEq` and a merged slot's identity must not
/// depend on which bound arrived first: the same two domains met in either order are one
/// merge. That is the argument `RefinementSet`'s equality rests on, and the reason a bare
/// tuple will not do here. Boxed: every function slot carries the `Option` and almost none
/// of them fill it.
#[derive(Debug, Clone)]
pub struct CombinedDomains(Box<(CompactType, CompactType)>);

impl CombinedDomains {
    fn new(a: CompactType, b: CompactType) -> Self {
        CombinedDomains(Box::new((a, b)))
    }

    /// The two domains, in the order they were met — a rendering order, never an identity.
    pub(super) fn pair(&self) -> (&CompactType, &CompactType) {
        (&self.0.0, &self.0.1)
    }

    /// Both domains rewritten by `f` — for a pass that rebuilds the slot and must carry
    /// them across. Dropping them there is silent: the merged position survives and reads
    /// as one domain, so the diagnostic loses a side rather than failing.
    pub(super) fn map(self, mut f: impl FnMut(CompactType) -> CompactType) -> Self {
        let (a, b) = *self.0;
        CombinedDomains::new(f(a), f(b))
    }
}

impl PartialEq for CombinedDomains {
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = self.pair();
        let (c, d) = other.pair();
        (a == c && b == d) || (a == d && b == c)
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
            atoms,
            rec,
            var,
            fun,
            refinements,
            history_slot,
        } = self;
        Occupied {
            atoms: atoms.len(),
            fun: fun.as_ref(),
            others: rec.is_some()
                || var.is_some()
                || refinements.as_ref().is_some_and(|r| !r.is_empty())
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
/// function's kind, which only the caller knows.
///
/// `None` when the position denotes no domain set at all: its concrete content must
/// be nothing but atoms, since anything alongside them (a record, a nested function, a
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
    // A witness atom denotes no domain *set*: it is one domain, the one the witness
    // picked, and which one is not settled here. Same reading as a bare variable —
    // naming a position is not filling it.
    let bare_atoms = o.atoms >= 1
        && o.fun.is_none()
        && !o.others
        && !ct.atoms.iter().any(|a| matches!(a, AtomKey::Witness(_)));
    bare_atoms.then(|| ct.atoms.iter().map(|a| a.to_type()).collect())
}

/// Whether these **types** denote more than one domain — the [`denotes_several_domains`]
/// reading, applied after a merge has put both sides in one position.
/// Whether a contravariant meet of two **data** domains had to combine anything — which is
/// two domains meeting, not one domain reached twice.
///
/// Read on the inputs, because the meet erases the evidence: it unions a record's fields and
/// a position's refinements, so `{a}` and `{b}` leave as the single domain `{a, b}` and the
/// merged position no longer says they disagreed. A domain is the data and data domains are
/// invariant, so combining is exactly the narrowing the representation exists to refuse.
///
/// A position that **names** rather than fills — a bare variable, a witness reference — is
/// not a domain to disagree with: consuming a sum is what resolves it, and
/// [`denoted_domains`] excludes witness atoms for the same reason.
fn data_domains_disagree(a: &CompactType, b: &CompactType) -> bool {
    let names_only = |ct: &CompactType| {
        let o = ct.occupied();
        (o.atoms == 0 && o.fun.is_none() && !o.others)
            || ct.atoms.iter().any(|x| matches!(x, AtomKey::Witness(_)))
    };
    if names_only(a) || names_only(b) {
        return false;
    }
    let keys = |ct: &CompactType| {
        ct.rec
            .as_ref()
            .map(|r| r.keys().cloned().collect::<Vec<_>>())
    };
    a.refinements != b.refinements || a.atoms != b.atoms || keys(a) != keys(b)
}

fn denotes_several_domains_ty(ds: &[Type]) -> bool {
    let mut seen: Vec<&Type> = Vec::new();
    for d in ds {
        if !seen.contains(&d) {
            seen.push(d);
        }
    }
    seen.len() > 1
}

/// The binders a **position** is over, from the kind of the variable it stands at.
///
/// A join of collections is over its own index, not over either arm's: the variable holds
/// both below its kind, so the kind's arity is what they agree on and its positions are what
/// each arm's binder corresponds to. The lowest-numbered variable answers, so the position
/// gives one answer however many variables were merged into it.
///
/// Identity only. What the position ranges over is the merge of what reached it
/// ([`merge_binders`]), which is a lattice operation and not a question for the kind graph.
fn position_binders(vars: &BTreeSet<InferVarId>) -> Option<Vec<crate::ccl::ty::WitnessId>> {
    let v = vars.iter().min().and_then(crate::ccl::infer_var::lookup)?;
    let binders = v.fun_kind.binders();
    (!binders.is_empty()).then(|| binders.iter().map(|w| *w.id()).collect())
}

/// The binders of a merged position: the position's own identity, over the merge of what
/// each side said it ranges over.
///
/// Position `i` against position `i`, because that is what a kind edge relates. A side with
/// no binders is a plain collection meeting a sum and contributes nothing to range over.
fn merge_binders(
    pol: bool,
    a: &[CompactWitness],
    b: &[CompactWitness],
    position: Option<Vec<crate::ccl::ty::WitnessId>>,
) -> Vec<CompactWitness> {
    let (longer, shorter) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    longer
        .iter()
        .enumerate()
        .map(|(i, w)| CompactWitness {
            id: position
                .as_ref()
                .and_then(|p| p.get(i))
                .cloned()
                .unwrap_or(w.id),
            type_kind: match shorter.get(i) {
                Some(other) => {
                    CompactTypeKind::merge(pol, w.type_kind.clone(), other.type_kind.clone())
                }
                None => w.type_kind.clone(),
            },
        })
        .collect()
}

impl CompactFun {
    /// Merge two function slots. `pol` is the *outer* polarity; the domain merges
    /// contravariantly (at `!pol`), the codomain covariantly (at `pol`).
    fn merge(
        pol: bool,
        a: CompactFun,
        b: CompactFun,
        position: Option<Vec<crate::ccl::ty::WitnessId>>,
    ) -> CompactFun {
        let name = a.name.clone().or_else(|| b.name.clone());
        let codomain = Box::new(CompactType::merge(pol, *a.codomain, *b.codomain));
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
        // **A data domain's refinements are part of it**, and the guard below cannot see
        // them, because it reads the position *after* the merge: a contravariant meet unions
        // refinements, so `{𝑑 | 𝑝}` and `𝑑` arrive as two domains and leave as one. Distinct
        // *shapes* survive the meet and are counted; a distinct refinement is resolved by it,
        // and the join then denotes a collection filtered by a predicate only one side owed.
        //
        // Compared on the inputs for that reason. Their refinement lists are compared rather
        // than the whole positions, which would demand representational identity the meet
        // exists to smooth over — variable ids and slot order among them.
        // Recorded whatever the kind is, because an unpinned one can still become `Data`
        // and the meet has already erased the evidence by the time it does. An earlier
        // combination outranks this one: it is the pair that first had no common answer.
        let combined = a
            .combined
            .clone()
            .or_else(|| b.combined.clone())
            .or_else(|| {
                data_domains_disagree(&a.domain, &b.domain)
                    .then(|| CombinedDomains::new((*a.domain).clone(), (*b.domain).clone()))
            });
        let kind = a.kind.clone().join(b.kind.clone());
        // **The binders belong to the position, not to either side.** Two collections
        // meeting here are a *join*, and what the join is over is the kind of the variable
        // they met at — which holds both of them below it, so its binders are one per index
        // and correspond to each side's. Taking one side's instead would answer with
        // whichever arm happened to arrive first.
        //
        // A position with no variable is one type reached once: it keeps its own.
        let binders = merge_binders(pol, &a.binders, &b.binders, position);
        // A domain disagreement is a fact about the **domains**, so it is recorded beside
        // the kind rather than inside it: the kind still says what the function is, and the
        // flag says the arms are over data that has no common answer.
        let domains_disagree = a.domains_disagree
            || b.domains_disagree
            || (kind.is_data()
                && (combined.is_some()
                    || denoted_domains(&domain).is_some_and(|ds| denotes_several_domains_ty(&ds))));
        CompactFun {
            name,
            kind,
            binders,
            domains_disagree,
            domain,
            combined,
            codomain,
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
    /// Arrow shape, if any: see [`CompactFun`]. Carries the Pi binder, the merged
    /// [`KindPin`], the [`CompactTypeKind`], and the codomain. Recursively merged
    /// with polarity flip on the domain. Plain functions *and* dependent sums both
    /// live here — one slot, so the two ways a sum reaches a position (directly, and
    /// as the domain a consumed sum named) merge instead of colliding.
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

    /// [`CompactType::merge`], reachable from the integration tests.
    ///
    /// The merge is `pub(super)` because it is the bound fold's step and nothing
    /// outside the solver has a bound list to fold; `tests/differential_oracle.rs`
    /// folds one anyway, to diff each step against the model's `merge`. The
    /// feature gate adds this door rather than widening the merge's own
    /// visibility, so the production configuration is the ungated one.
    #[cfg(any(test, feature = "test-helpers"))]
    pub fn merge_bounds(pol: bool, lhs: CompactType, rhs: CompactType) -> CompactType {
        Self::merge(pol, lhs, rhs)
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
        if lhs.imposes_nothing() {
            return rhs.absorbing_vars_of(lhs);
        }
        if rhs.imposes_nothing() {
            return lhs.absorbing_vars_of(rhs);
        }
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
        // a function-bodied one needs `𝐵[𝑑]` at the compact level, which arrives with the
        // migration off the `fun` slot.
        let mut vars = lhs.vars;
        vars.extend(rhs.vars);
        #[allow(clippy::mutable_key_type)]
        // `AtomKey::Witness` holds a `RefCell` kind; ordering reads its `uid` alone.
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
            (Some(a), Some(b)) => Some(CompactFun::merge(pol, a, b, position_binders(&vars))),
        };
        let refinements = match (lhs.refinements, rhs.refinements) {
            // `None` is the identity, exactly as for the shape slots above.
            (None, r) | (r, None) => r,
            (Some(a), Some(b)) => Some(Self::merge_refinements(pol, a, b)),
        };
        // Conjunction at both polarities: the position must satisfy every kinding
        // constraint of every variable that determines it. Deduplicated so a variable
        // reached twice through the bound graph does not grow the list.
        let mut kinds = lhs.kinds;
        for k in rhs.kinds {
            if !kinds.contains(&k) {
                kinds.push(k);
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
            atoms,
            kinds,
            rec,
            var,
            fun,
            refinements,
            history_slot,
        }
    }

    /// Whether this contribution says nothing about the position at all — an
    /// unresolved variable and nothing else.
    ///
    /// Every component's `None` already acts as its own merge identity, so the
    /// per-slot merges pass an empty contribution through unchanged; this
    /// whole-contribution test exists for the cross-slot Σ laws, which must not
    /// fire against a side that says nothing.
    ///
    /// The variables themselves are still carried across by
    /// [`absorbing_vars_of`](Self::absorbing_vars_of); they are this
    /// contribution's only content, and they join at every polarity.
    fn imposes_nothing(&self) -> bool {
        let CompactType {
            vars: _,
            atoms,
            rec,
            var,
            fun,
            refinements,
            history_slot,
            kinds,
        } = self;
        atoms.is_empty()
            && rec.is_none()
            && var.is_none()
            && fun.is_none()
            && refinements.is_none()
            && history_slot.is_none()
            && kinds.is_empty()
    }

    /// Take the variable identities of a contribution that
    /// [`imposes_nothing`](Self::imposes_nothing), leaving everything else as-is.
    fn absorbing_vars_of(mut self, identity: CompactType) -> CompactType {
        self.vars.extend(identity.vars);
        self
    }
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
        #[allow(clippy::mutable_key_type)]
        // `AtomKey::Witness` holds a `RefCell` kind; ordering reads its `uid` alone.
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
    debug_assert!(
        refinement_slot_present(&term) && st.rec_vars.values().all(refinement_slot_present),
        "a position carrying content must carry a refinement slot: only a hole and a \
         bare variable leave it absent"
    );
    CompactGraph {
        term,
        rec_vars: st.rec_vars,
    }
}

/// Whether every position in `ct` that carries content also carries a refinement
/// slot — the post-condition of the walk above.
///
/// The slot's `None` belongs to exactly the two contributions that are not
/// values, a hole ([`CompactType::empty`]) and a bare variable
/// ([`CompactType::from_var`]), and neither carries content. Nothing in the type
/// system says so: every value-shaped arm has to be built from
/// [`CompactType::value`], across a dozen construction sites. A position that
/// carried content with the slot absent would read as the merge identity and so
/// *absorb* a sibling bound's refinements instead of intersecting with none of its
/// own, which is the collapse [`CompactType::refinements`] documents — `Int`
/// joined with `{Int | p}` would keep `p`.
///
/// Variable contributions are not content: a bare variable's whole content is
/// its identity, so `vars` is the one populated field the slot may accompany as
/// `None`.
fn refinement_slot_present(ct: &CompactType) -> bool {
    let carries_content = !ct.atoms.is_empty()
        || ct.rec.is_some()
        || ct.var.is_some()
        || ct.fun.is_some()
        || ct.history_slot.is_some();
    if carries_content && ct.refinements.is_none() {
        return false;
    }
    ct.rec
        .iter()
        .flat_map(|m| m.values())
        .all(refinement_slot_present)
        && ct
            .var
            .iter()
            .flat_map(|v| v.tags.values())
            .all(refinement_slot_present)
        && ct
            .fun
            .iter()
            .all(|f| refinement_slot_present(&f.domain) && refinement_slot_present(&f.codomain))
        && ct.history_slot.iter().all(|(value, domain, _)| {
            refinement_slot_present(value) && refinement_slot_present(domain)
        })
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

/// Whether any refinement in this position's own set references `binder` by *name*.
///
/// The negation is the compaction boundary's form of **landing closes**: a refinement
/// referencing its function's binder has that reference converted to an index
/// (`Name::PiBound`) when it lands, so the function's spelling carries no refinement
/// identity afterwards. Two consequences rest on it — `CompactFun::merge` may keep
/// either side's binder name (`a.name.or(b.name)`) without changing what the merged
/// refinements mean, and `coalesce_compact_go` can decide whether to keep the binder from
/// the codomain alone. A refinement referencing some *other* free name is unaffected and
/// stays free; only the function's own binder is at stake.
///
/// Not recursive: a nested function rebinding the same spelling is a different
/// binder, and its refinements land against it instead.
fn refinements_name_binder(ct: &CompactType, binder: &Name) -> bool {
    // `count_free` is the shared free-occurrence walk: it covers every node kind,
    // and it respects shadowing. Both matter. A reference reached through an
    // `Apply`, a `Proj`, or a `Cast` is the common shape (`__elem.a == x` is a
    // `BinOp` over an `Apply` of a `Proj`), so a walk naming the kinds it
    // descends under-approximates and this assertion passes vacuously wherever
    // it is wrong. And a predicate that binds the same spelling itself — a
    // filter's `λ x → …` under a function whose Pi binder is also `x` — holds no
    // *free* reference to the binder, which is what the invariant is about.
    ct.refinements.as_ref().is_some_and(|set| {
        set.iter()
            .any(|r| crate::ccl::ccl_utils::count_free(binder, &r.predicate) > 0)
    })
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

/// A witness [`TypeKind`] as a [`CompactTypeKind`]: listed candidates decomposed into the
/// lattice, a description carried whole. The one conversion, so a kind reaching the
/// carrier as a Σ's witness and one reaching it as a *kinding constraint* on a free
/// witness become the same thing — which is what lets binding read either.
fn compact_type_kind(
    type_kind: &crate::ccl::ty::TypeKind,
    pol: bool,
    subst_acc: &Subst,
    st: &mut CompactState,
) -> CompactTypeKind {
    use crate::ccl::ty::TypeKind;
    // Variant for variant: every type a kind carries — a listing's candidates, a bound's
    // parameter — is a position, so it compacts like one. A kind that carries no type has
    // nothing to decompose and crosses as itself.
    match type_kind {
        TypeKind::Enumerated(domains) => CompactTypeKind::Enumerated(
            domains
                .iter()
                .map(|d| compact_go(d, pol, subst_acc, None, st))
                .collect(),
        ),
        TypeKind::SubtypesOf(k) => {
            CompactTypeKind::SubtypesOf(Box::new(compact_go(k, pol, subst_acc, None, st)))
        }
        TypeKind::UIntRanges => CompactTypeKind::UIntRanges,
        TypeKind::Type => CompactTypeKind::Type,
    }
}

/// `acc` extended with the **binder correspondence** this kind states.
///
/// A kind variable's binders are the positions on it, and everything recorded below it is a
/// collection whose binders correspond to those positions one for one. So a reference to an
/// arm's binder, reaching a consumer, denotes the consumer's — and the map that says so is
/// derivable here and nowhere earlier: it needs an arity, and an arity is what the bounds
/// answer once the kind graph is closed.
///
/// Composed into the accumulated substitution exactly as a Pi binder's rename is, so every
/// bound the walk records below this function is already spelled in this kind's binders.
/// Every kind variable's binder correspondence, one per line. Diagnostic only — the
/// substitution half of [`crate::ccl::ty::dump_kind_vars`], which shows only the edges.
#[cfg(debug_assertions)]
pub fn dump_kind_correspondences() -> String {
    let mut out = String::new();
    for v in crate::ccl::ty::fun_kind_vars() {
        let kind = crate::ccl::ty::FunKind::Var(Rc::clone(&v));
        let corr = fun_kind_correspondence(&kind, &Subst::id());
        if corr.is_id() {
            continue;
        }
        out.push_str(&format!("k{}: {}\n", v.uid.0, corr.render_witnesses()));
    }
    out
}

fn fun_kind_correspondence(fun_kind: &crate::ccl::ty::FunKind, acc: &Subst) -> Subst {
    let crate::ccl::ty::FunKind::Var(k) = fun_kind else {
        return acc.clone();
    };
    let Some(arity) = k.arity() else {
        return acc.clone();
    };
    // Built on its own and **composed** onto the accumulator, not inserted into it: a
    // reference already renamed by an outer hop has to be carried on by this one. Inserting
    // leaves the outer entry pointing at a name this hop has since moved, so a chain
    // resolves to its first hop and the walk answers with an intermediate spelling.
    let mut hop = Subst::id();
    // A **bound** relates two spellings of one collection, so position *i* is position *i*;
    // a **source** contributes its positions to a stretch of this kind's, so the offset
    // walks. Both at any depth: a binder corresponds to this kind's whether it reached it
    // directly or through another variable, and only the ends of such a chain are ever
    // spelled in a type — the middle is a kind nothing writes.
    // This kind's own binders, picked once — every rename below targets one of them.
    let mine = k.binders();
    // **Both directions.** A bound relates position `i` to position `i` whichever way it was
    // drawn, so which side a kind was recorded on says nothing about whether its binders
    // correspond to this one's. (Unlike [`FunKindVar::binder_kind`], where the direction is
    // the whole point: an upper bound is a *demand*, so it says what a position must satisfy
    // rather than what reached it.)
    let mut stack: Vec<(crate::ccl::ty::FunKind, usize)> = k
        .lower()
        .into_iter()
        .chain(k.upper())
        .map(|l| (l, 0))
        .collect();
    let mut offset = 0;
    for src in k.built_over() {
        let n = src.arity().unwrap_or(0);
        stack.push((src, offset));
        offset += n;
    }
    // **One hop.** A correspondence is what the relations *this* kind is in state, and
    // nothing further: composition across a chain belongs to the walk, which crosses each
    // kind in turn and composes that kind's own correspondence as it goes.
    //
    // Flattening the chain into one map states true things about binders several hops away —
    // and a binder that far off may be *owned* elsewhere, by a written sum whose occurrences
    // also sit outside whatever region a caller is rewriting. Renaming it there is a
    // half-finished α-conversion. Restricting to one hop is what keeps the map applicable
    // wherever the correspondence holds rather than only at the one position that happens to
    // scope over every name in it.
    while let Some((below, at)) = stack.pop() {
        for (i, w) in below.named_binders().iter().enumerate() {
            if at + i >= arity {
                break;
            }
            let Some(mine) = mine.get(at + i) else {
                break;
            };
            if w.id() != mine.id() {
                hop = hop.extended_witness_rename(w.id(), mine.id());
            }
        }
    }
    // **A binder shadows the accumulated substitution below the function that binds it**,
    // exactly as the Pi binder does on the codomain. An outer entry keyed on one of `mine`
    // says how this binder is spelled in a kind it corresponds to, which is a fact about the
    // name outside; below, the name denotes the binder.
    let ids: Vec<crate::ccl::ty::WitnessId> = mine.iter().map(|w| *w.id()).collect();
    Subst::then(&acc.shadow_witnesses(&ids), &hop)
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
        // A witness reference is an ordinary atom: nullary, standing for one candidate
        // without saying which, matching only itself (see [`AtomKey::Witness`]). The
        // range comes from the variable the occurrence carries, so nothing is looked
        // up by name.
        // **A reference arrives spelled in the binders of whatever it flowed into.** The
        // accumulated substitution carries the correspondence each enclosing kind states
        // ([`fun_kind_correspondence`]), so an arm's binder reaching a consumer is the
        // consumer's by the time it lands in a position.
        Type::WitnessRef(w) => {
            let named = match subst_acc.apply_witnesses(ty) {
                Type::WitnessRef(x) => x,
                _ => *w,
            };
            CompactType::from_atom(AtomKey::Witness(named))
        }
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
            fun_kind,
            domain: d,
            codomain: c,
        } => {
            // **The kind's binder correspondence rides the walk from here down**, so an
            // arm's occurrences arrive already spelled in this function's binders.
            let owned_acc = fun_kind_correspondence(fun_kind, subst_acc);
            let subst_acc = &owned_acc;
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
            debug_assert!(
                name.as_ref()
                    .is_none_or(|binder| !refinements_name_binder(&cod, binder)),
                "landing closes: a function's own refinement must reference its binder by index, \
                 not by name"
            );
            // **What the kind states this function binds**, spelled in the binders the walk
            // arrived in. Recovering the list from what landed in the domain instead reads
            // the shape of a position rather than the fact the kind states, and answers a
            // multi-generator comprehension from the arity of its index tuple. Which *name*
            // each position answers to is settled at materialization, where every reference
            // to it has merged (`super::coalesce::named_by_domain`).
            //
            // Substituted for the same reason the domain is: an enclosing kind's
            // correspondence renames a reference in the body, and the binder it refers to
            // moves with it or the function binds a name its body no longer spells.
            //
            // **The kind's children compact here**, at the polarity and under the
            // substitution the walk reached this function with. They are candidate *domains*,
            // so they take the domain's polarity, and a candidate carrying a refinement needs
            // the same accumulated discharges the domain does.
            let binders: Vec<CompactWitness> = fun_kind
                .named_binders()
                .iter()
                .map(|w| {
                    // The binder keeps what it ranges over; only its **name** moves.
                    let id = match subst_acc.apply_witnesses(&Type::WitnessRef(*w.id())) {
                        Type::WitnessRef(x) => x,
                        _ => *w.id(),
                    };
                    CompactWitness {
                        id,
                        type_kind: compact_type_kind(&w.type_kind(), !pol, subst_acc, st),
                    }
                })
                .collect();
            CompactType {
                fun: Some(CompactFun {
                    // **Compute or data, never which index.** A slot carrying binders is a
                    // sum by carrying them; the pin's own sum spelling says the same thing
                    // twice and the two can then disagree.
                    kind: match fun_kind.resolved() {
                        KindPin::Sum(_) => KindPin::Data,
                        other => other,
                    },
                    name: name.clone(),
                    binders,
                    domains_disagree: false,
                    domain: Box::new(dom),
                    combined: None,
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
            history_kind,
        } => {
            let value = compact_go(value, pol, subst_acc, None, st);
            let domain = compact_go(domain, pol, subst_acc, None, st);
            CompactType {
                history_slot: Some((Box::new(value), Box::new(domain), *history_kind)),
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
            // **A variable states a binder correspondence too**, and it is the only thing
            // that states the one a join needs: two conditional arms are two sums recorded
            // below one variable's kind, each spelled in its own binder, and the kind is what
            // puts those binders in correspondence with the position's. Applied on the way
            // in, exactly as a function's own kind is, so every bound below arrives spelled
            // in the position's binders.
            let owned_acc = fun_kind_correspondence(
                &crate::ccl::ty::FunKind::Var(Rc::clone(&state.fun_kind)),
                subst_acc,
            );
            let subst_acc = &owned_acc;
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
            let type_kinds = s.type_kinds.clone();
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
                    // A sum is a shape: it is what the position *is*, and it
                    // determines the position as much as an atom does.
                    // Not shape. These are carried across the fallback explicitly
                    // below, rather than deciding whether it fires.
                    vars: _,
                    refinements: _,
                    kinds: _,
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
            // The variable's kinding constraints join its identity: they are facts
            // about what this position resolves to, and coalesce reads them there.
            for k in type_kinds {
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
    use crate::ccl::infer::solver::{CoalesceError, coalesce_compact};
    use crate::ccl::{BaseType, Refinement, TypedExpr};

    /// The landing-closes check asks whether a refinement holds a **free**
    /// reference to the function's binder. A predicate that binds the same
    /// spelling itself holds none, so the check must not fire on it — the
    /// distinction a walk without a scope cannot make.
    #[test]
    fn a_predicate_binding_the_binder_s_spelling_holds_no_free_reference() {
        let binder = Name::raw("x");
        // `λ x → x`: the reference resolves to the predicate's own binder.
        let refined = |p: TypedExpr| CompactType {
            refinements: Some(RefinementSet::from_iter([Refinement::born(Rc::new(p))])),
            ..Default::default()
        };
        let shadowed = refined(TypedExpr::lambda(
            binder.clone(),
            Type::Base(BaseType::Int),
            TypedExpr::var(binder.clone()),
        ));
        assert!(
            !refinements_name_binder(&shadowed, &binder),
            "a binder the predicate introduces is not a reference to the function's"
        );

        // The same spelling, unbound: a genuine free reference.
        let free = refined(TypedExpr::var(binder.clone()));
        assert!(
            refinements_name_binder(&free, &binder),
            "a free reference by name is what the invariant forbids"
        );
    }

    /// **A refinement is part of a data domain, so a join may not acquire one.** The
    /// contravariant meet a `fun` slot's domain takes *unions* refinements, so a domain
    /// carrying a filter and one carrying none merge to the filtered domain — and the joined
    /// collection then denotes rows filtered by a predicate only one side owed. That is the
    /// wrong-answer half of the losslessness `FunKind::Data` exists to enforce.
    ///
    /// Reported as a domain conflict rather than by dropping the refinement, which is the
    /// other wrong answer: it loses a filter the program wrote.
    ///
    /// A distinct domain *shape* needs no test here — it survives the meet as two denoted
    /// domains and the guard already counts it. A refinement is the case the meet *resolves*,
    /// which is why it has to be compared before merging.
    #[test]
    fn a_data_join_does_not_acquire_one_sides_domain_refinement() {
        let filtered_domain = CompactType {
            refinements: Some(RefinementSet::one(Refinement::born(Rc::new(
                TypedExpr::lit(crate::ccl::Lit::Bool(true)),
            )))),
            ..CompactType::from_atom(AtomKey::UIntRange(2))
        };
        let data_fun = |domain: CompactType| CompactType {
            fun: Some(CompactFun {
                binders: Vec::new(),
                name: None,
                kind: KindPin::Data,
                domains_disagree: false,
                domain: Box::new(domain),
                combined: None,
                codomain: Box::new(CompactType::from_atom(AtomKey::Prim(BaseType::Int))),
            }),
            ..Default::default()
        };
        // Positive polarity: the join a conditional's two arms build.
        let merged = CompactType::merge(
            true,
            data_fun(filtered_domain),
            data_fun(CompactType::from_atom(AtomKey::UIntRange(2))),
        );
        assert!(
            merged.fun.expect("fun slot present").domains_disagree,
            "a data join must not acquire a refinement only one side carried"
        );
    }

    /// The control: two data functions over the *same* refined domain join without
    /// conflict. The rule is about a refinement one side lacks, not about refinements.
    #[test]
    fn a_data_join_over_one_refined_domain_is_fine() {
        let refined = || CompactType {
            refinements: Some(RefinementSet::one(Refinement::born(Rc::new(
                TypedExpr::lit(crate::ccl::Lit::Bool(true)),
            )))),
            ..CompactType::from_atom(AtomKey::UIntRange(2))
        };
        let data_fun = |domain: CompactType| CompactType {
            fun: Some(CompactFun {
                binders: Vec::new(),
                name: None,
                kind: KindPin::Data,
                domains_disagree: false,
                domain: Box::new(domain),
                combined: None,
                codomain: Box::new(CompactType::from_atom(AtomKey::Prim(BaseType::Int))),
            }),
            ..Default::default()
        };
        let merged = CompactType::merge(true, data_fun(refined()), data_fun(refined()));
        assert_eq!(merged.fun.expect("fun slot present").kind, KindPin::Data);
    }

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

    /// A function slot of `kind` over one record domain with `fields`.
    fn fun_over(kind: KindPin, fields: &[&str]) -> CompactType {
        let int = || CompactType::from_atom(AtomKey::Prim(BaseType::Int));
        let mut rec = BTreeMap::new();
        for f in fields {
            rec.insert(FieldKey::Name(SmolStr::from(*f)), int());
        }
        CompactType {
            fun: Some(CompactFun {
                binders: Vec::new(),
                name: None,
                kind,
                domains_disagree: false,
                domain: Box::new(CompactType {
                    rec: Some(rec),
                    ..CompactType::value()
                }),
                combined: None,
                codomain: Box::new(int()),
            }),
            ..CompactType::value()
        }
    }

    fn as_graph(term: CompactType) -> CompactGraph {
        CompactGraph {
            term,
            rec_vars: BTreeMap::new(),
        }
    }

    /// A `Data` bound and two undetermined-kind bounds over distinct domains at
    /// one position: the kinds join to `Data`, so all three domains *are* the
    /// data and no single one of them holds it — every association rejects.
    ///
    /// Reading the kind to pick the domain rule made the association decide
    /// that. An undetermined pair took the contravariant meet, `{a} ⊓ {b}` is
    /// `{a, b}`, and that deduplicated against the data bound's own `{a, b}` —
    /// so one association accepted a collection over `{a, b}` for a join of
    /// three collections over `{a, b}`, `{a}`, and `{b}`.
    #[test]
    fn undetermined_kinds_join_without_deciding_the_domain_rule() {
        let data = fun_over(KindPin::Data, &["a", "b"]);
        let u1 = fun_over(KindPin::Unpinned, &["a"]);
        let u2 = fun_over(KindPin::Unpinned, &["b"]);
        for (x, y, z) in [
            (data.clone(), u1.clone(), u2.clone()),
            (u1.clone(), data.clone(), u2.clone()),
            (u1.clone(), u2.clone(), data.clone()),
        ] {
            let associations = [
                CompactType::merge(
                    true,
                    CompactType::merge(true, x.clone(), y.clone()),
                    z.clone(),
                ),
                CompactType::merge(true, x, CompactType::merge(true, y, z)),
            ];
            for merged in associations {
                let err = coalesce_compact(&as_graph(merged))
                    .expect_err("three distinct data domains have no single join");
                assert!(
                    matches!(err, CoalesceError::DomainJoinConflict { .. }),
                    "expected a domain-join conflict; got {err:?}"
                );
            }
        }
    }

    /// Two undetermined-kind bounds over distinct domains still join: the merge keeps the
    /// kind unpinned, and the resolved kind's rule — here the capability default nothing
    /// pinned away from — applies once at coalesce, meeting the domains contravariantly.
    #[test]
    fn two_undetermined_kinds_join_to_a_capability_over_the_met_domain() {
        let merged = CompactType::merge(
            true,
            fun_over(KindPin::Unpinned, &["a"]),
            fun_over(KindPin::Unpinned, &["b"]),
        );
        assert_eq!(
            merged.fun.as_ref().map(|f| f.kind.clone()),
            Some(KindPin::Unpinned),
            "an unpinned kind stays unpinned through the merge"
        );
        let ty = coalesce_compact(&as_graph(merged)).expect("the domains meet");
        let Type::Fun {
            fun_kind, domain, ..
        } = &ty
        else {
            panic!("expected a function; got {ty}");
        };
        assert_eq!(*fun_kind, crate::ccl::ty::FunKind::Compute);
        assert_eq!(
            *domain,
            Box::new(Type::Record(vec![
                ("a".to_string(), Type::Base(BaseType::Int)),
                ("b".to_string(), Type::Base(BaseType::Int)),
            ])),
            "the met domain is the union of the two records' fields"
        );
    }

    /// The merge is commutative under `CompactType`'s own equality, including once
    /// a positive join has accumulated two domain alternatives. Appending them into
    /// a `Vec` broke this: `CompactFun`'s derived `PartialEq` compares positionally,
    /// so the two arrival orders produced unequal slots — and structural equality is
    /// load-bearing where types are identities.
    #[test]
    fn a_positive_join_of_two_domains_is_order_insensitive() {
        let fun = |dom: BaseType| CompactType {
            fun: Some(CompactFun {
                binders: Vec::new(),
                name: None,
                kind: KindPin::Data,
                domains_disagree: false,
                domain: Box::new(CompactType::from_atom(AtomKey::Prim(dom))),
                combined: None,
                codomain: Box::new(CompactType::from_atom(AtomKey::Prim(BaseType::Int))),
            }),
            ..CompactType::value()
        };
        let a = fun(BaseType::Int);
        let b = fun(BaseType::String);
        let ab = CompactType::merge(true, a.clone(), b.clone());
        let ba = CompactType::merge(true, b, a);
        assert_eq!(
            ab, ba,
            "the merged slot does not depend on which arrived first"
        );
        // Two *plain* collections over distinct domains have no join: entering a sum is a
        // term, so nothing here builds one (`design/type-inference.md`, "Only a term
        // builds a sum"). What the order-insensitivity claim protects is that the
        // rejection is the same rejection either way.
        for merged in [ab, ba] {
            let err = coalesce_compact(&as_graph(merged))
                .expect_err("two distinct data domains have no single join");
            assert!(
                matches!(err, CoalesceError::DomainJoinConflict { .. }),
                "expected a domain-join conflict; got {err:?}"
            );
        }
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
            fun_kind: FunKind::Data(None),
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
            "an α-variant merge must be arrival-order-independent"
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
            fun_kind: FunKind::Data(None),
            domain: Box::new(Type::UIntRange(3)),
            codomain: Box::new(Type::Fun {
                name: Some(Name::raw("y")),
                fun_kind: FunKind::Data(None),
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

#[cfg(test)]
mod refinement_slot_tests {
    use super::*;

    /// The two contributions that are not values carry no refinement slot, and the
    /// checker accepts them: a hole imposes nothing and a bare variable's whole
    /// content is its identity.
    #[test]
    fn a_hole_and_a_bare_variable_need_no_refinement_slot() {
        assert!(refinement_slot_present(&CompactType::empty()));
        assert!(refinement_slot_present(&CompactType::from_var(InferVarId(
            0
        ))));
    }

    /// The violation the post-condition exists for, which no test program
    /// reaches and nothing in the type system forbids: content with the slot
    /// absent, which merges as the identity and absorbs a sibling's refinements.
    #[test]
    fn content_without_a_refinement_slot_is_rejected() {
        let bad = CompactType {
            refinements: None,
            ..CompactType::from_atom(AtomKey::Prim(BaseType::Int))
        };
        assert!(!refinement_slot_present(&bad));
        assert!(refinement_slot_present(&CompactType::from_atom(
            AtomKey::Prim(BaseType::Int)
        )));
    }

    /// Nested, so a violation below the root is caught: the walk builds every
    /// payload from the same arms.
    #[test]
    fn a_violation_below_the_root_is_rejected() {
        let bad = CompactType {
            refinements: None,
            ..CompactType::from_atom(AtomKey::Prim(BaseType::Int))
        };
        let outer = CompactType {
            rec: Some([(FieldKey::Index(0), bad)].into_iter().collect()),
            ..CompactType::value()
        };
        assert!(!refinement_slot_present(&outer));
    }
}
